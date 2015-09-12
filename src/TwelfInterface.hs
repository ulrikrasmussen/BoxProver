{-# LANGUAGE FlexibleContexts #-}
module TwelfInterface where

import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Except
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Typeable
import qualified Data.Map as M
import           System.IO
import           System.IO.Temp

import qualified Language.Twelf.AST as AST
import           Language.Twelf.IntSyn
import           Language.Twelf.Parser
import           Language.Twelf.Reconstruct
import           Language.Twelf.TwelfServer

checkDecls :: String -> String -> String -> IO (Either String String)
checkDecls twelfServer fitchPath declString = withTwelfServer twelfServer False $ do
  (fitchResp, loadSucceeded) <- runTwelfCmd' $ "loadFile " ++ fitchPath
  if not loadSucceeded then
      return . Left . concat $ [
                  "An error occurred while loading Fitch definition:\n",
                  fitchResp,
                  "\n"]
    else do
      (resp, declSucceeded) <- runTwelfCmd' $ "readDecl\n" ++ declString
      return $ if declSucceeded then Right resp else Left resp

extractDecl :: String -> String -> String -> IO (ConstName, A, M)
extractDecl twelfServer fitchPath declString = do
  fitchSigText <- T.readFile fitchPath
  let Right (ds, ps) = parseSig initParserState fitchPath fitchSigText
  case parseDecl ps "<proof declaration>" (T.pack declString) of
    Left err -> error $ show err
    Right (d, _) -> withTwelfServer twelfServer False $ do
      _ <- reconstruct ds
      [(_, DDefn n a m)] <- M.toList <$> extract [d]
      return (n, a, m)

isDefn :: AST.Decl -> Bool
isDefn (AST.DDefn _ _ _ _) = True
isDefn _ = True

test :: (MonadIO m, MonadMask m) => TwelfMonadT m (Either String String)
test = runExceptT $ do
         lift $ runTwelfCmd "help"

defnName :: Decl -> String
defnName (DDefn n _ _) = n
defnName _ = error "Not a definition"

convertDefn :: AST.Decl -> AST.Decl -> (String, A, M)
convertDefn (AST.DDefn _ n ta tm) (AST.DDefn _ _ ta' tm')
            = (n
              ,inferImplicitA ta $ toType M.empty ta'
              ,inferImplicitM tm $ toTerm M.empty tm')
convertDefn _ _ = error "Not a definition"

data CheckException = CheckException String
  deriving (Show, Typeable)

instance Exception CheckException

checkException :: (MonadThrow m) => String -> m a
checkException = throwM . CheckException

getFullDefn :: (MonadThrow m, MonadIO m)
            => AST.Decl -> TwelfMonadT m (String, A, M)
getFullDefn astDecl@(AST.DDefn _ n _ _) = do
  _ <- runTwelfCmd "set Print.implicit true"
  fullDeclStr <- runTwelfCmd $ "decl " ++ n ++ "\n"
  let fullDeclResult = parseDecl initParserState "<twelf process>" (T.pack fullDeclStr)
  astFullDecl <- either (checkException . show) (return . fst) fullDeclResult
  return $ convertDefn astDecl astFullDecl
getFullDefn _ = error "Not a definition"

check' :: (MonadMask m, MonadIO m) => String -> String -> TwelfMonadT m (String, [(String, A, M)])
check' fitchPath declString = do
  (fitchResp, fitchSucceeded) <- runTwelfCmd' $ "loadFile " ++ fitchPath
  when (not fitchSucceeded) $ checkException $ concat $
           [ "An error occurred while loading Fitch definition:\n"
           , fitchResp
           , "\n" ]
  -- Twelf succeeded. Assume that our own parser can parse the Fitch signature.
  -- We need the parser state to correctly parse with fixity information.
  fitchSig <- liftIO $ T.readFile fitchPath
  fitchParserState <- either (checkException . show) (\(_, ps) -> return ps)
     $ parseSig initParserState "Fitch signature" fitchSig
  -- Parse the user-provided signature. For now, we only accept term definitions.
  let sigResult = parseSig fitchParserState "<BoxProver input>" (T.pack declString)
  astDefs <- either
               (checkException . show)
               (\(ds,_) -> if any (not . isDefn) ds then
                               checkException "Signature may only contain definitions."
                           else
                               return ds)
               sigResult
  -- Load the file into Twelf and reconstruct all types and implicit parameters.
  withSystemTempFile "twelf-input" $ \tmpPath h -> do
    liftIO $ (hPutStr h declString >> hFlush h)
    (declResp, declSucceeded) <- runTwelfCmd' $ "loadFile " ++ tmpPath
    when (not declSucceeded) $ checkException declResp
    defns <- forM astDefs getFullDefn
    return (declResp, defns)

check :: (MonadMask m, MonadIO m)
      => String -> String -> String -> m (Either String (String, [(String, A, M)]))
check twelfServer fitchPath declString =
    catch
      (withTwelfServer twelfServer False $ do
       res <- check' fitchPath declString
       return . Right $ res)
      (\(CheckException err) -> return . Left $ err)
