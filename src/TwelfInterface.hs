module TwelfInterface where

import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M

import           Language.Twelf.IntSyn
import           Language.Twelf.Parser
import           Language.Twelf.Reconstruct
import           Language.Twelf.TwelfServer

checkDecl :: String -> String -> String -> IO (Either String String)
checkDecl twelfServer fitchPath declString = withTwelfServer twelfServer False $ do
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

{-
example :: IO ()
example = do
  h <- openFile "examples.elf" ReadMode
  declString <- hGetContents h
  _ <- checkProof bin declString
  (_,_,m) <- extractProof "/home/ulrik/twelf/bin/twelf-server" declString
  let lp = linearize $ convertOpenProofTerm m
  putStrLn $ renderMarkup $ render lp
-}
