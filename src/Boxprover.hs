module Main where

import           Control.Monad
import           Control.Monad.Except

import           System.IO
import           System.Exit

import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import           Text.Blaze.Renderer.Pretty

import           Language.Twelf.IntSyn
import           Language.Twelf.Parser
import           Language.Twelf.Reconstruct
import           Language.Twelf.TwelfServer

import           Syntax
import           LinearProof
import           RenderHtml

myProof :: String
myProof = "trivial : proof (A => B $) = top_i ; [x] imp_i _."

checkProof :: String -> String -> IO (Either String ())
checkProof twelfServer declString = withTwelfServer twelfServer False $ do
  (fitchResp, loadSucceeded) <- runTwelfCmd' "loadFile fitch.elf"
  when (not loadSucceeded) $ liftIO $ do
    hPutStrLn stderr "An error occurred while loading Fitch definition."
    hPutStrLn stderr fitchResp
    exitWith (ExitFailure 1)
  (resp, declSucceeded) <- runTwelfCmd' $ "readDecl\n" ++ declString
  return $ if declSucceeded then Right () else Left resp

example1 :: IO ()
example1 = do
  let bin = "/home/ulrik/twelf/bin/twelf-server"
  Right () <- checkProof bin myProof
  (n, a, m) <- extractProof bin myProof
  putStrLn $ "Proof name: " ++ n
  putStrLn $ show a
  putStrLn $ show m

extractProof :: String -> String -> IO (ConstName, A, M)
extractProof twelfServer declString = do
  fitchSigText <- T.readFile "fitch.elf"
  let Right (ds, ps) = parseSig initParserState "fitch.elf" fitchSigText
  case parseDecl ps "<proof declaration>" (T.pack declString) of
    Left err -> error $ show err
    Right (d, _) -> withTwelfServer twelfServer False $ do
      _ <- reconstruct ds
      [(_, DDefn n a m)] <- M.toList <$> extract [d]
      return (n, a, m)

example :: IO ()
example = do
  h <- openFile "examples.elf" ReadMode
  declString <- hGetContents h
  (_,_,m) <- extractProof "/home/ulrik/twelf/bin/twelf-server" declString
  let lp = linearize $ convertOpenProofTerm m
  putStrLn $ renderMarkup $ render lp
