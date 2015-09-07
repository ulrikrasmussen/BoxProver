{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import           Control.Applicative
import           Control.Monad.Reader
import           Data.Aeson
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BL
import           Data.Maybe (isJust, fromJust)
import           Data.String (fromString)
import           Data.Text.Lazy (toStrict)
import qualified Data.Vector as V
import           Snap.Core
import           Snap.Http.Server
import           Snap.Util.FileServe
import           System.Console.GetOpt
import           System.Exit
import           System.IO
import           Text.Blaze.Renderer.Text

import           Syntax
import           TwelfInterface
import           LinearProof
import           RenderHtml

data CustomConfig = CustomConfig
                    { twelfBinPath :: Maybe String
                    , baseSigPath :: Maybe String
                    }
                    deriving (Eq, Show)

emptyCustomConfig :: CustomConfig
emptyCustomConfig = CustomConfig { twelfBinPath = Nothing
                                 , baseSigPath = Nothing
                                 }

combineCustomConfig :: CustomConfig -> CustomConfig -> CustomConfig
combineCustomConfig c1 c2 =
  CustomConfig { twelfBinPath = twelfBinPath c2 <|> twelfBinPath c1
               , baseSigPath = baseSigPath c2 <|> baseSigPath c1
               }

options :: (MonadSnap m) => [OptDescr (Maybe (Config m CustomConfig))]
options =
  optDescrs emptyConfig ++
  [ Option [] ["twelf-server"] (ReqArg setTS "PATH") "path to twelf-server binary"
  , Option [] ["base-sig"] (ReqArg setBS "PATH") "path to base signature definition"
  ]
  where
    setBS p = Just $ setOther (emptyCustomConfig { baseSigPath = Just p }) emptyConfig
    setTS p = Just $ setOther (emptyCustomConfig { twelfBinPath = Just p }) emptyConfig

getTwelfBinPath :: (MonadReader CustomConfig m) => m String
getTwelfBinPath = asks (fromJust . twelfBinPath)

getBaseSigPath :: (MonadReader CustomConfig m) => m String
getBaseSigPath = asks (maybe "fitch.elf" id . baseSigPath)

main :: IO ()
main = do
  config <- extendedCommandLineConfig options combineCustomConfig emptyConfig
  let customConfig = maybe emptyCustomConfig id (getOther config)
  when (not . isJust $ twelfBinPath customConfig) $ do
    hPutStrLn stderr "no path to twelf-server binary specified."
    exitWith $ ExitFailure 1
  simpleHttpServe (config :: Config (ReaderT CustomConfig Snap) CustomConfig)
                  (runReaderT site customConfig)

site :: ReaderT CustomConfig Snap ()
site =
    ifTop (redirect "index.html") <|>
    route [ ("check", checkHandler)
          ] <|>
    serveDirectory "./frontend"

checkHandler :: ReaderT CustomConfig Snap ()
checkHandler = do
  let missingProofResponse = do
        modifyResponse $ setResponseStatus 500 "Internal Server Error"
        writeBS "500 Missing proof text"
        logError "Missing proof text"
        getResponse >>= finishWith
  let writeObj = writeBS . BS.concat . BL.toChunks . encode . object
  mproof <- getParam "proof"
  proof <- maybe missingProofResponse return mproof
  bin <- getTwelfBinPath
  fitch <- getBaseSigPath
  checkResult <- liftIO $ check bin fitch (BS.unpack proof)
  modifyResponse $ setHeader "Content-Type" "application/json"
  case checkResult of
    Left err -> writeObj
                  [ "check" .= Bool False
                  , "output" .= String (fromString err)
                  ]
    Right (resp, defns) ->
      writeObj
        [ "check" .= Bool True
        , "output" .= String (fromString resp)
        , "prooftables" .=
            (Array $ V.fromList
              [ object [
                  "name" .= String (fromString n)
                , "sequent" .= String (toStrict sequentmarkup)
                , "html" .= String (toStrict proofmarkup)
                , "closed" .= Bool (isClosedProof linearProof)
                ]
              | (n, a, m) <- defns
              , let opt@(Open _ (_, sq)) = convertOpenProofTerm a m
              , let sequentmarkup = renderMarkup $ renderSequent sq
              , let linearProof = linearize $ opt
              , let proofmarkup = renderMarkup $ render linearProof
              ])
        ]
