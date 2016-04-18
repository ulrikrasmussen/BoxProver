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
import           Data.Text.Encoding (encodeUtf8)
import           Data.Text.Lazy (toStrict)
import qualified Data.Time as Time
import qualified Data.Vector as V
import           Snap.Core
import           Snap.Http.Server
import           Snap.Util.FileServe
import           System.Console.GetOpt
import           System.Exit
import           System.IO
import           Text.Blaze.Renderer.Text

import           LinearProof
import qualified RenderData as RD
import           RenderHtml
import           Syntax
import           TwelfInterface

data CustomConfig = CustomConfig
                    { twelfBinPath :: Maybe String
                    , baseSigPath :: Maybe String
                    , checkLogPath :: Maybe String
                    }
                    deriving (Eq, Show)

emptyCustomConfig :: CustomConfig
emptyCustomConfig = CustomConfig { twelfBinPath = Nothing
                                 , baseSigPath = Nothing
                                 , checkLogPath = Nothing
                                 }

combineCustomConfig :: CustomConfig -> CustomConfig -> CustomConfig
combineCustomConfig c1 c2 =
  CustomConfig { twelfBinPath = twelfBinPath c2 <|> twelfBinPath c1
               , baseSigPath  = baseSigPath c2  <|> baseSigPath c1
               , checkLogPath = checkLogPath c2 <|> checkLogPath c1
               }

options :: (MonadSnap m) => [OptDescr (Maybe (Config m CustomConfig))]
options =
  optDescrs emptyConfig ++
  [ Option [] ["twelf-server"] (ReqArg setTS "PATH") "path to twelf-server binary"
  , Option [] ["base-sig"] (ReqArg setBS "PATH") "path to base signature definition"
  , Option [] ["check-log"] (OptArg setCP "PATH") "path to check request log"
  ]
  where
    setBS p = Just $ setOther (emptyCustomConfig { baseSigPath = Just p }) emptyConfig
    setTS p = Just $ setOther (emptyCustomConfig { twelfBinPath = Just p }) emptyConfig
    setCP p = Just $ setOther (emptyCustomConfig { checkLogPath = p }) emptyConfig

getTwelfBinPath :: (MonadReader CustomConfig m) => m String
getTwelfBinPath = asks (fromJust . twelfBinPath)

getBaseSigPath :: (MonadReader CustomConfig m) => m String
getBaseSigPath = asks (maybe "fitch.elf" id . baseSigPath)

getCheckLogPath :: (MonadReader CustomConfig m) => m (Maybe String)
getCheckLogPath = asks checkLogPath

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
          , ("export", exportHandler)
          ] <|>
    serveDirectory "./frontend"

logProof :: BS.ByteString -> ReaderT CustomConfig Snap ()
logProof proof = do
  mp <- getCheckLogPath
  flip (maybe (return ())) mp $ \p -> do
    req <- getRequest
    let remoteAddr = rqRemoteAddr req
    t <- liftIO Time.getCurrentTime
    liftIO $ BS.appendFile p $ BS.concat [
        "["
      , remoteAddr
      , " - "
      , fromString $ show t
      , "]\n"
      , proof
      , "\n\n"
      ]

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
  logProof proof
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
              , let opt@(Open hs (_, sq)) = convertOpenProofTerm a m
              , let sequentmarkup = renderMarkup $ renderOpen renderSequent (Open hs sq)
              , let linearProof = linearize $ opt
              , let proofmarkup = renderMarkup $ render linearProof
              ])
        ]

exportHandler :: ReaderT CustomConfig Snap ()
exportHandler = do
  proof <- readRequestBody (42 * 1024)
  modifyResponse $ setHeader "Content-Type" "text/plain"
  bin <- getTwelfBinPath
  fitch <- getBaseSigPath
  proofDecoded <- maybe (error "url decode error") return $ urlDecode $ BL.toStrict $ proof
  checkResult <- liftIO $ check bin fitch (BS.unpack $ proofDecoded)
  case checkResult of
    Left err -> writeBS $ "Error: " `BS.append` (fromString err)
    Right (_resp, defns) ->
      forM_ defns $ \(_n, a, m) ->
        let opt@(Open _hs (_, sq)) = convertOpenProofTerm a m
            OpenLineProof _ frags = linearize opt
        in case RD.renderLinearProof sq frags of
             Left err -> writeBS $ "Error: " `BS.append` (fromString err)
             Right txt -> writeBS $ encodeUtf8 $ txt
