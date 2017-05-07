{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Concurrent (threadDelay)
import Control.Exception hiding (TypeError)
import Control.Monad
import Data.Char
import Data.Map (Map)
import Data.Monoid
import Dhall
import Dhall.Core
import Dhall.Parser
import Dhall.Import
import Dhall.TypeCheck
import qualified Data.Map as Map
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
import System.Directory
import System.FilePath
import System.FSNotify
import Text.Trifecta.Delta (Delta(..))

import Debug.Trace


-- | A dhall type, e.g. "entry" for "file.entry.dh"
-- Should only contain lower-case strings.
newtype DhallType = DhallType String
  deriving (Eq, Ord, Show)

-- | Turn a string into a 'DhallType'.
-- >>> dhallType "Entry"
-- DhallType "entry"
dhallType :: String -> DhallType
dhallType = DhallType . map toLower

-- | Get the 'DhallType' for a file.
-- >>> dhallTypeOf "file.entry.dh"
-- DhallType "entry"
dhallTypeOf :: FilePath -> DhallType
dhallTypeOf f =
  case takeExtension . dropExtension $ f of
    "" -> throw $ WithoutType f
    (_:xs) -> DhallType . map toLower $ xs


data CheckException
  = CouldntFindTypeDefs
  | ParseException FilePath ParseError
  | UnknownType FilePath DhallType
  | WithoutType FilePath
  | TypeChecking FilePath (TypeError Src)
  deriving (Show)

instance Exception CheckException where
  displayException CouldntFindTypeDefs =
    "Error: Expected a .dhall file with type definitions, but couldn't find it."
  displayException (UnknownType f (DhallType t)) =
    "Error: The file " ++ f ++ "has an unknown type: " ++ t
  displayException (ParseException f pe) =
    "While parsing " ++ f ++ ":" ++ displayException pe
  displayException (TypeChecking f te) =
    "While type checking " ++ f ++ ":" ++ displayException te
  displayException (WithoutType f) =
    "The file " ++ f ++ " seems to have no type associated with it."


main :: IO ()
main = do
  here <- getCurrentDirectory
  printExceptions $ do
    typedefs <- allTypeDefs here
    dhallfiles <- allDhallFiles here
    forM_ dhallfiles $ printExceptions . checkFile typedefs
    putStrLn "Watching for changes.."
    withManager $ \mgr -> do
      watchTree mgr here isDhallFile $ \event -> do
        case event of
          Added f utc -> do
            putStrLn $ "\nAdded: " ++ f
            printExceptions $ do
              expr <- loadFile f
              checkFile typedefs (f, expr)
              putStrLn "No errors."
          Modified f utc -> do
            putStrLn $ "\nModified: " ++ f
            printExceptions $ do
              expr <- loadFile f
              checkFile typedefs (f, expr)
              putStrLn "No errors."
          Removed f utc -> pure ()
      forever $ threadDelay 1000000
  where
    -- | Print 'CheckException's and recover.
    printExceptions comp = do
      result <- try comp
      case result of
        Left e -> putStrLn $ displayException (e :: CheckException)
        Right v -> pure v

    isDhallFile f = (flip elem [".dhall", ".dh"] . takeExtension . eventPath) f
                 && (not . (==) '.' . head . takeFileName . eventPath) f


-- | A list of all files in a directory with the one of the given extensions,
-- using absolute paths.
--
-- >>> allFiles "/home/user" [".hs"]
-- ["/home/user/project/Main.hs", ...]
allFiles :: Foldable t => FilePath -> t String -> IO [FilePath]
allFiles dir exts = do
  setCurrentDirectory dir
  files <- mapM makeAbsolute =<< listDirectory dir
  inThisDir <- flip filterM files $ \f -> do
    exists <- doesFileExist f
    let valid = takeExtension f `elem` exts
    pure $ exists && valid
  subdirs <- filterM doesDirectoryExist files
  inSubDirs <- forM subdirs $ \d -> do
    allFiles (dir </> d) exts
  pure $ inThisDir ++ concat inSubDirs


-- | Get all type definitions in the ".dhall" directory of a given directory
-- and return them in a map of filename without ".dht" -> expression in file.
allTypeDefs :: FilePath -> IO (Map DhallType (Expr Src X))
allTypeDefs dir = do
  isThere <- doesDirectoryExist (dir </> ".dhall")
  when (not isThere) $ do
    throwIO CouldntFindTypeDefs
  files <- allFiles (dir </> ".dhall") [".dht"]
  exprs <- forM files $ \f -> do
    let name = dhallType $ takeFileName $ dropExtension f
    sequence (name, loadFile f)
  pure $ Map.fromList exprs


-- | Get all a list of all dhall files in the given directory using absolute paths.
allDhallFiles :: FilePath -> IO [(FilePath, Expr Src X)]
allDhallFiles dir = do
  files <- allFiles dir [".dh", ".dhall"]
  forM files $ \f -> do
    sequence (f, loadFile f)


-- | Compile a dhall file.
loadFile :: FilePath -> IO (Expr Src X)
loadFile f = do
  let delta = Directed "(input)" 0 0 0 0
  content <- TLIO.readFile f
  case exprFromText delta content of
    Left e -> throwIO $ ParseException f e
    Right e -> do
      setCurrentDirectory (takeDirectory f)
      load e


-- | Typecheck a single file against one of the given types.
-- Throws an exception on failure to do so.
--
-- >>> checkFile (Map.fromList [("conf", .. )]) ("file.conf.dh", ..)
-- /throws/ TypeChecking "file.conf.dh" (TypeError ..)
checkFile :: Map DhallType (Expr Src X) -> (FilePath, Expr Src X) -> IO ()
checkFile types (f, expr) = do
  let name = dhallTypeOf f
  case Map.lookup name types of
    Nothing -> do
      throwIO $ UnknownType f name
    Just t -> do
      let annot = case (expr, t) of
            (Note (Src begin1 end1 bytes1) _, Note (Src begin2 end2 bytes2) _) ->
              Note (Src begin1 end1 bytes') (Annot expr t)
              where
                bytes' = bytes1 <> "\n\n : \n\n" <> bytes2
            _ -> Annot expr t
      case typeOf annot of
        Left err -> throwIO $ TypeChecking f err
        Right _ -> pure ()
