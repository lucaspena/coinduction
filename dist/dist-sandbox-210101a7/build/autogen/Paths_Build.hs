{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_Build (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/lpena/coinduction/.shake/.cabal-sandbox/bin"
libdir     = "/Users/lpena/coinduction/.shake/.cabal-sandbox/lib/x86_64-osx-ghc-8.0.1/Build-0.1.0.0-Ay5HVbPN3JIDZjCL5QYdVY"
datadir    = "/Users/lpena/coinduction/.shake/.cabal-sandbox/share/x86_64-osx-ghc-8.0.1/Build-0.1.0.0"
libexecdir = "/Users/lpena/coinduction/.shake/.cabal-sandbox/libexec"
sysconfdir = "/Users/lpena/coinduction/.shake/.cabal-sandbox/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "Build_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "Build_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "Build_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "Build_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "Build_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
