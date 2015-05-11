module Paths_CG (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/pepijn/.cabal/bin"
libdir     = "/Users/pepijn/.cabal/lib/x86_64-osx-ghc-7.10.1/CG_C9MTUyr6bNF3vouKA2PsiE"
datadir    = "/Users/pepijn/.cabal/share/x86_64-osx-ghc-7.10.1/CG-0.1.0.0"
libexecdir = "/Users/pepijn/.cabal/libexec"
sysconfdir = "/Users/pepijn/.cabal/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "CG_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "CG_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "CG_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "CG_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "CG_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
