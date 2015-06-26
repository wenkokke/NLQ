{-# LANGUAGE OverloadedStrings, FlexibleContexts, PartialTypeSignatures, TupleSections, RecordWildCards, ScopedTypeVariables #-}
module Main where


import           Prelude hiding (lex)
import           Control.Exception (IOException, handle)
import           Control.Monad (forM,forM_,when,unless)
import           Data.List (stripPrefix)
import           Data.List.Split (splitOn)
import           Data.Map (Map)
import           Data.Maybe (fromMaybe,maybe)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Void (Void)
import           System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import           System.Directory (renameFile,doesFileExist,getDirectoryContents,createDirectoryIfMissing)
import           System.Environment (getProgName,getArgs,getEnv)
import           System.Exit (ExitCode(..), exitSuccess, exitFailure)
import           System.FilePath (takeBaseName,dropExtension,(</>),(<.>),(-<.>))
import           System.IO
import           System.Process
import qualified Text.Parsec as P (parse)
import           Text.Printf (printf)

import           CG.Prover
import           CG.Parser
import           CG.Base hiding (Term)
import           CG.Parsing
import           CG.ToAgda


descInstalled :: FilePath -> IO ()
descInstalled dir = do
  let
    readDesc :: FilePath -> IO (Maybe String)
    readDesc f =
      handle (\(e :: IOException) -> return Nothing)
      (stripPrefix "-- " . T.unpack <$> withFile f ReadMode T.hGetLine)

  filesAndDirectories <- getDirectoryContents dir
  forM_ filesAndDirectories $ \fileOrDirectory -> do
    isFile <- doesFileExist (dir </> fileOrDirectory)
    when isFile $ do
      mbDesc <- readDesc (dir </> fileOrDirectory)
      case mbDesc of
       Nothing   -> return ()
       Just desc -> do
         putStrLn (printf "%s%-32s  %s" (replicate 19 ' ') fileOrDirectory desc)



main :: IO ()
main = do

  args <- getArgs

  let (actions, _, _) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTasks   = tasks
              , optLexicon = mbLexicon
              , optSystem  = sys@System{..}
              , optOutput  = out
              , optGoal    = g
              , optDepth   = d
              , optVerbose = verbose
              } = opts

  let
    mbHandles :: IO (Maybe Handle, Maybe Handle)
    mbHandles =
      if verbose then return (Nothing, Nothing)
      else do f <- openFile "/dev/null" AppendMode; return (Just f, Just f)

    -- run a command
    runCommand :: String -> [String] -> Maybe FilePath -> IO ()
    runCommand cmd args dir = do
      putStrLn (showCommandForUser cmd args)
      (mbOut,mbErr) <- mbHandles
      p <- runProcess cmd args dir Nothing Nothing mbOut mbErr
      e <- waitForProcess p
      case e of
       ExitSuccess   -> return ()
       ExitFailure r -> error ("Error in `"++cmd++"' (exit "++show r++")")

    -- use the given lexicon, otherwise read the default lexicon
    givenOrDefaultLexicon :: IO (Map String (Term ConId Void))
    givenOrDefaultLexicon = case mbLexicon of
      Just lx -> return lx
      Nothing -> do hPutStrLn stderr "Reading default lexicon..."; readLexicon "default"


  when (null tasks)
       (putStrLn "Usage: For basic information, try the `--help' option.")

  let
    runTask :: Task -> IO [Result]
    runTask (Solve str) = case P.parse judgement "" str of
      Left  e -> error (show e)
      Right g -> return $ map (uncurry Solved) (solve sys d [g])
    runTask (Parse sent expr) = do
      lx <- givenOrDefaultLexicon
      return (map (uncurry $ Parsed sent expr) (parse sys d lx sent g))

  proofs <- concat <$> mapM runTask tasks

  let
    generateAgda :: Maybe FilePath -> IO [FilePath]
    generateAgda  Nothing  = writeAgdaFile stdout "Main" sys proofs g
    generateAgda (Just fn) = withFile fn WriteMode (\h -> writeAgdaFile h (takeBaseName fn) sys proofs g)

    generateLaTeX :: Maybe FilePath -> IO [FilePath]
    generateLaTeX targetDir = do
      home <- fromMaybe "." <$> getCgHome

      let mainFile = home </> "Main.agda"
      createDirectoryIfMissing True home
      fileList    <- withFile mainFile WriteMode (\h -> writeAgdaFile h "Main" sys proofs g)

      agdaInclude <- map ("-i"++) . (home:) . splitOn ":" <$> getEnv "AGDA_PATH"
      let args = "--compile" : "--compile-dir" : home : agdaInclude ++ [mainFile]

      runCommand "agda" args (Just home)
      runCommand (dropExtension mainFile) [] targetDir

      return fileList

    generatePNG :: Maybe FilePath -> IO [FilePath]
    generatePNG mbDir = do

      let targetDir = fromMaybe "." mbDir
      home <- fromMaybe "." <$> getCgHome
      latexFiles <- generateLaTeX (Just home)

      forM_ latexFiles $ \latexFile -> do

        putStrLn ("Processing `"++latexFile++"'...")

        contents <- readFile (home </> latexFile <.> "tex")
        writeFile (home </> latexFile <.> "standalone_tex") . unlines $
          [ "\\documentclass[preview,border={10pt 10pt 50pt 10pt}]{standalone}"
          , preamble
          , "\\begin{document}"
          , contents
          , "\\end{document}"
          ]

        let args1 = ["-shell-escape"
                    ,"-output-directory",home
                    ,latexFile <.> "standalone_tex"]
        runCommand "pdflatex" args1 (Just home)

        let args2 = ["-density","300"
                    ,home </> latexFile <.> "pdf"
                    ,"-quality","90"
                    ,home </> latexFile <.> "png"]
        runCommand "convert" args2 (Just home)

        renameFile (home </> latexFile <.> "png") (targetDir </> latexFile <.> "png")

      return latexFiles

  case out of
    StdOut         -> mapM_ printResult proofs
    AgdaFile fn -> do maybe (return ()) checkFile fn; generateAgda fn; return ()
    LaTeX    mb -> do generateLaTeX mb >>= mapM_ (putStrLn . (<.> "tex"))
    PNG      mb -> do generatePNG mb >>= mapM_ (putStrLn . (<.> "png"))


-- * Command-Line Options

data Task
  = Solve String
  | Parse String [String]

data Output
  = StdOut                    -- ^ Print proofs to the standard output.
  | AgdaFile (Maybe FilePath) -- ^ Convert proofs to an Agda program and print it.
  | LaTeX    (Maybe FilePath) -- ^ Convert proofs to LaTeX files.
  | PNG      (Maybe FilePath) -- ^ Convert proofs to PNG files.

data Options = Options
  { optTasks      :: [Task]
  , optLexicon    :: Maybe (Map String (Term ConId Void))
  , optSystem     :: System ConId
  , optOutput     :: Output
  , optGoal       :: Term ConId Void
  , optDepth      :: Int
  , optVerbose    :: Bool
  }

defaultOptions :: Options
defaultOptions    = Options
  { optTasks      = []
  , optLexicon    = Nothing
  , optSystem     = error "System must be specified."
  , optOutput     = StdOut
  , optGoal       = Con (NegAtom "s") []
  , optDepth      = 5
  , optVerbose    = False
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> return opt { optTasks = optTasks opt ++ [Solve arg] }) "SEQUENT")
    "Search for proof of a sequent."

  , Option [] ["parse"]
    (ReqArg (\arg opt -> return opt { optTasks = optTasks opt ++ [Parse arg []] }) "SENTENCE")
    "Parse the given sentence."

  , Option [] ["to","or"]
    (ReqArg addExpected "EXPRESSION")
    "Generate check if the previous test results in this expression."

  , Option "s" ["system"]
    (ReqArg (\arg opt -> do sys <- readSystem arg; return opt { optSystem = sys }) "SYSTEM_FILE")
    "Type-logical system (see below)."

  , Option "d" ["depth"]
    (ReqArg (\arg opt -> return opt { optDepth = read arg }) "SEARCH_DEPTH")
    "Set the search depth. For systems marked as `infinite' only. Defaults to `5'."

  , Option "l" ["lexicon"]
    (ReqArg (\arg opt -> do lex <- readLexicon arg; return opt { optLexicon = Just lex }) "LEXICON_FILE")
    "Lexicon used in parsing. Defaults to `$CGTOOL_HOME/lex/default'."

  , Option "g" ["goal"]
    (ReqArg (\arg opt -> do g <- parseGoal arg; return opt { optGoal = g }) "GOAL_FORMULA")
    "Goal formula for parsing. Defaults to `s⁻'."

  , Option [] ["to-agda"]
    (OptArg (\arg opt -> do return opt { optOutput = AgdaFile arg }) "AGDA_FILE")
    "Produce an Agda module, and write it to the given file (or stdout)."

  , Option [] ["to-latex"]
    (OptArg (\arg opt -> do return opt { optOutput = LaTeX arg }) "DIRECTORY")
    "Produce a TeX file for each proof, and write it to DIRECTORY."

  , Option [] ["to-png"]
    (OptArg (\arg opt -> do return opt { optOutput = PNG arg }) "DIRECTORY")
    "Produce a PNG file for each proof, and write it to DIRECTORY."

  , Option "v" ["verbose"]
    (NoArg (\opt -> return opt { optVerbose = True }))
    "Verbose output."

  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              mbCgHome <- getCgHome
              case mbCgHome of
               Nothing     -> do
                 putStrLn "Warning: `$CGTOOL_HOME' is not set."
                 exitFailure
               Just cgHome -> do
                 hPutStrLn stderr (printf "\nAvailable systems (in `%s')\n" (cgHome </> "sys"))
                 descInstalled (cgHome </> "sys")
                 hPutStrLn stderr (printf "\nAvailable lexicons (in `%s')\n" (cgHome </> "lex"))
                 descInstalled (cgHome </> "lex")
                 exitSuccess
            ))
    "Show help."
  ]



-- * Helper functions

compileAgda :: FilePath -> FilePath -> IO ExitCode
compileAgda dir mainFile = do
  agdaInclude <- map ("-i"++) . (dir:) . splitOn ":" <$> getEnv "AGDA_PATH"
  let args = "--compile" : "--compile-dir" : dir : agdaInclude ++ [mainFile]
  (ext,out,err) <- readProcessWithExitCode "agda" args ""
  case ext of
   ExitSuccess -> return ExitSuccess
   _           -> do hPutStrLn stdout out; hPutStrLn stderr err; return ext

-- |Check if a given file exists, and if so ask for a confirmation
--  for overwriting the file.
checkFile :: FilePath -> IO ()
checkFile fn = do
  fileExists <- doesFileExist fn
  unless fileExists $ do
    hSetBuffering stdout NoBuffering
    putStr (fn ++ " exists. Overwrite? (y/n) ")
    hSetBuffering stdin NoBuffering
    hSetEcho stdin False
    hFlushInput stdin
    answer <- yorn
    when (answer == 'Y') exitSuccess
  where
    hFlushInput hdl = do
      r <- hReady hdl
      when r (hGetChar hdl >> hFlushInput hdl)

    yorn = do
      c <- getChar
      if c == 'Y' || c == 'N' then return c
      else if c == 'y' then return 'Y'
      else if c == 'n' then return 'N'
      else yorn


-- |Print results.
printResult :: Result -> IO ()
printResult (Solved     g p) = do print g; print p
printResult (Parsed s _ g p) = do putStrLn s; print g; print p


-- |Add an expected result to the most recent @Parse@ task.
addExpected :: String -> Options -> IO Options
addExpected expr opt@Options{..} = do
  progName <- getProgName

  when (null optTasks) $
    do putStrLn ("Usage: "++progName++"--parse SENTENCE --to "
                 ++"EXPRESSION [--or EXPRESSION]"); exitFailure

  let lastTask = last optTasks

  unless (isParse lastTask) $
    do putStrLn ("Usage: "++progName++"--parse SENTENCE --to "
                 ++"EXPRESSION [--or EXPRESSION]"); exitFailure

  let (Parse sent exprs) = lastTask
  return opt { optTasks = init optTasks ++ [Parse sent (exprs ++ [expr])]}


-- |Check if given Task is a parse-task with no expected result.
isParse :: Task -> Bool
isParse (Parse _ _) = True
isParse _           = False


-- preamble.tex
preamble :: String
preamble = unlines
  [ "\\usepackage{adjustbox}%"
  , "\\usepackage[labelformat=empty]{caption}%"
  , "\\usepackage{amssymb}%"
  , "\\usepackage{amsmath}%"
  , "\\usepackage{bussproofs}%"
  , "\\usepackage[usenames,dvipsnames]{color}%"
  , "\\usepackage{etoolbox}%"
  , "\\usepackage{mdframed}%"
  , "\\usepackage{pict2e}%"
  , "\\usepackage{picture}%"
  , "\\usepackage{scalerel}%"
  , "\\usepackage{stmaryrd}%"
  , "\\usepackage{textgreek}%"
  , "\\usepackage{ucs}%"
  , "\\usepackage[utf8x]{inputenc}%"
  , "\\usepackage{xifthen}%"
  , ""
  , "\\EnableBpAbbreviations%"
  , ""
  , "\\makeatletter"
  , "\\newcommand{\\pictslash}[2]{%"
  , "  \\vcenter{%"
  , "    \\sbox0{$\\m@th#1\\varobslash$}\\dimen0=.55\\wd0"
  , "    \\hbox to\\wd 0{%"
  , "      \\hfil\\pictslash@aux#2\\hfil"
  , "    }%"
  , "  }%"
  , "}"
  , "\\newcommand{\\pictslash@aux}[2]{%"
  , "    \\begin{picture}(\\dimen0,\\dimen0)"
  , "    \\roundcap"
  , "    \\linethickness{.15ex}"
  , "    \\put(0,#1\\dimen0){\\line(1,#2){\\dimen0}}"
  , "    \\end{picture}%"
  , "}"
  , "\\makeatother"
  , ""
  , "\\newcommand{\\varslash}{%"
  , "  \\mathbin{\\mathpalette\\pictslash{{0}{1}}}%"
  , "}"
  , "\\newcommand{\\varbslash}{%"
  , "  \\mathbin{\\mathpalette\\pictslash{{1}{-1}}}%"
  , "}"
  , "\\newcommand{\\focus}[1]{%"
  , "  \\adjustbox{padding=.4em .15ex .1em .15ex,bgcolor=Cyan}{%"
  , "    \\ensuremath{\\color{white}\\rule[-4pt]{0pt}{14pt}#1}"
  , "  }%"
  , "}"
  , ""
  , "\\newcommand{\\varbox}[1][]{\\ifthenelse{\\isempty{#1}}{\\Box}{\\,[\\,#1\\,]\\,}}"
  , "\\newcommand{\\vardia}[1][]{\\ifthenelse{\\isempty{#1}}{\\Diamond}{\\,\\langle\\,#1\\,\\rangle\\,}}"
  , "\\newcommand{\\varpref}[1]{{}_{#1}}"
  , "\\newcommand{\\varsuff}[1]{{}^{#1}}"
  , "\\newcommand{\\vardown}[1]{\\,\\cdot\\,#1\\,\\cdot\\,}"
  , "\\renewcommand{\\fCenter}{\\mathbin{\\vdash}}"
  ]
