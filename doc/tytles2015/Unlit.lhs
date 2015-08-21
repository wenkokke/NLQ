> {-# LANGUAGE OverloadedStrings, RecordWildCards, ViewPatterns #-}
> module Main where


> import           Data.Char (isSpace,toLower)
> import           Data.Maybe (fromMaybe)
> import           Data.Text (Text)
> import qualified Data.Text    as T
> import qualified Data.Text.IO as T
> import           System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
> import           System.Environment (getProgName,getArgs)
> import           System.Exit (exitSuccess)
> import           System.IO (hPutStrLn,stderr)


> data Style = BirdTag
>            | LaTeX
>            | OrgMode
>            | Markdown Fence


> data Fence = Tilde
>            | Backtick


> data Options = Options
>   { optKeep  :: Bool  -- ^ Replace non-code with spaces, instead of removing it.
>   , optStyle :: Style -- ^ Style of literate code to replace.
>   }


> main :: IO ()
> main = do
>   args <- getArgs
>   let (actions, _, _) = getOpt Permute options args
>   opts <- foldl (>>=) (return defaultOptions) actions
>   T.interact (unlit opts)


> unlit :: Options -> Text -> Text
> unlit (Options k sty) = let
>
>   dl x = case T.break (=='\n') x of
>     (before, after) -> T.append (strip k before) after
>
>   ss x = if k then x else fromMaybe x (T.stripPrefix " " x)
>
>   in case sty of
>       BirdTag           -> handlePrefix    k ss ">"
>       LaTeX             -> handleOpenClose k id "\\begin{code}" "\\end{code}"
>       OrgMode           -> handleOpenClose k dl "#+BEGIN_SRC"   "#+END_SRC"
>       Markdown Tilde    -> handleOpenClose k dl "~~~"           "~~~"
>       Markdown Backtick -> handleOpenClose k dl "```"           "```"



> handlePrefix :: Bool -> (Text -> Text) -> Text -> Text -> Text
> handlePrefix k f prefix = T.unlines . map helper . T.lines
>   where
>     helper x = case T.stripPrefix prefix x of
>       Just x' -> strip k prefix `T.append` f x'
>       Nothing -> x


> handleOpenClose :: Bool -> (Text -> Text) -> Text -> Text -> Text -> Text
> handleOpenClose k f open close = uptoOpen
>   where
>
>     uptoOpen :: Text -> Text
>     uptoOpen x
>       | T.null after = strip k before
>       | otherwise    = strip k before `T.append`
>                        (
>                          strip k open
>                          `T.append`
>                          uptoClose (f (T.drop (T.length open) after))
>                        )
>       where
>         (before, after) = T.breakOn open x
>
>     uptoClose :: Text -> Text
>     uptoClose x
>       | T.null after = error ("unlit: unterminated " ++ T.unpack open)
>       | otherwise    = before `T.append`
>                        (
>                          strip k close
>                          `T.append`
>                          uptoOpen (f (T.drop (T.length close) after))
>                        )
>       where
>         (before, after) = T.breakOn close x


> strip :: Bool -> Text -> Text
> strip True  str = T.map (\x -> if isSpace x then x else ' ') str
> strip False _   = ""


> defaultOptions :: Options
> defaultOptions = Options
>   { optKeep = False
>   , optStyle = LaTeX
>   }


> options :: [ OptDescr (Options -> IO Options) ]
> options =
>   [ Option [] ["latex"]
>     (NoArg (\opt -> do return opt { optStyle = LaTeX }))
>     "Convert literate code in LaTeX style to code."
>   , Option [] ["bird"]
>     (NoArg (\opt -> do return opt { optStyle = BirdTag }))
>     "Convert literate code in Bird style to code."
>   , Option [] ["org-mode"]
>     (NoArg (\opt -> do return opt { optStyle = OrgMode }))
>     "Convert literate code in Org mode to code."
>   , Option [] ["markdown"]
>     (ReqArg (\arg opt -> do return opt { optStyle = Markdown (parseFence arg) }) "FENCE_TYPE")
>     "Convert literate code in Markdown style to code."
>   , Option "k" ["keep"]
>     (NoArg (\opt -> do return opt { optKeep = True }))
>     "Keep non-code as white space."
>   , Option "h" ["help"]
>     (NoArg  (\_ -> do
>                 prg <- getProgName
>                 hPutStrLn stderr (usageInfo prg options)
>                 exitSuccess
>            ))
>    "Show help."
>   ]


> parseFence :: String -> Fence
> parseFence (map toLower -> "tilde"   ) = Tilde
> parseFence (map toLower -> "backtick") = Backtick
> parseFence                  fence      = error ("unlit: undefined fence `"++fence++"'")
