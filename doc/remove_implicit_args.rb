#!/usr/bin/env ruby
# encoding: utf-8


# Regular expression for filtering implicit arguments from raw Agda
# source code:
RE_RAW = /(?<!record)(?<!λ)\s*(∀\s*)?\{+([^=^\{^\}]*)\}+(\s*→)?/


# Regular expression for filtering implicit arguments from typeset
# Agda LaTeX code using `agda --latex`:
RE_TEX = %r{
  (?<!\\AgdaKeyWord\{record\})
  (?<!\\AgdaSymbol\{λ\})
  \s*
  (\\AgdaSymbol{∀}\s*)?
  (\\AgdaSymbol\{\\\{\})+
  (.
  (?<!\\AgdaSymbol\{=\})
  (?<!\\AgdaSymbol\{\\\{\})
  (?<!\\AgdaSymbol\{\\\}\})
  )*
  (\\AgdaSymbol\{\\\}\})+
  (
    (
      (
        \s*\\<(\[\d+\])?%
        (
          \s*\\\\?
          \s*\\>\[\d+\]\s*\\AgdaIndent\{\d+\}\{\}\s*\\<\[\d+\]%
        )?
        \s*\\>\[\d+\]
      )?
      \s*\\AgdaSymbol\{→\}
      (
        \s*\\<\[\d+\]%
      )?
    )?
  )?
}xm



def correct_indent(str)
  indent = nil
  rest   = str.split("\n")
  first  = [rest.shift]
  rest.map! { |ln|
    unless ln =~ /^\s*$/
      if indent.nil? and not
        indent = ln.chars.take_while{ |c| c =~ /^\s*$/ }.length
      end
      ln[0..indent-1] = '' unless indent == 0 or ln.length < indent
      next ln
    end
  }
  (first + rest).join("\n")
end


def format(file,str)
  case File.basename(file,File.extname(file))
  when 'type-logical_grammar'
    str.
      gsub("\\AgdaInductiveConstructor{∙}" , "").
      gsub("\\AgdaInductiveConstructor{·}" , "").
      gsub("\\AgdaPostulate{FORALL}"       , "\\AgdaPostulate{$\\forall$}").
      gsub("\\AgdaPostulate{EXISTS}"       , "\\AgdaPostulate{$\\exists$}").
      gsub(/\\AgdaPostulate\{([\\_A-Z]+)\}/) { "\\AgdaPostulate{\\textsc{#{$1.downcase}}}" }

  when 'non-associative_lambek_calculus'
    str.
      gsub("\\AgdaModule{SC\\_}"                  , "\\AgdaModule{SC}").
      gsub("\\AgdaModule{R\\_}"                   , "\\AgdaModule{R}").
      gsub("\\AgdaModule{RM\\_}"                  , "\\AgdaModule{RM}").
      gsub("\\AgdaDatatype{SC\\_}"                , "\\AgdaDatatype{SC}").
      gsub("\\AgdaDatatype{R\\_}"                 , "\\AgdaDatatype{R}").
      gsub("\\AgdaDatatype{RM\\_}"                , "\\AgdaDatatype{RM}").
      gsub("\\AgdaFunction{⊢SC}"                  , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{⊢R}"                   , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{⊢RM}"                  , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{SC.⊢SC}"               , "\\AgdaFunction{⊢\\textsuperscript{SC}}").
      gsub("\\AgdaFunction{R.⊢R}"                 , "\\AgdaFunction{⊢\\textsuperscript{R}}").
      gsub("\\AgdaFunction{RM.⊢RM}"               , "\\AgdaFunction{⊢\\textsuperscript{RM}}").
      gsub("\\AgdaInductiveConstructor{∙}"        , "\\AgdaInductiveConstructor{,}").
      gsub("\\AgdaInductiveConstructor{\\_∙\\_}"  , "\\AgdaInductiveConstructor{\\_,\\_}").
      gsub("\\AgdaInductiveConstructor{∙>}"       , "\\AgdaInductiveConstructor{,>}").
      gsub("\\AgdaInductiveConstructor{<∙}"       , "\\AgdaInductiveConstructor{<,}").
      gsub("\\AgdaInductiveConstructor{\\_∙>\\_}" , "\\AgdaInductiveConstructor{\\_,>\\_}").
      gsub("\\AgdaInductiveConstructor{\\_<∙\\_}" , "\\AgdaInductiveConstructor{\\_<,\\_}").

      gsub('\\AgdaInductiveConstructor{-}'        ,'\\AgdaInductiveConstructor{$-$}').
      gsub('\\AgdaInductiveConstructor{+}'        ,'\\AgdaInductiveConstructor{$+$}')

  when 'display_calculus'
    str.
      gsub("\\AgdaFunction{findAllRM}"  , "\\AgdaFunction{findAll\\textsuperscript{RM}}").
      gsub("\\AgdaModule{RM\\_}"           , "\\AgdaModule{RM}").
      gsub("\\AgdaDatatype{RM\\_}"         , "\\AgdaDatatype{RM}").
      gsub("\\AgdaFunction{⊢RM}"           , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{RM.⊢RM}"        , "\\AgdaFunction{⊢\\textsuperscript{RM}}").

      gsub("\\AgdaFunction{findAllNL}"     , "\\AgdaFunction{findAll\\textsuperscript{NL}}").
      gsub(%r{(\\AgdaFunction\{NL\.\[\})
              ((.(?<!\\AgdaFunction\{\[\})(?<!\\AgdaFunction\{NL\.\[\}))*)
              (\\AgdaFunction\{\]⊢NL\})}xm)\
          { "\\AgdaFunction{[}#{$2}\\AgdaFunction{]⊢\\textsuperscript{NL}}" }.
      gsub("\\AgdaFunction{NL.⊢NL}"        , "\\AgdaFunction{⊢\\textsuperscript{NL}}").
      gsub("\\AgdaFunction{NL.⊢NL[}"       , "\\AgdaFunction{⊢\\textsuperscript{NL}[}").
      gsub("\\AgdaModule{NL\\_}"           , "\\AgdaModule{NL}").
      gsub("\\AgdaDatatype{NL\\_}"         , "\\AgdaDatatype{NL}").
      gsub("\\AgdaFunction{⊢NL[}"          , "\\AgdaFunction{⊢[}").
      gsub("\\AgdaFunction{⊢NL}"           , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{]⊢NL}"          , "\\AgdaFunction{]⊢}").

      gsub(%r{(\\AgdaFunction\{fNL\.\[\})
              ((.(?<!\\AgdaFunction\{\[\})(?<!\\AgdaFunction\{fNL\.\[\}))*)
              (\\AgdaFunction\{\]⊢fNL\})}xm)\
          { "\\AgdaFunction{[}#{$2}\\AgdaFunction{]⊢\\textsuperscript{fNL}}" }.
      gsub("\\AgdaFunction{fNL.⊢fNL}"      , "\\AgdaFunction{⊢\\textsuperscript{fNL}}").
      gsub("\\AgdaFunction{fNL.⊢fNL[}"     , "\\AgdaFunction{⊢\\textsuperscript{fNL}[}").
      gsub("\\AgdaModule{fNL\\_}"          , "\\AgdaModule{fNL}").
      gsub("\\AgdaDatatype{fNL\\_}"        , "\\AgdaDatatype{fNL}").
      gsub("\\AgdaFunction{⊢fNL[}"         , "\\AgdaFunction{⊢[}").
      gsub("\\AgdaFunction{⊢fNL}"          , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{]⊢fNL}"         , "\\AgdaFunction{]⊢}").

      gsub('\\AgdaInductiveConstructor{-}' ,'\\AgdaInductiveConstructor{$-$}').
      gsub('\\AgdaInductiveConstructor{+}' ,'\\AgdaInductiveConstructor{$+$}')

  when 'lambek-grishin_calculus'
    str.
      gsub("\\AgdaModule{RM\\_}"           , "\\AgdaModule{RM}").
      gsub("\\AgdaDatatype{RM\\_}"         , "\\AgdaDatatype{RM}").
      gsub("\\AgdaFunction{⊢RM}"           , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{RM.⊢RM}"        , "\\AgdaFunction{⊢\\textsuperscript{RM}}").

      gsub(%r{(\\AgdaFunction\{LG\.\[\})
              ((.(?<!\\AgdaFunction\{\[\})(?<!\\AgdaFunction\{LG\.\[\}))*)
              (\\AgdaFunction\{\]⊢LG\})}xm)\
          { "\\AgdaFunction{[}#{$2}\\AgdaFunction{]⊢\\textsuperscript{LG}}" }.
      gsub("\\AgdaFunction{LG.⊢LG}"        , "\\AgdaFunction{⊢\\textsuperscript{LG}}").
      gsub("\\AgdaFunction{LG.⊢LG[}"       , "\\AgdaFunction{⊢\\textsuperscript{LG}[}").
      gsub("\\AgdaModule{LG\\_}"           , "\\AgdaModule{LG}").
      gsub("\\AgdaFunction{⊢LG[}"          , "\\AgdaFunction{⊢[}").
      gsub("\\AgdaFunction{⊢LG}"           , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{]⊢LG}"          , "\\AgdaFunction{]⊢}").

      gsub(%r{(\\AgdaFunction\{fLG\.\[\})
              ((.(?<!\\AgdaFunction\{\[\})(?<!\\AgdaFunction\{fLG\.\[\}))*)
              (\\AgdaFunction\{\]⊢fLG\})}xm)\
          { "\\AgdaFunction{[}#{$2}\\AgdaFunction{]⊢\\textsuperscript{fLG}}" }.
      gsub("\\AgdaFunction{fLG.⊢fLG}"        , "\\AgdaFunction{⊢\\textsuperscript{fLG}}").
      gsub("\\AgdaFunction{fLG.⊢fLG[}"       , "\\AgdaFunction{⊢\\textsuperscript{fLG}[}").
      gsub("\\AgdaModule{fLG\\_}"           , "\\AgdaModule{fLG}").
      gsub("\\AgdaDatatype{fLG\\_}"         , "\\AgdaDatatype{fLG}").
      gsub("\\AgdaFunction{⊢fLG[}"          , "\\AgdaFunction{⊢[}").
      gsub("\\AgdaFunction{⊢fLG}"           , "\\AgdaFunction{⊢}").
      gsub("\\AgdaFunction{]⊢fLG}"          , "\\AgdaFunction{]⊢}").

      gsub('\\AgdaInductiveConstructor{-}' ,'\\AgdaInductiveConstructor{$-$}').
      gsub('\\AgdaInductiveConstructor{+}' ,'\\AgdaInductiveConstructor{$+$}')

  when 'continuation-passing_style'
    str.
      gsub('\\AgdaInductiveConstructor{-}' ,'\\AgdaInductiveConstructor{$-$}').
      gsub('\\AgdaInductiveConstructor{+}' ,'\\AgdaInductiveConstructor{$+$}')

  when 'syntactically_delimited_continuations'
    str.
      gsub("\\AgdaInductiveConstructor{∙}" , "").
      gsub("\\AgdaInductiveConstructor{·}" , "").
      gsub("\\AgdaPostulate{FORALL}" , "\\AgdaPostulate{$\\forall$}").
      gsub("\\AgdaPostulate{EXISTS}" , "\\AgdaPostulate{$\\exists$}").
      gsub(/\\AgdaPostulate\{([\\_A-Z]+)\}/) { "\\AgdaPostulate{\\textsc{#{$1.downcase}}}" }.
      gsub("\\AgdaSymbol{(}\\AgdaBound{k} \\AgdaSymbol{:} \\AgdaDatatype{Bool} \\AgdaSymbol{→} \\AgdaDatatype{Bool}\\AgdaSymbol{)}","\\AgdaBound{k}")

  when 'other'
    str.
      gsub("\\AgdaPostulate{FORALL}" , "\\AgdaPostulate{$\\forall$}").
      gsub("\\AgdaPostulate{EXISTS}" , "\\AgdaPostulate{$\\exists$}").
      gsub(/\\AgdaPostulate\{([\\_A-Z]+)\}/) { "\\AgdaPostulate{\\textsc{#{$1.downcase}}}" }
  else
    str
  end
end


if ARGV.length == 3
  File.open(ARGV[2], "w:UTF-8") do |out|
    File.open(ARGV[1], "r:UTF-8") do |src|
      out.write(
        case ARGV[0]
        when 'raw'
          src.read.gsub(/```(.*?)```/m) {
            "```#{ correct_indent($1.gsub(RE_RAW, '')) }```"
          }
        when 'tex'
          src.read.gsub(/\\begin{code}(.*)\\end{code}/m) {
            "\\begin{code}#{ format(ARGV[1], $1.rstrip.gsub(RE_TEX, '')) }\n\\end{code}"
          }
        end
      )
    end
  end
end
