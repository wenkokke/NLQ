#!/usr/bin/env ruby
# encoding: utf-8

BeginCode  = "\\begin{code}"
EndCode    = "\\end{code}"

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
  (\s*\\AgdaSymbol\{→\})?
}xm


# Strip the implicit arguments from a code block.
def remove_implicit_args(flag, ln)
  case flag
  when 'raw'
    ln.gsub(RE_RAW, '')
  when 'tex'
    ln.gsub(RE_TEX, '')
      .gsub('\\AgdaInductiveConstructor{·}','')
      .gsub('\\AgdaInductiveConstructor{∙}','')
      .gsub('\\AgdaSymbol{λ} \\AgdaBound{A=B} \\AgdaSymbol{→} \\AgdaFunction{subst} \\AgdaSymbol{(\\_} \\AgdaFunction{⊢NL\\_}\\AgdaSymbol{)} \\AgdaBound{A=B}','')
      .gsub('\\AgdaFunction{\\_⊢NL\\_}','\\AgdaFunction{\\_⊢\\textsuperscript{NL}\\_}')
      .gsub('\\AgdaDatatype{NL}','')
      .gsub('\\AgdaModule{NL\\_}','\AgdaModule{NL}')
      .gsub('\\AgdaInductiveConstructor{-}','\\AgdaInductiveConstructor{$-$}')
      .gsub('\\AgdaInductiveConstructor{+}','\\AgdaInductiveConstructor{$+$}')
      .gsub('⇐','\\ensuremath{\\varslash}')
      .gsub('⇒','\\ensuremath{\\varbslash}')
  end
end


if ARGV.length == 3
  File.open(ARGV[2], "w:UTF-8") do |out|
    File.open(ARGV[1], "r:UTF-8") do |src|
      out.write(
        src.read.gsub(/\\begin{code}(.*?)\\end{code}/m) {
          "\\begin{code}#{ remove_implicit_args(ARGV[0], $1).rstrip }\n\\end{code}"
        }
      )
    end
  end
end
