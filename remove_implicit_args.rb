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
  str.
    gsub('\\AgdaInductiveConstructor{-}' ,'\\AgdaInductiveConstructor{$-$}').
    gsub('\\AgdaInductiveConstructor{+}' ,'\\AgdaInductiveConstructor{$+$}')
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
