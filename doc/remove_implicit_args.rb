#!/usr/bin/env ruby
# encoding: utf-8

BeginCode  = "```"
EndCode    = "```"


# Strip the implicit arguments from a code block.
def remove_implicit_args(ln)
  ln.gsub(/(?<!record)(?<!λ)\s*(∀\s*)?\{([^=^\}]*)\}(\s*→)?/, '')
end


# Strip the first n characters from the start of each line, where n is
# the indentation depth of the first line with content.
# Note: the assumption is that the text will indeed indent out further
# than the first line with content. Therefore, code blocks that do this
# should be split up into multiple code blocks.
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

if ARGV.length == 2
  File.open(ARGV[1], "w:UTF-8") do |out|
    File.open(ARGV[0], "r:UTF-8") do |src|
      out.write(
        src.read.gsub(/#{BeginCode}(.*?)#{EndCode}/m) {
          if $1.lstrip.start_with?('keep_implicit_args')
            "#{BeginCode}#{ correct_indent($1) }\n#{EndCode}"
          else
            "#{BeginCode}#{ correct_indent(remove_implicit_args($1)) }\n#{EndCode}"
          end
        }
      )
    end
  end
end
