#!/usr/bin/env ruby
# encoding: utf-8

BeginCode  = "```"
EndCode    = "```"
REImplicit = /(?<!record)(?<!λ)\s*(∀\s*)?\{([^=^\}]*)\}(\s*→)?/

def remove_implicit_args(src)
  src.gsub(/#{BeginCode}(.*?)#{EndCode}/m) do |m|
    "#{BeginCode}#{ $1.gsub(REImplicit, '') }#{EndCode}"
  end
end


if ARGV.length == 2
  File.open(ARGV[1], "w:UTF-8") do |out|
    File.open(ARGV[0], "r:UTF-8") do |src|
      out.write(remove_implicit_args(src.read))
    end
  end
end
