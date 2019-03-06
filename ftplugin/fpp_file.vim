" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Behaves just like C
runtime! ftplugin/c.vim ftplugin/c_*.vim ftplugin/c/*.vim

"" Quit when a syntax file was already loaded.
"if exists('b:current_syntax')
"   finish
"endif
"
"" Set 'comments' to format dashed lists in comments.
"setlocal comments=sO:*\ -,mO:*\ \ ,exO:*/,s1:/*,mb:*,ex:*/,://
"setlocal iskeyword+=$
"
"syn match  fpp_fileStatement "^verilog\|^incdir\|^include\(\s*\)$"
"hi def link fpp_fileStatement		Statement
"
"let b:current_syntax = 'fpp_file'
