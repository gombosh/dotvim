"xrun Log file syntax highlighting 
function! ElogSettings()
   "colorscheme evening
   hi Cursorline term=none cterm=none ctermbg=Green guibg=darkred
   hi statusline guibg=darkred
   augroup CursorLine
      au!
      au VimEnter,WinEnter,BufWinEnter * setlocal cursorline
      au WinLeave * setlocal nocursorline
   augroup END
	syn match ERROR "UVM_ERROR*"
	syn match comp_err "Error"
	syn match comp_warn "Warning"
	syn match FAILED "FAILED*"
	syn match failed "failed*"
	syn match warning "WARNING"
	syn match info "UVM_INFO"
	syn match passed "passed*"
	syn match PASSED "PASSED*"
	syn match match "ITEM MATCH"
   syn match miss "MISSMATCH"
	syn match TstLog "Test_Log"
	hi def msg guibg=Black guifg=Black
	hi ERROR 	gui=bold guibg=Red guifg=Black
	hi comp_err gui=bold guibg=Red guifg=Black
	hi comp_warn gui=bold guibg=Brown guifg=Black
	hi FAILED 	gui=bold guibg=Red guifg=Black
	hi failed 	gui=bold guibg=Red guifg=Black
	hi warning 	gui=bold guibg=Orange guifg=White
	hi info 	   gui=bold guibg=Gray guifg=Red
	hi PASSED 	gui=bold guibg=Green guifg=Black
	hi passed 	gui=bold guibg=Green guifg=Black
	hi match 	gui=bold guibg=Green guifg=Blue
   hi miss     gui=bold guifg=Red
	hi TstLog  	gui=bold guibg=Blue guifg=Green
endfunction
autocmd BufRead *.log :call ElogSettings()
