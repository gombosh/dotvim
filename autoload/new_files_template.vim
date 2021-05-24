"New file packages
autocmd! BufNewFile *.py call InsertPythonPackage() 

"TODO change name
function! InsertPythonPackage() 
    let dir = getcwd() 
    
    let result = append(0,"#!/usr/bin/env python3")
    let result = append(1, "'''")     
    let result = append(2, "-------------------------------------------------------------------------") 
    let filename = expand("%") 
    let result = append(3, "File name    : " . filename ) 
    let result = append(4, "Title        : ") 
    let result = append(5, "Project      : ") 
    let username = expand("$USER") 
    let result = append(6, "Developers   :  " . username) 
    let date = strftime("%a %b %d, %Y  %I:%M%p")
    if has('win32')
       let result = append(7, "Created      : ") 
    elseif has('unix')
       let result = append(7, "Created      : " . date) 
    endif
    let result = append(8, "Description  : ") 
    let result = append(9, "Notes        : ") 
    let result = append(10, "---------------------------------------------------------------------------") 
    let result = append(11, "Copyright 2021 (c) Satixfy Ltd") 
    let result = append(12, "---------------------------------------------------------------------------*/")
    let result = append(13, "'''")     
  
endfunction

autocmd! BufNewFile *.v,*.sv,*.svh,*.c,*.cpp,*.h call InsertVerilogPackage()

"TODO change name
function! InsertVerilogPackage() 
    let filename = expand("%") 
    let date = strftime("%a %b %d, %Y  %I:%M%p")
	 let result = append(0, "// -------------------------------------------------------------------------")
	 let result = append(1, "// File name		: " . filename . " ")
	 let result = append(2, "// Title				: ")
	 let result = append(3, "// Project      	: ")
	 let username = expand("$USER") 
	 let result = append(4, "// Developers   	: " . username . " ")
	 let result = append(5, "// Created      	: " . date . " ")
	 let result = append(6, "// Last modified  : ")
	 let result = append(7, "// Description  	: ")
	 let result = append(8, "// Notes        	: ")
	 let result = append(9, "// Version			: 0.1")
	 let result = append(10, "// ---------------------------------------------------------------------------")
	 let result = append(11, "// Copyright 2021 (c) Satixfy Ltd")
	 let result = append(12, "// Confidential Proprietary ")
	 let result = append(13, "// ---------------------------------------------------------------------------")
endfunction
" }}}
