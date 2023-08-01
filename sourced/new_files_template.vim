"New file packages
let newfile_template_company_name = "GuardKnox Ltd"
let newfile_template_date = strftime("%a %b %d, %Y  %I:%M%p")
let newfile_template_year = strftime("%Y")
let newfile_template_username = expand("$USERNAME") 

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
    let result = append(6, "Developers   :  " . g:newfile_template_username) 
    let date = strftime("%a %b %d, %Y  %I:%M%p")
    let result = append(7, "Created      : " . g:newfile_template_date) 
    let result = append(8, "Description  : ") 
    let result = append(9, "Notes        : ") 
    let result = append(10, "---------------------------------------------------------------------------") 
    let result = append(11, "Copyright " . g:newfile_template_year . " (c) " . g:newfile_template_company_name)
    let result = append(12, "---------------------------------------------------------------------------*/")
    let result = append(13, "'''")     
  
endfunction

autocmd! BufNewFile *.v,*.sv,*.svh,*.c,*.cpp,*.h call InsertVerilogPackage()

"TODO change name
function! InsertVerilogPackage() 
    let filename = expand("%") 
	 let result = append(0, "// -------------------------------------------------------------------------")
	 let result = append(1, "// File name		: " . filename . " ")
	 let result = append(2, "// Title				: ")
	 let result = append(3, "// Project      	: ")
	 let result = append(4, "// Developers   	: " . g:newfile_template_username . " ")
	 let result = append(5, "// Created      	: " . g:newfile_template_date . " ")
	 let result = append(6, "// Last modified  : ")
	 let result = append(7, "// Description  	: ")
	 let result = append(8, "// Notes        	: ")
	 let result = append(9, "// Version			: 0.1")
	 let result = append(10, "// ---------------------------------------------------------------------------")
     let result = append(11, "// Copyright " . g:newfile_template_year . " (c) " . g:newfile_template_company_name)
	 let result = append(12, "// Confidential Proprietary ")
	 let result = append(13, "// ---------------------------------------------------------------------------")
endfunction
" }}}
