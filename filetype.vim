	" my filetype file
	if exists("did_load_filetypes")
    "if exists("did_load_filetypes_userafter2")
	  finish
	endif
    let did_load_filetypes_userafter = 1
	augroup filetypedetect
     au! BufRead,BufNewFile *.vsif setf vsif
     au! BufRead,BufNewFile *.f setf f_file
     au! BufRead,BufNewFile *.fpp setf fpp_file
     au! BufRead,BufNewFile depend.txt setf depend_file
     au! BufRead,BufNewFile *.jenkinsfile setf groovy
	augroup END
