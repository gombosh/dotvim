" Tag settings - http://vim.wikia.com/wiki/VimTip94
" Vim will search for the file named 'tags', starting with the current directory and then going to the parent directory and then 
" recursively to the directory one level above, till it either locates the 'tags' file or reaches the root '/' directory.
set tags=tags;/
set tagstack " this setting should replace SET_TAGS_LOCATION
"Tags location function
if has("python3")
"autocmd BufReadPost * call SET_TAGS_LOCATION()
"autocmd BufEnter * call SET_TAGS_LOCATION()
function! SET_TAGS_LOCATION()
python3 << endpython
import vim
import os
def set_tags_location():
  pwd = os.getcwd()
  vim.command("set tags=~/tags")
  if "users" in pwd:
    splitted_pwd = pwd.split("/")
    while "users" in splitted_pwd[:-2]:
      workdir_path = "/".join(splitted_pwd)
      workdir_tags = workdir_path+"/tags"
      if os.path.exists(workdir_tags):
        vim.command("set tags="+workdir_tags)
        break
      else:
        splitted_pwd = splitted_pwd[:-1]

set_tags_location()
endpython
endfunction

"Env var setting functions
autocmd BufEnter * call SET_WS()
function! SET_WS()
python3 << endpython
import vim
import os
def set_ws():
  if os.getenv("WS"):
     return

  pwd = os.getcwd()
  if "users" in pwd:
    splitted_pwd = pwd.split("/")
    while "users" in splitted_pwd[:-2]:
      workdir_path = "/".join(splitted_pwd)
      workdir_params = workdir_path+"/.params"
      if os.path.exists(workdir_params):
        os.environ["WS"] = workdir_path
        break
      else:
        splitted_pwd = splitted_pwd[:-1]

set_ws()
endpython
endfunction

function! Pydiff()
python3 << endpython
import vim
import os
def PyDiff():
	file1 = vim.buffers[1].name
	file2 = vim.buffers[2].name
	result = os.popen("~dorong/scripts/largediff.py "+file1+" "+file2)
	for line in result:
		print line

PyDiff()
endpython
endfunction

function! MyPwd()
python3 << endpython
   import os
   def MyPwd(file):
      print os.path.abspath(file)

   MyPwd("%")
endpython
endfunction
endif
