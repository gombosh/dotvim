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

"""Python code
"if has("python")
"function! Doron()
"python << endpython
"import vim
"def doron():
"   (row, col) = vim.current.window.cursor
"   row = row
"   lines = []
"   max_len_line = 0
"   max_len_first = 0
"   max_len_second = 0
"   i = row
"   while True:
"      print i
"      line = vim.current.buffer[i].replace("\t"," ").strip()
"      if line:
"         while "  " in line:
"            line = line.replace("  "," ")
"
"         line = line.split(" ")
"         if len(line) < 2:
"            break
"
"         lines.append(line)
"         if len(line) > max_len_line:
"            max_len_line = len(line)
"
"         if len(line[0]) > max_len_first:
"            max_len_first = len(line[0])
"
"         if len(line) > 2 and len(line[1]) > max_len_second:
"            max_len_second = len(line[1])
"
"         i += 1
"      else:
"         break
"
"   for i in range(len(lines)):
"      white_spaces1 = 1 + max_len_first - len(lines[i][0])
"      white_spaces2 = 1 + max_len_second - len(lines[i][1])
"      print white_spaces1,white_spaces2,max_len_first,max_len_second
"      if max_len_line == 2:      
"         vim.current.buffer[row] = "\t"+lines[i][0]+white_spaces1*" "+lines[i][1]
"      elif max_len_line >= 3:
"         if len(lines[i]) == 3:
"            vim.current.buffer[row] = "\t"+lines[i][0]+white_spaces1*" "+lines[i][1]+white_spaces2*" "+lines[i][2]
"         elif len(lines[i]) == 2:
"            vim.current.buffer[row] = "\t"+lines[i][0]+white_spaces1*" "+(max_len_second+1)*" "+lines[i][1]
"         else:
"            vim.current.buffer[row] = "\t"+lines[i][0]+white_spaces1*" "+lines[i][1]+white_spaces2*" "+lines[i][2]+" ".join(lines[i][3:])
"
"      row += 1
"
"doron()
"endpython
"endfunction
"
"function! CP1()
"python << endpython
"import vim
"def cp1():
"    list_of_vars = []
"    max_var_size = 0    
"    (row, col) = vim.current.window.cursor
"    for i in range(row):
"        line = vim.current.buffer[i].split("//")[0]
"        if "_p1" in line:
"            line = line.replace("\t"," ").split("_p1")
"            for j in range(len(line)-1):
"                var_name = line[j].split(" ")[-1]
"                var_name = var_name.replace("(","").replace("&","").replace("|","").replace("~","").replace("{","")
"                if var_name not in list_of_vars:
"                   range_dec = "not_found"  
"                   for new_scan_i in range(row):
"                      new_scan_line = vim.current.buffer[new_scan_i]
"                      if var_name in new_scan_line and (("input" in new_scan_line) or ("output" in new_scan_line) or ("reg" in new_scan_line) or ("wire" in new_scan_line)):
"                         if "[" in new_scan_line:
"                            range_dec = "["+new_scan_line.split("[")[1].split("]")[0]+"]"
"                         else:
"                            range_dec = ""
"                         break
"                     
"                   if range_dec == "not_found":
"                      print "can't find declaration for ",var_name
"                      return
"
"                   if len(var_name)+len(range_dec) > max_var_size:
"                      max_var_size = len(var_name)+len(range_dec)
"
"                   list_of_vars.append([var_name,range_dec])
"                else:
"                    continue
"        else:
"            continue
"
"    vim.current.buffer.append("\talways @(posedge sclk or negedge sclk_rst_n)")
"    vim.current.buffer.append("\tbegin")
"    vim.current.buffer.append("\t\tif (~sclk_rst_n)")
"    vim.current.buffer.append("\t\tbegin")
"    for var in list_of_vars:
"        white_spaces = max_var_size - len(var[0]) - len(var[1]) + 4
"        vim.current.buffer.append("\t\t\t"+var[0]+"_p1"+var[1]+white_spaces*" "+"<=\t`RDEL 1'b0;")
"
"    vim.current.buffer.append("\t\tend")
"    vim.current.buffer.append("\t\telse")
"    vim.current.buffer.append("\t\tbegin")
"    for var in list_of_vars:
"        white_spaces = max_var_size - len(var[0]) - len(var[1]) + 4
"        vim.current.buffer.append("\t\t\t"+var[0]+"_p1"+var[1]+white_spaces*" "+"<=\t`RDEL "+var[0]+var[1]+";")
"
"    vim.current.buffer.append("\t\tend")
"    vim.current.buffer.append("\tend")
"
"cp1()
"endpython
"endfunction
"
"function! CP2()
"python << endpython
"import vim
"def cp2():
"    list_of_vars = []
"    max_var_size = 0
"    (row, col) = vim.current.window.cursor
"    for i in range(row):
"        line = vim.current.buffer[i].split("//")[0]
"        if "_p2" in line:
"            line = line.replace("\t"," ").split("_p2")
"            for j in range(len(line)-1):
"                var_name = line[j].split(" ")[-1]
"                var_name = var_name.replace("(","").replace("&","").replace("|","").replace("~","").replace("{","")
"                if var_name not in list_of_vars:
"                   range_dec = "not_found"
"                   for new_scan_i in range(row):
"                      new_scan_line = vim.current.buffer[new_scan_i]
"                      if var_name in new_scan_line and (("input" in new_scan_line) or ("output" in new_scan_line) or ("reg" in new_scan_line) or ("wire" in new_scan_line)):
"                         if "[" in new_scan_line:
"                            range_dec = "["+new_scan_line.split("[")[1].split("]")[0]+"]"
"                         else:
"                            range_dec = ""
"                         break
"                     
"                   if range_dec == "not_found":
"                      print "can't find declaration for ",var_name
"                      return
"
"                   if len(var_name)+len(range_dec) > max_var_size:
"                      max_var_size = len(var_name)+len(range_dec)
"
"                   list_of_vars.append([var_name,range_dec])
"                else:
"                   continue
"        else:
"            continue
"
"    vim.current.buffer.append("\talways @(posedge sclk or negedge sclk_rst_n)")
"    vim.current.buffer.append("\tbegin")
"    vim.current.buffer.append("\t\tif (~sclk_rst_n)")
"    vim.current.buffer.append("\t\tbegin")
"    for var in list_of_vars:
"        white_spaces = max_var_size - len(var[0]) - len(var[1]) + 4
"        vim.current.buffer.append("\t\t\t"+var[0]+"_p2"+var[1]+white_spaces*" "+"<=\t`RDEL 1'b0;")
"
"    vim.current.buffer.append("\t\tend")
"    vim.current.buffer.append("\t\telse")
"    vim.current.buffer.append("\t\tbegin")
"    for var in list_of_vars:
"        white_spaces = max_var_size - len(var[0]) - len(var[1]) + 4       
"        vim.current.buffer.append("\t\t\t"+var[0]+"_p2"+var[1]+white_spaces*" "+"<=\t`RDEL "+var[0]+"_p1"+var[1]+";")
"
"    vim.current.buffer.append("\t\tend")
"    vim.current.buffer.append("\tend")
"
"cp2()
"endpython
"endfunction
"endif

