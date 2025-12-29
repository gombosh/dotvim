This is a plugin suite for nvim.

first time use:
go to your home directory (can be found by using ":echo $HOME" from nvim).
usually for windows: C:\Users\<username> linux: /home/<username>

### windows:
```
git clone https://github.com/gombosh/dotvim.git vimfiles
```
```
nvim +PlugInstall +qall (or run "PluginUpdate" from inside vim, ignore the initial errors).
  
reomve any _vimrc and _gvimrc files you have.
  
create a myvimrc file to overide/add functionality.

copy the init.vim to the AppData/Local/nvim folder (create it if missing)

### linux:
```
git clone https://github.com/gombosh/dotvim.git .vim
cd .vim
nvim +PlugInstall +qall (or run "PluginUpdate" from inside vim, ignore the initial errors).
```
reomve any ~/.vimrc and ~/.gvimrc files you have.
  
create a ~/myvimrc file to overide/add functionality.

### temp dirs (create manually):
create "gvim_tmp" directory in parallel to .vim directory (for tmp operational files)
you should monitor these directories any maybe do some cleanup once in a while.

I think in the minimum that the local "myvimrc" should contain the following line:
colorscheme torte

to update files use:
git pull

to update plugins:
PluginUpdate

yes I know, I should have a script which updates everything.

to check in use 
git add .
git commit -m "message"
git push

latest changes:
added vimcompletesme which is very simple and useful.
cleanup and move to vundle.

oldef changes:
- python3 support
- fixed backup dir not existing issue
- fixed fold doesn't exist issue

tagbar instead of taglist
airline changed to full path
solarise color scheme not tested

CSCOPE SUPPORT ADDED!!!!
to use it you must have the cscope executable in your "PATH".
for windows the file is a part of the repository at "vimfiles\bin" so just add it to "PATH".

## Troubleshooting:
if under windows we get an error when opening vim:
```
coc.nvim node is not executable
```
please download node.js for windows at https://nodejs.org/en/download/
