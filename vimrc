" .vimrc File
" Maintained by: Doron Gombosh
" doron.gombosh@satixfy.com
" http://www.satixfy.com
"""DEBUG
":verbose imap <tab>
"""Version checking
"version 8.1
if version < 800
	finish
else
set t_BE=
"Forget compatibility with Vi. Believe me, it's better this way.
set nocompatible              " be iMproved, required

"""Vundle plugins loading
""""Vundle initial loading settings
filetype off                  " required
" set the runtime path to include Vundle and initialize
if has('win32')
   set rtp+=$HOME/vimfiles/bundle/Vundle.vim
   call vundle#begin('$HOME/vimfiles/bundle')
else
   set rtp+=~/.vim/bundle/Vundle.vim
   call vundle#begin()
endif
" alternatively, pass a path where Vundle should install plugins
"call vundle#begin('~/some/path/here')

""""Plugins
" let Vundle manage Vundle, required
" this gets and manages plugins from git
Plugin 'VundleVim/Vundle.vim'

"Tree view
Plugin 'scrooloose/nerdtree'
Plugin 'greggerz/nerdtree-svn-plugin'
" use F6 as the main access key

" this colors paranthesis opening/closing in the same color.
Plugin 'kien/rainbow_parentheses.vim'
" this works automatically

" this is the nice buttom line with info
Plugin 'vim-airline/vim-airline'
" already setup for you, but you can play with it if you want.

" this allows movement in the code from declaration to instance etc. (beta)
Plugin 'brookhong/cscope.vim'
"<leader>fa to start

" fuzzy smart file search
Plugin 'ctrlpvim/ctrlp.vim'
" ctrl-p to activate, then just write what's on your mind
" F5 from inside ctrlp will update the database

" new plugin for fast grepping - TODO need to experiment with this.
"Plugin 'wsdjeg/flygrep.vim'
Plugin 'mhinz/vim-grepper'
"for now I've put it on F10 (and S-F10)

" commands for repositories, auto detects the type of repo
Plugin 'vcscommand.vim'
" use :VCS<command> will all the regular repo commands

" auto syntax checking, should appear at the buttom line
"Plugin 'scrooloose/syntastic'
" disabled for now because it doesn't play well with airline
" trying an alternative
" lint on the fly
Plugin 'w0rp/ale'

" mega plugin with many cool features for systemverilog - TODO help commands +
" disabled for now because it doesn't play well with airline
" TODO check for alternatitve
" add snipets + makeprg fpr xcelium analyze
Plugin 'vhda/verilog_systemverilog.vim'
"<leader>i/o/u/I (after tags file is ready)
"for verilog_systemverilog - highlighes the matches of words
Plugin 'vimtaku/hl_matchit.vim'
"for verilog_systemverilog - autocompleation with tab
Plugin 'ervandew/supertab'
Plugin 'shougo/deoplete.nvim'
Plugin 'roxma/nvim-yarp'
Plugin 'roxma/vim-hug-neovim-rpc'

"for verilog_systemverilog - auto search for functions/variables in file
"(needs ctags to be working)
Plugin 'majutsushi/tagbar'
" activate with F4
"for verilog_systemverilog - should make folding faster in systemverilog
"I don't know of any specific settings it needs to be working.
Plugin 'Konfekt/FastFold'
"no need to do anything.

" align text
Plugin 'godlygeek/tabular'
" use leader + a + =/:/<space>

" Plugin 'TaskList.vim' - not using it

"Auto close paranthesis
Plugin 'raimondi/delimitmate'

" open files with line numbers - old and problematic version
"disabled.
"Plugin 'bogado/file-line'

" open files with line numbers
Plugin 'kopischke/vim-fetch'

"if !has('win32')
"   Plugin 'valloric/youcompleteme'
"endif
"Best (and simplest) completion I found so far.
Plugin 'maralla/completor.vim'
"Plugin 'ajh17/VimCompletesMe.git'

"Snippet plugins
"-----------------
"advanced snipets, need py3
Plugin 'SirVer/ultisnips'
"Plugin 'MarcWeber/vim-addon-mw-utils'
"Plugin 'tomtom/tlib_vim'
"Plugin 'garbas/vim-snipmate', {'pinned': 1}
Plugin 'honza/vim-snippets'
"-----------------

"Tons of colorschemes to choose from.
Plugin 'flazz/vim-colorschemes'

"Full undo history in a side window.
Plugin 'sjl/gundo.vim'
"use F3 to toggle.

" diff dirs!!
Plugin 'will133/vim-dirdiff'
" use :DirDiff <dir1> <dir2>
" note: don't put the last slash on directory path
" example: ':DirDiff a/b/c/ d/e/f/' wont work, but ':DirDiff a/b/c d/e/f' will.

" made some changes so it's not controlled by vundle
" it's part of my git repo
" in windows please close seperatly with 
" git clone --recurse-submodules https://github.com/python-mode/python-mode -c core.symlinks=true bundle/python-mode
if !has('win32')
   Plugin 'klen/python-mode' ", {'pinned': 1}
else
   Plugin 'klen/python-mode', {'pinned': 1}
endif
Plugin 'davidhalter/jedi-vim'
Plugin 'tweekmonster/impsort.vim'

" for html (I use it rarely)
Plugin 'rstacruz/sparkup'
Plugin 'tpope/vim-surround'
Plugin 'hallettj/jslint.vim'
Plugin 'mattn/emmet-vim'
Plugin 'scrooloose/nerdcommenter'
Plugin 'tweekmonster/django-plus.vim'
"TODO add usage info

Plugin 'vim/killersheep'

""""Extra plugins to test in the future
"check this next (looks really cool)
"Plugin 'terryma/vim-multiple-cursors' "select multiple cursors to type to
"Plugin 'tomtom/tcomment_vim' "better commenting by filetype
"Plugin 'tpope/vim-endwise' "might be able to add 'end' automatically in systemverilog

"Plugin 'Valloric/YouCompleteMe'
" The following are examples of different formats supported.
" Keep Plugin commands between vundle#begin/end.
" plugin on GitHub repo
"Plugin 'tpope/vim-fugitive'
" plugin from http://vim-scripts.org/vim/scripts.html
" Plugin 'L9'
" Git plugin not hosted on GitHub
"Plugin 'git://git.wincent.com/command-t.git'
" git repos on your local machine (i.e. when working on your own plugin)
"Plugin 'file:///home/gmarik/path/to/plugin'
" The sparkup vim script is in a subdirectory of this repo called vim.
" Pass the path to set the runtimepath properly.
"Plugin 'rstacruz/sparkup', {'rtp': 'vim/'}
" Install L9 and avoid a Naming conflict if you've already installed a
" different version somewhere else.
" Plugin 'ascenator/L9', {'name': 'newL9'}

""""Vundle ending loading settings
" All of your Plugins must be added before the following line
call vundle#end()            " required
filetype plugin indent on    " required
" To ignore plugin indent changes, instead use:
"filetype plugin on
"
" Brief help
" :PluginList       - lists configured plugins
" :PluginInstall    - installs plugins; append `!` to update or just :PluginUpdate
" :PluginSearch foo - searches for foo; append `!` to refresh local cache
" :PluginClean      - confirms removal of unused plugins; append `!` to auto-approve removal
"
" see :h vundle for more details or wiki for FAQ
" Put your non-Plugin stuff after this line
endif
set encoding=utf-8

if has("eval")
   packadd! matchit
endif
"let loaded_matchit = 1
"runtime macros/matchit.vim

if has('win32')
   set pythonthreedll=python37.dll
   set pythonthreehome=C:\Users\Doron_Dell\AppData\Local\Programs\Python\Python37-32
endif

if has('python3')
   silent! python3 1
endif

autocmd! BufEnter *

"Enable filetypes
syntax on

set visualbell              " enable the visual bell - I have this 'ding' sound on every tab.

"don't Write the file automatically when switching between files.
set noautowrite

set backspace=2 "make backspace work like most other apps (actually erases the characters)

"Tab stuff http://vimcasts.org/episodes/tabs-and-spaces/
set tabstop=3 "the width of the tab character (in spaces)
set shiftwidth=3 "shiftwidth == softtabstop so i can work with spaces and not tabs
set softtabstop=3 "how many white spaces to insert when tabbing
set expandtab "transform tabs to spaces"


"If you Want a different map leader than \ use this in your myvimrc file
"set mapleader = ",";

"Ever notice a slight lag after typing the leader key + command? This lowers
"the timeout.
"set timeoutlen=500

"Display current cursor position in lower right corner.
"set ruler

"add to taswk list
"map <leader>td <Plug>TaskList

au VimEnter * RainbowParenthesesToggle
au Syntax * RainbowParenthesesLoadRound
au Syntax * RainbowParenthesesLoadSquare
au Syntax * RainbowParenthesesLoadBraces

" UltiSnips triggering
"let g:UltiSnipsExpandTrigger = '<C-j>'
"let g:UltiSnipsJumpForwardTrigger = '<C-j>'
"let g:UltiSnipsJumpBackwardTrigger = '<C-k>'
let g:UltiSnipsExpandTrigger = '<tab>'

" If this variable is set, augroup is defined, and start highlighting.
let g:hl_matchit_enable_on_vim_startup = 1

"for python activate supertab completion - need to move to filetype detect file
" this was old stuff from before python mode
"au FileType python set omnifunc=pythoncomplete#Complete
" dorong - brought this back for verilog_systemverilog
let g:SuperTabDefaultCompletionType = 'context'
"set completeopt=menuone,longest,preview
let g:loaded_python_provider = 0
let g:deoplete#enable_at_startup = 1
let g:python3_host_prog=expand('$HOME\AppData\Local\Programs\Python\Python37-32\python.exe')

"""Python-Mode plugin settings
"use python3 for pymode
let g:pymode_python = 'python3'
"Enable pymode indentatio
let g:pymode_indent = 1
"Enable pymode folding
let g:pymode_folding = 1
"enable pymode motion
let g:pymode_motion = 1
"enable pymode documentation script and set 'K' as a key for displaying docs
let g:pymode_doc = 1
let g:pymode_doc_bind = 'K'
"Turn on the run code script and bind <leader>r to run command
let g:pymode_run = 1
let g:pymode_run_bind = '<leader>r'
"enable breakpoints and set to <leader>b
let g:pymode_breakpoint = 1
let g:pymode_breakpoint_bind = '<leader>b'
"enable auto lint on write
let g:pymode_lint = 1
let g:pymode_lint_on_write = 1
let g:pymode_lint_message = 1
let g:pymode_lint_checkers = ['pyflakes', 'pep8', 'mccabe']
let g:pymode_lint_ignore = ["E501", "W",]   "skip 'too long' warning
"enable all python highliting
let g:pymode_syntax_all = 1
"E.g. "E501,W002", "E2,W" (Skip all Warnings and Errors that starts with E2) and etc
let g:pymode_lint_select = ["E501", "W0011", "W430"]
"set location for rope projects
let g:pymode_rope_project_root = "$HOME/rope_projects"

"disable rope lookup project
let g:pymode_rope_lookup_project = 0 "fix a bug in python mode
"for pymode plugin - remove red end of line 
"let g:pymode_options_max_line_length = 0
let g:pymode_options_colorcolumn = 0
"Turn off code completion support in the plugin
let g:pymode_rope_completion = 0
"Turn off the rope script
let g:pymode_rope = 0

let g:jedi#use_splits_not_buffers = "left"

"""Fonts and Color Schemes
"Set the color scheme. Change this to your preference.
"We have a plugin with 1000 schemes installed
if has("eval")
   colorscheme badwolf
else
   colorscheme torte
endif

"Set font type and size. Depends on the resolution. Larger screens, prefer h20
"set guifont=LucidaTypewriter\ \9
if !has('win32')
   set guifont=Monospace\ \11
   nmap <silent> + :let &guifont=substitute(&guifont, '\(\d\+\)', '\=submatch(1) + 1', '')<CR>
   nmap <silent> _ :let &guifont=substitute(&guifont, '\(\d\+\)', '\=(submatch(1) - 1)', '')<CR>
else
   set guifont=Consolas:h11:cANSI
   nmap <silent> + :let &guifont=substitute(&guifont, '\(\d\+\)', '\=submatch(1) + 1', '')<CR>
   nmap <silent> _ :let &guifont=substitute(&guifont, '\(\d\+\)', '\=(submatch(1) - 1)', '')<CR>
endif

"""revision history tool
let g:gundo_prefer_python3 = 1
map <F3> :GundoToggle<CR>

"""Tags control
map <F4> :Tagbar<CR>
if has('win32')
   let g:tagbar_ctags_bin = '$HOME/vimfiles/bin/ctags.exe'
else
   let g:tagbar_ctags_bin = '/home/dorong/bin/ctags/bin/ctags'
endif
""""Taglist - not installed
"let Tlist_Ctags_Cmd="C:/\ctags58/\ctags.exe"
""""Tagbar
"let g:tagbar_ctags_bin = "C:/ctags58/ctags.exe"

"""Global settings
"following seeting are controlled by external plugin so I disabled them here.
"set shortmess=xotI "shorten messages so you dont have to press enter, but i don't use this for now.
"set showcmd "Show command in bottom right portion of the screen
set showmatch "When a bracket is inserted briefly jump to the matching one

"Indent stuff - needs to be controlled for each filetype seperatlly
"set smartindent "this one tries to guess the indent, but it's bad in most cases
set autoindent "this one is simpler, just takes the indent from the last line, but if I have a special indent file for some filetype, it will overwrite this.
"
"set whichwrap=bshl<>[]      "select which keys can wrap lines, I disabled it here, but it looks like it's activated somewhere else.
"
"set laststatus=2 "Always show the status line - done by plugin, no need for this
"
"Prefer a slightly higher line height - that's the gap between lines
set linespace=3

"
"Better line wrapping
set wrap
" Make shift-W toggle between wrap and unwrap longlines
map <S-W>  :set wrap! <CR>
"
" Allow virtual edit, place cursor wherever you want
" set ve=all
set ve=block
"
" set the maximum line size (longer than that will be broken to 2 lines) set
" by plugin but quite anoying.
"set textwidth=79
"set textwidth=0 "unlimited

" this make some big changes, not everyone will like it.
" so I removed it
"set formatoptions=qrnl1
"
"Set incremental searching (jump to results as you type)
set incsearch
"
"Highlight searching
set hlsearch
"
" case insensitive search
set ignorecase
set smartcase


"Hide mouse when typing - can be anoying because you have to move the mouse
"to see where it is.
"set mousehide
"
"Shortcut to fold tags with leader (usually \) + ft - don't know what that is.
"nnoremap <leader>ft Vatzf
"
" Create dictionary for custom expansions FIXME useful for UVM, but UVM has
" it's own plugins so leave it disabled for now
"set dictionary+=/store/public/Temp/uvm_dict.txt
"
"Opens a vertical split and switches over (\v)
nnoremap <leader>v <C-w>v<C-w>l
"
"very usefull for the anoying dos/unix files - force to dos mode.
map <leader>dos :e ++ff=dos<CR>
map <leader>unix :e ++ff=unix<CR>
"the next one actually changes the file. save and check in after you do that
"for permanent fix.
map <leader>dos2unix :%s/\r\(\n\)/\1/g<CR>
"
"Split windows below the current window. - I like this better
set splitbelow
set splitright
"
" session settings for mksession, the defaults are good enough
"set sessionoptions=resize,winpos,winsize,buffers,tabpages,folds,curdir,help
"
"Set up an HTML5 template for all new .html files FIXME for system verilog
"autocmd BufNewFile * silent! 0r $VIMHOME/templates/%:e.tpl

"Shortcut for editing  vimrc file in a new tab - this is one of the most
"usefull things in the world!
nmap <leader>ev :tabedit $MYVIMRC<cr>

"Saves time; maps the spacebar to colon
"nmap <space> :
" Make Space bar enter insert mode - I'm just used to that, sorry.
map <Space> <Insert>

" Make shift-insert work like in Xterm
map <S-Insert> <MiddleMouse>
map! <S-Insert> <MiddleMouse>
"
"Automatically change current directory to that of the file in the buffer
"vim actually has a native function for this 'autochdir' but this is better
if has("eval")
   set autochdir
else
   autocmd BufEnter,BufRead * cd %:p:h
endif
"
"Map code completion to , + tab TODO might be use
"imap <leader><tab> <C-x><C-o>
"
"Auto-completion menu for command line - behave like bash
set wildmode=list:longest
" More useful command-line completion
set wildmenu
" wildchar key that triggers command-line expansion
"set wildchar=<Tab>
"
" Set showmode (show the mode in the bottom - visual/insert etc.) - done by plugin
"set smd
"
" Make complete look in dictionary - makes it slower, I don't think it's good
"set cpt=.,k,b,t,i
"
" Show full tag of completion
set sft
"
" number of screen lines to show around the cursor
set scrolloff=3
"
" supposed to make it full screen, but I never saw it working well
"if has("gui_running")
"  " GUI is running or is about to start.
"  " Maximize gvim window.
"  set lines=999 columns=999
"endif
"
" Make history buffer larger default 20
set hi=100
"
if !has('win32')
   "" Make shell commands work faster
   set shell=/bin/bash
endif
"
" suffixesadd - used when searching for a file with gf
set suffixesadd=.v,.py,.sv,.c,.cpp,.h,.svh
"
"path - This is a list of directories which will be searched when using gf
"add spv include and uvm include
"set path=.,,./**,../**
set path=.
"
"be xterm
"
" Make block mode work in insert mode
map! <C-V> <Esc><C-V>
"
"
""""Highlight current line
"Highlight the line of the cursor (helps to mark the current line in bold).
hi Cursor guifg=Black guibg=green
hi Cursorline term=none cterm=none ctermbg=Green guibg=darkred
augroup CursorLine
  au!
  au VimEnter,WinEnter,BufWinEnter * setlocal cursorline
  au WinLeave * setlocal nocursorline
augroup END

"http://vim.wikia.com/wiki/Make_Vim_completion_popup_menu_work_just_like_in_an_IDE
"set completeopt=longest,menuone
"inoremap <expr> <CR> pumvisible() ? "\<C-y>" : "\<C-g>u\<CR>"
"inoremap <expr> <C-n> pumvisible() ? '<C-n>' :
"  \ '<C-n><C-r>=pumvisible() ? "\<lt>Down>" : ""<CR>'
"inoremap <expr> <M-,> pumvisible() ? '<C-n>' :
"  \ '<C-x><C-o><C-n><C-p><C-r>=pumvisible() ? "\<lt>Down>" : ""<CR>'
"
"nmap <silent> ,da :exec "1," . bufnr('$') . "bd"<cr>
"
"Bubble single lines (kicks butt)
"http://vimcasts.org/episodes/bubbling-text/
"nmap <C-Up> ddkP
"nmap <C-Down> ddp
"
"Bubble multiple lines
"vmap <C-Up> xkP`[V`]
"vmap <C-Down> xp`[V`]
"
""" Source the vimrc file after saving it. This way, you don't have to reload Vim to see the changes.
if has("autocmd")
 augroup myvimrchooks
  au!
  if has('win32')
     autocmd bufwritepost vimrc source $HOME/vimfiles/vimrc
  elseif has('unix')
     autocmd bufwritepost vimrc source $HOME/.vim/vimrc
  endif
 augroup END
endif
"
""" easier window navigation
"nmap <C-h> <C-w>h
"nmap <C-j> <C-w>j
"nmap <C-k> <C-w>k
"nmap <C-l> <C-w>l
"allows to navigate open windows using the - ALT + arrow keys
nmap <silent> <A-Up> :wincmd k<CR>
nmap <silent> <A-Down> :wincmd j<CR>
nmap <silent> <A-Left> :wincmd h<CR>
nmap <silent> <A-Right> :wincmd l<CR>
"set smarttab "inset tabs at start of line and spaces at middle
"move btween windows with ctrl
map <c-j> <c-w>j
map <c-k> <c-w>k
map <c-l> <c-w>l
map <c-h> <c-w>h

"
"Spelling corrects. Just for example. Add yours below.
"iab teh the
"iab Teh The
"
""" Get to home dir easier
" <leader>hm is easier to type than :cd ~
"nmap <leader>hm :cd ~/ <CR>
"
""" Saves file when Vim window loses focus
"au FocusLost * :wa
"
""" Backups
if has("vms")
  set nobackup		" do not keep a backup file, use versions instead
else
   if !isdirectory(expand("$HOME")."/backup")
      call mkdir(expand("$HOME")."/backup", "p")
   endif
  set backup		" keep a backup file (restore to previous version)
  set backupdir=$HOME/backup " backups
  if has('persistent_undo')
    set undofile	" keep an undo file (undo changes after closing)
  endif
endif

"set directory=~/.vim/tmp/swap// " swap files
set noswapfile
"
"If you exit Vim and later start it again, you would normally lose a lot of
"information.  The viminfo file can be used to remember that information, which
"enables you to continue where you left off.
"set viminfo='100,\"50,:200  " read /write a .viminfo file, don't store more than 50 lines of registers
"
"""Mouse
" Use popup menu for right mouse button and keep shift-left mouse button as search
set mousemodel=popup
map <S-LeftMouse> <LeftMouse>*
map! <S-LeftMouse> <Esc><LeftMouse>*
"
""" confirm start a dialog when a command fails
set cf
"
""" equalalways	make all windows the same size when adding/removing windows
"set noea
"
"""New file packages
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
    let result = append(11, "Copyright 2019 (c) Satixfy Ltd") 
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
	 let result = append(11, "// Copyright 2019 (c) Satixfy Ltd")
	 let result = append(12, "// Confidential Proprietary ")
	 let result = append(13, "// ---------------------------------------------------------------------------")
endfunction
"
"
""" map the [ ] keys
" go to start/end of next line
"map [ 0<NL> 
"map ] $<NL>
"
""" save and suspend
map Z :w<NL>
"
"
"
"""Menu items for Commenting and Un-Commenting code 
"amenu 20.435 &Edit.-SEP4- : 
"amenu Edit.Comment <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call Comment(fl, ll)<CR> 
"amenu Edit.UnComment <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call UnComment(fl, ll)<CR>
" Insert # comments
"vmap <F2> <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call Comment(fl, ll)<CR> 
vmap <F2> :call NERDComment('x', 'toggle')<CR> 
nmap <F2> :call NERDComment('n', 'toggle')<CR> 
imap <F2> <ESC>:call NERDComment('n', 'toggle')<CR>
"vmap <S-F2> <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call UnComment(fl, ll)<CR>
vmap <S-F2> :call NERDComment('x', 'sexy')<CR>
"autocmd BufEnter *.c,*.h,*.cpp,*.v,*.vh,*.sv,*.svi,*.svh vmap <F2> <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call Comment(fl, ll)<CR>
"autocmd BufEnter *.c,*.h,*.cpp,*.v,*.vh,*.sv,*.svi,*.svh vmap <S-F2> <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call UnComment(fl, ll)<CR>
"autocmd BufEnter *.vim,*.vmap vmap <F2>  <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call CommentVim(fl, ll)<CR>
"autocmd BufEnter *.vim,*.vmap vmap <S-F2> <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call UnCommentVim(fl, ll)<CR>
"autocmd BufEnter *.py,*.sh,*.mk,*.tcl vmap <F2>  <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call Commentpy(fl, ll)<CR>
"autocmd BufEnter *.py,*.sh,*.mk,*.tcl vmap <S-F2> <ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call UnCommentpy(fl, ll)<CR>
"
"Function for commenting a block of Visually selected text 
"function! Comment(fl, ll) 
    "let i=a:fl 
"let comment="//" 
"while i<=a:ll 
    "let cl=getline(i) 
"let cl2=comment.cl 
"call setline(i, cl2) 
"let i=i+1 
"endwhile 
"endfunction 

""Function for Un-Commenting a block of Visually selected text 
"function! UnComment(fl, ll) 
    "let i=a:fl 
"let comment="//" 
"while i<=a:ll 
    "let cl=getline(i) 
"let cl2=substitute(cl, "//", "", "") 
"call setline(i, cl2) 
"let i=i+1 
"endwhile 
"endfunction 
""
""-------------------------------------------------------------------
""Function for commenting a block of Visually selected text 
"function! Commentpy(fl, ll) 
    "let i=a:fl 
"let comment="#" 
"while i<=a:ll 
    "let cl=getline(i) 
"let cl2=comment.cl 
"call setline(i, cl2) 
"let i=i+1 
"endwhile 
"endfunction 

""Function for Un-Commenting a block of Visually selected text 
"function! UnCommentpy(fl, ll) 
    "let i=a:fl 
"let comment="#" 
"while i<=a:ll 
    "let cl=getline(i) 
"let cl2=substitute(cl, "#", "", "") 
"call setline(i, cl2) 
"let i=i+1 
"endwhile 
"endfunction 
""-------------------------------------------------------------------
""Function for commenting a block of Visually selected text 
"function! CommentVim(fl, ll) 
    "let i=a:fl 
"let comment="\"" 
"while i<=a:ll 
    "let cl=getline(i) 
"let cl2=comment.cl 
"call setline(i, cl2) 
"let i=i+1 
"endwhile 
"endfunction 

""Function for Un-Commenting a block of Visually selected text 
"function! UnCommentVim(fl, ll) 
    "let i=a:fl 
"let comment="\"" 
"while i<=a:ll 
    "let cl=getline(i) 
"let cl2=substitute(cl, "\"", "", "") 
"call setline(i, cl2) 
"let i=i+1 
"endwhile 
"endfunction 
"
"""Old F10 box lines 
"map <F10> :co .<NL>:s/[!-~]/-/g<NL>:s/- -/---/g<NL>:s/-  -/----/g<NL><ESC>`<:let fl=line(".")<CR>`>:let ll=line(".")<CR>:call Comment(fl, ll)<CR>
"map <F10> :co .<CR>:s/[!-~]/-/g<CR>:s/- -/---/g<CR>I#<esc>
"map <F10> :co .<CR><S-V>r-<esc>v<F2>yykP
"
"
"""Syntax folding and Highlighting
"TODO move to global file
"au BufReadPost *.vsif so ~/bin/vsif.vim
let g:verilog_syntax_fold_lst = "all"
let g:verilog_efm_level = "error"
let g:verilog_efm_uvm_lst = "all"
"let g:verilog_efm_uvm_lst = "fatal,error,warning"
let g:verilog_navigate_split = 1

if has("eval")
   "Enable code folding - let's let the plugin control that
   set foldenable
   "set foldlevel=99
   set foldmethod=syntax
   "set foldmethod=indent
endif
nnoremap <leader>i :VerilogFollowInstance<CR>
nnoremap <leader>I :VerilogFollowPort<CR>
nnoremap <leader>u :VerilogGotoInstanceStart<CR>
nnoremap <leader>o :VerilogReturnInstance<CR>


"
""" maximum of 12 tabs opened with -p
set tabpagemax=12
"
"""guioptions	list of flags that specify how the GUI works
set go+=acegmiLTrtb
set guitablabel=%t
"
"""Plugin Settings
""""VCS (svn) plugin settings 
map <S-F11> :!svn lock %<CR>
map <S-F12> :!svn ci % -m "Fixed a Bug"<CR>
map <F12> :tabnew 

map <F11> :close <CR>
"fix problem where opening a tab causes the bottom line to dissapear
set showtabline=2 
"VCS diff to trunk
set listchars=eol:$,tab:\>\ ,trail:.,extends:>,precedes:<
set nolist   " to turn on (use :set nolist to turn off)
map <leader>dt :VCSVimDiff<CR>

""""Grep Plugin
map <F9>  :MyGrep 
imap <F9> <ESC>:MyGrep 
map <S-F9> :MyGrep "<cword>" .<CR>
vmap <S-F9> :MyGrep "<cword>" .<CR>
imap <S-F9> <ESC>:MyGrep "<cword>" .<CR>
map <F10> :Grepper -tool ag<cr>
nnoremap <S-F10> :Grepper -tool ag -cword -noprompt<cr>

"Add grep abbilty to gvim - TODO deprecate this
function! MyGrep(...)
  if a:0 < 2
    echo "Usage: MyGrep <options> <pattern> <dir>"
    echo 'Example: MyGrep -r "cow" ~/Desktop/*'
    return
  endif
  if a:0 == 2
    let options = '-rsinI'
    let pattern = a:1
    let dir = a:2
  else
    let options = a:1 . 'snI'
    let pattern = a:2
    let dir = a:3
  endif
  let exclude = 'grep -v "/.svn"'
  let cmd = 'grep '.options.' '.pattern.' '.dir. '| '.exclude
  let cmd_output = system(cmd)
  if cmd_output == ""
    echomsg "Pattern " . pattern . " not found"
    return
  endif

  let tmpfile = tempname()
  exe "redir! > " . tmpfile
  silent echon '[grep search for "'.pattern.'" with options "'.options.'"]'."\n"
  silent echon cmd_output
  redir END

  let old_efm = &efm
  set efm=%f:%\\s%#%l:%m

  execute "silent! cgetfile " . tmpfile
  let &efm = old_efm
  botright copen

  call delete(tmpfile)
endfunction

command! -nargs=* -complete=file MyGrep call MyGrep(<f-args>)

""""CSCOPE Plugin
"----------
" CSCOPE "
"----------
if has('win32')
   let g:cscope_cmd = "$HOME/vimfiles/bin/cscope.exe"
else
   let g:cscope_cmd = '$HOME/.vim/bin/cscope.exe'
endif
"let g:cscope_interested_files = '\.c$\|\.cpp$\|\.h$\|\.hpp'
let g:cscope_interested_files = '\.py$'

nnoremap <leader>fa :call CscopeFindInteractive(expand('<cword>'))<CR>
nnoremap <leader>l :call ToggleLocationList()<CR>

" s: Find this C symbol
nnoremap  <leader>fs :call CscopeFind('s', expand('<cword>'))<CR>
" g: Find this definition
nnoremap  <leader>fg :call CscopeFind('g', expand('<cword>'))<CR>
" d: Find functions called by this function
nnoremap  <leader>fd :call CscopeFind('d', expand('<cword>'))<CR>
" c: Find functions calling this function
nnoremap  <leader>fc :call CscopeFind('c', expand('<cword>'))<CR>
" t: Find this text string
nnoremap  <leader>ft :call CscopeFind('t', expand('<cword>'))<CR>
" e: Find this egrep pattern
nnoremap  <leader>fe :call CscopeFind('e', expand('<cword>'))<CR>
" f: Find this file
nnoremap  <leader>ff :call CscopeFind('f', expand('<cword>'))<CR>
" i: Find files #including this file
nnoremap  <leader>fi :call CscopeFind('i', expand('<cword>'))<CR>

""""NERD TREE Plugin
"Show hidden files in NerdTree
let NERDTreeShowHidden=1
"toggle nerdtree with f6
map  <silent> <F6>   :NERDTreeToggle<CR>
imap  <silent> <F6>   <Esc>:NERDTreeToggle<CR>
"autopen NERDTree and focus cursor in new document
"autocmd VimEnter * NERDTree
"autocmd VimEnter * wincmd p

""""AirLine plugin
set laststatus=2 "always show status line
" here is an example of how you could replace the branch indicator with
" the current working directory, followed by the filename.
let g:airline_section_b = "[" . hostname() . ']%{getcwd()}'

set number "Show lines numbers
highlight LineNr ctermfg=grey ctermbg=black guibg=black guifg=grey

""""Tabular Plugin settings - auto align text
nmap <Leader>a= :Tab /=<CR>
vmap <Leader>a= :Tab /=<CR>
nmap <Leader>a: :Tab /:\zs<CR>
vmap <Leader>a: :Tab /:\zs<CR>
nmap <Leader>a<Space> :Tab / \zs<CR>
vmap <Leader>a<Space> :Tab / \zs<CR>

"""Emmet plugin settings
let g:user_emmet_leader_key='<C-space>'
"""FIXME work with session as project
"nmap <F3> <ESC>:call LoadSession()<CR> 
"let s:sessionloaded = 0 
"function! LoadSession() 
"    setlocal modifiable
"    source session.vim 
"    let s:sessionloaded = 1 
"endfunction 
"function! SaveSession() 
"    if s:sessionloaded == 1 
"        mksession! 
"    end 
"endfunction 
"autocmd VimLeave * call SaveSession() 
"
"let g:pydiction_location = '~/.vim/vimfiles/complete-dict'
"
"""Diff behaviour
" How to behave in Diff mode TODO check if better options
"if &diff
"    set co=171
"    set equalalways
"    "Option settings for diff mode (diffopt - dip):
"    " filler    - Show filler lines
"    " Context   - lines between a change and a fold
"    " icase     - Ignore changes in case of text
"    " iwhite    - Ignore changes in amount of white space
"    set dip=filler,iwhite,icase
"
"endif
"
"done by plugin
"set stl=%1*(%n)\ %2*%F\ %1*%y%w%m%r%=\ \ \ %2*Row=%l\ Col=%c\%V%3*\ %P%*
"
""" Make Shift-Arrow select like in Solaris
"map! <S-C-Left> <Right><Esc>vb<Left><Insert>
"map! <S-C-Right> <Right><Esc>ve<Right><Insert>
"map! <S-Left> <Right><Esc>v<Left><Insert>
"map! <S-Right> <Right><Esc>v<Right><Insert>
"map! <S-Up> <Esc>v<Up><Insert>
"map! <S-Down> <Esc>v<Down><Insert>
"map <S-C-Left> <Right><Esc>vb<Left>
"map <S-C-Right> <Esc>vw<Right>
"map <S-Left> <Right><Esc>v<Left>
"map <S-Right> <Esc>v<Right>
map <S-Up> <Esc>v<Up>
map <S-Down> <Esc>v<Down>
map <S-Left> <Esc>gT
map <S-Right> <Esc>gt
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
"if has('win32')
"   source $HOME/vimfiles/bundle/matchit/plugin/matchit.vim
"elseif has('unix')
"   source $HOME/.vim/bundle/matchit/plugin/matchit.vim
"endif
"
"""Old matchit settings
"No need for this as the systemverilog plugin should take care of it.
"if exists('loaded_matchit')
"let b:match_ignorecase=0
"let b:match_words=
"  \ '\<begin\>:\<end\>,' .
"  \ '\<if\>:\<else\>,' .
"  \ '\<module\>:\<endmodule\>,' .
"  \ '\<class\>:\<endclass\>,' .
"  \ '\<program\>:\<endprogram\>,' .
"  \ '\<clocking\>:\<endclocking\>,' .
"  \ '\<property\>:\<endproperty\>,' .
"  \ '\<sequence\>:\<endsequence\>,' .
"  \ '\<package\>:\<endpackage\>,' .
"  \ '\<covergroup\>:\<endgroup\>,' .
"  \ '\<primitive\>:\<endprimitive\>,' .
"  \ '\<specify\>:\<endspecify\>,' .
"  \ '\<generate\>:\<endgenerate\>,' .
"  \ '\<interface\>:\<endinterface\>,' .
"  \ '\<function\>:\<endfunction\>,' .
"  \ '\<task\>:\<endtask\>,' .
"  \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
"  \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
"  \ '`ifdef\>:`else\>:`endif\>,'
"endif

"""Old filetypes settings
"autocmd BufRead,BufNewFile *.v,*.vh setfiletype verilog
"autocmd BufRead,BufNewFile *.v,*.vh set expandtab tabstop=4 softtabstop=2 shiftwidth=2
"autocmd BufRead,BufNewFile *.sv,*.svi set filetype=verilog_systemverilog
"autocmd BufRead,BufNewFile *.sv,*.svi set expandtab tabstop=4 softtabstop=2 shiftwidth=2

"""syntastic syntax helper
if has('unix')
   let g:syntastic_python_python_exec = '/sw/common/bin/python3.7'
endif
" syntastic doesn't work well with airline, TODO check why
"set statusline+=%#warningmsg#
"set statusline+=%{SyntasticStatuslineFlag()}
"set statusline+=%*
"let g:syntastic_always_populate_loc_list = 1
"let g:syntastic_auto_loc_list = 1
"let g:syntastic_check_on_open = 1
"let g:syntastic_check_on_wq = 0

"""Tags location function
if has("python3")
"autocmd BufReadPost * call SET_TAGS_LOCATION()
autocmd BufEnter * call SET_TAGS_LOCATION()
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

"""Env var setting functions
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

"""xrun Log file syntax highlighting
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

"""Dont know what this is
vmap <C-S> e <ESC> /<C-R>*<CR>

"""File name with line number detection
"make vim detect filenames with : so it can open the line and columb
"set isfname+=:
"set isfname-=,
"make vim detect filenames with {} so it can open a filename with env var ${WS}
"set isfname+={,}

"""Some automatic log settings 
"autocmd BufReadPost *.log silent %s!,!:!g
"autocmd BufReadPost *.log silent %s!|!:!g
"autocmd BufReadPost *.log :0
"autocmd BufReadPost *.log :/\*E

"""Title line settings
"let &titlestring = hostname() . "[vim(" . expand("%:t") . ")]"
let &titlestring = "%t"
if &term == "screen"
  set t_ts=^[k
  set t_fs=^[\
endif
if &term == "screen" || &term == "xterm"
  set title
endif

"""Do not complete tags (why not?)
" not to use tags
"set complete-=t

"""search for visualy selected text - requested by someone, don't remember who.
vnoremap // y/<C-R>"<CR>

"""Hex mode
" ex command for toggling hex mode - define mapping if desired
command! -bar Hexmode call ToggleHex()

" helper function to toggle hex mode
function! ToggleHex()
  " hex mode should be considered a read-only operation
  " save values for modified and read-only for restoration later,
  " and clear the read-only flag for now
  let l:modified=&mod
  let l:oldreadonly=&readonly
  let &readonly=0
  let l:oldmodifiable=&modifiable
  let &modifiable=1
  if !exists("b:editHex") || !b:editHex
    " save old options
    let b:oldft=&ft
    let b:oldbin=&bin
    " set new options
    setlocal binary " make sure it overrides any textwidth, etc.
    silent :e " this will reload the file without trickeries 
              "(DOS line endings will be shown entirely )
    let &ft="xxd"
    " set status
    let b:editHex=1
    " switch to hex editor
    %!xxd
  else
    " restore old options
    let &ft=b:oldft
    if !b:oldbin
      setlocal nobinary
    endif
    " set status
    let b:editHex=0
    " return to normal editing
    %!xxd -r
  endif
  " restore values for modified and read only state
  let &mod=l:modified
  let &readonly=l:oldreadonly
  let &modifiable=l:oldmodifiable
endfunction

""" Error format settings (for quickfix list)
"let &errorformat="%f:%l:%c: %t%*[^:]:%m,%f:%l: %t%*[^:]:%m," . &errorformat
"let &errorformat="Warning-%t%* %m" . &errorformat

map <F5> :VerilogErrorFormat ncverilog 1<CR>

"""Load personal vimrc
if filereadable(glob("$HOME/myvimrc")) 
    source $HOME/myvimrc
endif

"""this needs to be moved from here
autocmd! BufNewFile *.py call InsertPythonPackage() 

"""VIMRC folding setting
"" vim:fdm=expr:fdl=0
"" vim:fde=getline(v\:lnum)=~'^""'?'>'.(matchend(getline(v\:lnum),'""*')-2)\:'='
