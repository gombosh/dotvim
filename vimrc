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
"fix copy paste problem
set t_BE=
"Forget compatibility with Vi. Believe me, it's better this way.
set nocompatible              " be iMproved, required


" Vimplug plugins loading {{{
""""Vundle initial loading settings
filetype off                  " required for vundle
" set the runtime path to include Vundle and initialize
if has('win32')
   "set rtp+=$HOME/vimfiles/bundle/Vundle.vim
   call plug#begin('$HOME/vimfiles/plugged')
else
   "set rtp+=~/.vim/bundle/Vundle.vim
   silent! call plug#begin('~/.vim/plugged')
endif
" alternatively, pass a path where Vundle should install plugins
"call vundle#begin('~/some/path/here')
" }}}

"Plugins {{{
" let Vundle manage Vundle, required
" this gets and manages plugins from git
"Plug 'VundleVim/Vundle.vim'

"for ozr
Plug 'vim-scripts/VisIncr'

"Tree view
Plug 'scrooloose/nerdtree', { 'on' : ['NERDTree','NERDTreeToggle'] }
"Plug 'greggerz/nerdtree-svn-plugin' not working in linux
" use F6 as the main access key

" this colors paranthesis opening/closing in the same color.
Plug 'kien/rainbow_parentheses.vim'
" this works automatically

" this is the nice buttom line with info
Plug 'itchyny/lightline.vim'
"Plug 'vim-airline/vim-airline'
" already setup for you, but you can play with it if you want.

" this allows movement in the code from declaration to instance etc. (beta)
"Plug 'brookhong/cscope.vim'
"<leader>fa to start

" fuzzy smart file search
Plug 'ctrlpvim/ctrlp.vim'
" ctrl-p to activate, then just write what's on your mind
" F5 from inside ctrlp will update the database

" new plugin for fast grepping - TODO need to experiment with this.
"Plug 'wsdjeg/flygrep.vim'
Plug 'mhinz/vim-grepper'
"for now I've put it on F10 (and S-F10)

" commands for repositories, auto detects the type of repo
Plug 'vim-scripts/vcscommand.vim'
" use :VCS<command> will all the regular repo commands
Plug 'mhinz/vim-signify', { 'on' : 'SignifyToggle' }

" auto syntax checking, should appear at the buttom line
" it doesn't play well with airline
Plug 'scrooloose/syntastic'
" trying an alternative
" lint on the fly - disabled until I can get it working
"Plug 'w0rp/ale'
Plug 'dense-analysis/ale'

" mega plugin with many cool features for systemverilog - TODO help commands +
" disabled for now because it doesn't play well with airline
" TODO check for alternatitve
" add snipets + makeprg fpr xcelium analyze
Plug 'vhda/verilog_systemverilog.vim', { 'for' : 'verilog_systemverilog,log' }
"<leader>i/o/u/I (after tags file is ready)
"for verilog_systemverilog - highlighes the matches of words
Plug 'vimtaku/hl_matchit.vim'
"for verilog_systemverilog - autocompleation with tab
Plug 'ervandew/supertab'

"for verilog_systemverilog - auto search for functions/variables in file
"(needs ctags to be working)
Plug 'majutsushi/tagbar' ", { 'on' : 'Tagbar' }
" activate with F4
"for verilog_systemverilog - should make folding faster in systemverilog
"I don't know of any specific settings it needs to be working.
Plug 'Konfekt/FastFold'
"no need to do anything.

" align text
Plug 'junegunn/vim-easy-align'
Plug 'godlygeek/tabular'
" use leader + a + =/:/<space>

" Plug 'TaskList.vim' - not using it

"Auto close paranthesis
"Plug 'raimondi/delimitmate'
Plug 'jiangmiao/auto-pairs'

"Add lines of intentation
Plug 'yggdroot/indentline'

" open files with line numbers - old and problematic version
"disabled.
"Plug 'bogado/file-line'

" open files with line numbers
Plug 'kopischke/vim-fetch'

"if !has('win32')
"   Plug 'valloric/youcompleteme'
"endif
"Best (and simplest) completion I found so far.
Plug 'maralla/completor.vim'
"Plug 'ajh17/VimCompletesMe.git'
if has('nvim')
  Plug 'Shougo/deoplete.nvim', { 'do': ':UpdateRemotePlugins' }
else
  Plug 'Shougo/deoplete.nvim'
  Plug 'roxma/nvim-yarp'
  Plug 'roxma/vim-hug-neovim-rpc'
endif
Plug 'deoplete-plugins/deoplete-jedi'

"Snippet plugins
"-----------------
"advanced snipets, need py3
Plug 'sirver/ultisnips'
"Plug 'MarcWeber/vim-addon-mw-utils'
"Plug 'tomtom/tlib_vim'
"Plug 'garbas/vim-snipmate', {'pinned': 1}
Plug 'honza/vim-snippets'
"-----------------

"Tons of colorschemes to choose from.
Plug 'flazz/vim-colorschemes'

" diff dirs!!
Plug 'will133/vim-dirdiff'
" use :DirDiff <dir1> <dir2>
" note: don't put the last slash on directory path
" example: ':DirDiff a/b/c/ d/e/f/' wont work, but ':DirDiff a/b/c d/e/f' will.

" made some changes so it's not controlled by vundle
" it's part of my git repo
" in windows please close seperatly with 
" git clone --recurse-submodules https://github.com/python-mode/python-mode -c core.symlinks=true bundle/python-mode
"if !has('win32')
"   Plug 'python-mode/python-mode' ", {'pinned': 1}
"else
"Plug 'python-mode/python-mode', { 'branch': 'develop' }
"Plug 'python-mode/python-mode', { 'for': 'python', 'branch': 'develop' }
Plug 'python-mode/python-mode', { 'for': 'python', 'branch': 'develop' }
"endif
Plug 'davidhalter/jedi-vim'
"Plug 'tweekmonster/impsort.vim'

Plug 'scrooloose/nerdcommenter'

" for html (I use it rarely)
Plug 'rstacruz/sparkup', { 'for' : 'html' }
Plug 'tpope/vim-surround', { 'for' : 'html' }
Plug 'hallettj/jslint.vim', { 'for' : 'html' }
Plug 'mattn/emmet-vim', { 'for' : 'html' }
"Plug 'tweekmonster/django-plus.vim'
"Plug 'vim-scripts/django.vim'
"TODO add usage info

Plug 'vim/killersheep'
Plug 'mtdl9/vim-log-highlighting'

Plug 'yegappan/mru'
Plug 'mileszs/ack.vim'
Plug 'ryanoasis/vim-devicons'


"Plug 'shemerey/vim-project'
"Plug 'vim-scripts/vimprj'
"Plug 'vim-scripts/DfrankUtil'
"Plug 'vim-scripts/indexer.tar.gz'
"Plug 'vim-vdebug/vdebug'
"Plug 'skywind3000/asyncrun.vim'

Plug 'yegappan/mru'
Plug 'mileszs/ack.vim'


""""Extra plugins to test in the future
"check this next (looks really cool)
"Plug 'terryma/vim-multiple-cursors' "select multiple cursors to type to
"Plug 'tomtom/tcomment_vim' "better commenting by filetype
"Plug 'tpope/vim-endwise' "might be able to add 'end' automatically in systemverilog

"Plug 'Valloric/YouCompleteMe'
" The following are examples of different formats supported.
" Keep Plug commands between vundle#begin/end.
" plugin on GitHub repo
"Plug 'tpope/vim-fugitive'
" plugin from http://vim-scripts.org/vim/scripts.html
" Plug 'L9'
" Git plugin not hosted on GitHub
"Plug 'git://git.wincent.com/command-t.git'
" git repos on your local machine (i.e. when working on your own plugin)
"Plug 'file:///home/gmarik/path/to/plugin'
" The sparkup vim script is in a subdirectory of this repo called vim.
" Pass the path to set the runtimepath properly.
"Plug 'rstacruz/sparkup', {'rtp': 'vim/'}
" Install L9 and avoid a Naming conflict if you've already installed a
" different version somewhere else.
" Plug 'ascenator/L9', {'name': 'newL9'}
" }}}

""""Vimplug ending loading settings {{{
" All of your Plugins must be added before the following line
call plug#end()            " required
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
" }}}
set encoding=utf-8

"if this is a modern version of vim, start matchit buildin plugin
if has("eval")
   packadd! matchit
   runtime macros/matchit.vim
endif

if has('win32') && !has('nvim')
   set pythonthreedll=python39.dll
   set pythonthreehome=C:\Users\gombo\AppData\Local\Programs\Python\Python39-32
endif

"Enable filetypes
syntax enable

set visualbell t_vb= " disable bell and visual bell - I have this 'ding' sound on every tab or any other flashes.

"don't Write the file automatically when switching between files.
set noautowrite

set backspace=2 "make backspace work like most other apps (actually erases the characters)

"Tab stuff http://vimcasts.org/episodes/tabs-and-spaces/
set tabstop=3 "the width of the tab character (in spaces)
set shiftwidth=3 "shiftwidth == softtabstop so i can work with spaces and not tabs
set softtabstop=3 "how many white spaces to insert when tabbing
set expandtab "transform tabs to spaces"
"set switchbuf+=usetab,newtab //FIXME switch to new tab when quickfix is opened

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

" dorong - brought this back for verilog_systemverilog
let g:SuperTabDefaultCompletionType = 'context'
"set completeopt=menuone,longest,preview
let g:loaded_python_provider = 0
let g:deoplete#enable_at_startup = 1
if has('win32')
   let g:python3_host_prog=expand('$HOME\AppData\Local\Programs\Python\Python39-32\python.exe')
endif

"Python-Mode plugin settings {{{
"use python3 for pymode
let g:pymode_python = 'python3'
"Enable pymode indentatio
let g:pymode_indent = 1
"Enable pymode folding
let g:pymode_folding = 0
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
let g:pymode_lint_ignore = "E501"   "skip 'too long' warning
"let g:pymode_lint_ignore = ["E501", "W",]   "skip 'too long' warning
"enable all python highliting
let g:pymode_syntax_all = 1
"E.g. "E501,W002", "E2,W" (Skip all Warnings and Errors that starts with E2) and etc
let g:pymode_lint_select = ["E501", "W0011", "W430"]
"set location for rope projects
let g:pymode_rope_project_root = "$HOME/rope_projects"

"disable rope lookup project
let g:pymode_rope = 0
let g:pymode_rope_lookup_project = 0 "fix a bug in python mode
"for pymode plugin - remove red end of line 
"let g:pymode_options_max_line_length = 0
let g:pymode_options_colorcolumn = 0
"Turn off code completion support in the plugin
let g:pymode_rope_completion = 0
"Turn off the rope script
let g:pymode_rope = 0

let g:jedi#use_splits_not_buffers = "left"
" }}}

"Fonts and Color Schemes {{{
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
" }}}

"Tags control {{{
map <F4> :Tagbar<CR>
if has('win32')
   let g:tagbar_ctags_bin = '$HOME/vimfiles/bin/ctags.exe'
else
   let g:tagbar_ctags_bin = '/home/dorong/bin/ctags/bin/ctags'
endif

"Global settings {{{
set showmatch "When a bracket is inserted briefly jump to the matching one

"Indent stuff - needs to be controlled for each filetype seperatlly
"set smartindent "this one tries to guess the indent, but it's bad in most cases
set autoindent "this one is simpler, just takes the indent from the last line, but if I have a special indent file for some filetype, it will overwrite this.

"Prefer a slightly higher line height - that's the gap between lines
set linespace=3

"
"Better line wrapping
set wrap
" Make shift-W toggle between wrap and unwrap longlines
map <S-W>  :set wrap! <CR>

" Allow virtual edit, place cursor wherever you want
" set ve=all
set ve=block

"Set incremental searching (jump to results as you type)
set incsearch
"
"Highlight searching
set hlsearch
"
" case insensitive search
set ignorecase
set smartcase

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
"vim actually has a native function for this 'autochdir' so use that for
"modern version. otherwise, use a workaround.
if has("eval")
   set autochdir
else
   autocmd BufEnter,BufRead * cd %:p:h
endif

"Auto-completion menu for command line - behave like bash
set wildmode=list:longest
" More useful command-line completion
set wildmenu

" Show full tag of completion
set showfulltag

" number of screen lines to show around the cursor
set scrolloff=3

" Make history buffer larger default 20
set hi=100
"
if ($OS == 'Windows_NT')
   " 1.2 executing OS command within Vim
   set shell=c:\Windows\system32\cmd.exe
   " shell command flag
   set shellcmdflag=/c
else
   set shell=/bin/bash
endif
"
" suffixesadd - used when searching for a file with gf
set suffixesadd=.v,.py,.sv,.c,.cpp,.h,.svh,.vsif,.sh
"
"path - This is a list of directories which will be searched when using gf
"add spv include and uvm include
"set path=.,,./**,../**
set path=.,./**

" Make block mode work in insert mode
map! <C-V> <Esc><C-V>
" }}}
"
"Highlight current line {{{
"Highlight the line of the cursor (helps to mark the current line in bold).
hi Cursor guifg=Black guibg=green
hi Cursorline term=none cterm=none ctermbg=Green guibg=darkred
augroup CursorLine
  au!
  au VimEnter,WinEnter,BufWinEnter * setlocal cursorline
  au WinLeave * setlocal nocursorline
augroup END

"Bubble single lines (kicks butt)
"http://vimcasts.org/episodes/bubbling-text/
nmap <C-Up> ddkP
nmap <C-Down> ddp
"Bubble multiple lines
vmap <C-Up> xkP`[V`]
vmap <C-Down> xp`[V`]

" Source the vimrc file after saving it. This way, you don't have to reload Vim to see the changes. {{{
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
" }}}

"allows to navigate open windows using the - ALT + arrow keys
nmap <silent> <A-Up> :wincmd k<CR>
nmap <silent> <A-Down> :wincmd j<CR>
nmap <silent> <A-Left> :wincmd h<CR>
nmap <silent> <A-Right> :wincmd l<CR>

"move btween windows with ctrl
map <c-j> <c-w>j<c-w>_
map <c-k> <c-w>k<c-w>_
map <c-l> <c-w>l<c-w>|
map <c-h> <c-w>h<c-w>|
map <c-=> <c-w>=

"Copy current filename with path to clipboard
map! <leader>pwd <Esc>:let @* = expand('%:p')<cr>

" Backups {{{
if has('unix')
   set backupdir=.backup/,~/.backup/,/tmp//
   set directory=.swp/,~/.swp/,/tmp//
   set undodir=.undo/,~/.undo/,/tmp//
   set undofile
   set backup
   set swapfile
else
   if !isdirectory(expand("$HOME")."/backup")
      call mkdir(expand("$HOME")."/backup", "p")
   endif
   set backupdir=$HOME/backup " backups
   set backup		" keep a backup file (restore to previous version)
   if has('persistent_undo')
      set undofile	" keep an undo file (undo changes after closing)
   endif
endif

"If you exit Vim and later start it again, you would normally lose a lot of
"information.  The viminfo file can be used to remember that information, which
"enables you to continue where you left off.
"set viminfo='100,\"50,:200  " read /write a .viminfo file, don't store more than 50 lines of registers
set viminfo='20,\"50 " read /write a .viminfo file, don't store more than 50 lines of registers

"Mouse {{{
" Use popup menu for right mouse button and keep shift-left mouse button as search
set mousemodel=popup
set mouse=a
map <S-LeftMouse> <LeftMouse>*
map! <S-LeftMouse> <Esc><LeftMouse>*
" }}}

" confirm start a dialog when a command fails {{{
set cf
" }}}


" Commenting and Un-Commenting code {{{
vmap <F2> :call NERDComment('x', 'toggle')<CR> 
nmap <F2> :call NERDComment('n', 'toggle')<CR> 
imap <F2> <ESC>:call NERDComment('n', 'toggle')<CR>
vmap <S-F2> :call NERDComment('x', 'sexy')<CR>
" }}}

"MRU
map <F1> :MRU <cr>
let g:ackprg = '/sw/common/bin/ack -s -H --nogroup --column'
set lazyredraw "shoud make things faster

"Syntax folding and Highlighting {{{
"TODO move to global file
"au BufReadPost *.vsif so ~/bin/vsif.vim
"let g:verilog_syntax_fold_lst = "all"
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
   "set foldmethod=marker
endif

nnoremap <leader>i :VerilogFollowInstance<CR>
nnoremap <leader>I :VerilogFollowPort<CR>
nnoremap <leader>u :VerilogGotoInstanceStart<CR>
nnoremap <leader>o :VerilogReturnInstance<CR>
" }}}

""" maximum of 12 tabs opened with -p
set tabpagemax=12
"
"""guioptions	list of flags that specify how the GUI works
set go+=acegmiLTrtb
set guitablabel=%t
"
"Plugin Settings {{{
""""VCS (svn) plugin settings 
map <S-F11> <ESC>:SignifyToggle<CR>
map <S-F12> :!svn ci % -m "Fixed a Bug"<CR>

map <F12> :tabnew 
map <F11> :close <CR>
"fix problem where opening a tab causes the bottom line to dissapear
set showtabline=2 
set listchars=eol:$,tab:\>\ ,trail:.,extends:>,precedes:<
set nolist   " to turn on (use :set nolist to turn off)
"VCS diff to trunk
map <leader>dt :SignifyDiff<CR>
set updatetime=100 "for async update of signify
let g:signify_disable_by_default = 1 "dont start signify by default

""""Grep Plugin
map <F9>  :MyGrep 
imap <F9> <ESC>:MyGrep 
map <S-F9> :MyGrep "<cword>" .<CR>
vmap <S-F9> :MyGrep "<cword>" .<CR>
imap <S-F9> <ESC>:MyGrep "<cword>" .<CR>
map <F10> :Grepper -tool ag<cr>
nnoremap <S-F10> :Grepper -tool ag -cword -noprompt<cr>
map <leader>g :%!grep 

command! -nargs=* -complete=file MyGrep call MyGrep(<f-args>)

"CSCOPE Plugin - plugin is disabled {{{
"----------
" CSCOPE "
"----------
"if has('win32')
   "let g:cscope_cmd = "$HOME/vimfiles/bin/cscope.exe"
"else
   "let g:cscope_cmd = '$HOME/.vim/bin/cscope.exe'
"endif
""let g:cscope_interested_files = '\.c$\|\.cpp$\|\.h$\|\.hpp'
"let g:cscope_interested_files = '\.py$'

"nnoremap <leader>fa :call CscopeFindInteractive(expand('<cword>'))<CR>
"nnoremap <leader>l :call ToggleLocationList()<CR>

"" s: Find this C symbol
"nnoremap  <leader>fs :call CscopeFind('s', expand('<cword>'))<CR>
"" g: Find this definition
"nnoremap  <leader>fg :call CscopeFind('g', expand('<cword>'))<CR>
"" d: Find functions called by this function
"nnoremap  <leader>fd :call CscopeFind('d', expand('<cword>'))<CR>
"" c: Find functions calling this function
"nnoremap  <leader>fc :call CscopeFind('c', expand('<cword>'))<CR>
"" t: Find this text string
"nnoremap  <leader>ft :call CscopeFind('t', expand('<cword>'))<CR>
"" e: Find this egrep pattern
"nnoremap  <leader>fe :call CscopeFind('e', expand('<cword>'))<CR>
"" f: Find this file
"nnoremap  <leader>ff :call CscopeFind('f', expand('<cword>'))<CR>
"" i: Find files #including this file
"nnoremap  <leader>fi :call CscopeFind('i', expand('<cword>'))<CR>
" }}}

"NERD TREE Plugin {{{
"Show hidden files in NerdTree
let NERDTreeShowHidden=1
"toggle nerdtree with f6
map  <silent> <F6>   :NERDTreeToggle<CR>
imap  <silent> <F6>   <Esc>:NERDTreeToggle<CR>
" }}}
map <F7> :profile start /home/$USER/gvim_profile.log<CR>:profile func *<CR>:profile file *<CR>

set number "Show lines numbers
highlight LineNr ctermfg=grey ctermbg=black guibg=black guifg=grey
" }}}

""""easy align
" Start interactive EasyAlign in visual mode (e.g. vip<Enter>)
vmap <Enter> <Plug>(EasyAlign)
" Start interactive EasyAlign for a motion/text object (e.g. gaip)
nmap ga <Plug>(EasyAlign)
"remove all extra white spaces
map <leader>s :%s/\s\+/ /g<CR>:noh<CR>
vmap <leader>s :s/\s\+/ /g<CR>:noh<CR>

"delimitmate plugin settings {{{
let delimitMate_expand_cr = 1
au FileType verilog_systemverilog inoremap begin begin<CR>end<up><end><CR>
"au FileType verilog_systemverilog let b:delimitMate_matchpairs = "(:),[:],{:}"
au FileType verilog_systemverilog let b:delimitMate_quotes = "\""
au FileType vim let b:delimitMate_quotes = "' ` *"
" }}}

"Emmet plugin settings - only loaded for html {{{
let g:user_emmet_leader_key='<C-Space>'
" }}}

map <S-Up> <Esc>v<Up>
map <S-Down> <Esc>v<Down>
map <S-Left> <Esc>gT
map <S-Right> <Esc>gt

"syntastic syntax helper {{{
if has('unix')
   let g:syntastic_python_python_exec = '/sw/common/bin/python3'
endif
if has('win32')
   set pythonthreedll=python38.dll
   set pythonthreehome=C:\Users\Doron_Dell\AppData\Local\Programs\Python\Python38-32
endif

"for python activate supertab completion - need to move to filetype detect file
" this was old stuff from before python mode
"au FileType python set omnifunc=pythoncomplete#Complete
"
let g:loaded_python_provider = 0
let g:deoplete#enable_at_startup = 1
if has('win32')
   let g:python3_host_prog=expand('$HOME\AppData\Local\Programs\Python\Python38-32\python.exe')
endif

"Python-Mode plugin settings
"use python3 for pymode
let g:pymode_python = 'python3'
"Enable pymode indentatio
let g:pymode_indent = 1
"Enable pymode folding
let g:pymode_folding = 0
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
let g:pymode_lint_ignore = "E501"   "skip 'too long' warning
"let g:pymode_lint_ignore = ["E501", "W",]   "skip 'too long' warning
"enable all python highliting
let g:pymode_syntax_all = 1
"E.g. "E501,W002", "E2,W" (Skip all Warnings and Errors that starts with E2) and etc
let g:pymode_lint_select = ["E501", "W0011", "W430"]
"set location for rope projects
let g:pymode_rope_project_root = "$HOME/rope_projects"

"disable rope lookup project
let g:pymode_rope = 0
let g:pymode_rope_lookup_project = 0 "fix a bug in python mode
"for pymode plugin - remove red end of line 
"let g:pymode_options_max_line_length = 0
let g:pymode_options_colorcolumn = 0
"Turn off code completion support in the plugin
let g:pymode_rope_completion = 0
"Turn off the rope script
let g:pymode_rope = 0

let g:jedi#use_splits_not_buffers = "left"

" syntastic doesn't work well with airline, TODO check why
"set statusline+=%#warningmsg#
"set statusline+=%{SyntasticStatuslineFlag()}
"set statusline+=%*
"let g:syntastic_always_populate_loc_list = 1
"let g:syntastic_auto_loc_list = 1
"let g:syntastic_check_on_open = 1
"let g:syntastic_check_on_wq = 0
" }}}

"""search for visualy selected text - requested by someone, don't remember who.
vnoremap // y/<C-R>"<CR>

"""Hex mode
" ex command for toggling hex mode - define mapping if desired
command! -bar Hexmode call ToggleHex()

"map <F5> :set makeprg=cat\ #<<CR>:VerilogErrorFormat ncverilog 3<CR>:cfile %<CR>:copen<CR>:cn<CR>
map <F5> :set makeprg=grep\ -e\ UVM_FATAL\ -e\ *E\ -e\ *W\ -e\ *F\ %<CR>:VerilogErrorFormat ncverilog 1<CR>:tab sb<CR>:make<CR>:copen<CR><CR>
nnoremap } :<C-R>=len(getqflist())==1?"cc":"cn"<CR><CR>
nnoremap { :<C-R>=len(getqflist())==1?"cc":"cp"<CR><CR>

"""Load personal vimrc
if filereadable(glob("$HOME/myvimrc")) 
    source $HOME/myvimrc
endif

"""this needs to be moved from here
autocmd! BufNewFile *.py call InsertPythonPackage() 
