" .vimrc File
" Maintained by: Doron Gombosh
" doron.gombosh@satixfy.com
" http://www.satixfy.com
"https://github.com/gombosh/dotvim.git

"""Version checking
"version 8.1
"also supports vim 9.0 and nvim
if version < 800 | finish | endif

" Sections:
"    -> General
"    -> VIM user interface
"    -> Colors and Fonts
"    -> Files and backups
"    -> Text, tab and indent related
"    -> Visual mode related
"    -> Moving around, tabs and buffers
"    -> Status line
"    -> Editing mappings
"    -> vimgrep searching and cope displaying
"    -> Misc
"    -> Helper functions

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => General
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"fix copy paste problem
set t_BE=

" set the path of .vim directory
if has('win32') || has ('win64')
    let $VIMHOME = $HOME."/vimfiles"
else
    let $VIMHOME = $HOME."/.vim"
endif

"Forget compatibility with Vi. Believe me, it's better this way.
set nocompatible              " be iMproved, required



"If you Want a different map leader than \ use this in your myvimrc file
"set mapleader = ",";
"Ever notice a slight lag after typing the leader key + command? This lowers the timeout.
set ttimeoutlen=500


"don't Write the file automatically when switching between files.
set noautowrite

if ($OS == 'Windows_NT')
   " 1.2 executing OS command within Vim
   set shell=c:\Windows\system32\cmd.exe
   " shell command flag
   set shellcmdflag=/c
else
   set shell=/bin/bash
endif



"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => VIM user interface
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Show full tag of completion
"set showfulltag

" number of screen lines to show around the cursor
set scrolloff=2

set number "Show lines numbers
highlight LineNr ctermfg=grey ctermbg=black guibg=black guifg=grey

"Auto-completion menu for command line - behave like bash
set wildmode=list:longest
" More useful command-line completion
"set wildmenu "this will give a menu in the command line instead
"set completeopt=menuone,longest,preview

" Ignore compiled files
set wildignore=*.o,*~,*.pyc
if has("win32")
    set wildignore+=.git\*,.hg\*,.svn\*
else
    set wildignore+=*/.git/*,*/.hg/*,*/.svn/*,*/.DS_Store
endif

set lines=210 columns=999

"Display current cursor position in lower right corner.
"set ruler

" Height of the command bar
set cmdheight=1

" A buffer becomes hidden when it is abandoned
set hidden

" Configure backspace so it acts as it should act
set backspace=eol,start,indent
set whichwrap+=<,>,h,l
"set backspace=2 "make backspace work like most other apps (actually erases the characters)

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

" Don't redraw while executing macros (good performance config)
set lazyredraw "shoud make things faster

" For regular expressions turn magic on
set magic

" Show matching brackets when text indicator is over them
set showmatch "When a bracket is inserted briefly jump to the matching one
" How many blinks when matching brackets
set mat=2
let g:matchparen_timeout = 2
let g:matchparen_insert_timeout = 2

" No annoying sound on errors
set visualbell t_vb= " disable bell and visual bell - I have this 'ding' sound on every tab or any other flashes.
set noerrorbells
"set novisualbell
"set t_vb=
set timeoutlen=500 "how much time to wait for a command

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Colors and Fonts
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"Enable filetypes
syntax enable

try
    colorscheme torte
catch
endtry
"Set the color scheme. Change this to your preference.
"We have a plugin with 1000 schemes installed
"set background=dark

" Set extra options when running in GUI mode
if has("gui_running")
    "set guioptions-=T
    "set guioptions-=e
    "set t_Co=256
    "set guitablabel=%M\ %t
    set go+=acegmiLTrtb
    set guitablabel=%t
endif

" Set utf8 as standard encoding and en_US as the standard language
set encoding=utf-8

" Use Unix as the standard file type
set fileformats=unix,dos,mac

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Files, backups and undo
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
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

map <F12> :tabnew 
map <F11> :close <CR>

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Text, tab and indent related
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Use spaces instead of tabs
set expandtab
"Tab stuff http://vimcasts.org/episodes/tabs-and-spaces/
set tabstop=3 "the width of the tab character (in spaces)
set shiftwidth=3 "shiftwidth == softtabstop so i can work with spaces and not tabs
set softtabstop=3 "how many white spaces to insert when tabbing
"set switchbuf+=usetab,newtab //FIXME switch to new tab when quickfix is opened

" Be smart when using tabs ;)
set smarttab

" 1 tab == 4 spaces
set shiftwidth=4
set tabstop=4

"Indent stuff - needs to be controlled for each filetype seperatlly
"set smartindent "this one tries to guess the indent, but it's bad in most cases
set autoindent "this one is simpler, just takes the indent from the last line, but if I have a special indent file for some filetype, it will overwrite this.

"Prefer a slightly higher line height - that's the gap between lines
set linespace=3

"Better line wrapping
set wrap
" Make shift-W toggle between wrap and unwrap longlines
map <S-W>  :set wrap! <CR>

""""""""""""""""""""""""""""""
" => Visual mode related
""""""""""""""""""""""""""""""
" Visual mode pressing * searches for the current selection
" Super useful! From an idea by Michael Naumann
vnoremap <silent> * :<C-u>call VisualSelection('', '')<CR>/<C-R>=@/<CR><CR>
"""search for visualy selected text - requested by someone, don't remember who.
"vnoremap // y/<C-R>"<CR>

map <S-Up> <Esc>v<Up>
map <S-Down> <Esc>v<Down>
map <S-Left> <Esc>gT
map <S-Right> <Esc>gt

" Make block mode work in insert mode
map! <C-V> <Esc><C-V>

""" maximum of 12 tabs opened with -p
set tabpagemax=12

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Moving around, tabs, windows and buffers
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Disable highlight when <leader><cr> is pressed
map <silent> <leader><cr> :noh<cr>

"Split windows below the current window. - I like this better
set splitbelow
set splitright

" Specify the behavior when switching between buffers 
try
  set switchbuf=useopen,usetab,newtab
  set stal=2
catch
endtry

" Return to last edit position when opening files (You want this!)
au BufReadPost * if line("'\"") > 1 && line("'\"") <= line("$") | exe "normal! g'\"" | endif

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

"Opens a vertical split and switches over (\v)
nnoremap <leader>v <C-w>v<C-w>l

" suffixesadd - used when searching for a file with gf
set suffixesadd=.v,.py,.sv,.c,.cpp,.h,.svh,.vsif,.sh
"path - This is a list of directories which will be searched when using gf
"add spv include and uvm include
"set path=.,,./**,../**
set path=.,./**

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

set nofoldenable
"if has("eval")
   ""Enable code folding - let's let the plugin control that
   "set foldenable
   ""set foldlevel=99
   "set foldmethod=syntax
   ""set foldmethod=indent
   ""set foldmethod=marker
"endif

""""""""""""""""""""""""""""""
" => Status line
""""""""""""""""""""""""""""""
" Always show the status line
set laststatus=2

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Editing mappings
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"very usefull for the anoying dos/unix files - force to dos mode.
map <leader>dos :e ++ff=dos<CR>
map <leader>unix :e ++ff=unix<CR>

"the next one actually changes the file. save and check in after you do that
"for permanent fix.
map <leader>dos2unix :%s/\r\(\n\)/\1/g<CR>

" Make Space bar enter insert mode - I'm just used to that, sorry.
map <Space> <Insert>

" Make shift-insert work like in Xterm
map <S-Insert> <MiddleMouse>
map! <S-Insert> <MiddleMouse>
" Use popup menu for right mouse button and keep shift-left mouse button as search
set mousemodel=popup
set mouse=a
map <S-LeftMouse> <LeftMouse>*
map! <S-LeftMouse> <Esc><LeftMouse>*

"Bubble single lines (kicks butt)
"http://vimcasts.org/episodes/bubbling-text/
nmap <C-Up> ddkP
nmap <C-Down> ddp
"Bubble multiple lines
vmap <C-Up> xkP`[V`]
vmap <C-Down> xp`[V`]

"add nice block around text
nnoremap <leader># I#<Space><Esc>A<Space>#<Esc>yy2P<C-V>$r#2j.

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Misc
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
if has('win32') && !has('nvim')
    set pythonthreedll=python310.dll
    set pythonthreehome=$TEMP\..\Programs\Python\Python310
endif

"Shortcut for editing  vimrc file in a new tab - this is one of the most
"usefull things in the world!
nmap <leader>ev :tabedit $MYVIMRC<cr>
nmap <leader>ep :tabedit $VIMHOME/sourced/plugin_config.vim<cr>

" Source the vimrc file after saving it. This way, you don't have to reload Vim to see the changes. {{{
if has("autocmd")
 augroup myvimrchooks
  au!
     autocmd bufwritepost vimrc,plugin_config.vim source $MYVIMRC
 augroup END
endif

"Automatically change current directory to that of the file in the buffer
"vim actually has a native function for this 'autochdir' so use that for
"modern version. otherwise, use a workaround.
autocmd BufEnter,BufRead * silent! lcd %:p:h
"if has("eval")
"   set autochdir
"else
"   "autocmd BufEnter,BufRead * cd %:p:h
"endif

"Highlight current line {{{
"Highlight the line of the cursor (helps to mark the current line in bold).
"hi Cursor guifg=Black guibg=green
hi Cursorline term=none cterm=none ctermbg=Green guibg=darkred
augroup CursorLine
  au!
  au VimEnter,WinEnter,BufWinEnter * setlocal cursorline
  au WinLeave * setlocal nocursorline
augroup END

"Copy current filename with path to clipboard
map <leader>pwd <Esc>:let @* = expand('%:p')<cr>

set cf "jump to first error in quickfix

"""Hex mode
" ex command for toggling hex mode - define mapping if desired
"source $VIMHOME/sourced/hexmode.vim
"command! -bar Hexmode call ToggleHex()

map <F7> :profile start /home/$USER/gvim_profile.log<CR>:profile func *<CR>:profile file *<CR>

"fix problem where opening a tab causes the bottom line to dissapear
set showtabline=2 
set listchars=eol:$,tab:\>\ ,trail:.,extends:>,precedes:<
set nolist   " to turn on (use :set nolist to turn off)
set isfname-=,
":set includeexpr=substitute(v:fname,'\\|',':','g')

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" => Helper functions
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
function! CmdLine(str)
    call feedkeys(":" . a:str)
endfunction 

function! VisualSelection(direction, extra_filter) range
    let l:saved_reg = @"
    execute "normal! vgvy"

    let l:pattern = escape(@", "\\/.*'$^~[]")
    let l:pattern = substitute(l:pattern, "\n$", "", "")

    if a:direction == 'gv'
        call CmdLine("Ack '" . l:pattern . "' " )
    elseif a:direction == 'replace'
        call CmdLine("%s" . '/'. l:pattern . '/')
    endif

    let @/ = l:pattern
    let @" = l:saved_reg
endfunction

"let g:ale_disable_lsp = 1

"Set up an HTML5 template for all new .html files FIXME for system verilog
"autocmd BufNewFile * silent! 0r $VIMHOME/templates/%:e.tpl
"source $VIMHOME/sourced/set_title.vim
source $VIMHOME/sourced/my_python_functions.vim
source $VIMHOME/sourced/new_files_template.vim
"source $VIMHOME/sourced/set_title.vim
"source $VIMHOME/sourced/elog_settings.vim
source $VIMHOME/sourced/plugin_config.vim


"""Load personal vimrc
if filereadable(glob("$HOME/myvimrc")) 
    source $HOME/myvimrc
endif
