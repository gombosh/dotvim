" .vimrc File
" Maintained by: Doron Gombosh
" doron.gombosh@satixfy.com
" http://www.satixfy.com
"https://github.com/gombosh/dotvim.git

if !has('nvim')
    set ttymouse=xterm2
else

"{{ set the path of .vim directory
if has('win32') || has ('win64')
    let $VIMHOME = $HOME."/vimfiles"
else
    let $VIMHOME = $HOME."/.vim"
endif

"{{Leader key
"If you Want a different map leader than \ use this in your myvimrc file
"set mapleader = ",";
"Ever notice a slight lag after typing the leader key + command? This lowers the timeout.
set ttimeoutlen=500
"}}
"
"{{AutoWrite
"don't Write the file automatically when switching between files.
set noautowrite
"}}
"
"{{Shell
if ($OS == 'Windows_NT')
   " 1.2 executing OS command within Vim
   set shell=c:\Windows\system32\cmd.exe
   " shell command flag
   set shellcmdflag=/c
else
   set shell=/bin/bash
endif
"}}
"}


"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{VIM user interface
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Show full tag of completion
"set showfulltag

" number of screen lines to show around the cursor
set scrolloff=2

set number "Show lines numbers
"highlight LineNr ctermfg=grey ctermbg=black guibg=black guifg=grey

"Auto-completion menu for command line - behave like bash
set wildmode=list:longest

"" Ignore compiled files
"set wildignore=*.o,*~,*.pyc
if has("win32")
    set wildignore+=.git\*,.hg\*,.svn\*
else
    set wildignore+=*/.git/*,*/.hg/*,*/.svn/*,*/.DS_Store
endif

" case insensitive search
set ignorecase
set smartcase
"
" For regular expressions turn magic on
set magic
"
"" Show matching brackets when text indicator is over them
"set showmatch "When a bracket is inserted briefly jump to the matching one
"" How many blinks when matching brackets
"set mat=2
"let g:matchparen_timeout = 2
"let g:matchparen_insert_timeout = 2
"
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
""{ Colors and Fonts
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
""Enable filetypes
syntax enable
"
try
    colorscheme torte
catch
endtry
"Set the color scheme. Change this to your preference.
"We have a plugin with 1000 schemes installed

"" Use Unix as the standard file type
"set fileformats=unix,dos,mac
"}
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{ Files, backups and undo
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
"}
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{ Text, tab and indent related
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Use spaces instead of tabs
set expandtab
"Tab stuff http://vimcasts.org/episodes/tabs-and-spaces/
set tabstop=3 "the width of the tab character (in spaces)
set shiftwidth=3 "shiftwidth == softtabstop so i can work with spaces and not tabs
set softtabstop=3 "how many white spaces to insert when tabbing
"set switchbuf+=usetab,newtab //FIXME switch to new tab when quickfix is opened

" 1 tab == 4 spaces
set shiftwidth=4
set tabstop=4

""Prefer a slightly higher line height - that's the gap between lines
set linespace=3

"Better line wrapping
set wrap
" Make shift-W toggle between wrap and unwrap longlines
map <S-W>  :set wrap! <CR>

""""""""""""""""""""""""""""""
"{ Visual mode related
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
"}
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{ Moving around, tabs, windows and buffers
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

"set nofoldenable
if has("eval")
   ""Enable code folding - let's let the plugin control that
   "set foldenable
   ""set foldlevel=99
   "set foldmethod=syntax
   ""set foldmethod=indent
   "set foldmethod=marker
    set foldmethod=expr
    set foldexpr=VimFolds(v:lnum) 
    set foldtext=MyFoldText()
endif

function! VimFolds(lnum)
    " get content of current line and the line below
    let l:cur_line = getline(a:lnum)
    let l:next_line = getline(a:lnum+1)

    if l:cur_line =~# '^"{'
        return '>' . (matchend(l:cur_line, '"{*') - 1)
    else
        if l:cur_line ==# '' && (matchend(l:next_line, '"{*') - 1) == 1
            return 0
        else
            return '='
        endif
    endif
endfunction

function! MyFoldText()
    let line = getline(v:foldstart)
    let folded_line_num = v:foldend - v:foldstart
    let line_text = substitute(line, '^"{\+', '', 'g')
    let fillcharcount = &textwidth - len(line_text) - len(folded_line_num)
    return '+'. repeat('-', 4) . line_text . repeat('.', fillcharcount) . ' (' . folded_line_num . ' L)'
endfunction
"}
""""""""""""""""""""""""""""""
"{ Status line
""""""""""""""""""""""""""""""
" Always show the status line
set laststatus=2
"}
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{ Editing mappings
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
""Bubble multiple lines
vmap <C-Up> xkP`[V`]
vmap <C-Down> xp`[V`]

"add nice block around text
nnoremap <leader># I#<Space><Esc>A<Space>#<Esc>yy2P<C-V>$r#2j.
"}
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{ Misc
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
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
if has("eval")
   set autochdir
else
    autocmd BufEnter,BufRead * silent! lcd %:p:h
endif

"Highlight current line {{{
"Highlight the line of the cursor (helps to mark the current line in bold).
"hi Cursor guifg=Black guibg=green
hi Cursorline term=none cterm=none ctermbg=lightgray guibg=darkred
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

"}
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
"{ Helper functions
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

"Set up an HTML5 template for all new .html files FIXME for system verilog
"autocmd BufNewFile * silent! 0r $VIMHOME/templates/%:e.tpl
"source $VIMHOME/sourced/set_title.vim
source $VIMHOME/sourced/my_python_functions.vim
source $VIMHOME/sourced/new_files_template.vim
"source $VIMHOME/sourced/set_title.vim
"source $VIMHOME/sourced/elog_settings.vim
source $VIMHOME/sourced/plugin_config.vim
"}
"{ Load personal vimrc
if filereadable(glob("$HOME/myvimrc")) 
    source $HOME/myvimrc
endif
"}
endif
