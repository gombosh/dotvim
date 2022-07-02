" Brief help
" :PluginList       - lists configured plugins
" :PluginInstall    - installs plugins; append `!` to update or just :PluginUpdate
" :PluginSearch foo - searches for foo; append `!` to refresh local cache
" :PluginClean      - confirms removal of unused plugins; append `!` to auto-approve removal
"
" Vimplug plugins loading
"
"filetype off                  " required for vundle
if has('win32')
   call plug#begin('$HOME/vimfiles/plugged')
else
   silent! call plug#begin('~/.vim/plugged')
endif
" alternatively, pass a path where it should install plugins
"call plug#begin('~/some/path/here')

" }}}

Plug 'github/copilot.vim'

"Tree view
Plug 'scrooloose/nerdtree', { 'on' : ['NERDTree','NERDTreeToggle'] }
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
Plug 'mhinz/vim-grepper', { 'on': ['Grepper', '<plug>(GrepperOperator)'] }
"for now I've put it on F10 (and S-F10)
" ACK is another option for grepping
Plug 'mileszs/ack.vim'
" asyncrun allows to run command asynchonously. use :AsyncRun <command>
Plug 'skywind3000/asyncrun.vim'

" commands for repositories, auto detects the type of repo
" VCSUpdate, VCSVimDiff, VCSCommit etc
Plug 'vim-scripts/vcscommand.vim'
" use :VCS<command> will all the regular repo commands
Plug 'mhinz/vim-signify', { 'on' : 'SignifyToggle' }
" activate with Shift-F11 - will show status for each line
"
Plug 'tpope/vim-fugitive'

"" mega plugin with many cool features for systemverilog - TODO help commands +
" disabled for now because it doesn't play well with airline
" TODO check for alternatitve
" add snipets + makeprg fpr xcelium analyze
Plug 'vhda/verilog_systemverilog.vim', { 'for' : 'systemverilog,verilog_systemverilog,log' }
"<leader>i/o/u/I (after tags file is ready)
"for verilog_systemverilog - autocompleation with tab
Plug 'ervandew/supertab'

"for verilog_systemverilog - auto search for functions/variables in file
"(needs ctags to be working)
Plug 'majutsushi/tagbar' ", { 'on' : 'Tagbar' }
" activate with F4
"for verilog_systemverilog - should make folding faster in systemverilog
"I don't know of any specific settings it needs to be working.
"Plug 'Konfekt/FastFold'
"no need to do anything.

" align text
Plug 'junegunn/vim-easy-align'
" visual select text, press enter, then select the alignment character
Plug 'godlygeek/tabular'
" use leader + a + =/:/<space>

" Plug 'TaskList.vim' - not using it

"Auto close paranthesis
"Plug 'raimondi/delimitmate'
Plug 'jiangmiao/auto-pairs'

"Add lines of intentation
Plug 'yggdroot/indentline'

" open files with line numbers
Plug 'kopischke/vim-fetch'

"Best (and simplest) completion I found so far.
"Plug 'maralla/completor.vim'
"Plug 'ajh17/VimCompletesMe.git'
"if has('nvim')
"  Plug 'Shougo/deoplete.nvim', { 'do': ':UpdateRemotePlugins' }
"else
"  Plug 'Shougo/deoplete.nvim'
"  Plug 'roxma/nvim-yarp'
"  Plug 'roxma/vim-hug-neovim-rpc'
"endif
"Plug 'deoplete-plugins/deoplete-jedi'

"Snippet plugins
"-----------------
"advanced snipets, need py3
"Plug 'sirver/ultisnips'
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

" it's part of my git repo
" in windows please close seperatly with 
" git clone --recurse-submodules https://github.com/python-mode/python-mode -c core.symlinks=true bundle/python-mode
"if !has('win32')
"   Plug 'python-mode/python-mode' ", {'pinned': 1}
"else
"Plug 'python-mode/python-mode', { 'branch': 'develop' }
"Plug 'python-mode/python-mode', { 'for': 'python', 'branch': 'develop' }
"Plug 'python-mode/python-mode', { 'for': 'python', 'branch': 'develop' }
"endif

Plug 'psf/black', { 'branch': 'stable' }
Plug 'davidhalter/jedi-vim', { 'for' : 'python' }
Plug 'tweekmonster/impsort.vim', { 'for' : 'python' }
"Plug 'sheerun/vim-polyglot', { 'for' : 'python' } "disabled - we use ale

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

" MOST COMPLICATED!
" auto syntax checking, should appear at the buttom line
" it doesn't play well with airline - replaced by ALE
"Plug 'scrooloose/syntastic'
" trying an alternative
" lint on the fly
Plug 'dense-analysis/ale'

Plug 'neoclide/coc.nvim', {'branch': 'release'}

"Vimplug ending loading settings {{{
" All of your Plugins must be added before the following line
call plug#end()            " required

" Enable filetype plugins
filetype plugin indent on    " required

"if this is a modern version of vim, start matchit builtin plugin
if has("eval")
   packadd! matchit
   runtime macros/matchit.vim
   " If this variable is set, augroup is defined, and start highlighting.
   let g:hl_matchit_enable_on_vim_startup = 1
endif

syntax enable

"-----------"
" UltiSnips
"-----------"
let g:UltiSnipsUsePythonVersion = 3
"let g:UltiSnipsExpandTrigger = '<C-j>'
"let g:UltiSnipsJumpForwardTrigger = '<C-j>'
"let g:UltiSnipsJumpBackwardTrigger = '<C-k>'
let g:UltiSnipsExpandTrigger = '<tab>'

""""""""""""
" Lightline "
""""""""""""
let g:lightline = {
      \ 'active': {
      \   'left': [ [ 'mode', 'paste' ], [ 'readonly', 'absolutepath', 'modified' ] ],
      \ }
      \ }

"----------"
" Supertab "
"----------"
" dorong - brought this back for verilog_systemverilog
let g:SuperTabDefaultCompletionType = 'context'

"###########
"# impsort #
"###########
nnoremap <leader>is :<c-u>ImpSort!<cr>
"---------"
" Deoplete
"---------"
"let g:deoplete#enable_at_startup = 1
"if has('win32')
   "let g:python3_host_prog=expand('$HOME\AppData\Local\Programs\Python\Python39-32\python.exe')
"endif
"let g:loaded_python_provider = 0 "disable python2 support - we use python3
"let g:deoplete#file#enable_buffer_path = 1
"let g:deoplete#enable_smart_case = 1
"let g:deoplete#sources#jedi#python_path = 'python3'
"-----------"
"Python-Mode
"-----------"
""use python3 for pymode
"let g:pymode_python = 'python3'
""Enable pymode indentatio
"let g:pymode_indent = 1
""Enable pymode folding
"let g:pymode_folding = 0
""enable pymode motion
"let g:pymode_motion = 1
""enable pymode documentation script and set 'K' as a key for displaying docs
"let g:pymode_doc = 1
"let g:pymode_doc_bind = 'K'
""Turn on the run code script and bind <leader>r to run command
"let g:pymode_run = 1
"let g:pymode_run_bind = '<leader>r'
""enable breakpoints and set to <leader>b
"let g:pymode_breakpoint = 1
"let g:pymode_breakpoint_bind = '<leader>b'
""enable auto lint on write
"let g:pymode_lint = 1
"let g:pymode_lint_on_write = 1
"let g:pymode_lint_message = 1
"let g:pymode_lint_checkers = ['pyflakes', 'pep8', 'mccabe']
"let g:pymode_lint_ignore = "E501"   "skip 'too long' warning
""let g:pymode_lint_ignore = ["E501", "W",]   "skip 'too long' warning
""enable all python highliting
"let g:pymode_syntax_all = 1
""E.g. "E501,W002", "E2,W" (Skip all Warnings and Errors that starts with E2) and etc
"let g:pymode_lint_select = ["E501", "W0011", "W430"]
""set location for rope projects
"let g:pymode_rope_project_root = "$HOME/rope_projects"
"
""disable rope lookup project
"let g:pymode_rope = 0
"let g:pymode_rope_lookup_project = 0 "fix a bug in python mode
""for pymode plugin - remove red end of line 
""let g:pymode_options_max_line_length = 0
"let g:pymode_options_colorcolumn = 0
""Turn off code completion support in the plugin
"let g:pymode_rope_completion = 0
""Turn off the rope script
"let g:pymode_rope = 0

"-----"
" Jedi
"-----"
"let g:jedi#use_splits_not_buffers = "left"

"--------"
" TagBar "
"--------"
map <F4> :Tagbar<CR>
if has('win32')
   let g:tagbar_ctags_bin = '$VIMHOME/bin/ctags.exe'
else
   let g:tagbar_ctags_bin = '$VIMHOME/bin/uctags/bin/ctags'
endif

"---------------"
" NerdCommenter "
"---------------"
vmap <F2> :call NERDComment('x', 'toggle')<CR> 
nmap <F2> :call NERDComment('n', 'toggle')<CR> 
imap <F2> <ESC>:call NERDComment('n', 'toggle')<CR>
vmap <S-F2> :call NERDComment('x', 'sexy')<CR>

"-----"
" MRU "
"-----"
map <F1> :MRU <cr>


"------------"
" ACK (grep) "
"------------"
let g:ackprg = '/sw/common/bin/ack -s -H --nogroup --column'

""""Grep Plugin
source $VIMHOME/sourced/my_grep.vim
"map  <F9>  :MyGrep
"imap <F9> <ESC>:MyGrep
"map  <S-F9> :MyGrep "<cword>" .<CR>
"vmap <S-F9> :MyGrep "<cword>" .<CR>
"imap <S-F9> <ESC>:MyGrep "<cword>" .<CR>
map  <F9>  :Ack 
imap <F9> <ESC>:Ack 
map  <S-F9> :Ack "<cword>" .<CR>
vmap <S-F9> :Ack "<cword>" .<CR>
imap <S-F9> <ESC>:Ack "<cword>" .<CR>
map <F10> :Grepper -tool git<cr>
nnoremap <S-F10> :Grepper -tool git -cword -noprompt<cr>
map <leader>g :AsyncRun grep %<left><left>  
let g:asyncrun_open = 8 "open the quickfix window automatically
"map <leader>g :%!grep 
command! -nargs=* -complete=file MyGrep call MyGrep(<f-args>)
" --------------------- "
" Verilog Systemverilog "
" --------------------- "
"au BufReadPost *.vsif so ~/bin/vsif.vim
"let g:verilog_syntax_fold_lst = "all"
let g:verilog_efm_level = "error"
let g:verilog_efm_uvm_lst = "all"
"let g:verilog_efm_uvm_lst = "fatal,error,warning"
let g:verilog_navigate_split = 1

"map <F5> :set makeprg=cat\ #<<CR>:VerilogErrorFormat ncverilog 3<CR>:cfile %<CR>:copen<CR>:cn<CR>
map <F5> :set makeprg=grep\ -e\ UVM_FATAL\ -e\ *E\ -e\ *W\ -e\ *F\ %<CR>:VerilogErrorFormat ncverilog 1<CR>:tab sb<CR>:make<CR>:copen<CR><CR>
nnoremap } :<C-R>=len(getqflist())==1?"cc":"cn"<CR><CR>
nnoremap { :<C-R>=len(getqflist())==1?"cc":"cp"<CR><CR>

nnoremap <leader>i :VerilogFollowInstance<CR>
nnoremap <leader>I :VerilogFollowPort<CR>
nnoremap <leader>u :VerilogGotoInstanceStart<CR>
nnoremap <leader>o :VerilogReturnInstance<CR>

"---------------------"
" rainbow_parentheses
"---------------------"
au VimEnter * RainbowParenthesesToggle
au Syntax * RainbowParenthesesLoadRound
au Syntax * RainbowParenthesesLoadSquare
au Syntax * RainbowParenthesesLoadBraces

" --------- "
" Syntastic "
" --------- "
" syntastic doesn't work well with airline, TODO check why
"set statusline+=%#warningmsg#
"set statusline+=%{SyntasticStatuslineFlag()}
"set statusline+=%*
"let g:syntastic_always_populate_loc_list = 1
"let g:syntastic_auto_loc_list = 1
"let g:syntastic_check_on_open = 1
"let g:syntastic_check_on_wq = 0
if has('unix')
   let g:syntastic_python_python_exec = '/usr/local/bin/python3'
endif

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

" ---------- "
" easy-align "
" ---------- "
" Start interactive EasyAlign in visual mode (e.g. vip<Enter>)
vmap <Enter> <Plug>(EasyAlign)
" Start interactive EasyAlign for a motion/text object (e.g. gaip)
nmap ga <Plug>(EasyAlign)
"remove all extra white spaces
map <leader>s :%s/\s\+/ /g<CR>:noh<CR>
vmap <leader>s :s/\s\+/ /g<CR>:noh<CR>

" --------- "
" NERD TREE "
" --------- "
"Show hidden files in NerdTree
let NERDTreeShowHidden=1
"toggle nerdtree with f6
map  <silent> <F6>   :NERDTreeToggle<CR>
imap  <silent> <F6>   <Esc>:NERDTreeToggle<CR>

" ----- "
" EMMET "
" ----- "
"Emmet plugin settings - only loaded for html
let g:user_emmet_leader_key='<C-Space>'

" ----------- "
" delimitmate "
" ----------- "
"let delimitMate_expand_cr = 1
"au FileType verilog_systemverilog inoremap begin begin<CR>end<up><end><CR>
""au FileType verilog_systemverilog let b:delimitMate_matchpairs = "(:),[:],{:}"
"au FileType verilog_systemverilog let b:delimitMate_quotes = "\""
"au FileType vim let b:delimitMate_quotes = "' ` *"

" ----------- "
" autopairs "
" ----------- "
au FileType verilog_systemverilog let g:AutoPairs = {'(':')', '[':']', '{':'}','"':'"'}
au FileType vim let g:AutoPairs = {'(':')', '[':']', '{':'}',"'":"'"}
"let g:AutoPairsShortcutToggle = '<C-S-p>' 
let g:AutoPairsShortcutFastWrap = '<C-.>'
"let g:AutoPairsShortcutJump = '<C-S-n>'
let g:AutoPairsShortcutBackInsert = '<C-,>'

 "ALE
let g:ale_fixers = {
      \    'python': ['yapf'],
      \}

let g:ale_linters = {
      \    'systemverilog': ['/sw/common/bin/svls'],
      \    'verilog_systemverilog': ['/sw/common/bin/svls'],
      \}

let g:tagbar_type_systemverilog = {
        \ 'ctagstype'   : 'SystemVerilog',
        \ 'kinds'       : [
            \ 'b:blocks:1:1',
            \ 'c:constants:1:0',
            \ 'e:events:1:0',
            \ 'f:functions:1:1',
            \ 'm:modules:0:1',
            \ 'n:nets:1:0',
            \ 'p:ports:1:0',
            \ 'r:registers:1:0',
            \ 't:tasks:1:1',
            \ 'A:assertions:1:1',
            \ 'C:classes:0:1',
            \ 'V:covergroups:0:1',
            \ 'I:interfaces:0:1',
            \ 'M:modport:0:1',
            \ 'K:packages:0:1',
            \ 'P:programs:0:1',
            \ 'R:properties:0:1',
            \ 'T:typedefs:0:1'
        \ ],
        \ 'sro'         : '.',
        \ 'kind2scope'  : {
            \ 'm' : 'module',
            \ 'b' : 'block',
            \ 't' : 'task',
            \ 'f' : 'function',
            \ 'C' : 'class',
            \ 'V' : 'covergroup',
            \ 'I' : 'interface',
            \ 'K' : 'package',
            \ 'P' : 'program',
            \ 'R' : 'property'
        \ },
    \ }
" --------------------- "
" Signify (repo browser)"
" --------------------- "
map <leader>dt :SignifyDiff<CR>
set updatetime=1000 "for async update of signify
let g:signify_disable_by_default = 1 "dont start signify by default
map <S-F11> <ESC>:SignifyToggle<CR>

" --- "
" VCS "
" --- "
map <S-F12> :!svn ci % -m "Fixed a Bug"<CR>

