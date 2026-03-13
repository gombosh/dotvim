" Plugins file
"{Vimplug plugins loading
"
"filetype off " required for vundle
if has('win32')
 call plug#begin('$HOME/vimfiles/plugged')
else
 silent! call plug#begin('~/.vim/plugged')
endif
" alternatively, pass a path where it should install plugins
"call plug#begin('~/some/path/here')
"}
"{Copilot 
"" run copilot setup first
Plug 'github/copilot.vim'
"}
" Brief help
"{Tree view (NERDTree)
Plug 'scrooloose/nerdtree', { 'on' : ['NERDTree','NERDTreeToggle'] }
" use F6 as the main access key
"}
"{fuzzy search files
Plug 'ibhagwan/fzf-lua'
" ctrl-p to activate, then just write what's on your mind
"}
"{grep plugins - new plugin for fast grepping - TODO need to experiment with this.
Plug 'mhinz/vim-grepper', { 'on': ['Grepper', '<plug>(GrepperOperator)'] }
"for now I've put it on F10 (and S-F10)
"}
"{asyncrun - this allows to run commands asynchronously
" asyncrun allows to run command asynchonously. use :AsyncRun <command>
Plug 'skywind3000/asyncrun.vim'
"}
"{Repository control - commands for repositories, auto detects the type of repo
" VCSUpdate, VCSVimDiff, VCSCommit etc
Plug 'vim-scripts/vcscommand.vim'
" use :VCS<command> will all the regular repo commands
Plug 'mhinz/vim-signify', { 'on' : 'SignifyToggle' }
" activate with Shift-F11 - will show status for each line
Plug 'tpope/vim-fugitive'
"}
"{plugins for aligning text
Plug 'junegunn/vim-easy-align'
" visual select text, press enter, then select the alignment character
"}
"{Auto close paranthesis
Plug 'windwp/nvim-autopairs'
"}
"{Add lines of intentation
Plug 'lukas-reineke/indent-blankline.nvim'
"}
"{vim-fetch - open files with line numbers
Plug 'kopischke/vim-fetch'
"}
"{vim-colorschemes - Tons of colorschemes to choose from.
Plug 'flazz/vim-colorschemes'
"}
"{vim-dirdiff - diff dirs!!
Plug 'will133/vim-dirdiff'
" use :DirDiff <dir1> <dir2>
" note: don't put the last slash on directory path
" example: ':DirDiff a/b/c/ d/e/f/' wont work, but ':DirDiff a/b/c d/e/f' will.
"}

Plug 'psf/black', { 'for' : 'python', 'branch': 'stable' }
Plug 'tweekmonster/impsort.vim', { 'for' : 'python' }
Plug 'jmcantrell/vim-virtualenv', { 'for' : 'python' }
"}
"{Games
Plug 'vim/killersheep'
"}
"{vim-log-highlighting - log highlighting
Plug 'fei6409/log-highlight.nvim'
"}
"{mru - most recently used files
Plug 'wsdjeg/mru.nvim'
"}
"{status line
Plug 'nvim-lualine/lualine.nvim'
"}
"{Vimplug ending loading settings
" All of your Plugins must be added before the following line
call plug#end() " required
" Enable filetype plugins
filetype plugin indent on " required
"}

"{impsort settings
nnoremap <leader>is :<c-u>ImpSort!<cr>
"}
"{Commenter settings
" Use Neovim's built-in commenting with your F2 muscle memory
nmap <F2> gcc
vmap <F2> gc
imap <F2> <Esc>gcc
" Note: Built-in doesn't have a direct 'sexy' equivalent, 
" but Shift-F2 can trigger a block comment:
vmap <S-F2> gb
"}
"{MRU settings
map <F1> :MRU <cr>
"}
"{Grep Plugin settings
source $VIMHOME/sourced/my_grep.vim
"map <F9> :MyGrep
"imap <F9> <ESC>:MyGrep
"map <S-F9> :MyGrep "<cword>" .<CR>
"vmap <S-F9> :MyGrep "<cword>" .<CR>
"imap <S-F9> <ESC>:MyGrep "<cword>" .<CR>
map <F9> :Ag
imap <F9> <ESC>:Ag 
map <S-F9> :Ag "<cword>" .<CR>
vmap <S-F9> :Ag "<cword>" .<CR>
imap <S-F9> <ESC>:Ag "<cword>" .<CR>
map <F10> :Grepper -tool git<cr>
nnoremap <S-F10> :Grepper -tool git -cword -noprompt<cr>
map <leader>g :AsyncRun grep %<left><left> 
let g:asyncrun_open = 8 "open the quickfix window automatically
"map <leader>g :%!grep 
command! -nargs=* -complete=file MyGrep call MyGrep(<f-args>)
"}

"{easy-align settings
" Start interactive EasyAlign in visual mode (e.g. vip<Enter>)
vmap <Enter> <Plug>(EasyAlign)
" Start interactive EasyAlign for a motion/text object (e.g. gaip)
nmap ga <Plug>(EasyAlign)
"remove all extra white spaces
map <leader>s :%s/\s\+/ /g<CR>:noh<CR>
vmap <leader>s :s/\s\+/ /g<CR>:noh<CR>
"}
"{NERD TREE settings
"Show hidden files in NerdTree
let NERDTreeShowHidden=1
"toggle nerdtree with f6
map <silent> <F6> :NERDTreeToggle<CR>
imap <silent> <F6> <Esc>:NERDTreeToggle<CR>

" Use netrw for remote files/directories, and NERDTree for everything else. {{{1
 " Function to open the file or NERDTree or netrw.
 " Returns: 1 if a file explorer was opened; otherwise, 0.
 function! s:OpenFileOrBrowser(...)
 if a:0 == 0 || a:1 == ''
 NERDTree
 elseif filereadable(a:1)
 execute 'edit '.a:1
 elseif a:1 =~? '^\(scp\|ftp\)://' " Add other protocols as needed.
 execute 'Vexplore '.a:1
 return 1
 elseif isdirectory(a:1)
 execute 'NERDTree '.a:1
 return 1
 endif
 return 0
 endfunction
 " Auto commands to handle OS commandline arguments.
 autocmd StdinReadPre * let s:std_in=1
 autocmd VimEnter * if argc()==1 && !exists('s:std_in') | if <SID>OpenFileOrBrowser(argv()[0]) | wincmd p | enew | wincmd p | endif | endif
 " Command to call the OpenFileOrBrowser function.
 command! -n=? -complete=file -bar Edit :call <SID>OpenFileOrBrowser('<args>')
 " Command-mode abbreviation to replace the :edit Vim command.
 cnoreabbrev e Edit
"}
"{Copilot settings
let g:copilot_filetypes = {
 \ 'gitcommit': v:true,
 \ 'markdown': v:true,
 \ 'yaml': v:true,
 \ 'python': v:true,
 \ 'groovy': v:true
 \ }

autocmd BufReadPre *
 \ let f=getfsize(expand("<afile>"))
 \ | if f > 100000 || f == -2
 \ | let b:copilot_enabled = v:false
 \ | endif
"{VirtualEnv settings
let g:virtualenv_directory = expand('./.venv')
"}
"{ibl settings

lua << EOF
require("ibl").setup {
 indent = {
 char = "▎", -- Common thin line character
 },
 scope = {
 enabled = true, -- Highlights the current indentation level
 show_start = false,
 show_end = false,
 },
}
EOF
"}
"{fuzzy lua search
" --- Fzf-Lua Configuration ---
"  need to install some stuff to make it work:
"  choco install fzf ripgrep fd (windows)
"  sudo apt install fzf (linux)
lua << EOF
local fzf = require('fzf-lua')

fzf.setup({
  "default", -- Use "default" profile (simpler for Windows than "fzf-native")
  winopts = {
    preview = {
      layout = "vertical", -- Vertical preview works better on most Windows screens
    },
  },
  files = {
    -- Force using 'fd' if you have it, as it's faster on Windows NTFS
    -- cmd = "fd --type f --hidden --follow --exclude .git",
  },
})

-- Keybindings
local map = vim.keymap.set
map('n', '<leader>ff', fzf.files, { desc = 'Fzf Files' })
map('n', '<leader>fg', fzf.live_grep, { desc = 'Fzf Live Grep' })
map('n', '<leader>fb', fzf.buffers, { desc = 'Fzf Buffers' })
map('n', '<leader>fh', fzf.help_tags, { desc = 'Fzf Help' })
map('n', '<leader>gs', fzf.git_status, { desc = 'Fzf Git Status' })
EOF
"}
"{lualine
lua << EOF
require('lualine').setup {
  options = {
    theme = 'auto', -- Automatically picks a theme based on your colorscheme
  }
}
EOF
"}
"
