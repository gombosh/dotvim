local opt = vim.opt

-- General Settings
opt.ttimeoutlen = 500
opt.timeoutlen = 500
opt.autowrite = false
opt.scrolloff = 4
opt.number = true
opt.wildmode = "list:longest"
opt.wildignore = "*.o,*~,*.pyc"
if vim.fn.has("win32") == 1 then
    opt.wildignore:append(".git\\*,.hg\\*,.svn\\*")
    opt.shell = "cmd.exe"
    opt.shellcmdflag = "/c"
else
    opt.wildignore:append("*/.git/*,*/.hg/*,*/.svn/*,*/.DS_Store")
    opt.shell = "/bin/bash"
end

-- Search and Case
opt.ignorecase = true
opt.smartcase = true
opt.magic = true

-- Matching Brackets
opt.showmatch = true
opt.mat = 2
vim.g.matchparen_timeout = 2
vim.g.matchparen_insert_timeout = 2

-- UI and Behavior
opt.virtualedit = "block"
opt.splitbelow = true
opt.splitright = true
opt.termguicolors = true
opt.laststatus = 2
opt.showtabline = 1
opt.mouse = "a"
opt.mousemodel = "popup"
opt.listchars = { eol = "$", tab = "> ", trail = ".", extends = ">", precedes = "<" }
opt.list = false -- nolist
opt.isfname:remove(",")

-- Indentation and Tabs
opt.expandtab = true
opt.tabstop = 3
opt.shiftwidth = 3
opt.softtabstop = 3
opt.wrap = true

-- Files, Backups, and Undo
if vim.fn.has("unix") == 1 then
    opt.backupdir = ".backup/,~/.backup/,/tmp//"
    opt.directory = ".swp/,~/.swp/,/tmp//"
    opt.undodir = ".undo/,~/.undo/,/tmp//"
    opt.undofile = true
    opt.backup = true
    opt.swapfile = true
else
    local backup_dir = vim.fn.expand("$HOME/backup")
    if vim.fn.isdirectory(backup_dir) == 0 then
        vim.fn.mkdir(backup_dir, "p")
    end
    opt.backupdir = backup_dir
    opt.backup = true
    opt.undofile = true
end

-- Path and Suffixes
opt.suffixesadd = ".v,.py,.sv,.c,.cpp,.h,.svh,.vsif,.sh"
opt.path:append(".,./**")

-- Behavior
opt.switchbuf = "useopen,usetab,newtab"

-- Colorscheme (Default)
vim.cmd([[colorscheme torte]])
