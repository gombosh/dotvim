local map = vim.keymap.set
local utils = require("config.utils")

-- Leader Key
vim.g.mapleader = "\\" -- Default backslash

-- General Mappings
map("", "<leader><cr>", ":noh<cr>", { silent = true, desc = "Clear search highlights" })
map("", "<Space>", "<Insert>", { desc = "Enter Insert Mode" })

-- Navigation (Alt + Arrows)
map("n", "<A-Up>", ":wincmd k<CR>", { silent = true })
map("n", "<A-Down>", ":wincmd j<CR>", { silent = true })
map("n", "<A-Left>", ":wincmd h<CR>", { silent = true })
map("n", "<A-Right>", ":wincmd l<CR>", { silent = true })

-- Navigation (Ctrl + hjkl)
map("", "<c-j>", "<c-w>j<c-w>_", { desc = "Move to window below and maximize height" })
map("", "<c-k>", "<c-w>k<c-w>_", { desc = "Move to window above and maximize height" })
map("", "<c-l>", "<c-w>l<c-w>|", { desc = "Move to window right and maximize width" })
map("", "<c-h>", "<c-w>h<c-w>|", { desc = "Move to window left and maximize width" })
map("", "<c-=>", "<c-w>=", { desc = "Equalize window sizes" })

-- Tab Navigation (Shift + Left/Right)
map("", "<S-Left>", ":gT<CR>", { silent = true })
map("", "<S-Right>", ":gt<CR>", { silent = true })
map("", "<S-Up>", "v<Up>", { desc = "Start visual mode and move up" })
map("", "<S-Down>", "v<Down>", { desc = "Start visual mode and move down" })

-- Functional Mappings
map("n", "<F12>", ":tabnew<CR>", { desc = "New tab" })
map("n", "<F11>", ":close<CR>", { desc = "Close window" })
map("n", "<S-W>", ":set wrap!<CR>", { desc = "Toggle wrap" })

-- Visual Selection Search (*)
map("v", "*", function()
  utils.visual_selection("", "")
  -- Trigger search for the pattern set in utils.visual_selection
  vim.api.nvim_feedkeys(vim.api.nvim_replace_termcodes("/<CR>", true, true, true), "n", false)
end, { silent = true, desc = "Search for current selection" })

-- Editing Mappings
map("n", "<leader>dos", ":e ++ff=dos<CR>", { desc = "Re-edit file as DOS format" })
map("n", "<leader>unix", ":e ++ff=unix<CR>", { desc = "Re-edit file as Unix format" })
map("n", "<leader>dos2unix", ":%s/\\r\\(\\n\\)/\\1/g<CR>", { desc = "Convert file to Unix format" })

-- Bubbling text (Ctrl + Up/Down)
map("n", "<C-Up>", "ddkP", { desc = "Bubble line up" })
map("n", "<C-Down>", "ddp", { desc = "Bubble line down" })
map("v", "<C-Up>", "xkP`[V`]", { desc = "Bubble selection up" })
map("v", "<C-Down>", "xp`[V`]", { desc = "Bubble selection down" })

-- Built-in Commenting (F2 muscle memory)
map("n", "<F2>", "gcc", { remap = true, desc = "Toggle line comment" })
map("v", "<F2>", "gc", { remap = true, desc = "Toggle selection comment" })
map("i", "<F2>", "<Esc>gcc", { remap = true, desc = "Toggle line comment" })
map("v", "<S-F2>", "gb", { remap = true, desc = "Toggle block comment" })

-- Misc Utility
map("n", "<leader>pwd", ":let @* = expand('%:p')<cr>", { desc = "Copy current file path to clipboard" })
map("n", "<leader>ev", function()
  local config_path = vim.fn.stdpath("config")
  vim.cmd("tabedit " .. config_path .. "/lua/config/options.lua")
end, { desc = "Edit Neovim configuration" })

-- Right-click/Mouse mappings
map("", "<S-LeftMouse>", "<LeftMouse>*")
map("!", "<S-LeftMouse>", "<Esc><LeftMouse>*")
map("", "<S-Insert>", "<MiddleMouse>")
map("!", "<S-Insert>", "<MiddleMouse>")

-- Block mode in insert mode
map("!", "<C-V>", "<Esc><C-V>", { desc = "Enter block mode from insert mode" })

-- Vertical split and switch
map("n", "<leader>v", "<C-w>v<C-w>l", { desc = "Vertical split and switch" })

-- Grepper Mappings
map("n", "<F10>", ":GrepperGit<cr>", { silent = true, desc = "Search in Git repo" })
map("n", "<S-F10>", ":Grepper -tool git -cword -noprompt<cr>", { silent = true, desc = "Grep word in Git repo" })
map("n", "<leader>g", ":AsyncRun grep %<left><left>", { desc = "Async grep current file" })
