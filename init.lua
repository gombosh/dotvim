-- Neovim Configuration Entry Point
-- Maintained by: Jules (Migrated from Vimscript to Lua)

-- Load General Options
require("config.options")

-- Setup Lazy.nvim and Plugins
require("config.lazy")

-- Load Keymaps
require("config.keymaps")

-- Load Auto-commands and Templates
require("config.autocmds")

-- Load personal overrides (if file exists)
local home = os.getenv("HOME")
local myvimrc = home .. "/myvimrc"
if vim.fn.filereadable(myvimrc) == 1 then
    vim.cmd("source " .. myvimrc)
end
