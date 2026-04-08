# Neovim Configuration (Lua-based)

This is a modern, modular Neovim configuration migrated from a legacy Vimscript/GVim setup. It uses **[lazy.nvim](https://github.com/folke/lazy.nvim)** for plugin management and follows best practices for Neovim 0.9+.

## Installation (Linux)

1. **Backup your current configuration:**
   ```bash
   mv ~/.config/nvim ~/.config/nvim.bak
   ```

2. **Clone this repository into the Neovim config directory:**
   ```bash
   git clone https://github.com/gombosh/dotvim.git ~/.config/nvim
   ```

3. **Install Neovim (if not already installed):**
   Ensure you have Neovim 0.9 or later. On Ubuntu:
   ```bash
   sudo apt install fzf ripgrep fd-find
   ```

4. **Launch Neovim:**
   The first time you run `nvim`, `lazy.nvim` will automatically download and install all plugins.
   ```bash
   nvim
   ```

## Key Features
- **Plugin Manager:** `lazy.nvim` (Faster startup, lazy-loading).
- **Fuzzy Search:** `fzf-lua` (Replaces older FZF integrations).
- **Status Line:** `lualine.nvim`.
- **Modular Structure:** Separated `options.lua`, `keymaps.lua`, and `autocmds.lua`.
- **Legacy Removal:** All GVim and Vim 8 specific logic has been removed for a cleaner experience.

## Configuration Structure
- `init.lua`: Main entry point.
- `lua/config/`: Core settings and configuration logic.
    - `options.lua`: General Neovim settings.
    - `keymaps.lua`: Custom key mappings.
    - `autocmds.lua`: Auto-commands and file templates.
    - `lazy.lua`: Plugin manager initialization.
- `lua/plugins/`: Modular plugin definitions.
    - `init.lua`: Plugin list and their specific settings.

## Custom Overrides
To add your own personal overrides without modifying this repository, create a `~/myvimrc` file. This file will be sourced at the end of the configuration.
