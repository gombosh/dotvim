local autocmd = vim.api.nvim_create_autocmd
local augroup = vim.api.nvim_create_augroup
local utils = require("config.utils")

-- Restore cursor position on file read
autocmd("BufReadPost", {
  group = augroup("RestoreCursor", { clear = true }),
  callback = function()
    local mark = vim.api.nvim_buf_get_mark(0, '"')
    local lcount = vim.api.nvim_buf_line_count(0)
    if mark[1] > 0 and mark[1] <= lcount then
      pcall(vim.api.nvim_win_set_cursor, 0, mark)
    end
  end,
})

-- Change current directory to that of the file in the buffer
autocmd({ "BufEnter", "BufRead" }, {
  group = augroup("AutoChDir", { clear = true }),
  callback = function()
    local path = vim.fn.expand("%:p:h")
    if vim.fn.isdirectory(path) == 1 then
      vim.api.nvim_set_current_dir(path)
    end
  end,
})

-- Highlight current line only in the active window
local cursorline_group = augroup("CursorLine", { clear = true })
autocmd({ "VimEnter", "WinEnter", "BufWinEnter" }, {
  group = cursorline_group,
  callback = function()
    vim.opt_local.cursorline = true
  end,
})
autocmd("WinLeave", {
  group = cursorline_group,
  callback = function()
    vim.opt_local.cursorline = false
  end,
})

-- Handle Workspace Tags and Environment Variable
local workspace_group = augroup("WorkspaceSettings", { clear = true })
autocmd("BufReadPost", {
  group = workspace_group,
  callback = function()
    utils.set_tags_location()
  end,
})
autocmd("BufEnter", {
  group = workspace_group,
  callback = function()
    utils.set_ws()
  end,
})

-- Template Insertion Functions
local function insert_python_template()
  local username = os.getenv("USER") or os.getenv("USERNAME") or "Unknown"
  local date = os.date("%a %b %d, %Y %I:%M%p")
  local year = os.date("%Y")
  local company = "GuardKnox Ltd"
  local filename = vim.fn.expand("%:t")

  local lines = {
    "#!/usr/bin/env python3",
    "'''",
    "-------------------------------------------------------------------------",
    "File name    : " .. filename,
    "Title        : ",
    "Project      : ",
    "Developers   : " .. username,
    "Created      : " .. date,
    "Description  : ",
    "Notes        : ",
    "---------------------------------------------------------------------------",
    "Copyright " .. year .. " (c) " .. company,
    "---------------------------------------------------------------------------*/",
    "'''",
  }
  vim.api.nvim_buf_set_lines(0, 0, 0, false, lines)
end

local function insert_verilog_template()
  local username = os.getenv("USER") or os.getenv("USERNAME") or "Unknown"
  local date = os.date("%a %b %d, %Y %I:%M%p")
  local year = os.date("%Y")
  local company = "GuardKnox Ltd"
  local filename = vim.fn.expand("%:t")

  local lines = {
    "// -------------------------------------------------------------------------",
    "// File name		: " .. filename,
    "// Title				: ",
    "// Project      	: ",
    "// Developers   	: " .. username,
    "// Created      	: " .. date,
    "// Last modified  : ",
    "// Description  	: ",
    "// Notes        	: ",
    "// Version			: 0.1",
    "// ---------------------------------------------------------------------------",
    "// Copyright " .. year .. " (c) " .. company,
    "// Confidential Proprietary ",
    "// ---------------------------------------------------------------------------",
  }
  vim.api.nvim_buf_set_lines(0, 0, 0, false, lines)
end

-- Template Auto-commands
local template_group = augroup("FileTemplates", { clear = true })
autocmd("BufNewFile", {
  group = template_group,
  pattern = "*.py",
  callback = insert_python_template,
})
autocmd("BufNewFile", {
  group = template_group,
  pattern = { "*.v", "*.sv", "*.svh", "*.c", "*.cpp", "*.h" },
  callback = insert_verilog_template,
})
