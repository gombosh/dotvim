local M = {}

-- Equivalent of the VisualSelection function from the original vimrc
function M.visual_selection(direction, extra_filter)
  local saved_reg = vim.fn.getreg('"')
  vim.cmd('normal! vgvy')
  local pattern = vim.fn.escape(vim.fn.getreg('"'), "\\/.*'$^~[]")
  pattern = vim.fn.substitute(pattern, "\n$", "", "")

  if direction == "gv" then
    -- Requires a search plugin like 'Ack' or 'Ag'
    -- For fzf-lua, we could use live_grep with the pattern
    require("fzf-lua").live_grep({ default_query = pattern })
  elseif direction == "replace" then
    vim.api.nvim_feedkeys(":%s" .. "/" .. pattern .. "/", "n", false)
  end

  vim.fn.setreg("/", pattern)
  vim.fn.setreg('"', saved_reg)
end

-- WS environment variable logic (Modern replacement for SET_WS)
function M.set_ws()
  if os.getenv("WS") then
    return
  end
  local pwd = vim.fn.getcwd()
  if pwd:find("users") then
    local splitted_pwd = vim.split(pwd, "/")
    while #splitted_pwd > 2 and pwd:find("users") do
      local workdir_path = table.concat(splitted_pwd, "/")
      local workdir_params = workdir_path .. "/.params"
      if vim.fn.filereadable(workdir_params) == 1 then
        vim.env.WS = workdir_path
        break
      end
      table.remove(splitted_pwd)
    end
  end
end

return M
