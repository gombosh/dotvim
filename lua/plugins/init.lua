return {
  -- Copilot
  {
    "github/copilot.vim",
    config = function()
      vim.g.copilot_filetypes = {
        gitcommit = true,
        markdown = true,
        yaml = true,
        python = true,
        groovy = true,
      }
      -- Auto-disable for large files
      vim.api.nvim_create_autocmd("BufReadPre", {
        callback = function()
          local f = vim.fn.getfsize(vim.fn.expand("<afile>"))
          if f > 100000 or f == -2 then
            vim.b.copilot_enabled = false
          end
        end,
      })
    end,
  },

  -- NERDTree
  {
    "preservim/nerdtree",
    cmd = { "NERDTree", "NERDTreeToggle" },
    keys = {
      { "<F6>", ":NERDTreeToggle<CR>", silent = true, desc = "Toggle NERDTree" },
    },
    config = function()
      vim.g.NERDTreeShowHidden = 1
    end,
  },

  -- Fzf-lua
  {
    "ibhagwan/fzf-lua",
    dependencies = { "nvim-tree/nvim-web-devicons" },
    keys = {
      { "<leader>ff", function() require("fzf-lua").files() end, desc = "Fzf Files" },
      { "<leader>fg", function() require("fzf-lua").live_grep() end, desc = "Fzf Live Grep" },
      { "<leader>fb", function() require("fzf-lua").buffers() end, desc = "Fzf Buffers" },
      { "<leader>fh", function() require("fzf-lua").help_tags() end, desc = "Fzf Help" },
      { "<leader>gs", function() require("fzf-lua").git_status() end, desc = "Fzf Git Status" },
      { "<F9>", ":FzfLua ag<CR>", desc = "Ag search" },
    },
    config = function()
      -- Check for fdfind (common on Ubuntu/Debian) and alias it to fd if found
      if vim.fn.executable("fdfind") == 1 and vim.fn.executable("fd") == 0 then
        -- We can tell fzf-lua to use fdfind
        require("fzf-lua").setup({
          "default",
          winopts = {
            preview = {
              layout = "vertical",
            },
          },
          files = {
            cmd = "fdfind --type f --hidden --follow --exclude .git",
          },
          grep = {
            rg_opts = "--column --line-number --no-heading --color=always --smart-case --max-columns=4096 -e",
          }
        })
      else
        require("fzf-lua").setup({
          "default",
          winopts = {
            preview = {
              layout = "vertical",
            },
          },
        })
      end
    end,
  },

  -- Grepper
  {
    "mhinz/vim-grepper",
    cmd = { "Grepper", "GrepperGit" },
    config = function()
      vim.api.nvim_create_user_command("GrepperGit", "Grepper -tool git", {})
    end,
  },

  -- AsyncRun
  {
    "skywind3000/asyncrun.vim",
    config = function()
      vim.g.asyncrun_open = 8
    end,
  },

  -- Version Control
  { "vim-scripts/vcscommand.vim" },
  { "mhinz/vim-signify" },
  { "tpope/vim-fugitive" },

  -- Alignment
  {
    "junegunn/vim-easy-align",
    keys = {
      { "ga", "<Plug>(EasyAlign)", mode = { "n" }, desc = "EasyAlign" },
      { "<Enter>", "<Plug>(EasyAlign)", mode = { "v" }, desc = "EasyAlign" },
    },
  },

  -- Auto Pairs
  {
    "windwp/nvim-autopairs",
    event = "InsertEnter",
    config = true,
  },

  -- Indent Blankline
  {
    "lukas-reineke/indent-blankline.nvim",
    main = "ibl",
    config = function()
      require("ibl").setup({
        indent = { char = "▎" },
        scope = {
          enabled = true,
          show_start = false,
          show_end = false,
        },
      })
    end,
  },

  -- Colorschemes
  { "flazz/vim-colorschemes" },

  -- DirDiff
  { "will133/vim-dirdiff" },

  -- Python specific
  { "psf/black", ft = "python" },
  { "tweekmonster/impsort.vim", ft = "python" },
  {
    "jmcantrell/vim-virtualenv",
    ft = "python",
    config = function()
      vim.g.virtualenv_directory = vim.fn.expand("./.venv")
    end,
  },

  -- MRU
  {
    "wsdjeg/mru.nvim",
    keys = {
      { "<F1>", ":MRU<CR>", desc = "Recent Files" },
    },
  },

  -- Status line
  {
    "nvim-lualine/lualine.nvim",
    dependencies = { "nvim-tree/nvim-web-devicons" },
    config = function()
      require("lualine").setup({
        options = { theme = "auto" },
      })
    end,
  },

  -- Misc
  { "kopischke/vim-fetch" },
  { "fei6409/log-highlight.nvim", config = true },
}
