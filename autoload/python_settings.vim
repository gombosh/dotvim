"for python activate supertab completion - need to move to filetype detect file
" this was old stuff from before python mode
"au FileType python set omnifunc=pythoncomplete#Complete
"
"Python-Mode plugin settings
"use python3 for pymode
let g:pymode_python = 'python3'
"Enable pymode indentatio
let g:pymode_indent = 1
"Enable pymode folding
let g:pymode_folding = 0
"enable pymode motion
let g:pymode_motion = 1
"enable pymode documentation script and set 'K' as a key for displaying docs
let g:pymode_doc = 1
let g:pymode_doc_bind = 'K'
"Turn on the run code script and bind <leader>r to run command
let g:pymode_run = 1
let g:pymode_run_bind = '<leader>r'
"enable breakpoints and set to <leader>b
let g:pymode_breakpoint = 1
let g:pymode_breakpoint_bind = '<leader>b'
"enable auto lint on write
let g:pymode_lint = 1
let g:pymode_lint_on_write = 1
let g:pymode_lint_message = 1
let g:pymode_lint_checkers = ['pyflakes', 'pep8', 'mccabe']
let g:pymode_lint_ignore = "E501"   "skip 'too long' warning
"let g:pymode_lint_ignore = ["E501", "W",]   "skip 'too long' warning
"enable all python highliting
let g:pymode_syntax_all = 1
"E.g. "E501,W002", "E2,W" (Skip all Warnings and Errors that starts with E2) and etc
let g:pymode_lint_select = ["E501", "W0011", "W430"]
"set location for rope projects
let g:pymode_rope_project_root = "$HOME/rope_projects"

"disable rope lookup project
let g:pymode_rope = 0
let g:pymode_rope_lookup_project = 0 "fix a bug in python mode
"for pymode plugin - remove red end of line 
"let g:pymode_options_max_line_length = 0
let g:pymode_options_colorcolumn = 0
"Turn off code completion support in the plugin
let g:pymode_rope_completion = 0
"Turn off the rope script
let g:pymode_rope = 0

let g:jedi#use_splits_not_buffers = "left"
