" Put in ~/.config/nvim/syntax/parser_ll1_tests.vim
" then enable with :set syntax=parser_ll1_tests

syn match section "#.*$"
syn keyword kw Input Parser Expect Ok Err
syn match punct '^>'
syn match punct ' >'

hi def link section Constant
hi def link punct   Statement
hi def link kw      PreProc

