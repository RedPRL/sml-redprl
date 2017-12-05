# redprl.vim

This vim plugin requires Vim 8 (released September 2016).

## Setup

Move this directory to `~/.vim/pack/foo/start/vim-redprl`. (The names `foo` and
`vim-redprl` don't matter.)

If `redprl` is not in your `PATH`, add the following line to your `.vimrc`:

    let g:redprl_path = '$HOME/path/to/redprl'

If you want to recheck the current buffer with a short key combination, add the
following line to your `.vimrc`, replacing `<F5>` as appropriate:

    au FileType redprl nnoremap <F5> :RedPRL<CR>

## Use

While editing a .prl file, run `:RedPRL` to check the current buffer and display
the output in a separate buffer. If there are any syntax errors, the cursor will
jump to the first one.
