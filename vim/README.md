# redprl.vim

This vim plugin requires Vim 8 (released September 2016).

## Use

While editing a .prl file, run `:RedPRL` or `<LocalLeader>l` (`l` for `load`)
in the command (normal) mode to check the current buffer and display the output
in a separate buffer. Run `<LocalLeader>p` (`p` for `partial`) to check the current
buffer, ignoring lines below the cursor's current position.

If there are any syntax errors, the cursor will jump to the first one.

## Setup

This plugin is compatible with Vim 8's package system. You can (re)install it by
running the following shell command from the current directory:

    DEST=~/.vim/pack/redprl-org/start ;
    [ -d $DEST/vim-redprl ] && rm -r $DEST/vim-redprl ;
    mkdir -p $DEST && cp -r . $DEST/vim-redprl

If `redprl` is not in your `PATH`, add the following line to your `.vimrc`:

    let g:redprl_path = '/path/to/redprl'

If you want to enable printing traces, add the following line to your `.vimrc`:

    let g:redprl_trace = 1
