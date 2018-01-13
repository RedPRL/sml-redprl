" vim-RedPRL ftplugin
" Language:     RedPRL
" Author:       Carlo Angiuli
" Last Change:  2018 January 6

if (exists("b:did_ftplugin") || !has('job'))
  finish
endif

if (!exists('g:redprl_trace'))
  let g:redprl_trace = 0
endif

if (!exists('g:redprl_path'))
  let g:redprl_path = 'redprl'
endif

command! RedPRL :call CheckBuffer()

set errorformat =%E%f:%l.%c-%*\\d.%*\\d\ [%trror]:
set errorformat+=%Z%m

function! CheckBuffer()
  if (exists('s:job'))
    call job_stop(s:job, 'int')
  endif

  if (!bufexists('RedPRL') || (winbufnr(bufwinnr('RedPRL')) != bufnr('RedPRL')))
    belowright vsplit RedPRL
    set buftype=nofile
    set syntax=redprl
    setlocal noswapfile
  else
    execute bufwinnr('RedPRL') . 'wincmd w'
  endif
  silent %d
  wincmd p

  let s:job = job_start(g:redprl_path .
    \(g:redprl_trace ? ' --trace' : '') .
    \' --width=' . s:EditWidth() .
    \' --from-stdin=' . bufname('%'), {
    \'in_io': 'buffer', 'in_buf': bufnr('%'),
    \'out_io': 'buffer', 'out_name': 'RedPRL', 'out_msg': 0,
    \'err_io': 'buffer', 'err_msg': 0,
    \'exit_cb': 'CheckBufferExit'})
endfunction

function! CheckBufferExit(j,status)
  let errbuf = ch_getbufnr(a:j, 'err')
  if (errbuf != -1)
    execute 'cgetbuffer ' . errbuf
    execute 'bwipeout ' . errbuf
    call setqflist([], 'r', {'title': 'RedPRL Errors'})
  endif
  if (len(getqflist()) > 1)
    copen
    cc
  else
    cclose
  endif
  if (exists('s:job'))
    unlet s:job
  endif
endfunction

function! s:EditWidth()
  execute bufwinnr('RedPRL') . 'wincmd w'

  let l:width = winwidth(winnr())
  if (has('linebreak') && (&number || &relativenumber))
    let l:width -= &numberwidth
  endif
  if (has('folding'))
    let l:width -= &foldcolumn
  endif
  if (has('signs'))
    redir => l:signs
    silent execute 'sign place buffer=' . bufnr('%')
    redir END
    if (&signcolumn == "yes" || len(split(l:signs, "\n")) > 2)
      let l:width -= 2
    endif
  endif

  wincmd p
  return l:width
endfunction

let b:did_ftplugin = 1
