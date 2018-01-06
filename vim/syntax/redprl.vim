" vim-RedPRL syntax
" Language:     RedPRL
" Author:       Carlo Angiuli
" Last Change:  2018 January 6

if exists("b:current_syntax")
  finish
endif

setlocal iskeyword+=-
setlocal iskeyword+=/

syn keyword redDecl Def Extract Print Rule Tac Thm Quit
syn keyword redSort dim hyp exp lvl tac jdg knd
syn match   redHole '?\(\h\w*\)\?'
syn match   redMeta '#'

syn keyword redExpr ax fcom bool tt ff if wbool wool wif wbool-rec wool-rec nat
syn keyword redExpr zero succ nat-rec int negsucc int-rec void S1 base loop
syn keyword redExpr S1-rec lam record tuple path line pushout left right glue
syn keyword redExpr pushout-rec coeq cecod cedom coeq-rec mem ni box cap V VV WU
syn keyword redExpr Vin Vproj U abs hcom com coe lmax omega
syn match   redExpr '[$*!@=+]\|->\|\~>\|<\~'

syn keyword redTac auto auto-step case cut-lemma elim else exact fresh goal
syn keyword redTac hyp id lemma let claim match of print progress
syn keyword redTac query rec reduce refine repeat rewrite symmetry
syn keyword redTac then unfold use with fail inversion concl
syn match   redTac '[;`]'

syn keyword redSeq at by in true type synth discrete kan hcom coe stable
syn match   redSeq '>>'

syn region  redComm start="//" end="$"

syn match   redMesg '\[\(Info\|Output\|Warning\|Error\|Trace\)\]'
syn keyword redMesg Trace

hi def link redDecl Structure
hi def link redSort Identifier
hi def link redHole Error
hi def link redMeta Identifier
hi def link redExpr Identifier
hi def link redTac  Statement
hi def link redSeq  Normal
hi def link redComm Comment
hi def link redMesg Structure

let b:current_syntax = "redprl"
