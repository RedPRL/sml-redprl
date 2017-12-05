" vim-RedPRL syntax
" Language:     RedPRL
" Author:       Carlo Angiuli
" Last Change:  2017 December 5

if exists("b:current_syntax")
  finish
endif

setlocal iskeyword+=-

syn keyword redDecl Def Extract Print Rule Tac Thm
syn keyword redSort dim hyp exp lvl tac triv jdg knd
syn match   redHole '?\(\h\w*\)\?'
syn match   redMeta '#'

syn keyword redExpr bool-rec nat-rec int-rec S1-rec pushout-rec
syn keyword redExpr tv ax fcom bool tt ff if wbool wool wif
syn keyword redExpr nat zero succ int negsucc void
syn keyword redExpr S1 base loop lam app record tuple path
syn keyword redExpr line abs pushout left right glue
syn keyword redExpr box cap V Vin Vproj universe U hcom ghcom coe
syn keyword redExpr com gcom lmax
syn match   redExpr '[$*!@=+]\|->\|\~>\|<\~'

syn keyword redTac auto auto-step case cut-lemma elim else exact fresh goal
syn keyword redTac hyp id lemma let claim match of print progress
syn keyword redTac query rec reduce refine repeat rewrite rewrite-hyp symmetry
syn keyword redTac then unfold use with
syn match   redTac '[;`]'

syn keyword redSeq at by in true type synth discrete kan hcom coe cubical
syn match   redSeq '>>'

syn region  redComm start="//" end="$"

syn match   redMesg '\[\(Info\|Output\|Warning\|Error\|Trace\)\]'

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
