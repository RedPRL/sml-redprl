" vim-RedPRL syntax
" Language:     RedPRL
" Author:       Carlo Angiuli
" Last Change:  2018 March 21

if exists("b:current_syntax")
  finish
endif

setlocal iskeyword=@,48-57,-,',/

syn sync minlines=50

syn match   redprlParenErr ')'
syn match   redprlBrackErr ']'

syn region  redprlEncl transparent start="(" end=")" contains=ALLBUT,redprlParenErr
syn region  redprlEncl transparent start="\[" end="\]" contains=ALLBUT,redprlBrackErr

syn keyword redprlDecl define print theorem tactic quit extract
syn keyword redprlSort dim hyp exp lvl tac jdg knd
syn match   redprlHole '?\k*'
syn match   redprlMeta '#'

syn keyword redprlExpr ax fcom bool tt ff if nat
syn keyword redprlExpr zero succ nat-rec int pos negsucc int-rec void S1 base loop
syn keyword redprlExpr S1-rec lam record tuple path line pushout left right glue
syn keyword redprlExpr pushout-rec coeq cecod cedom coeq-rec mem ni box cap ecom V VV WU
syn keyword redprlExpr Vin Vproj U abs hcom com ghcom gcom coe lmax omega
syn match   redprlExpr '[$*!@=+]\|->\|\~>\|<\~'

syn keyword redprlTac auto auto-step case cut-lemma elim else exact goal
syn keyword redprlTac hyp id lemma let claim match of print trace progress
syn keyword redprlTac query reduce refine repeat rewrite symmetry
syn keyword redprlTac then unfold use with without fail inversion concl assumption
syn match   redprlTac '[;`]'

syn keyword redprlSeq at by in true type synth discrete kan pre

syn region  redprlComm start="\k\@1<!//" end="$"
syn region  redprlBlockComm start="/\*" end="\*/" contains=redprlBlockComm

syn match   redprlMesg '\[\(Info\|Output\|Warning\|Error\)\]'
syn keyword redprlMesg Trace

syn match   redprlAnon '_\d\+'
syn match   redprlAnon '_\d\+\/\k\+'

hi def link redprlParenErr Error
hi def link redprlBrackErr Error
hi def link redprlDecl Structure
hi def link redprlSort Identifier
hi def link redprlHole Special
hi def link redprlMeta Identifier
hi def link redprlExpr Identifier
hi def link redprlTac  Statement
hi def link redprlSeq  Normal
hi def link redprlComm Comment
hi def link redprlBlockComm Comment
hi def link redprlMesg Structure
hi def link redprlAnon NonText

let b:current_syntax = "redprl"
