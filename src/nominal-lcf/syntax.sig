signature NOMINAL_LCF_SYNTAX =
sig
  type symbol
  type variable
  type sort

  type statement
  type multitactic
  type tactic

  type sign

  structure VarCtx : DICT
    where type key = variable

  structure Multi :
  sig
    datatype view =
        ALL of statement
      | EACH of statement list
      | FOCUS of int * statement

    val out : sign -> multitactic -> view
  end

  structure Stmt :
  sig
    type 'a binding = symbol list * 'a

    datatype view =
        SEQ of multitactic binding list
      | TAC of tactic
      | VAR of variable

    val out : sign -> statement -> view
  end
end

