structure NominalLcfView =
struct
  datatype seq_mode = 
      PARALLEL
    | SEQUENTIAL

  datatype ('mtac, 'tac, 'rule) tactic_view =
      RULE of 'rule
    | MTAC of 'mtac

  datatype ('ann, 'mtac, 'tac, 'var, 'atom) multitactic_view =
      ALL of seq_mode * 'tac
    | EACH of seq_mode * 'tac list
    | FOCUS of int * 'tac
    | PROGRESS of 'mtac
    | ORELSE of 'mtac * 'mtac
    | REC of 'var * 'mtac
    | VAR of 'var
    | SEQ of 'atom list * 'mtac * 'mtac
    | HOLE of 'ann 
end

signature NOMINAL_LCF_SYNTAX =
sig
  type atom = Sym.t
  type variable = Var.t

  (* A [rule] is an atomic tactic, a leaf node of a proof. *)
  type rule

  (* A [tactic] operates on a single judgment. *)
  type tactic

  (* A [multitactic] operates on a full proof-state. *)
  type multitactic

  (* The notion of a signature may differ depending on the refinement theory.
   * Signatures might contain declarations, definitional extensions, etc.; the
   * Nominal LCF theory is completely agnostic on this count. *)
  type sign

  (* The type of annotations *)
  type ann

  structure VarCtx : DICT
    where type key = variable

  val tactic : sign -> tactic -> (multitactic, tactic, rule) NominalLcfView.tactic_view
  val multitactic : sign -> multitactic -> (ann, multitactic, tactic, variable, atom) NominalLcfView.multitactic_view
end

