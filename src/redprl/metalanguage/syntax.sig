signature METALANGUAGE_SYNTAX =
sig
  type osym
  type osort
  type ovalence
  type oterm
  type oast

  type mlvar
  type meta

  structure Ctx : DICT where type key = mlvar
  val freshVar : unit -> mlvar
  type ('b, 'a) scope

  datatype mltype =
     UNIT
   | ARR of mltype * mltype
   | PROD of mltype * mltype
   | OTERM of osort
   | THEOREM
   | META of meta

  type rule_name = string

  type ('s, 'o, 't) omatch_clause = (('s * ovalence) list, 'o * 't) scope

  datatype ('v, 's, 'o, 'a) mltermf =
     VAR of 'v
   | LET of 'a * ('v, 'a) scope
   | FUN of ('v, 'a) scope
   | APP of 'a * 'a
   | PAIR of 'a * 'a
   | FST
   | SND
   | QUOTE of 'o | GOAL
   | REFINE of rule_name
   | EACH of 'a list
   | TRY of 'a * 'a
   | PUSH of ('s list, 'a) scope
   | NIL
   | PROVE of 'a * 'a
   | OMATCH of 'a * ('s, 'o, 'a) omatch_clause list
   | PRINT of 'a
   | EXACT of 'a

  type annotation = Pos.t option
  datatype ('v, 's, 'o) mlterm = :@ of ('v, 's, 'o, ('v, 's, 'o) mlterm) mltermf * annotation

  type src_mlterm = (string, string, oast * osort) mlterm
  type mlterm_ = (mlvar, osym, oterm) mlterm

  val unscope : ('b, 't) scope -> 'b * 't
  val scope : mlvar * (mlvar, 's, 'o) mlterm -> (mlvar, (mlvar, 's, 'o) mlterm) scope
  val oscope : osym list * ('v, osym, oterm) mlterm -> (osym list, ('v, osym, oterm) mlterm) scope

  structure Ast :
  sig
    val fn_ : string * src_mlterm -> annotation -> src_mlterm
    val let_ : src_mlterm * (string * src_mlterm) -> annotation -> src_mlterm
    val push : string list * src_mlterm -> annotation -> src_mlterm
  end

  structure Resolver :
  sig
    val resolve : (string, string, oast * osort) mlterm -> mlterm_
  end
end
