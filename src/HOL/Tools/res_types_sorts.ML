(*  Author:     Jia Meng, Cambridge University Computer Laboratory
    ID:         $Id$
    Copyright 2004 University of Cambridge

Transformation of Isabelle arities and class relations into clauses
(defined in the structure Clause).
*)

signature RES_TYPES_SORTS =
sig
  exception ARITIES of string
  val arity_clause: string * (string * string list list) list -> ResClause.arityClause list
  val arity_clause_sg: Sign.sg -> ResClause.arityClause list list * (string * 'a list) list
  val arity_clause_thy: theory -> ResClause.arityClause list list * (string * 'a list) list
  type classrelClauses
  val classrel_clause: string * string list -> ResClause.classrelClause list
  val classrel_clauses_classrel: Sorts.classes -> ResClause.classrelClause list list
  val classrel_clauses_sg: Sign.sg -> ResClause.classrelClause list list
  val classrel_clauses_thy: theory -> ResClause.classrelClause list list
  val classrel_of_sg: Sign.sg -> Sorts.classes
  val multi_arity_clause:
    (string * (string * string list list) list) list ->
    (string * 'a list) list ->
    ResClause.arityClause list list * (string * 'a list) list
  val tptp_arity_clause_thy: theory -> string list list
  val tptp_classrel_clauses_sg : Sign.sg -> string list list
end;

structure ResTypesSorts: RES_TYPES_SORTS =
struct

(* Isabelle arities *)

exception ARITIES of string;

fun arity_clause (tcons, []) = raise ARITIES tcons
  | arity_clause (tcons, [ar]) = [ResClause.make_axiom_arity_clause (tcons, ar)]
  | arity_clause (tcons, ar1 :: ars) =
      ResClause.make_axiom_arity_clause (tcons, ar1) :: arity_clause (tcons, ars);

fun multi_arity_clause [] expts = ([], expts)
  | multi_arity_clause ((tcon, []) :: tcons_ars) expts =
      multi_arity_clause tcons_ars ((tcon, []) :: expts)
  | multi_arity_clause (tcon_ar :: tcons_ars) expts =
      let val result = multi_arity_clause tcons_ars expts
      in ((arity_clause tcon_ar :: fst result), snd result) end;

fun arity_clause_sg sg =
  let val arities = #arities (Type.rep_tsig (Sign.tsig_of sg))
  in multi_arity_clause (Symtab.dest arities) [] end;

fun arity_clause_thy thy = arity_clause_sg (Theory.sign_of thy);

fun tptp_arity_clause_thy thy =
  map (map ResClause.tptp_arity_clause) (#1 (arity_clause_thy thy));


(* Isabelle classes *)

type classrelClauses = ResClause.classrelClause list Symtab.table;

val classrel_of_sg = #2 o #classes o Type.rep_tsig o Sign.tsig_of;
val classrel_clause = ResClause.classrelClauses_of;
fun classrel_clauses_classrel (C: Sorts.classes) = map classrel_clause (Graph.dest C);
val classrel_clauses_sg = classrel_clauses_classrel o classrel_of_sg;
val classrel_clauses_thy = classrel_clauses_sg o Theory.sign_of;

val tptp_classrel_clauses_sg =
  map (map ResClause.tptp_classrelClause) o classrel_clauses_sg;

end;
