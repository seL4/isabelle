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
  val arity_clause_thy: theory -> ResClause.arityClause list 
  type classrelClauses
  val classrel_clause: string * string list -> ResClause.classrelClause list
  val classrel_clauses_classrel: Sorts.classes -> ResClause.classrelClause list list
  val classrel_clauses_thy: theory -> ResClause.classrelClause list 
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
      let val (cls,ary) = multi_arity_clause tcons_ars expts
      in ((arity_clause tcon_ar @ cls), ary) end;

fun arity_clause_thy thy =
  let val arities = #arities (Type.rep_tsig (Sign.tsig_of thy))
  in #1 (multi_arity_clause (Symtab.dest arities) []) end;


(* Isabelle classes *)

type classrelClauses = ResClause.classrelClause list Symtab.table;

val classrel_of = #2 o #classes o Type.rep_tsig o Sign.tsig_of;
val classrel_clause = ResClause.classrelClauses_of;
fun classrel_clauses_classrel (C: Sorts.classes) = map classrel_clause (Graph.dest C);
val classrel_clauses_thy = List.concat o classrel_clauses_classrel o classrel_of;

end;
