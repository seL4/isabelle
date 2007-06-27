(* ========================================================================= *)
(* DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                     *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Rule =
sig

(* ------------------------------------------------------------------------- *)
(* An equation consists of two terms (t,u) plus a theorem (stronger than)    *)
(* t = u \/ C.                                                               *)
(* ------------------------------------------------------------------------- *)

type equation = (Term.term * Term.term) * Thm.thm

val ppEquation : equation Parser.pp

val equationToString : equation -> string

(* Returns t = u if the equation theorem contains this literal *)
val equationLiteral : equation -> Literal.literal option

val reflEqn : Term.term -> equation

val symEqn : equation -> equation

val transEqn : equation -> equation -> equation

(* ------------------------------------------------------------------------- *)
(* A conversion takes a term t and either:                                   *)
(* 1. Returns a term u together with a theorem (stronger than) t = u \/ C.   *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type conv = Term.term -> Term.term * Thm.thm

val allConv : conv

val noConv : conv

val thenConv : conv -> conv -> conv

val orelseConv : conv -> conv -> conv

val tryConv : conv -> conv

val repeatConv : conv -> conv

val firstConv : conv list -> conv

val everyConv : conv list -> conv

val rewrConv : equation -> Term.path -> conv

val pathConv : conv -> Term.path -> conv

val subtermConv : conv -> int -> conv

val subtermsConv : conv -> conv  (* All function arguments *)

(* ------------------------------------------------------------------------- *)
(* Applying a conversion to every subterm, with some traversal strategy.     *)
(* ------------------------------------------------------------------------- *)

val bottomUpConv : conv -> conv

val topDownConv : conv -> conv

val repeatTopDownConv : conv -> conv  (* useful for rewriting *)

(* ------------------------------------------------------------------------- *)
(* A literule (bad pun) takes a literal L and either:                        *)
(* 1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.     *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type literule = Literal.literal -> Literal.literal * Thm.thm

val allLiterule : literule

val noLiterule : literule

val thenLiterule : literule -> literule -> literule

val orelseLiterule : literule -> literule -> literule

val tryLiterule : literule -> literule

val repeatLiterule : literule -> literule

val firstLiterule : literule list -> literule

val everyLiterule : literule list -> literule

val rewrLiterule : equation -> Term.path -> literule

val pathLiterule : conv -> Term.path -> literule

val argumentLiterule : conv -> int -> literule

val allArgumentsLiterule : conv -> literule

(* ------------------------------------------------------------------------- *)
(* A rule takes one theorem and either deduces another or raises an Error    *)
(* exception.                                                                *)
(* ------------------------------------------------------------------------- *)

type rule = Thm.thm -> Thm.thm

val allRule : rule

val noRule : rule

val thenRule : rule -> rule -> rule

val orelseRule : rule -> rule -> rule

val tryRule : rule -> rule

val changedRule : rule -> rule

val repeatRule : rule -> rule

val firstRule : rule list -> rule

val everyRule : rule list -> rule

val literalRule : literule -> Literal.literal -> rule

val rewrRule : equation -> Literal.literal -> Term.path -> rule

val pathRule : conv -> Literal.literal -> Term.path -> rule

val literalsRule : literule -> LiteralSet.set -> rule

val allLiteralsRule : literule -> rule

val convRule : conv -> rule  (* All arguments of all literals *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- reflexivity                                                     *)
(*   x = x                                                                   *)
(* ------------------------------------------------------------------------- *)

val reflexivity : Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------- symmetry                                            *)
(*   ~(x = y) \/ y = x                                                       *)
(* ------------------------------------------------------------------------- *)

val symmetry : Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------- transitivity                            *)
(*   ~(x = y) \/ ~(y = z) \/ x = z                                           *)
(* ------------------------------------------------------------------------- *)

val transitivity : Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- functionCongruence (f,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   f x0 ... x{n-1} = f y0 ... y{n-1}                                       *)
(* ------------------------------------------------------------------------- *)

val functionCongruence : Term.function -> Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- relationCongruence (R,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}                                     *)
(* ------------------------------------------------------------------------- *)

val relationCongruence : Atom.relation -> Thm.thm

(* ------------------------------------------------------------------------- *)
(*   x = y \/ C                                                              *)
(* -------------- symEq (x = y)                                              *)
(*   y = x \/ C                                                              *)
(* ------------------------------------------------------------------------- *)

val symEq : Literal.literal -> rule

(* ------------------------------------------------------------------------- *)
(*   ~(x = y) \/ C                                                           *)
(* ----------------- symNeq ~(x = y)                                         *)
(*   ~(y = x) \/ C                                                           *)
(* ------------------------------------------------------------------------- *)

val symNeq : Literal.literal -> rule

(* ------------------------------------------------------------------------- *)
(* sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)           *)
(* ------------------------------------------------------------------------- *)

val sym : Literal.literal -> rule

(* ------------------------------------------------------------------------- *)
(*   ~(x = x) \/ C                                                           *)
(* ----------------- removeIrrefl                                            *)
(*         C                                                                 *)
(*                                                                           *)
(* where all irreflexive equalities.                                         *)
(* ------------------------------------------------------------------------- *)

val removeIrrefl : rule

(* ------------------------------------------------------------------------- *)
(*   x = y \/ y = x \/ C                                                     *)
(* ----------------------- removeSym                                         *)
(*       x = y \/ C                                                          *)
(*                                                                           *)
(* where all duplicate copies of equalities and disequalities are removed.   *)
(* ------------------------------------------------------------------------- *)

val removeSym : rule

(* ------------------------------------------------------------------------- *)
(*   ~(v = t) \/ C                                                           *)
(* ----------------- expandAbbrevs                                           *)
(*      C[t/v]                                                               *)
(*                                                                           *)
(* where t must not contain any occurrence of the variable v.                *)
(* ------------------------------------------------------------------------- *)

val expandAbbrevs : rule

(* ------------------------------------------------------------------------- *)
(* simplify = isTautology + expandAbbrevs + removeSym                        *)
(* ------------------------------------------------------------------------- *)

val simplify : Thm.thm -> Thm.thm option

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- freshVars                                                        *)
(*   C[s]                                                                    *)
(*                                                                           *)
(* where s is a renaming substitution chosen so that all of the variables in *)
(* C are replaced by fresh variables.                                        *)
(* ------------------------------------------------------------------------- *)

val freshVars : rule

(* ------------------------------------------------------------------------- *)
(*               C                                                           *)
(* ---------------------------- factor                                       *)
(*   C_s_1, C_s_2, ..., C_s_n                                                *)
(*                                                                           *)
(* where each s_i is a substitution that factors C, meaning that the theorem *)
(*                                                                           *)
(*   C_s_i = (removeIrrefl o removeSym o Thm.subst s_i) C                    *)
(*                                                                           *)
(* has fewer literals than C.                                                *)
(*                                                                           *)
(* Also, if s is any substitution that factors C, then one of the s_i will   *)
(* result in a theorem C_s_i that strictly subsumes the theorem C_s.         *)
(* ------------------------------------------------------------------------- *)

val factor' : Thm.clause -> Subst.subst list

val factor : Thm.thm -> Thm.thm list

end
