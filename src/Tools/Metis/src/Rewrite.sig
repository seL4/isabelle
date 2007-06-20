(* ========================================================================= *)
(* ORDERED REWRITING FOR FIRST ORDER TERMS                                   *)
(* Copyright (c) 2003-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Rewrite =
sig

(* ------------------------------------------------------------------------- *)
(* A type of rewrite systems.                                                *)
(* ------------------------------------------------------------------------- *)

datatype orient = LeftToRight | RightToLeft

type reductionOrder = Term.term * Term.term -> order option

type equationId = int

type equation = Rule.equation

type rewrite

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : reductionOrder -> rewrite

val peek : rewrite -> equationId -> (equation * orient option) option

val size : rewrite -> int

val equations : rewrite -> equation list

val toString : rewrite -> string

val pp : rewrite Parser.pp

(* ------------------------------------------------------------------------- *)
(* Add equations into the system.                                            *)
(* ------------------------------------------------------------------------- *)

val add : rewrite -> equationId * equation -> rewrite

val addList : rewrite -> (equationId * equation) list -> rewrite

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the rewrite order).          *)
(* ------------------------------------------------------------------------- *)

val rewrConv : rewrite -> reductionOrder -> Rule.conv

val rewriteConv : rewrite -> reductionOrder -> Rule.conv

val rewriteLiteralsRule :
    rewrite -> reductionOrder -> LiteralSet.set -> Rule.rule

val rewriteRule : rewrite -> reductionOrder -> Rule.rule

val rewrIdConv : rewrite -> reductionOrder -> equationId -> Rule.conv

val rewriteIdConv : rewrite -> reductionOrder -> equationId -> Rule.conv

val rewriteIdLiteralsRule :
    rewrite -> reductionOrder -> equationId -> LiteralSet.set -> Rule.rule

val rewriteIdRule : rewrite -> reductionOrder -> equationId -> Rule.rule

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system.                                 *)
(* ------------------------------------------------------------------------- *)

val reduce' : rewrite -> rewrite * equationId list

val reduce : rewrite -> rewrite

val isReduced : rewrite -> bool

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule.                                              *)
(* ------------------------------------------------------------------------- *)

val rewrite : equation list -> Thm.thm -> Thm.thm

val orderedRewrite : reductionOrder -> equation list -> Thm.thm -> Thm.thm

end
