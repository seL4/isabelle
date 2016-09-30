(*  Title:      Tools/Argo/argo_lit.ML
    Author:     Sascha Boehme

Representation of literals. Literals are terms with a polarity, either positive or negative.
A literal for term t with positive polarity is equivalent to t.
A literal for term t with negative polarity is equivalent to the propositional negation of t.
*)

signature ARGO_LIT =
sig
  datatype literal = Pos of Argo_Term.term | Neg of Argo_Term.term
  val literal: Argo_Term.term -> bool -> literal
  val dest: literal -> Argo_Term.term * bool
  val term_of: literal -> Argo_Term.term
  val signed_id_of: literal -> int
  val signed_expr_of: literal -> Argo_Expr.expr
  val negate: literal -> literal
  val eq_id: literal * literal -> bool
  val eq_lit: literal * literal -> bool
  val dual_lit: literal * literal -> bool
end

structure Argo_Lit: ARGO_LIT =
struct

(* data type *)

datatype literal = Pos of Argo_Term.term | Neg of Argo_Term.term


(* operations *)

fun literal t true = Pos t
  | literal t false = Neg t

fun dest (Pos t) = (t, true)
  | dest (Neg t) = (t, false)

fun term_of (Pos t) = t
  | term_of (Neg t) = t

fun signed_id_of (Pos t) = Argo_Term.id_of t
  | signed_id_of (Neg t) = ~(Argo_Term.id_of t)

fun signed_expr_of (Pos t) = Argo_Term.expr_of t
  | signed_expr_of (Neg t) = Argo_Expr.mk_not (Argo_Term.expr_of t)

fun id_of (Pos t) = Argo_Term.id_of t
  | id_of (Neg t) = Argo_Term.id_of t

fun negate (Pos t) = Neg t
  | negate (Neg t) = Pos t

fun eq_id (lit1, lit2) = (id_of lit1 = id_of lit2)

fun eq_lit (Pos t1, Pos t2) = Argo_Term.eq_term (t1, t2)
  | eq_lit (Neg t1, Neg t2) = Argo_Term.eq_term (t1, t2)
  | eq_lit _ = false

fun dual_lit (Pos t1, Neg t2) = Argo_Term.eq_term (t1, t2)
  | dual_lit (Neg t1, Pos t2) = Argo_Term.eq_term (t1, t2)
  | dual_lit _ = false

end
