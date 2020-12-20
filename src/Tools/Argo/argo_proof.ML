(*  Title:      Tools/Argo/argo_proof.ML
    Author:     Sascha Boehme

The proof language of the Argo solver.

Proofs trace the inferences of the solver. They can be used to check unsatisfiability results.

The proof language is inspired by:

  Leonardo de Moura and Nikolaj Bjørner. Proofs and Refutations, and Z3. In
  Proceedings of the LPAR 2008 Workshops, Knowledge Exchange: Automated Provers and Proof
  Assistants, and the 7th International Workshop on the Implementation of Logics,
  volume 418 of CEUR Workshop Proceedings. CEUR-WS.org, 2008.
*)

signature ARGO_PROOF =
sig
  (* types *)
  type proof_id
  datatype tautology =
    Taut_And_1 of int | Taut_And_2 of int * int | Taut_Or_1 of int * int | Taut_Or_2 of int |
    Taut_Iff_1 | Taut_Iff_2 | Taut_Iff_3 | Taut_Iff_4 | Taut_Ite_Then | Taut_Ite_Else
  datatype side = Left | Right
  datatype inequality = Le | Lt
  datatype rewrite =
    Rewr_Not_True | Rewr_Not_False | Rewr_Not_Not | Rewr_Not_And of int | Rewr_Not_Or of int |
    Rewr_Not_Iff |
    Rewr_And_False of int | Rewr_And_Dual of int * int | Rewr_And_Sort of int * int list list |
    Rewr_Or_True of int | Rewr_Or_Dual of int * int | Rewr_Or_Sort of int * int list list |
    Rewr_Iff_True | Rewr_Iff_False | Rewr_Iff_Not_Not | Rewr_Iff_Refl | Rewr_Iff_Symm |
    Rewr_Iff_Dual |
    Rewr_Imp | Rewr_Ite_Prop | Rewr_Ite_True | Rewr_Ite_False | Rewr_Ite_Eq |
    Rewr_Eq_Refl | Rewr_Eq_Symm |
    Rewr_Neg | Rewr_Add of (Rat.rat * int option) list * (Rat.rat * int option) list | Rewr_Sub |
    Rewr_Mul_Nums of Rat.rat * Rat.rat | Rewr_Mul_Zero | Rewr_Mul_One | Rewr_Mul_Comm |
    Rewr_Mul_Assoc of side | Rewr_Mul_Sum of side | Rewr_Mul_Div of side |
    Rewr_Div_Zero | Rewr_Div_One | Rewr_Div_Nums of Rat.rat * Rat.rat |
    Rewr_Div_Num of side * Rat.rat | Rewr_Div_Mul of side * Rat.rat | Rewr_Div_Div of side |
    Rewr_Div_Sum | Rewr_Min_Eq | Rewr_Min_Lt | Rewr_Min_Gt | Rewr_Max_Eq | Rewr_Max_Lt |
    Rewr_Max_Gt | Rewr_Abs | Rewr_Eq_Nums of bool | Rewr_Eq_Sub | Rewr_Eq_Le |
    Rewr_Ineq_Nums of inequality * bool | Rewr_Ineq_Add of inequality * Rat.rat |
    Rewr_Ineq_Sub of inequality | Rewr_Ineq_Mul of inequality * Rat.rat |
    Rewr_Not_Ineq of inequality
  datatype conv =
    Keep_Conv | Then_Conv of conv * conv | Args_Conv of Argo_Expr.kind * conv list |
    Rewr_Conv of rewrite
  datatype rule =
    Axiom of int | Taut of tautology * Argo_Expr.expr | Conjunct of int * int | Rewrite of conv |
    Hyp of int * Argo_Expr.expr | Clause of int list | Lemma of int list | Unit_Res of int |
    Refl of Argo_Expr.expr | Symm | Trans | Cong | Subst | Linear_Comb
  type proof

  (* equalities and orders *)
  val eq_proof_id: proof_id * proof_id -> bool
  val proof_id_ord: proof_id ord

  (* conversion constructors *)
  val keep_conv: conv
  val mk_then_conv: conv -> conv -> conv
  val mk_args_conv: Argo_Expr.kind -> conv list -> conv
  val mk_rewr_conv: rewrite -> conv

  (* context *)
  type context
  val cdcl_context: context
  val cc_context: context
  val simplex_context: context
  val solver_context: context

  (* proof constructors *)
  val mk_axiom: int -> context -> proof * context
  val mk_taut: tautology -> Argo_Expr.expr -> context -> proof * context
  val mk_conj: int -> int -> proof -> context -> proof * context
  val mk_rewrite: conv -> proof -> context -> proof * context
  val mk_hyp: Argo_Lit.literal -> context -> proof * context
  val mk_clause: Argo_Lit.literal list -> proof -> context -> proof * context
  val mk_lemma: Argo_Lit.literal list -> proof -> context -> proof * context
  val mk_unit_res: Argo_Lit.literal -> proof -> proof -> context -> proof * context
  val mk_refl: Argo_Term.term -> context -> proof * context
  val mk_symm: proof -> context -> proof * context
  val mk_trans: proof -> proof -> context -> proof * context
  val mk_cong: proof -> proof -> context -> proof * context
  val mk_subst: proof -> proof -> proof -> context -> proof * context
  val mk_linear_comb: proof list -> context -> proof * context

  (* proof destructors *)
  val id_of: proof -> proof_id
  val dest: proof -> proof_id * rule * proof list

  (* string representations *)
  val string_of_proof_id: proof_id -> string
  val string_of_taut: tautology -> string
  val string_of_rule: rule -> string

  (* unsatisfiability *)
  exception UNSAT of proof
  val unsat: proof -> 'a (* raises UNSAT *)
end

structure Argo_Proof: ARGO_PROOF =
struct

(* types *)

datatype tautology =
  Taut_And_1 of int | Taut_And_2 of int * int | Taut_Or_1 of int * int | Taut_Or_2 of int |
  Taut_Iff_1 | Taut_Iff_2 | Taut_Iff_3 | Taut_Iff_4 | Taut_Ite_Then | Taut_Ite_Else

datatype side = Left | Right

datatype inequality = Le | Lt

datatype rewrite =
  Rewr_Not_True | Rewr_Not_False | Rewr_Not_Not | Rewr_Not_And of int | Rewr_Not_Or of int |
  Rewr_Not_Iff |
  Rewr_And_False of int | Rewr_And_Dual of int * int | Rewr_And_Sort of int * int list list |
  Rewr_Or_True of int | Rewr_Or_Dual of int * int | Rewr_Or_Sort of int * int list list |
  Rewr_Iff_True | Rewr_Iff_False | Rewr_Iff_Not_Not | Rewr_Iff_Refl | Rewr_Iff_Symm |
  Rewr_Iff_Dual |
  Rewr_Imp | Rewr_Ite_Prop | Rewr_Ite_True | Rewr_Ite_False | Rewr_Ite_Eq |
  Rewr_Eq_Refl | Rewr_Eq_Symm |
  Rewr_Neg | Rewr_Add of (Rat.rat * int option) list * (Rat.rat * int option) list | Rewr_Sub |
  Rewr_Mul_Nums of Rat.rat * Rat.rat | Rewr_Mul_Zero | Rewr_Mul_One | Rewr_Mul_Comm |
  Rewr_Mul_Assoc of side | Rewr_Mul_Sum of side | Rewr_Mul_Div of side |
  Rewr_Div_Zero | Rewr_Div_One | Rewr_Div_Nums of Rat.rat * Rat.rat |
  Rewr_Div_Num of side * Rat.rat | Rewr_Div_Mul of side * Rat.rat | Rewr_Div_Div of side |
  Rewr_Div_Sum | Rewr_Min_Eq | Rewr_Min_Lt | Rewr_Min_Gt | Rewr_Max_Eq | Rewr_Max_Lt |
  Rewr_Max_Gt | Rewr_Abs | Rewr_Eq_Nums of bool | Rewr_Eq_Sub | Rewr_Eq_Le |
  Rewr_Ineq_Nums of inequality * bool | Rewr_Ineq_Add of inequality * Rat.rat |
  Rewr_Ineq_Sub of inequality | Rewr_Ineq_Mul of inequality * Rat.rat |
  Rewr_Not_Ineq of inequality

datatype conv =
  Keep_Conv | Then_Conv of conv * conv | Args_Conv of Argo_Expr.kind * conv list |
  Rewr_Conv of rewrite

datatype rule =
  Axiom of int | Taut of tautology * Argo_Expr.expr | Conjunct of int * int | Rewrite of conv |
  Hyp of int * Argo_Expr.expr | Clause of int list | Lemma of int list | Unit_Res of int |
  Refl of Argo_Expr.expr | Symm | Trans | Cong | Subst | Linear_Comb

(*
  Proof identifiers are intentially hidden to prevent that functions outside of this structure
  are able to build proofs. Proof can hence only be built by the functions provided by
  this structure.
*)

datatype proof_id = Cdcl of int | Cc of int | Simplex of int | Solver of int

datatype proof = Proof of proof_id * rule * proof list


(* internal functions *)

val proof_id_card = 4

fun raw_proof_id (Cdcl i) = i
  | raw_proof_id (Cc i) = i
  | raw_proof_id (Simplex i) = i
  | raw_proof_id (Solver i) = i


(* equalities and orders *)

fun int_of_proof_id (Cdcl _) = 0
  | int_of_proof_id (Cc _) = 1
  | int_of_proof_id (Simplex _) = 2
  | int_of_proof_id (Solver _) = 3

fun eq_proof_id (Cdcl i1, Cdcl i2) = (i1 = i2)
  | eq_proof_id (Cc i1, Cc i2) = (i1 = i2)
  | eq_proof_id (Simplex i1, Simplex i2) = (i1 = i2)
  | eq_proof_id (Solver i1, Solver i2) = (i1 = i2)
  | eq_proof_id _ = false

fun proof_id_ord (Cdcl i1, Cdcl i2) = int_ord (i1, i2)
  | proof_id_ord (Cc i1, Cc i2) = int_ord (i1, i2)
  | proof_id_ord (Simplex i1, Simplex i2) = int_ord (i1, i2)
  | proof_id_ord (Solver i1, Solver i2) = int_ord (i1, i2)
  | proof_id_ord (id1, id2) = int_ord (int_of_proof_id id1, int_of_proof_id id2)


(* conversion constructors *)

val keep_conv = Keep_Conv

fun mk_then_conv Keep_Conv c = c
  | mk_then_conv c Keep_Conv = c
  | mk_then_conv c1 c2 = Then_Conv (c1, c2)

fun mk_args_conv k cs =
  if forall (fn Keep_Conv => true | _ => false) cs then Keep_Conv
  else Args_Conv (k, cs)

fun mk_rewr_conv r = Rewr_Conv r


(* context *)

(*
  The proof context stores the next unused identifier. Incidentally, the same type as
  for the proof identifier can be used as context. Every proof-producing module of the
  solver has its own proof identifier domain to ensure globally unique identifiers
  without sharing a single proof context.
*)

type context = proof_id

val cdcl_context = Cdcl 0
val cc_context = Cc 0
val simplex_context = Simplex 0
val solver_context = Solver 0

fun next_id (id as Cdcl i) = (id, Cdcl (i + 1))
  | next_id (id as Cc i) = (id, Cc (i + 1))
  | next_id (id as Simplex i) = (id, Simplex (i + 1))
  | next_id (id as Solver i) = (id, Solver (i + 1))


(* proof destructors *)

fun id_of (Proof (id, _, _)) = id

fun dest (Proof p) = p


(* proof constructors *)

fun mk_proof r ps cx =
  let val (id, cx) = next_id cx
  in (Proof (id, r, ps), cx) end

fun mk_axiom i = mk_proof (Axiom i) []
fun mk_taut t e = mk_proof (Taut (t, e)) []
fun mk_conj i n p = mk_proof (Conjunct (i, n)) [p]

fun mk_rewrite Keep_Conv p cx = (p, cx)
  | mk_rewrite c p cx = mk_proof (Rewrite c) [p] cx

fun mk_hyp lit = mk_proof (Hyp (Argo_Lit.signed_id_of lit, Argo_Lit.signed_expr_of lit)) []
fun mk_clause lits p cx = mk_proof (Clause (map Argo_Lit.signed_id_of lits)) [p] cx
fun mk_lemma lits p = mk_proof (Lemma (map Argo_Lit.signed_id_of lits)) [p]

(*
  Replay of unit-resolution steps can be optimized if all premises follow a specific form.
  Therefore, each premise is checked if it is in clausal form.
*)

fun check_clause (p as Proof (_, Clause _, _)) = p
  | check_clause (p as Proof (_, Lemma _, _)) = p
  | check_clause (p as Proof (_, Unit_Res _, _)) = p
  | check_clause _ = raise Fail "bad clause proof"

fun mk_unit t p1 p2 = mk_proof (Unit_Res (Argo_Term.id_of t)) (map check_clause [p1, p2])

fun mk_unit_res (Argo_Lit.Pos t) p1 p2 = mk_unit t p1 p2
  | mk_unit_res (Argo_Lit.Neg t) p1 p2 = mk_unit t p2 p1

fun mk_refl t = mk_proof (Refl (Argo_Term.expr_of t)) []
fun mk_symm p = mk_proof Symm [p]

fun mk_trans (Proof (_, Refl _, _)) p2 = pair p2
  | mk_trans p1 (Proof (_, Refl _, _)) = pair p1
  | mk_trans p1 p2 = mk_proof Trans [p1, p2]

fun mk_cong p1 p2 = mk_proof Cong [p1, p2]

fun mk_subst p1 (Proof (_, Refl _, _)) (Proof (_, Refl _, _)) = pair p1
  | mk_subst p1 p2 p3 = mk_proof Subst [p1, p2, p3]

fun mk_linear_comb ps = mk_proof Linear_Comb ps


(* string representations *)

fun string_of_proof_id id = string_of_int (proof_id_card * raw_proof_id id + int_of_proof_id id)

fun string_of_list l r f xs = enclose l r (space_implode ", " (map f xs))
fun parens f xs = string_of_list "(" ")" f xs
fun brackets f xs = string_of_list "[" "]" f xs

fun string_of_taut (Taut_And_1 n) = "and " ^ string_of_int n
  | string_of_taut (Taut_And_2 (i, n)) = "and " ^ parens string_of_int [i, n]
  | string_of_taut (Taut_Or_1 (i, n)) = "or " ^ parens string_of_int [i, n]
  | string_of_taut (Taut_Or_2 n) = "or " ^ string_of_int n
  | string_of_taut Taut_Iff_1 = "(p1 == p2) | p1 | p2"
  | string_of_taut Taut_Iff_2 = "(p1 == p2) | ~p1 | ~p2"
  | string_of_taut Taut_Iff_3 = "~(p1 == p2) | ~p1 | p2"
  | string_of_taut Taut_Iff_4 = "~(p1 == p2) | p1 | ~p2"
  | string_of_taut Taut_Ite_Then = "~p | (ite p t1 t2) = t1"
  | string_of_taut Taut_Ite_Else = "p | (ite p t1 t2) = t2"

fun string_of_rewr Rewr_Not_True = "~T = F"
  | string_of_rewr Rewr_Not_False = "~F = T"
  | string_of_rewr Rewr_Not_Not = "~~p = p"
  | string_of_rewr (Rewr_Not_And n) =
      "~(and [" ^ string_of_int n ^ "]) = (or [" ^ string_of_int n ^ "])" 
  | string_of_rewr (Rewr_Not_Or n) =
      "~(or [" ^ string_of_int n ^ "]) = (and [" ^ string_of_int n ^ "])"
  | string_of_rewr Rewr_Not_Iff = "~(p1 == p2) = (~p1 == ~p2)"
  | string_of_rewr (Rewr_And_False i) = "(and ... F(" ^ string_of_int i ^ ") ...) = F"
  | string_of_rewr (Rewr_And_Dual (i1, i2)) =
      "(and ... p(" ^ string_of_int i1 ^ ") ... ~p(" ^ string_of_int i2 ^ ") ...) = F"
  | string_of_rewr (Rewr_And_Sort (n, iss)) =
      "(and [" ^ string_of_int n ^ "]) = " ^
      "(and " ^ brackets (brackets string_of_int) iss ^ ")" 
  | string_of_rewr (Rewr_Or_True i) = "(or ... T(" ^ string_of_int i ^ ") ...) = T"
  | string_of_rewr (Rewr_Or_Dual (i1, i2)) =
      "(or ... p(" ^ string_of_int i1 ^ ") ... ~p(" ^ string_of_int i2 ^ ") ...) = T"
  | string_of_rewr (Rewr_Or_Sort (n, iss)) =
      "(or [" ^ string_of_int n ^ "]) = " ^
      "(or " ^ brackets (brackets string_of_int) iss ^ ")" 
  | string_of_rewr Rewr_Iff_True = "(p == T) = p"
  | string_of_rewr Rewr_Iff_False = "(p == F) = ~p"
  | string_of_rewr Rewr_Iff_Not_Not = "(~p1 == ~p2) = (p1 == p2)"
  | string_of_rewr Rewr_Iff_Refl = "(p == p) = T"
  | string_of_rewr Rewr_Iff_Symm = "(p1 == p2) = (p2 == p1)"
  | string_of_rewr Rewr_Iff_Dual = "(p == ~p) = F"
  | string_of_rewr Rewr_Imp = "(p1 --> p2) = (~p1 | p2)"
  | string_of_rewr Rewr_Ite_Prop = "(if p1 p2 p2) = ((~p1 | p2) & (p1 | p3) & (p2 | p3))"
  | string_of_rewr Rewr_Ite_True = "(if T t1 t2) = t1"
  | string_of_rewr Rewr_Ite_False = "(if F t1 t2) = t2"
  | string_of_rewr Rewr_Ite_Eq = "(if p t t) = t"
  | string_of_rewr Rewr_Eq_Refl = "(e = e) = T"
  | string_of_rewr Rewr_Eq_Symm = "(e1 = e2) = (e2 = e1)"
  | string_of_rewr Rewr_Neg = "-e = -1 * e"
  | string_of_rewr (Rewr_Add (p1, p2)) =
      let
        fun string_of_monom (n, NONE) = Rat.string_of_rat n
          | string_of_monom (n, SOME i) =
              (if n = @1 then "" else Rat.string_of_rat n ^ " * ") ^ "e" ^ string_of_int i
        fun string_of_polynom ms = space_implode " + " (map string_of_monom ms)
      in string_of_polynom p1 ^ " = " ^ string_of_polynom p2 end
  | string_of_rewr Rewr_Sub = "e1 - e2 = e1 + -1 * e2"
  | string_of_rewr (Rewr_Mul_Nums (n1, n2)) =
      Rat.string_of_rat n1 ^ " * " ^ Rat.string_of_rat n2 ^ " = " ^ Rat.string_of_rat (n1 * n2)
  | string_of_rewr Rewr_Mul_Zero = "0 * e = 0"
  | string_of_rewr Rewr_Mul_One = "1 * e = e"
  | string_of_rewr Rewr_Mul_Comm = "e1 * e2 = e2 * e1"
  | string_of_rewr (Rewr_Mul_Assoc Left) = "(e1 * e2) * e3 = e1 * (e2 * e3)"
  | string_of_rewr (Rewr_Mul_Assoc Right) = "e1 * (n * e2) = (e1 * n) * e2"
  | string_of_rewr (Rewr_Mul_Sum Left) = "(e1 + ... + em) * e = e1 * e + ... em * e"
  | string_of_rewr (Rewr_Mul_Sum Right) = "e * (e1 + ... + em) = e * e1 + ... e * em"
  | string_of_rewr (Rewr_Mul_Div Left) = "(e1 / e2) * e3 = (e1 * e3) / e2"
  | string_of_rewr (Rewr_Mul_Div Right) = "e1 * (e2 / * e3) = (e1 * e2) / e3"
  | string_of_rewr Rewr_Div_Zero = "0 / e = 0"
  | string_of_rewr Rewr_Div_One = "e / 1 = e"
  | string_of_rewr (Rewr_Div_Nums (n1, n2)) =
      Rat.string_of_rat n1 ^ " / " ^ Rat.string_of_rat n2 ^ " = " ^ Rat.string_of_rat (n1 / n2)
  | string_of_rewr (Rewr_Div_Num (Left, n)) =
      Rat.string_of_rat n ^ " / e = " ^ Rat.string_of_rat n ^ " * (1 / e)"
  | string_of_rewr (Rewr_Div_Num (Right, n)) =
      "e / " ^ Rat.string_of_rat n ^ " = " ^ Rat.string_of_rat (Rat.inv n) ^ " * e"
  | string_of_rewr (Rewr_Div_Mul (Left, n)) =
     "(" ^ Rat.string_of_rat n ^ " * e1) / e2 = " ^ Rat.string_of_rat n ^ " * (e1 / e2)"
  | string_of_rewr (Rewr_Div_Mul (Right, n)) =
    "e1 / (" ^ Rat.string_of_rat n ^ " * e2) = " ^ Rat.string_of_rat (Rat.inv n) ^ " * (e1 / e2)"
  | string_of_rewr (Rewr_Div_Div Left) = "(e1 / e2) / e3 = e1 / (e2 * e3)"
  | string_of_rewr (Rewr_Div_Div Right) = "e1 / (e2 / e3) = (e1 * e3) / e2"
  | string_of_rewr Rewr_Div_Sum = "(e1 + ... + em) / e = e1 / e + ... + em / e"
  | string_of_rewr Rewr_Min_Eq = "min e e = e"
  | string_of_rewr Rewr_Min_Lt = "min e1 e2 = (if e1 <= e2 then e1 else e2)"
  | string_of_rewr Rewr_Min_Gt = "min e1 e2 = (if e2 <= e1 then e2 else e1)"
  | string_of_rewr Rewr_Max_Eq = "max e e = e"
  | string_of_rewr Rewr_Max_Lt = "max e1 e2 = (if e1 < e2 then e2 else e1)"
  | string_of_rewr Rewr_Max_Gt = "max e1 e2 = (if e2 < e1 then e1 else e2)"
  | string_of_rewr Rewr_Abs = "abs e = (if 0 <= e then e else -e)"
  | string_of_rewr (Rewr_Eq_Nums true) = "(n1 = n2) = true"
  | string_of_rewr (Rewr_Eq_Nums false) = "(n1 ~= n2) = false"
  | string_of_rewr Rewr_Eq_Sub = "(e1 = e2) = (e1 - e2 = 0)"
  | string_of_rewr Rewr_Eq_Le = "(e1 = e2) = (and (e1 <= e2) (e2 <= e1))"
  | string_of_rewr (Rewr_Ineq_Nums (Le, true)) = "(n1 <= n2) = true"
  | string_of_rewr (Rewr_Ineq_Nums (Le, false)) = "(n1 <= n2) = false"
  | string_of_rewr (Rewr_Ineq_Nums (Lt, true)) = "(n1 < n2) = true"
  | string_of_rewr (Rewr_Ineq_Nums (Lt, false)) = "(n1 < n2) = false"
  | string_of_rewr (Rewr_Ineq_Add (Le, _)) = "(e1 <= e2) = (e1 + n <= e2 + n)"
  | string_of_rewr (Rewr_Ineq_Add (Lt, _)) = "(e1 < e2) = (e1 + n < e2 + n)"
  | string_of_rewr (Rewr_Ineq_Sub Le) = "(e1 <= e2) = (e1 - e2 <= 0)"
  | string_of_rewr (Rewr_Ineq_Sub Lt) = "(e1 < e2) = (e1 - e2 < 0)"
  | string_of_rewr (Rewr_Ineq_Mul (Le, _)) = "(e1 <= e2) = (n * e1 <= n * e2)"
  | string_of_rewr (Rewr_Ineq_Mul (Lt, _)) = "(e1 < e2) = (n * e1 < n * e2)"
  | string_of_rewr (Rewr_Not_Ineq Le) = "~(e1 <= e2) = (e2 < e1)"
  | string_of_rewr (Rewr_Not_Ineq Lt) = "~(e1 < e2) = (e2 <= e1)"

fun flatten_then_conv (Then_Conv (c1, c2)) = flatten_then_conv c1 @ flatten_then_conv c2
  | flatten_then_conv c = [c]

fun string_of_conv Keep_Conv = "_"
  | string_of_conv (c as Then_Conv _) =
      space_implode " then " (map (enclose "(" ")" o string_of_conv) (flatten_then_conv c))
  | string_of_conv (Args_Conv (k, cs)) =
      "args " ^ Argo_Expr.string_of_kind k ^ " " ^ brackets string_of_conv cs
  | string_of_conv (Rewr_Conv r) = string_of_rewr r

fun string_of_rule (Axiom i) = "axiom " ^ string_of_int i
  | string_of_rule (Taut (t, _)) = "tautology: " ^ string_of_taut t
  | string_of_rule (Conjunct (i, n)) = "conjunct " ^ string_of_int i ^ " of " ^ string_of_int n
  | string_of_rule (Rewrite c) = "rewrite: " ^ string_of_conv c
  | string_of_rule (Hyp (i, _)) = "hypothesis " ^ string_of_int i
  | string_of_rule (Clause is) = "clause " ^ brackets string_of_int is
  | string_of_rule (Lemma is) = "lemma " ^ brackets string_of_int is
  | string_of_rule (Unit_Res i) = "unit-resolution " ^ string_of_int i
  | string_of_rule (Refl _) = "reflexivity"
  | string_of_rule Symm = "symmetry"
  | string_of_rule Trans = "transitivity"
  | string_of_rule Cong = "congruence"
  | string_of_rule Subst = "substitution"
  | string_of_rule Linear_Comb = "linear-combination"


(* unsatisfiability *)

exception UNSAT of proof

fun unsat p = raise UNSAT p

end
