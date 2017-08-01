(*  Title:      Tools/Argo/argo_rewr.ML
    Author:     Sascha Boehme

Bottom-up rewriting of expressions based on rewrite rules and rewrite functions.
*)

signature ARGO_REWR =
sig
  (* conversions *)
  type conv = Argo_Expr.expr -> Argo_Expr.expr * Argo_Proof.conv
  val keep: conv
  val seq: conv list -> conv
  val args: conv -> conv
  val rewr: Argo_Proof.rewrite -> Argo_Expr.expr -> conv

  (* context *)
  type context
  val context: context

  (* rewriting *)
  val rewrite: context -> conv
  val rewrite_top: context -> conv
  val with_proof: conv -> Argo_Expr.expr * Argo_Proof.proof -> Argo_Proof.context ->
    (Argo_Expr.expr * Argo_Proof.proof) * Argo_Proof.context

  (* normalizations *)
  val nnf: context -> context
  val norm_prop: context -> context
  val norm_ite: context -> context
  val norm_eq: context -> context
  val norm_add: context -> context
  val norm_mul: context -> context
  val norm_arith: context -> context
end

structure Argo_Rewr: ARGO_REWR =
struct

(* conversions *)

(*
  Conversions are atomic rewrite steps.
  For every conversion there is a corresponding inference step.
*)

type conv = Argo_Expr.expr -> Argo_Expr.expr * Argo_Proof.conv

fun keep e = (e, Argo_Proof.keep_conv)

fun seq [] e = keep e
  | seq [cv] e = cv e
  | seq (cv :: cvs) e =
      let val ((e, c2), c1) = cv e |>> seq cvs
      in (e, Argo_Proof.mk_then_conv c1 c2) end

fun on_args f (Argo_Expr.E (k, es)) =
  let val (es, cs) = split_list (f es)
  in (Argo_Expr.E (k, es), Argo_Proof.mk_args_conv k cs) end

fun args cv e = on_args (map cv) e

fun all_args cv k (e as Argo_Expr.E (k', _)) = if k = k' then args (all_args cv k) e else cv e

fun rewr r e _ = (e, Argo_Proof.mk_rewr_conv r)


(* rewriting result *)

(*
  After rewriting an expression, further rewritings might be applicable. The result type is
  a simple means to control which parts of the rewriting result should be rewritten further.
  Only the top-most part of a result marked by R constructors is amenable to further rewritings.
*)

datatype result =
  E of Argo_Expr.expr |
  R of Argo_Expr.kind * result list 

fun expr_of (E e) = e
  | expr_of (R (k, ps)) = Argo_Expr.E (k, map expr_of ps)

fun top_most _ (E _) e = keep e
  | top_most cv (R (_, ps)) e = seq [on_args (map2 (top_most cv) ps), cv] e


(* context *)

(*
  The context stores lists of rewritings for every expression kind. A rewriting maps the
  arguments of an expression with matching kind to an optional rewriting result. Each
  rewriting might decide whether it is applicable to the given expression arguments and
  might return no result. The first rewriting that produces a result is applied.
*)

structure Kindtab = Table(type key = Argo_Expr.kind val ord = Argo_Expr.kind_ord)

type context =
  (int -> Argo_Expr.expr list -> (Argo_Proof.rewrite * result) option) list Kindtab.table

val context: context = Kindtab.empty

fun add_func k f = Kindtab.map_default (k, []) (fn fs => fs @ [f])
fun add_func' k f = add_func k (fn _ => f)

fun unary k f = add_func' k (fn [e] => f e | _ => raise Fail "not unary")
fun binary k f = add_func' k (fn [e1, e2] => f e1 e2 | _ => raise Fail "not binary")
fun ternary k f = add_func' k (fn [e1, e2, e3] => f e1 e2 e3 | _ => raise Fail "not ternary")
fun nary k f = add_func k f


(* rewriting *)

(*
  Rewriting proceeds bottom-up. The top-most result of a rewriting step is rewritten again
  bottom-up, if necessary. Only the first rewriting that produces a result for a given
  expression is applied. N-ary expressions are flattened before they are rewritten. For
  instance, flattening (and p (and q r)) produces (and p q r) where p, q and r are no
  conjunctions.
*)

fun first_rewr cv cx k n es e =
  (case get_first (fn f => f n es) (Kindtab.lookup_list cx k) of
    NONE => keep e
  | SOME (r, res) => seq [rewr r (expr_of res), top_most cv res] e) 

fun all_args_of k (e as Argo_Expr.E (k', es)) = if k = k' then maps (all_args_of k) es else [e]
fun kind_depth_of k (Argo_Expr.E (k', es)) =
  if k = k' then 1 + fold (Integer.max o kind_depth_of k) es 0 else 0

fun norm_kind cv cx (e as Argo_Expr.E (k, es)) =
  let val (n, es) = if Argo_Expr.is_nary k then (kind_depth_of k e, all_args_of k e) else (1, es)
  in first_rewr cv cx k n es e end

fun norm_args cv d (e as Argo_Expr.E (k, _)) =
  if d = 0 then keep e
  else if Argo_Expr.is_nary k then all_args (cv (d - 1)) k e
  else args (cv (d - 1)) e

fun norm cx d e = seq [norm_args (norm cx) d, norm_kind (norm cx 0) cx] e

fun rewrite cx = norm cx ~1   (* bottom-up rewriting *)
fun rewrite_top cx = norm cx 0   (* top-most rewriting *)

fun with_proof cv (e, p) prf =
  let
    val (e, c) = cv e
    val (p, prf) = Argo_Proof.mk_rewrite c p prf
  in ((e, p), prf) end


(* result constructors *)

fun mk_nary _ e [] = e
  | mk_nary _ _ [e] = e
  | mk_nary k _ es = R (k, es)

val e_true = E Argo_Expr.true_expr
val e_false = E Argo_Expr.false_expr
fun mk_not e = R (Argo_Expr.Not, [e])
fun mk_and es = mk_nary Argo_Expr.And e_true es
fun mk_or es = mk_nary Argo_Expr.Or e_false es
fun mk_iff e1 e2 = R (Argo_Expr.Iff, [e1, e2])
fun mk_ite e1 e2 e3 = R (Argo_Expr.Ite, [e1, e2, e3])
fun mk_num n = E (Argo_Expr.mk_num n)
fun mk_neg e = R (Argo_Expr.Neg, [e])
fun mk_add [] = raise Fail "bad addition"
  | mk_add [e] = e
  | mk_add es = R (Argo_Expr.Add, es)
fun mk_sub e1 e2 = R (Argo_Expr.Sub, [e1, e2])
fun mk_mul e1 e2 = R (Argo_Expr.Mul, [e1, e2])
fun mk_div e1 e2 = R (Argo_Expr.Div, [e1, e2])
fun mk_le e1 e2 = R (Argo_Expr.Le, [e1, e2])
fun mk_le' e1 e2 = mk_le (E e1) (E e2)
fun mk_eq e1 e2 = R (Argo_Expr.Eq, [e1, e2])


(* rewriting to negation normal form *)

fun rewr_not (Argo_Expr.E exp) =
  (case exp of
    (Argo_Expr.True, _) => SOME (Argo_Proof.Rewr_Not_True, e_false)
  | (Argo_Expr.False, _) => SOME (Argo_Proof.Rewr_Not_False, e_true)
  | (Argo_Expr.Not, [e]) => SOME (Argo_Proof.Rewr_Not_Not, E e)
  | (Argo_Expr.And, es) => SOME (Argo_Proof.Rewr_Not_And (length es), mk_or (map (mk_not o E) es))
  | (Argo_Expr.Or, es) => SOME (Argo_Proof.Rewr_Not_Or (length es), mk_and (map (mk_not o E) es))
  | (Argo_Expr.Iff, [Argo_Expr.E (Argo_Expr.Not, [e1]), e2]) =>
      SOME (Argo_Proof.Rewr_Not_Iff, mk_iff (E e1) (E e2))
  | (Argo_Expr.Iff, [e1, Argo_Expr.E (Argo_Expr.Not, [e2])]) =>
      SOME (Argo_Proof.Rewr_Not_Iff, mk_iff (E e1) (E e2))
  | (Argo_Expr.Iff, [e1, e2]) => 
      SOME (Argo_Proof.Rewr_Not_Iff, mk_iff (mk_not (E e1)) (E e2))
  | _ => NONE)

val nnf = unary Argo_Expr.Not rewr_not


(* propositional normalization *)

(*
  Propositional expressions are transformed into literals in the clausifier. Having
  fewer literals results in faster solver execution. Normalizing propositional expressions
  turns similar expressions into equal expressions, for which the same literal can be used.
  The clausifier expects that only negation, disjunction, conjunction and equivalence form
  propositional expressions. Expressions may be simplified to truth or falsity, but both
  truth and falsity eventually occur nowhere inside expressions.
*)

fun first_index pred xs =
  let val i = find_index pred xs
  in if i >= 0 then SOME i else NONE end

fun rewr_zero r zero _ es =
  Option.map (fn i => (r i, E zero)) (first_index (curry Argo_Expr.eq_expr zero) es)

fun rewr_dual r zero _ =
  let
    fun duals _ [] = NONE
      | duals _ [_] = NONE
      | duals i (e :: es) =
          (case first_index (Argo_Expr.dual_expr e) es of
            NONE => duals (i + 1) es
          | SOME i' => SOME (r (i, i + i' + 1), zero))
  in duals 0 end

fun rewr_sort r one mk n es =
  let
    val l = length es
    fun add (i, e) = if Argo_Expr.eq_expr (e, one) then I else Argo_Exprtab.cons_list (e, i)
    fun dest (e, i) (es, is) = (e :: es, i :: is)
    val (es, iss) = Argo_Exprtab.fold_rev dest (fold_index add es Argo_Exprtab.empty) ([], [])
    fun identity is = length is = l andalso forall (op =) (map_index I is)
  in
    if null iss then SOME (r (l, [[0]]), E one)
    else if n = 1 andalso identity (map hd iss) then NONE
    else (SOME (r (l, iss), mk (map E es)))
  end

fun rewr_imp e1 e2 = SOME (Argo_Proof.Rewr_Imp, mk_or [mk_not (E e1), E e2])

fun rewr_iff (e1 as Argo_Expr.E exp1) (e2 as Argo_Expr.E exp2) =
  (case (exp1, exp2) of
    ((Argo_Expr.True, _), _) => SOME (Argo_Proof.Rewr_Iff_True, E e2)
  | ((Argo_Expr.False, _), _) => SOME (Argo_Proof.Rewr_Iff_False, mk_not (E e2))
  | (_, (Argo_Expr.True, _)) => SOME (Argo_Proof.Rewr_Iff_True, E e1)
  | (_, (Argo_Expr.False, _)) => SOME (Argo_Proof.Rewr_Iff_False, mk_not (E e1))
  | ((Argo_Expr.Not, [e1']), (Argo_Expr.Not, [e2'])) =>
      SOME (Argo_Proof.Rewr_Iff_Not_Not, mk_iff (E e1') (E e2'))
  | _ =>
      if Argo_Expr.dual_expr e1 e2 then SOME (Argo_Proof.Rewr_Iff_Dual, e_false)
      else
        (case Argo_Expr.expr_ord (e1, e2) of
          EQUAL => SOME (Argo_Proof.Rewr_Iff_Refl, e_true)
        | GREATER => SOME (Argo_Proof.Rewr_Iff_Symm, mk_iff (E e2) (E e1))
        | LESS => NONE))

val norm_prop =
  nary Argo_Expr.And (rewr_zero Argo_Proof.Rewr_And_False Argo_Expr.false_expr) #>
  nary Argo_Expr.And (rewr_dual Argo_Proof.Rewr_And_Dual e_false) #>
  nary Argo_Expr.And (rewr_sort Argo_Proof.Rewr_And_Sort Argo_Expr.true_expr mk_and) #>
  nary Argo_Expr.Or (rewr_zero Argo_Proof.Rewr_Or_True Argo_Expr.true_expr) #>
  nary Argo_Expr.Or (rewr_dual Argo_Proof.Rewr_Or_Dual e_true) #>
  nary Argo_Expr.Or (rewr_sort Argo_Proof.Rewr_Or_Sort Argo_Expr.false_expr mk_or) #>
  binary Argo_Expr.Imp rewr_imp #>
  binary Argo_Expr.Iff rewr_iff


(* normalization of if-then-else expressions *)

fun rewr_ite (Argo_Expr.E (Argo_Expr.True, _)) e _ = SOME (Argo_Proof.Rewr_Ite_True, E e)
  | rewr_ite (Argo_Expr.E (Argo_Expr.False, _)) _ e = SOME (Argo_Proof.Rewr_Ite_False, E e)
  | rewr_ite e1 e2 e3 =
      if Argo_Expr.type_of e2 = Argo_Expr.Bool then
        SOME (Argo_Proof.Rewr_Ite_Prop,
          mk_and (map mk_or [[mk_not (E e1), E e2], [E e1, E e3], [E e2, E e3]]))
      else if Argo_Expr.eq_expr (e2, e3) then SOME (Argo_Proof.Rewr_Ite_Eq, E e2)
      else NONE

val norm_ite = ternary Argo_Expr.Ite rewr_ite


(* normalization of equality *)

(*
  In a normalized equality, the left-hand side is less than the right-hand side with respect to
  the expression order.
*)

fun rewr_eq e1 e2 =
  (case Argo_Expr.expr_ord (e1, e2) of
    EQUAL => SOME (Argo_Proof.Rewr_Eq_Refl, e_true)
  | GREATER => SOME (Argo_Proof.Rewr_Eq_Symm, mk_eq (E e2) (E e1))
  | LESS => NONE)

val norm_eq = binary Argo_Expr.Eq rewr_eq


(* arithmetic normalization *)

(* expression functions *)

fun scale n e =
  if n = @0 then mk_num @0
  else if n = @1 then e
  else mk_mul (mk_num n) e

fun dest_factor (Argo_Expr.E (Argo_Expr.Mul, [Argo_Expr.E (Argo_Expr.Num n, _), _])) = n
  | dest_factor _ = @1


(*
  Products are normalized either to a number or to the monomial form
    a * x
  where a is a non-zero number and is a variable or a product of variables.
  If x is a product, it contains no number factors. If x is a product, it is sorted
  based on the expression order. Hence, the product z * y * x will be rewritten
  to x * y * z. The coefficient a is dropped if it is equal to one;
  instead of 1 * x the expression x is used.
*)

fun mk_mul_comm e1 e2 = (Argo_Proof.Rewr_Mul_Comm, mk_mul (E e2) (E e1))
fun mk_mul_assocr e1 e2 e3 =
  (Argo_Proof.Rewr_Mul_Assoc Argo_Proof.Right, mk_mul (mk_mul (E e1) (E e2)) (E e3))

  (* commute numbers to the left *)
fun rewr_mul (Argo_Expr.E (Argo_Expr.Num n1, _)) (Argo_Expr.E (Argo_Expr.Num n2, _)) =
      SOME (Argo_Proof.Rewr_Mul_Nums (n1, n2), mk_num (n1 * n2))
  | rewr_mul e1 (e2 as Argo_Expr.E (Argo_Expr.Num _, _)) = SOME (mk_mul_comm e1 e2)
  | rewr_mul e1 (Argo_Expr.E (Argo_Expr.Mul, [e2 as Argo_Expr.E (Argo_Expr.Num _, _), e3])) =
      SOME (mk_mul_assocr e1 e2 e3)
  (* apply distributivity *)
  | rewr_mul (Argo_Expr.E (Argo_Expr.Add, es)) e =
      SOME (Argo_Proof.Rewr_Mul_Sum Argo_Proof.Left, mk_add (map (fn e' => mk_mul (E e') (E e)) es))
  | rewr_mul e (Argo_Expr.E (Argo_Expr.Add, es)) =
      SOME (Argo_Proof.Rewr_Mul_Sum Argo_Proof.Right, mk_add (map (mk_mul (E e) o E) es))
  (* commute non-numerical factors to the right *)
  | rewr_mul (Argo_Expr.E (Argo_Expr.Mul, [e1, e2])) e3 =
      SOME (Argo_Proof.Rewr_Mul_Assoc Argo_Proof.Left, mk_mul (E e1) (mk_mul (E e2) (E e3)))
  (* reduce special products *)
  | rewr_mul (e1 as Argo_Expr.E (Argo_Expr.Num n, _)) e2 =
      if n = @0 then SOME (Argo_Proof.Rewr_Mul_Zero, E e1)
      else if n = @1 then SOME (Argo_Proof.Rewr_Mul_One, E e2)
      else NONE
  (* combine products with quotients *)
  | rewr_mul (Argo_Expr.E (Argo_Expr.Div, [e1, e2])) e3 =
      SOME (Argo_Proof.Rewr_Mul_Div Argo_Proof.Left, mk_div (mk_mul (E e1) (E e3)) (E e2))
  | rewr_mul e1 (Argo_Expr.E (Argo_Expr.Div, [e2, e3])) =
      SOME (Argo_Proof.Rewr_Mul_Div Argo_Proof.Right, mk_div (mk_mul (E e1) (E e2)) (E e3))
  (* sort non-numerical factors *)
  | rewr_mul e1 (Argo_Expr.E (Argo_Expr.Mul, [e2, e3])) =
      (case Argo_Expr.expr_ord (e1, e2) of
        GREATER => SOME (mk_mul_assocr e1 e2 e3)
      | _ => NONE)
  | rewr_mul e1 e2 =
      (case Argo_Expr.expr_ord (e1, e2) of
        GREATER => SOME (mk_mul_comm e1 e2)
      | _ => NONE)

(*
  Quotients are normalized either to a number or to the monomial form
    a * x
  where a is a non-zero number and x is a variable. If x is a quotient,
  both dividend and divisor are not a number. The dividend and the divisor may both
  be products. If so, neither dividend nor divisor contains a numerical factor.
  Both dividend and divisor are not themselves quotients again. The dividend is never
  a sum; distributivity is applied to such quotients. The coefficient a is dropped
  if it is equal to one; instead of 1 * x the expression x is used.

  Several non-linear expressions can be rewritten to the described normal form.
  For example, the expressions (x * z) / y and x * (z / y) will be treated as equal
  variables by the arithmetic decision procedure. Yet, non-linear expression rewriting
  is incomplete and keeps several other expressions unchanged.
*)

fun rewr_div (Argo_Expr.E (Argo_Expr.Div, [e1, e2])) e3 =
      SOME (Argo_Proof.Rewr_Div_Div Argo_Proof.Left, mk_div (E e1) (mk_mul (E e2) (E e3)))
  | rewr_div e1 (Argo_Expr.E (Argo_Expr.Div, [e2, e3])) =
      SOME (Argo_Proof.Rewr_Div_Div Argo_Proof.Right, mk_div (mk_mul (E e1) (E e3)) (E e2))
  | rewr_div (Argo_Expr.E (Argo_Expr.Num n1, _)) (Argo_Expr.E (Argo_Expr.Num n2, _)) =
      if n2 = @0 then NONE
      else SOME (Argo_Proof.Rewr_Div_Nums (n1, n2), mk_num (n1 / n2))
  | rewr_div (Argo_Expr.E (Argo_Expr.Num n, _)) e =
      if n = @0 then SOME (Argo_Proof.Rewr_Div_Zero, mk_num @0)
      else if n = @1 then NONE
      else SOME (Argo_Proof.Rewr_Div_Num (Argo_Proof.Left, n), scale n (mk_div (mk_num @1) (E e)))
  | rewr_div (Argo_Expr.E (Argo_Expr.Mul, [Argo_Expr.E (Argo_Expr.Num n, _), e1])) e2 =
      SOME (Argo_Proof.Rewr_Div_Mul (Argo_Proof.Left, n), scale n (mk_div (E e1) (E e2)))
  | rewr_div e (Argo_Expr.E (Argo_Expr.Num n, _)) =
      if n = @0 then NONE
      else if n = @1 then SOME (Argo_Proof.Rewr_Div_One, E e)
      else SOME (Argo_Proof.Rewr_Div_Num (Argo_Proof.Right, n), scale (Rat.inv n) (E e))
  | rewr_div e1 (Argo_Expr.E (Argo_Expr.Mul, [Argo_Expr.E (Argo_Expr.Num n, _), e2])) =
      SOME (Argo_Proof.Rewr_Div_Mul (Argo_Proof.Right, n), scale (Rat.inv n) (mk_div (E e1) (E e2)))
  | rewr_div (Argo_Expr.E (Argo_Expr.Add, es)) e =
      SOME (Argo_Proof.Rewr_Div_Sum, mk_add (map (fn e' => mk_div (E e') (E e)) es))
  | rewr_div _ _ = NONE


(*
  Sums are flattened and normalized to the polynomial form
    a_0 + a_1 * x_1 + ... + a_n * x_n
  where all variables x_i are disjoint and where all coefficients a_i are
  non-zero numbers. Coefficients equal to one are dropped; instead of 1 * x_i
  the reduced monom x_i is used. The variables x_i are ordered based on the
  expression order to reduce the number of problem literals by sharing equal
  expressions.
*)

fun add_monom_expr i n e (p, s, etab) =
  let val etab = Argo_Exprtab.map_default (e, (i, @0)) (apsnd (Rat.add n)) etab
  in ((n, Option.map fst (Argo_Exprtab.lookup etab e)) :: p, s, etab) end

fun add_monom (_, Argo_Expr.E (Argo_Expr.Num n, _)) (p, s, etab) = ((n, NONE) :: p, s + n, etab)
  | add_monom (i, Argo_Expr.E (Argo_Expr.Mul, [Argo_Expr.E (Argo_Expr.Num n, _), e])) x =
      add_monom_expr i n e x
  | add_monom (i, e) x = add_monom_expr i @1 e x

fun rewr_add d es =
  let
    val (p1, s, etab) = fold_index add_monom es ([], @0, Argo_Exprtab.empty)
    val (p2, es) =
      []
      |> Argo_Exprtab.fold_rev (fn (e, (i, n)) => n <> @0 ? cons ((n, SOME i), scale n (E e))) etab
      |> s <> @0 ? cons ((s, NONE), mk_num s)
      |> (fn [] => [((@0, NONE), mk_num @0)] | xs => xs)
      |> split_list
    val ps = (rev p1, p2)
  in
    if d = 1 andalso eq_list (op =) ps then NONE
    else SOME (Argo_Proof.Rewr_Add ps, mk_add es)
  end


(*
  Equations are normalized to the normal form
    a_0 + a_1 * x_1 + ... + a_n * x_n = b
  or
    b = a_0 + a_1 * x_1 + ... + a_n * x_n
  An equation in normal form is rewritten to a conjunction of two non-strict inequalities. 
*)

fun rewr_eq_le e1 e2 = SOME (Argo_Proof.Rewr_Eq_Le, mk_and [mk_le' e1 e2, mk_le' e2 e1])

fun rewr_arith_eq (Argo_Expr.E (Argo_Expr.Num n1, _)) (Argo_Expr.E (Argo_Expr.Num n2, _)) =
      let val b = (n1 = n2)
      in SOME (Argo_Proof.Rewr_Eq_Nums b, if b then e_true else e_false) end
  | rewr_arith_eq (e1 as Argo_Expr.E (Argo_Expr.Num _, _)) e2 = rewr_eq_le e1 e2
  | rewr_arith_eq e1 (e2 as Argo_Expr.E (Argo_Expr.Num _, _)) = rewr_eq_le e1 e2
  | rewr_arith_eq e1 e2 = SOME (Argo_Proof.Rewr_Eq_Sub, mk_eq (mk_sub (E e1) (E e2)) (mk_num @0))

fun is_arith e = member (op =) [Argo_Expr.Real] (Argo_Expr.type_of e)

fun rewr_eq e1 e2 = if is_arith e1 then rewr_arith_eq e1 e2 else NONE


(*
  Arithmetic inequalities (less and less-than) are normalized to the normal form
    a_0 + a_1 * x_1 + ... + a_n * x_n ~ b
  or
    b ~ a_0 + a_1 * x_1 + ... + a_n * x_n
  such that most of the coefficients a_i are positive.

  Arithmetic inequalities of the form
    a * x ~ b
  or
    b ~ a * x
  are normalized to the form
    x ~ c
  or
    c ~ x
  where c is a number.
*)

fun norm_cmp_mul k r f e1 e2 n =
  let val es = if n > @0 then [e1, e2] else [e2, e1]
  in SOME (Argo_Proof.Rewr_Ineq_Mul (r, n), R (k, f (map (scale n o E) es))) end

fun count_factors pred es = fold (fn e => if pred (dest_factor e) then Integer.add 1 else I) es 0

fun norm_cmp_swap k r f e1 e2 es =
  let
    val pos = count_factors (fn n => n > @0) es
    val neg = count_factors (fn n => n < @0) es
    val keep = pos > neg orelse (pos = neg andalso dest_factor (hd es) > @0)
  in if keep then NONE else norm_cmp_mul k r f e1 e2 @~1 end

fun norm_cmp1 k r f e1 (e2 as Argo_Expr.E (Argo_Expr.Mul, [Argo_Expr.E (Argo_Expr.Num n, _), _])) =
      norm_cmp_mul k r f e1 e2 (Rat.inv n)
  | norm_cmp1 k r f e1 (e2 as Argo_Expr.E (Argo_Expr.Add, Argo_Expr.E (Argo_Expr.Num n, _) :: _)) =
      let fun mk e = mk_add [E e, mk_num (~ n)]
      in SOME (Argo_Proof.Rewr_Ineq_Add (r, ~ n), R (k, f [mk e1, mk e2])) end
  | norm_cmp1 k r f e1 (e2 as Argo_Expr.E (Argo_Expr.Add, es)) = norm_cmp_swap k r f e1 e2 es
  | norm_cmp1 _ _ _ _ _ = NONE

fun rewr_cmp _ r pred (Argo_Expr.E (Argo_Expr.Num n1, _)) (Argo_Expr.E (Argo_Expr.Num n2, _)) =
      let val b = pred n1 n2
      in SOME (Argo_Proof.Rewr_Ineq_Nums (r, b), if b then e_true else e_false) end
  | rewr_cmp k r _ (e1 as Argo_Expr.E (Argo_Expr.Num _, _)) e2 = norm_cmp1 k r I e1 e2
  | rewr_cmp k r _ e1 (e2 as Argo_Expr.E (Argo_Expr.Num _, _)) = norm_cmp1 k r rev e2 e1
  | rewr_cmp k r _ e1 e2 =
      SOME (Argo_Proof.Rewr_Ineq_Sub r, R (k, [mk_sub (E e1) (E e2), mk_num @0]))


(*
  Arithmetic expressions are normalized in order to reduce the number of
  problem literals. Arithmetically equal expressions are normalized to
  syntactically equal expressions as much as possible.
*)

fun rewr_neg e = SOME (Argo_Proof.Rewr_Neg, scale @~1 (E e))
fun rewr_sub e1 e2 = SOME (Argo_Proof.Rewr_Sub, mk_add [E e1, scale @~1 (E e2)])
fun rewr_abs e = SOME (Argo_Proof.Rewr_Abs, mk_ite (mk_le (mk_num @0) (E e)) (E e) (mk_neg (E e)))

fun rewr_min e1 e2 =
  (case Argo_Expr.expr_ord (e1, e2) of
    LESS => SOME (Argo_Proof.Rewr_Min_Lt, mk_ite (mk_le' e1 e2) (E e1) (E e2))
  | EQUAL => SOME (Argo_Proof.Rewr_Min_Eq, E e1)
  | GREATER => SOME (Argo_Proof.Rewr_Min_Gt, mk_ite (mk_le' e2 e1) (E e2) (E e1)))

fun rewr_max e1 e2 =
  (case Argo_Expr.expr_ord (e1, e2) of
    LESS => SOME (Argo_Proof.Rewr_Max_Lt, mk_ite (mk_le' e1 e2) (E e2) (E e1))
  | EQUAL => SOME (Argo_Proof.Rewr_Max_Eq, E e1)
  | GREATER => SOME (Argo_Proof.Rewr_Max_Gt, mk_ite (mk_le' e2 e1) (E e1) (E e2)))

val norm_add = nary Argo_Expr.Add rewr_add
val norm_mul = binary Argo_Expr.Mul rewr_mul

val norm_arith =
  unary Argo_Expr.Neg rewr_neg #>
  binary Argo_Expr.Sub rewr_sub #>
  norm_mul #>
  binary Argo_Expr.Div rewr_div #>
  norm_add #>
  binary Argo_Expr.Min rewr_min #>
  binary Argo_Expr.Max rewr_max #>
  unary Argo_Expr.Abs rewr_abs #>
  binary Argo_Expr.Eq rewr_eq #>
  binary Argo_Expr.Le (rewr_cmp Argo_Expr.Le Argo_Proof.Le Rat.le) #>
  binary Argo_Expr.Lt (rewr_cmp Argo_Expr.Lt Argo_Proof.Lt Rat.lt)

end
