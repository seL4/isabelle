(*  Title:      Tools/Argo/argo_simplex.ML
    Author:     Sascha Boehme

Linear arithmetic reasoning based on the simplex algorithm. It features:

 * simplification and normalization of arithmetic expressions
 * decision procedure for reals

These features might be added:

 * propagating implied inequality literals while assuming external knowledge
 * propagating equalities for fixed variables to all other theory solvers
 * pruning the tableau after new atoms have been added: eliminate unnecessary
   variables

The implementation is inspired by:

  Bruno Dutertre and Leonardo de Moura. A fast linear-arithmetic solver
  for DPLL(T). In Computer Aided Verification, pages 81-94. Springer, 2006.
*)

signature ARGO_SIMPLEX =
sig
  (* context *)
  type context
  val context: context

  (* enriching the context *)
  val add_atom: Argo_Term.term -> context -> Argo_Lit.literal option * context

  (* main operations *)
  val prepare: context -> context
  val assume: Argo_Common.literal -> context -> Argo_Lit.literal Argo_Common.implied * context
  val check: context -> Argo_Lit.literal Argo_Common.implied * context
  val explain: Argo_Lit.literal -> context -> (Argo_Cls.clause * context) option
  val add_level: context -> context
  val backtrack: context -> context
end

structure Argo_Simplex: ARGO_SIMPLEX =
struct

(* extended rationals *)

(*
  Extended rationals (c, k) are reals (c + k * e) where e is some small positive real number.
  Extended rationals are used to represent a strict inequality by a non-strict inequality:
    c < x  ~~  c + k * e <= e
    x < c  ~~  x <= c - k * e
*)

type erat = Rat.rat * Rat.rat

val erat_zero = (@0, @0)

fun add (c1, k1) (c2, k2) = (c1 + c2, k1 + k2)
fun sub (c1, k1) (c2, k2) = (c1 - c2, k1 - k2)
fun mul n (c, k) = (n * c, n * k)

val erat_ord = prod_ord Rat.ord Rat.ord

fun less_eq n1 n2 = is_less_equal (erat_ord (n1, n2))
fun less n1 n2 = is_less (erat_ord (n1, n2))


(* term functions *)

fun dest_monom (Argo_Term.T (_, Argo_Expr.Mul, [Argo_Term.T (_, Argo_Expr.Num n, _), t])) = (t, n)
  | dest_monom t = (t, @1)

datatype node = Var of Argo_Term.term | Num of Rat.rat
datatype ineq = Lower of Argo_Term.term * erat | Upper of Argo_Term.term * erat

fun dest_node (Argo_Term.T (_, Argo_Expr.Num n, _)) = Num n
  | dest_node t = Var t

fun dest_atom true (k as Argo_Expr.Le) t1 t2 = SOME (k, dest_node t1, dest_node t2)
  | dest_atom true (k as Argo_Expr.Lt) t1 t2 = SOME (k, dest_node t1, dest_node t2)
  | dest_atom false Argo_Expr.Le t1 t2 = SOME (Argo_Expr.Lt, dest_node t2, dest_node t1)
  | dest_atom false Argo_Expr.Lt t1 t2 = SOME (Argo_Expr.Le, dest_node t2, dest_node t1)
  | dest_atom _ _ _ _ = NONE

fun ineq_of pol (Argo_Term.T (_, k, [t1, t2])) =
      (case dest_atom pol k t1 t2 of
        SOME (Argo_Expr.Le, Var x, Num n) => SOME (Upper (x, (n, @0)))
      | SOME (Argo_Expr.Le, Num n, Var x) => SOME (Lower (x, (n, @0)))
      | SOME (Argo_Expr.Lt, Var x, Num n) => SOME (Upper (x, (n, @~1)))
      | SOME (Argo_Expr.Lt, Num n, Var x) => SOME (Lower (x, (n, @1)))
      | _ => NONE)
  | ineq_of _ _ = NONE


(* proofs *)

(*
  comment missing
*)

fun mk_ineq is_lt = if is_lt then Argo_Expr.mk_lt else Argo_Expr.mk_le
fun ineq_rule_of is_lt = if is_lt then Argo_Proof.Lt else Argo_Proof.Le

fun rewrite_top f = Argo_Rewr.rewrite_top (f Argo_Rewr.context)

fun unnegate_conv (e as Argo_Expr.E (Argo_Expr.Not, [Argo_Expr.E (Argo_Expr.Le, [e1, e2])])) =
      Argo_Rewr.rewr (Argo_Proof.Rewr_Not_Ineq Argo_Proof.Le) (Argo_Expr.mk_lt e2 e1) e
  | unnegate_conv (e as Argo_Expr.E (Argo_Expr.Not, [Argo_Expr.E (Argo_Expr.Lt, [e1, e2])])) =
      Argo_Rewr.rewr (Argo_Proof.Rewr_Not_Ineq Argo_Proof.Lt) (Argo_Expr.mk_le e2 e1) e
  | unnegate_conv e = Argo_Rewr.keep e

fun scale_conv r mk n e1 e2 =
  let
    fun scale e = Argo_Expr.mk_mul (Argo_Expr.mk_num n) e
    val (e1, e2) = if n > @0 then (scale e1, scale e2) else (scale e2, scale e1)
    val conv = Argo_Rewr.rewr (Argo_Proof.Rewr_Ineq_Mul (r, n)) (mk e1 e2)
  in Argo_Rewr.seq [conv, Argo_Rewr.args (rewrite_top Argo_Rewr.norm_mul)] end

fun dest_ineq (Argo_Expr.E (Argo_Expr.Le, [e1, e2])) = SOME (false, e1, e2)
  | dest_ineq (Argo_Expr.E (Argo_Expr.Lt, [e1, e2])) = SOME (true, e1, e2)
  | dest_ineq _ = NONE

fun scale_ineq_conv n e =
  if n = @1 then Argo_Rewr.keep e
  else
    (case dest_ineq e of
      NONE => raise Fail "bad inequality"
    | SOME (is_lt, e1, e2) => scale_conv (ineq_rule_of is_lt) (mk_ineq is_lt) n e1 e2 e)

fun simp_lit (n, (lit, p)) =
  let val conv = Argo_Rewr.seq [unnegate_conv, scale_ineq_conv n]
  in Argo_Rewr.with_proof conv (Argo_Lit.signed_expr_of lit, p) end

val combine_conv = rewrite_top Argo_Rewr.norm_add
fun reduce_conv r = Argo_Rewr.rewr (Argo_Proof.Rewr_Ineq_Nums (r, false)) Argo_Expr.false_expr

fun simp_combine es p prf =
  let
    fun dest e (is_lt, (es1, es2)) =
      let val (is_lt', e1, e2) = the (dest_ineq e)
      in (is_lt orelse is_lt', (e1 :: es1, e2 :: es2)) end
    val (is_lt, (es1, es2)) = fold_rev dest es (false, ([], []))
    val e = uncurry (mk_ineq is_lt) (apply2 Argo_Expr.mk_add (es1, es2))
    val conv = Argo_Rewr.seq [Argo_Rewr.args combine_conv, reduce_conv (ineq_rule_of is_lt)]
  in prf |> Argo_Rewr.with_proof conv (e, p) |>> snd end

fun linear_combination nlps prf =
  let val ((es, ps), prf) = fold_map simp_lit nlps prf |>> split_list
  in prf |> Argo_Proof.mk_linear_comb ps |-> simp_combine es |-> Argo_Proof.mk_lemma [] end

fun proof_of (lit, SOME p) (ls, prf) = ((lit, p), (ls, prf))
  | proof_of (lit, NONE) (ls, prf) =
      let val (p, prf) = Argo_Proof.mk_hyp lit prf
      in ((lit, p), (Argo_Lit.negate lit :: ls, prf)) end


(* tableau *)

(*
  The tableau consists of equations x_i = a_i1 * x_1 + ... a_ik * x_k where
  the variable on the left-hand side is called a basic variable and
  the variables on the right-hand side are called non-basic variables.

  For each basic variable, the polynom on the right-hand side is stored as a map
  from variables to coefficients. Only variables with non-zero coefficients are stored.
  The map is sorted by the term order of the variables for a deterministic order when
  analyzing a polynom.

  Additionally, for each basic variable a boolean flag is kept that, when false,
  indicates that the current value of the basic variable might be outside its bounds.
  The value of a non-basic variable is always within its bounds.

  The tableau is stored as a table indexed by variables. For each variable,
  both basic and non-basic, its current value is stored as extended rational
  along with either the equations or the occurrences.
*)

type basic = bool * (Argo_Term.term * Rat.rat) Ord_List.T
type entry = erat * basic option
type tableau = entry Argo_Termtab.table

fun dirty ms = SOME (false, ms)
fun checked ms = SOME (true, ms)

fun basic_entry ms = (erat_zero, dirty ms)
val non_basic_entry: entry = (erat_zero, NONE)

fun value_of tableau x =
  (case Argo_Termtab.lookup tableau x of
    NONE => erat_zero
  | SOME (v, _) => v)

fun first_unchecked_basic tableau =
  Argo_Termtab.get_first (fn (y, (v, SOME (false, ms))) => SOME (y, v, ms) | _ => NONE) tableau

local

fun coeff_of ms x = the (AList.lookup Argo_Term.eq_term ms x)

val eq_var = Argo_Term.eq_term
fun monom_ord sp = prod_ord Argo_Term.term_ord (K EQUAL) sp

fun add_monom m ms = Ord_List.insert monom_ord m ms
fun update_monom (m as (x, a)) = if a = @0 then AList.delete eq_var x else AList.update eq_var m

fun add_scaled_monom n (x, a) ms =
  (case AList.lookup eq_var ms x of
    NONE => add_monom (x, n * a) ms
  | SOME b => update_monom (x, n * a + b) ms)

fun replace_polynom x n ms' ms = fold (add_scaled_monom n) ms' (AList.delete eq_var x ms)

fun map_basic f (v, SOME (_, ms)) = f v ms
  | map_basic _ e = e

fun map_basic_entries x f =
  let
    fun apply (e as (v, SOME (_, ms))) = if AList.defined eq_var ms x then f v ms else e
      | apply ve = ve
  in Argo_Termtab.map (K apply) end

fun put_entry x e = Argo_Termtab.update (x, e)

fun add_new_entry (y as Argo_Term.T (_, Argo_Expr.Add, ts)) tableau =
      let val ms = Ord_List.make monom_ord (map dest_monom ts)
      in fold (fn (x, _) => put_entry x non_basic_entry) ms (put_entry y (basic_entry ms) tableau) end
  | add_new_entry x tableau = put_entry x non_basic_entry tableau

fun with_non_basic update_basic x f tableau =
  (case Argo_Termtab.lookup tableau x of
    NONE => tableau
  | SOME (v, NONE) => f v tableau
  | SOME (v, SOME (_, ms)) => if update_basic then put_entry x (v, dirty ms) tableau else tableau)

in

fun add_entry x tableau =
  if Argo_Termtab.defined tableau x then tableau
  else add_new_entry x tableau

fun basic_within_bounds y = Argo_Termtab.map_entry y (map_basic (fn v => fn ms => (v, checked ms)))

fun eliminate _ tableau = tableau

fun update_non_basic pred x v' = with_non_basic true x (fn v =>
  let fun update_basic n v ms = (add v (mul (coeff_of ms x) n), dirty ms)
  in pred v ? put_entry x (v', NONE) o map_basic_entries x (update_basic (sub v' v)) end)

fun update_pivot y vy ms x c v = with_non_basic false x (fn vx =>
  let
    val a = Rat.inv c
    val v' = mul a (sub v vy)

    fun scale_or_drop (x', b) = if Argo_Term.eq_term (x', x) then NONE else SOME (x', ~ a * b)
    val ms = add_monom (y, a) (map_filter scale_or_drop ms)

    fun update_basic v ms' =
      let val n = coeff_of ms' x
      in (add v (mul n v'), dirty (replace_polynom x n ms ms')) end
  in
    put_entry x (add vx v', dirty ms) #>
    put_entry y (v, NONE) #>
    map_basic_entries x update_basic
  end)

end


(* bounds *)

(*
  comment missing
*)

type bound = (erat * Argo_Common.literal) option
type atoms = (erat * Argo_Term.term) list
type bounds_atoms = ((bound * bound) * (atoms * atoms))
type bounds = bounds_atoms Argo_Termtab.table

val empty_bounds_atoms: bounds_atoms = ((NONE, NONE), ([], []))

fun on_some pred (SOME (n, _)) = pred n
  | on_some _ NONE = false

fun none_or_some pred (SOME (n, _)) = pred n
  | none_or_some _ NONE = true

fun bound_of (SOME (n, _)) = n
  | bound_of NONE = raise Fail "bad bound"

fun reason_of (SOME (_, r)) = r
  | reason_of NONE = raise Fail "bad reason"

fun bounds_atoms_of bounds x = the_default empty_bounds_atoms (Argo_Termtab.lookup bounds x)
fun bounds_of bounds x = fst (bounds_atoms_of bounds x)

fun put_bounds x bs bounds = Argo_Termtab.map_default (x, empty_bounds_atoms) (apfst (K bs)) bounds

fun has_bound_atoms bounds x =
  (case Argo_Termtab.lookup bounds x of
    NONE => false
  | SOME (_, ([], [])) => false
  | _ => true)

fun add_new_atom f x n t =
  let val ins = f (insert (eq_snd Argo_Term.eq_term) (n, t))
  in Argo_Termtab.map_default (x, empty_bounds_atoms) (apsnd ins) end

fun del_atom x t =
  let fun eq_atom (t1, (_, t2)) = Argo_Term.eq_term (t1, t2)
  in Argo_Termtab.map_entry x (apsnd (apply2 (remove eq_atom t))) end


(* context *)

type context = {
  tableau: tableau, (* values of variables and tableau entries for each variable *)
  bounds: bounds, (* bounds and unassigned atoms for each variable *)
  prf: Argo_Proof.context, (* proof context *)
  back: bounds list} (* stack storing previous bounds and unassigned atoms *)

fun mk_context tableau bounds prf back: context =
  {tableau=tableau, bounds=bounds, prf=prf, back=back}

val context = mk_context Argo_Termtab.empty Argo_Termtab.empty Argo_Proof.simplex_context []


(* declaring atoms *)

fun add_ineq_atom f t x n ({tableau, bounds, prf, back}: context) =
  (* TODO: check whether the atom is already known to hold *)
  (NONE, mk_context (add_entry x tableau) (add_new_atom f x n t bounds) prf back)

fun add_atom t cx =
  (case ineq_of true t of
    SOME (Lower (x, n)) => add_ineq_atom apfst t x n cx
  | SOME (Upper (x, n)) => add_ineq_atom apsnd t x n cx
  | NONE => (NONE, cx))


(* preparing the solver after new atoms have been added *)

(*
  Variables that do not directly occur in atoms can be eliminated from the tableau
  since no bounds will ever limit their value. This can reduce the tableau size
  substantially.
*)

fun prepare ({tableau, bounds, prf, back}: context) =
  let fun drop (xe as (x, _)) = not (has_bound_atoms bounds x) ? eliminate xe
  in mk_context (Argo_Termtab.fold drop tableau tableau) bounds prf back end


(* assuming external knowledge *)

fun bounds_conflict r1 r2 ({tableau, bounds, prf, back}: context) =
  let
    val ((lp2, lp1), (lits, prf)) = ([], prf) |> proof_of r2 ||>> proof_of r1
    val (p, prf) = linear_combination [(@~1, lp1), (@1, lp2)] prf
  in (Argo_Common.Conflict (lits, p), mk_context tableau bounds prf back) end

fun assume_bounds order x c bs ({tableau, bounds, prf, back}: context) =
  let
    val lits = []
    val bounds = put_bounds x bs bounds
    val tableau = update_non_basic (fn v => erat_ord (v, c) = order) x c tableau
  in (Argo_Common.Implied lits, mk_context tableau bounds prf back) end

fun assume_lower r x c (low, upp) cx =
  if on_some (fn l => less_eq c l) low then (Argo_Common.Implied [], cx)
  else if on_some (fn u => less u c) upp then bounds_conflict r (reason_of upp) cx
  else assume_bounds LESS x c (SOME (c, r), upp) cx

fun assume_upper r x c (low, upp) cx =
  if on_some (fn u => less_eq u c) upp then (Argo_Common.Implied [], cx)
  else if on_some (fn l => less c l) low then bounds_conflict (reason_of low) r cx
  else assume_bounds GREATER x c (low, SOME (c, r)) cx

fun with_bounds r t f x n ({tableau, bounds, prf, back}: context) =
  f r x n (bounds_of bounds x) (mk_context tableau (del_atom x t bounds) prf back)

fun choose f (SOME (Lower (x, n))) cx = f assume_lower x n cx
  | choose f (SOME (Upper (x, n))) cx = f assume_upper x n cx
  | choose _ NONE cx = (Argo_Common.Implied [], cx)

fun assume (r as (lit, _)) cx =
  let val (t, pol) = Argo_Lit.dest lit
  in choose (with_bounds r t) (ineq_of pol t) cx end


(* checking for consistency and pending implications *)

fun basic_bounds_conflict lower y ms ({tableau, bounds, prf, back}: context) =
  let
    val (a, low, upp) = if lower then (@1, fst, snd) else (@~1, snd, fst)
    fun coeff_proof f a x = apfst (pair a) o proof_of (reason_of (f (bounds_of bounds x)))
    fun monom_proof (x, a) = coeff_proof (if a < @0 then low else upp) a x
    val ((alp, alps), (lits, prf)) = ([], prf) |> coeff_proof low a y ||>> fold_map monom_proof ms
    val (p, prf) = linear_combination (alp :: alps) prf
  in (Argo_Common.Conflict (lits, p), mk_context tableau bounds prf back) end

fun can_compensate ord tableau bounds (x, a) =
  let val (low, upp) = bounds_of bounds x
  in
    if Rat.ord (a, @0) = ord then none_or_some (fn u => less (value_of tableau x) u) upp
    else none_or_some (fn l => less l (value_of tableau x)) low
  end

fun check (cx as {tableau, bounds, prf, back}: context) =
  (case first_unchecked_basic tableau of
    NONE => (Argo_Common.Implied [], cx)
  | SOME (y, v, ms) =>
      let val (low, upp) = bounds_of bounds y
      in
        if on_some (fn l => less v l) low then adjust GREATER true y v ms (bound_of low) cx
        else if on_some (fn u => less u v) upp then adjust LESS false y v ms (bound_of upp) cx
        else check (mk_context (basic_within_bounds y tableau) bounds prf back)
      end)

and adjust ord lower y vy ms v (cx as {tableau, bounds, prf, back}: context) =
  (case find_first (can_compensate ord tableau bounds) ms of
    NONE => basic_bounds_conflict lower y ms cx
  | SOME (x, a) => check (mk_context (update_pivot y vy ms x a v tableau) bounds prf back))


(* explanations *)

fun explain _ _ = NONE


(* backtracking *)

fun add_level ({tableau, bounds, prf, back}: context) =
  mk_context tableau bounds prf (bounds :: back)

fun backtrack ({back=[], ...}: context) = raise Empty
  | backtrack ({tableau, prf, back=bounds :: back, ...}: context) =
      mk_context tableau bounds prf back

end
