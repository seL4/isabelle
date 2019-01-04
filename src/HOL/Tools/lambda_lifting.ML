(*  Title:      HOL/Tools/lambda_lifting.ML
    Author:     Sascha Boehme, TU Muenchen

Lambda-lifting on terms, i.e., replacing (some) lambda-abstractions by
fresh names accompanied with defining equations for these fresh names in
terms of the lambda-abstractions' bodies.
*)

signature LAMBDA_LIFTING =
sig
  type context = (term * term) Termtab.table * Proof.context
  val init: Proof.context -> context
  val is_quantifier: term -> bool
  val lift_lambdas1: (term -> bool) -> string option -> term -> context ->
    term * context
  val finish: context -> term list * Proof.context
  val lift_lambdas: string option -> (term -> bool) -> term list ->
    Proof.context -> (term list * term list) * Proof.context
end

structure Lambda_Lifting: LAMBDA_LIFTING =
struct

fun mk_def Ts T lhs rhs =
  let fun mk_all T t = HOLogic.all_const T $ Abs (Name.uu, T, t)
  in fold mk_all Ts (HOLogic.eq_const T $ lhs $ rhs) end

fun mk_abs Ts = fold (fn T => fn t => Abs (Name.uu, T, t)) Ts

fun dest_abs Ts (Abs (_, T, t)) = dest_abs (T :: Ts) t
  | dest_abs Ts t = (Ts, t)

fun replace_lambda basename Us Ts t (cx as (defs, ctxt)) =
  let
    val t1 = mk_abs Us t
    val bs = sort int_ord (Term.add_loose_bnos (t1, 0, []))
    fun rep i k = if member (op =) bs i then (Bound k, k+1) else (Bound i, k)
    val (rs, _) = fold_map rep (0 upto length Ts - 1) 0
    val t2 = Term.subst_bounds (rs, t1)
    val Ts' = map (nth Ts) bs 
    val (_, t3) = dest_abs [] t2
    val t4 = mk_abs Ts' t2

    val T = Term.fastype_of1 (Us @ Ts, t)
    fun app f = Term.list_comb (f, map Bound (rev bs))
  in
    (case Termtab.lookup defs t4 of
      SOME (f, _) => (app f, cx)
    | NONE =>
        let
          val (n, ctxt') = yield_singleton Variable.variant_fixes basename ctxt
          val (is, UTs) = split_list (map_index I (Us @ Ts'))
          val f = Free (n, rev UTs ---> T)
          val lhs = Term.list_comb (f, map Bound (rev is))
          val def = mk_def UTs (Term.fastype_of1 (Us @ Ts, t)) lhs t3
        in (app f, (Termtab.update (t4, (f, def)) defs, ctxt')) end)
  end

type context = (term * term) Termtab.table * Proof.context

fun init ctxt = (Termtab.empty, ctxt)

fun is_quantifier (Const (\<^const_name>\<open>All\<close>, _)) = true
  | is_quantifier (Const (\<^const_name>\<open>Ex\<close>, _)) = true
  | is_quantifier _ = false

fun lift_lambdas1 is_binder basename =
  let
    val basename' = the_default Name.uu basename

    fun traverse Ts (t $ (u as Abs (n, T, body))) =
          if is_binder t then
            traverse Ts t ##>> traverse (T :: Ts) body #>> (fn (t', body') =>
            t' $ Abs (n, T, body'))
          else traverse Ts t ##>> traverse Ts u #>> (op $)
      | traverse Ts (t as Abs _) =
          let val (Us, u) = dest_abs [] t
          in traverse (Us @ Ts) u #-> replace_lambda basename' Us Ts end
      | traverse Ts (t $ u) = traverse Ts t ##>> traverse Ts u #>> (op $)
      | traverse _ t = pair t
  in traverse [] end

fun finish (defs, ctxt) = (Termtab.fold (cons o snd o snd) defs [], ctxt)

fun lift_lambdas basename is_binder ts ctxt =
  init ctxt
  |> fold_map (lift_lambdas1 is_binder basename) ts
  |-> (fn ts' => finish #>> pair ts')

end
