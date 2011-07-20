(*  Title:      HOL/Tools/lambda_lifting.ML
    Author:     Sascha Boehme, TU Muenchen

Lambda-lifting on terms, i.e., replacing (some) lambda-abstractions by
fresh names accompanied with defining equations for these fresh names in
terms of the lambda-abstractions' bodies.
*)

signature LAMBDA_LIFTING =
sig
  val lift_lambdas: Proof.context -> bool -> term list ->
    Proof.context * (term list * term list)
end

structure Lambda_Lifting: LAMBDA_LIFTING =
struct

fun mk_def triggers Ts T lhs rhs =
  let
    val eq = HOLogic.eq_const T $ lhs $ rhs
    fun trigger () =
      [[Const (@{const_name SMT.pat}, T --> @{typ SMT.pattern}) $ lhs]]
      |> map (HOLogic.mk_list @{typ SMT.pattern})
      |> HOLogic.mk_list @{typ "SMT.pattern list"}
    fun mk_all T t = HOLogic.all_const T $ Abs (Name.uu, T, t)
  in
    fold mk_all Ts (if triggers then @{const SMT.trigger} $ trigger () $ eq
      else eq)
  end

fun mk_abs Ts = fold (fn T => fn t => Abs (Name.uu, T, t)) Ts

fun dest_abs Ts (Abs (_, T, t)) = dest_abs (T :: Ts) t
  | dest_abs Ts t = (Ts, t)

fun replace_lambda triggers Us Ts t (cx as (defs, ctxt)) =
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
          val (n, ctxt') =
            yield_singleton Variable.variant_fixes Name.uu ctxt
          val (is, UTs) = split_list (map_index I (Us @ Ts'))
          val f = Free (n, rev UTs ---> T)
          val lhs = Term.list_comb (f, map Bound (rev is))
          val def = mk_def triggers UTs (Term.fastype_of1 (Us @ Ts, t)) lhs t3
        in (app f, (Termtab.update (t4, (f, def)) defs, ctxt')) end)
  end

fun traverse triggers Ts t =
  (case t of
    (q as Const (@{const_name All}, _)) $ Abs a =>
      abs_traverse triggers Ts a #>> (fn a' => q $ Abs a')
  | (q as Const (@{const_name Ex}, _)) $ Abs a =>
      abs_traverse triggers Ts a #>> (fn a' => q $ Abs a')
  | (l as Const (@{const_name Let}, _)) $ u $ Abs a =>
      traverse triggers Ts u ##>> abs_traverse triggers Ts a #>>
      (fn (u', a') => l $ u' $ Abs a')
  | Abs _ =>
      let val (Us, u) = dest_abs [] t
      in traverse triggers (Us @ Ts) u #-> replace_lambda triggers Us Ts end
  | u1 $ u2 => traverse triggers Ts u1 ##>> traverse triggers Ts u2 #>> (op $)
  | _ => pair t)

and abs_traverse triggers Ts (n, T, t) =
  traverse triggers (T::Ts) t #>> (fn t' => (n, T, t'))

fun lift_lambdas ctxt triggers ts =
  (Termtab.empty, ctxt)
  |> fold_map (traverse triggers []) ts
  |> (fn (us, (defs, ctxt')) =>
       (ctxt', (Termtab.fold (cons o snd o snd) defs [], us)))

end
