(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_annotate.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Supplement term with explicit type constraints that show up as 
type annotations when printing the term.
*)

signature SLEDGEHAMMER_ANNOTATE =
sig
  val annotate_types : Proof.context -> term -> term
end

structure Sledgehammer_Annotate : SLEDGEHAMMER_ANNOTATE =
struct

(* Util *)
fun post_traverse_term_type' f _ (t as Const (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Free (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Var (_, T)) s = f t T s
  | post_traverse_term_type' f env (t as Bound i) s = f t (nth env i) s
  | post_traverse_term_type' f env (Abs (x, T1, b)) s =
    let
      val ((b', s'), T2) = post_traverse_term_type' f (T1 :: env) b s
    in f (Abs (x, T1, b')) (T1 --> T2) s' end
  | post_traverse_term_type' f env (u $ v) s =
    let
      val ((u', s'), Type (_, [_, T])) = post_traverse_term_type' f env u s
      val ((v', s''), _) = post_traverse_term_type' f env v s'
    in f (u' $ v') T s'' end

fun post_traverse_term_type f s t =
  post_traverse_term_type' (fn t => fn T => fn s => (f t T s, T)) [] t s |> fst
fun post_fold_term_type f s t =
  post_traverse_term_type (fn t => fn T => fn s => (t, f t T s)) s t |> snd

(* Data structures, orders *)
val cost_ord = prod_ord int_ord (prod_ord int_ord int_ord)
structure Var_Set_Tab = Table(
  type key = indexname list
  val ord = list_ord Term_Ord.fast_indexname_ord)

(* (1) Generalize types *)
fun generalize_types ctxt t =
  t |> map_types (fn _ => dummyT)
    |> Syntax.check_term
         (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)

(* (2) Typing-spot table *)
local
fun key_of_atype (TVar (z, _)) =
    Ord_List.insert Term_Ord.fast_indexname_ord z
  | key_of_atype _ = I
fun key_of_type T = fold_atyps key_of_atype T []
fun update_tab t T (tab, pos) =
  (case key_of_type T of
     [] => tab
   | key =>
     let val cost = (size_of_typ T, (size_of_term t, pos)) in
       case Var_Set_Tab.lookup tab key of
         NONE => Var_Set_Tab.update_new (key, cost) tab
       | SOME old_cost =>
         (case cost_ord (cost, old_cost) of
            LESS => Var_Set_Tab.update (key, cost) tab
          | _ => tab)
     end,
   pos + 1)
in
val typing_spot_table =
  post_fold_term_type update_tab (Var_Set_Tab.empty, 0) #> fst
end

(* (3) Reverse-greedy *)
fun reverse_greedy typing_spot_tab =
  let
    fun update_count z =
      fold (fn tvar => fn tab =>
        let val c = Vartab.lookup tab tvar |> the_default 0 in
          Vartab.update (tvar, c + z) tab
        end)
    fun superfluous tcount =
      forall (fn tvar => the (Vartab.lookup tcount tvar) > 1)
    fun drop_superfluous (tvars, (_, (_, spot))) (spots, tcount) =
      if superfluous tcount tvars then (spots, update_count ~1 tvars tcount)
      else (spot :: spots, tcount)
    val (typing_spots, tvar_count_tab) =
      Var_Set_Tab.fold
        (fn kv as (k, _) => apfst (cons kv) #> apsnd (update_count 1 k))
        typing_spot_tab ([], Vartab.empty)
      |>> sort_distinct (rev_order o cost_ord o pairself snd)
  in fold drop_superfluous typing_spots ([], tvar_count_tab) |> fst end

(* (4) Introduce annotations *)
fun introduce_annotations ctxt spots t t' =
  let
    val thy = Proof_Context.theory_of ctxt
    val get_types = post_fold_term_type (K cons) []
    fun match_types tp =
      fold (Sign.typ_match thy) (op ~~ (pairself get_types tp)) Vartab.empty
    fun unica' b x [] = if b then [x] else []
      | unica' b x (y :: ys) =
        if x = y then unica' false x ys
        else unica' true y ys |> b ? cons x
    fun unica ord xs =
      case sort ord xs of x :: ys => unica' true x ys | [] => []
    val add_all_tfree_namesT = fold_atyps (fn TFree (x, _) => cons x | _ => I)
    fun erase_unica_tfrees env =
      let
        val unica =
          Vartab.fold (add_all_tfree_namesT o snd o snd) env []
          |> filter_out (Variable.is_declared ctxt)
          |> unica fast_string_ord
        val erase_unica = map_atyps
          (fn T as TFree (s, _) =>
              if Ord_List.member fast_string_ord unica s then dummyT else T
            | T => T)
      in Vartab.map (K (apsnd erase_unica)) env end
    val env = match_types (t', t) |> erase_unica_tfrees
    fun get_annot env (TFree _) = (false, (env, dummyT))
      | get_annot env (T as TVar (v, S)) =
        let val T' = Envir.subst_type env T in
          if T' = dummyT then (false, (env, dummyT))
          else (true, (Vartab.update (v, (S, dummyT)) env, T'))
        end
      | get_annot env (Type (S, Ts)) =
        (case fold_rev (fn T => fn (b, (env, Ts)) =>
                  let
                    val (b', (env', T)) = get_annot env T
                  in (b orelse b', (env', T :: Ts)) end)
                Ts (false, (env, [])) of
           (true, (env', Ts)) => (true, (env', Type (S, Ts)))
         | (false, (env', _)) => (false, (env', dummyT)))
    fun post1 _ T (env, cp, ps as p :: ps', annots) =
        if p <> cp then
          (env, cp + 1, ps, annots)
        else
          let val (_, (env', T')) = get_annot env T in
            (env', cp + 1, ps', (p, T') :: annots)
          end
      | post1 _ _ accum = accum
    val (_, _, _, annots) = post_fold_term_type post1 (env, 0, spots, []) t'
    fun post2 t _ (cp, annots as (p, T) :: annots') =
        if p <> cp then (t, (cp + 1, annots))
        else (Type.constraint T t, (cp + 1, annots'))
      | post2 t _ x = (t, x)
  in post_traverse_term_type post2 (0, rev annots) t |> fst end

(* (5) Annotate *)
fun annotate_types ctxt t =
  let
    val t' = generalize_types ctxt t
    val typing_spots =
      t' |> typing_spot_table
         |> reverse_greedy
         |> sort int_ord
  in introduce_annotations ctxt typing_spots t t' end

end
