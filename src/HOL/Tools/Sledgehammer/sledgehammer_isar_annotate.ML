(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_annotate.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Supplements term with a locally minmal, complete set of type constraints. Complete: The constraints
suffice to infer the term's types. Minimal: Reducing the set of constraints further will make it
incomplete.

When configuring the pretty printer appropriately, the constraints will show up as type annotations
when printing the term. This allows the term to be printed and reparsed without a change of types.

Note: Terms should be unchecked before calling "annotate_types_in_term" to avoid awkward syntax.
*)

signature SLEDGEHAMMER_ISAR_ANNOTATE =
sig
  val annotate_types_in_term : Proof.context -> term -> term
end;

structure Sledgehammer_Isar_Annotate : SLEDGEHAMMER_ISAR_ANNOTATE =
struct

fun post_traverse_term_type' f _ (t as Const (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Free (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Var (_, T)) s = f t T s
  | post_traverse_term_type' f env (t as Bound i) s = f t (nth env i) s
  | post_traverse_term_type' f env (Abs (x, T1, b)) s =
    let val ((b', s'), T2) = post_traverse_term_type' f (T1 :: env) b s in
      f (Abs (x, T1, b')) (T1 --> T2) s'
    end
  | post_traverse_term_type' f env (u $ v) s =
    let
      val ((u', s'), Type (_, [_, T])) = post_traverse_term_type' f env u s
      val ((v', s''), _) = post_traverse_term_type' f env v s'
    in f (u' $ v') T s'' end
    handle Bind => raise Fail "Sledgehammer_Isar_Annotate: post_traverse_term_type'"

fun post_traverse_term_type f s t =
  post_traverse_term_type' (fn t => fn T => fn s => (f t T s, T)) [] t s |> fst
fun post_fold_term_type f s t =
  post_traverse_term_type (fn t => fn T => fn s => (t, f t T s)) s t |> snd

fun fold_map_atypes f T s =
  (case T of
    Type (name, Ts) =>
    let val (Ts, s) = fold_map (fold_map_atypes f) Ts s in
      (Type (name, Ts), s)
    end
  | _ => f T s)

val indexname_ord = Term_Ord.fast_indexname_ord
val cost_ord = prod_ord int_ord (prod_ord int_ord int_ord)

structure Var_Set_Tab = Table(
  type key = indexname list
  val ord = list_ord indexname_ord)

fun generalize_types ctxt t =
  let
    val erase_types = map_types (fn _ => dummyT)
    (* use schematic type variables *)
    val ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern
    val infer_types = singleton (Type_Infer_Context.infer_types ctxt)
  in
     t |> erase_types |> infer_types
  end

fun match_types ctxt t1 t2 =
  let
    val thy = Proof_Context.theory_of ctxt
    val get_types = post_fold_term_type (K cons) []
  in
    fold (perhaps o try o Sign.typ_match thy) (get_types t1 ~~ get_types t2) Vartab.empty
  end

fun handle_trivial_tfrees ctxt t' subst =
  let
    val add_tfree_names = snd #> snd #> fold_atyps (fn TFree (x, _) => cons x | _ => I)

    val trivial_tfree_names =
      Vartab.fold add_tfree_names subst []
      |> filter_out (Variable.is_declared ctxt)
      |> distinct (op =)
    val tfree_name_trivial = Ord_List.member fast_string_ord trivial_tfree_names

    val trivial_tvar_names =
      Vartab.fold
        (fn (tvar_name, (_, TFree (tfree_name, _))) =>
               tfree_name_trivial tfree_name ? cons tvar_name
          | _ => I)
        subst
        []
      |> sort indexname_ord
    val tvar_name_trivial = Ord_List.member indexname_ord trivial_tvar_names

    val t' =
      t' |> map_types
              (map_type_tvar
                (fn (idxn, sort) =>
                  if tvar_name_trivial idxn then dummyT else TVar (idxn, sort)))

    val subst =
      subst |> fold Vartab.delete trivial_tvar_names
            |> Vartab.map
               (K (apsnd (map_type_tfree
                           (fn (name, sort) =>
                              if tfree_name_trivial name then dummyT
                              else TFree (name, sort)))))
  in
    (t', subst)
  end

fun key_of_atype (TVar (z, _)) = Ord_List.insert indexname_ord z
  | key_of_atype _ = I
fun key_of_type T = fold_atyps key_of_atype T []

fun update_tab t T (tab, pos) =
  ((case key_of_type T of
     [] => tab
   | key =>
     let val cost = (size_of_typ T, (size_of_term t, pos)) in
       (case Var_Set_Tab.lookup tab key of
         NONE => Var_Set_Tab.update_new (key, cost) tab
       | SOME old_cost =>
         (case cost_ord (cost, old_cost) of
           LESS => Var_Set_Tab.update (key, cost) tab
         | _ => tab))
     end),
   pos + 1)

val typing_spot_table = post_fold_term_type update_tab (Var_Set_Tab.empty, 0) #> fst

fun reverse_greedy typing_spot_tab =
  let
    fun update_count z =
      fold (fn tvar => fn tab =>
        let val c = Vartab.lookup tab tvar |> the_default 0 in
          Vartab.update (tvar, c + z) tab
        end)
    fun superfluous tcount = forall (fn tvar => the (Vartab.lookup tcount tvar) > 1)
    fun drop_superfluous (tvars, (_, (_, spot))) (spots, tcount) =
      if superfluous tcount tvars then (spots, update_count ~1 tvars tcount)
      else (spot :: spots, tcount)

    val (typing_spots, tvar_count_tab) =
      Var_Set_Tab.fold (fn kv as (k, _) => apfst (cons kv) #> apsnd (update_count 1 k))
        typing_spot_tab ([], Vartab.empty)
      |>> sort_distinct (rev_order o cost_ord o pairself snd)
  in
    fold drop_superfluous typing_spots ([], tvar_count_tab) |> fst
  end

fun introduce_annotations subst spots t t' =
  let
    fun subst_atype (T as TVar (idxn, S)) subst =
        (Envir.subst_type subst T, Vartab.update (idxn, (S, dummyT)) subst)
      | subst_atype T subst = (T, subst)

    val subst_type = fold_map_atypes subst_atype

    fun collect_annot _ T (subst, cp, ps as p :: ps', annots) =
        if p <> cp then
          (subst, cp + 1, ps, annots)
        else
          let val (T, subst) = subst_type T subst in
            (subst, cp + 1, ps', (p, T) :: annots)
          end
      | collect_annot _ _ x = x

    val (_, _, _, annots) = post_fold_term_type collect_annot (subst, 0, spots, []) t'

    fun insert_annot t _ (cp, annots as (p, T) :: annots') =
        if p <> cp then (t, (cp + 1, annots)) else (Type.constraint T t, (cp + 1, annots'))
      | insert_annot t _ x = (t, x)
  in
    t |> post_traverse_term_type insert_annot (0, rev annots) |> fst
  end

fun annotate_types_in_term ctxt t =
  let
    val t' = generalize_types ctxt t
    val subst = match_types ctxt t' t
    val (t'', subst') = handle_trivial_tfrees ctxt t' subst
    val typing_spots = t'' |> typing_spot_table |> reverse_greedy |> sort int_ord
  in
    introduce_annotations subst' typing_spots t t''
  end

end;
