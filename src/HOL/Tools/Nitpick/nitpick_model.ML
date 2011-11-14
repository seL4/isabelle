(*  Title:      HOL/Tools/Nitpick/nitpick_model.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Model reconstruction for Nitpick.
*)

signature NITPICK_MODEL =
sig
  type styp = Nitpick_Util.styp
  type scope = Nitpick_Scope.scope
  type rep = Nitpick_Rep.rep
  type nut = Nitpick_Nut.nut

  type params =
    {show_datatypes: bool,
     show_skolems: bool,
     show_consts: bool}

  type term_postprocessor =
    Proof.context -> string -> (typ -> term list) -> typ -> term -> term

  structure NameTable : TABLE

  val irrelevant : string
  val unknown : string
  val unrep : unit -> string
  val register_term_postprocessor :
    typ -> term_postprocessor -> morphism -> Context.generic -> Context.generic
  val register_term_postprocessor_global :
    typ -> term_postprocessor -> theory -> theory
  val unregister_term_postprocessor :
    typ -> morphism -> Context.generic -> Context.generic
  val unregister_term_postprocessor_global : typ -> theory -> theory
  val tuple_list_for_name :
    nut NameTable.table -> Kodkod.raw_bound list -> nut -> int list list
  val dest_plain_fun : term -> bool * (term list * term list)
  val reconstruct_hol_model :
    params -> scope -> (term option * int list) list
    -> (typ option * string list) list -> styp list -> styp list -> nut list
    -> nut list -> nut list -> nut NameTable.table -> Kodkod.raw_bound list
    -> Pretty.T * bool
  val prove_hol_model :
    scope -> Time.time option -> nut list -> nut list -> nut NameTable.table
    -> Kodkod.raw_bound list -> term -> bool option
end;

structure Nitpick_Model : NITPICK_MODEL =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Scope
open Nitpick_Peephole
open Nitpick_Rep
open Nitpick_Nut

structure KK = Kodkod

type params =
  {show_datatypes: bool,
   show_skolems: bool,
   show_consts: bool}

type term_postprocessor =
  Proof.context -> string -> (typ -> term list) -> typ -> term -> term

structure Data = Generic_Data
(
  type T = (typ * term_postprocessor) list
  val empty = []
  val extend = I
  fun merge data = AList.merge (op =) (K true) data
)

fun xsym s s' () = if print_mode_active Symbol.xsymbolsN then s else s'

val irrelevant = "_"
val unknown = "?"
val unrep = xsym "\<dots>" "..."
val maybe_mixfix = xsym "_\<^sup>?" "_?"
val base_mixfix = xsym "_\<^bsub>base\<^esub>" "_.base"
val step_mixfix = xsym "_\<^bsub>step\<^esub>" "_.step"
val abs_mixfix = xsym "\<guillemotleft>_\<guillemotright>" "\"_\""
val arg_var_prefix = "x"
val cyclic_co_val_name = xsym "\<omega>" "w"
val cyclic_const_prefix = xsym "\<xi>" "X"
fun cyclic_type_name () = nitpick_prefix ^ cyclic_const_prefix ()
val opt_flag = nitpick_prefix ^ "opt"
val non_opt_flag = nitpick_prefix ^ "non_opt"

type atom_pool = ((string * int) * int list) list

fun add_wacky_syntax ctxt =
  let
    val name_of = fst o dest_Const
    val thy = Proof_Context.theory_of ctxt |> Context.reject_draft
    val (maybe_t, thy) =
      Sign.declare_const_global ((@{binding nitpick_maybe}, @{typ "'a => 'a"}),
                          Mixfix (maybe_mixfix (), [1000], 1000)) thy
    val (abs_t, thy) =
      Sign.declare_const_global ((@{binding nitpick_abs}, @{typ "'a => 'b"}),
                          Mixfix (abs_mixfix (), [40], 40)) thy
    val (base_t, thy) =
      Sign.declare_const_global ((@{binding nitpick_base}, @{typ "'a => 'a"}),
                          Mixfix (base_mixfix (), [1000], 1000)) thy
    val (step_t, thy) =
      Sign.declare_const_global ((@{binding nitpick_step}, @{typ "'a => 'a"}),
                          Mixfix (step_mixfix (), [1000], 1000)) thy
  in
    (pairself (pairself name_of) ((maybe_t, abs_t), (base_t, step_t)),
     Proof_Context.transfer_syntax thy ctxt)
  end

(** Term reconstruction **)

fun nth_atom_number pool T j =
  case AList.lookup (op =) (!pool) T of
    SOME js =>
    (case find_index (curry (op =) j) js of
       ~1 => (Unsynchronized.change pool (cons (T, j :: js));
              length js + 1)
     | n => length js - n)
  | NONE => (Unsynchronized.change pool (cons (T, [j])); 1)
fun atom_suffix s =
  nat_subscript
  #> (s <> "" andalso Symbol.is_ascii_digit (List.last (raw_explode s)))  (* FIXME Symbol.explode (?) *)
     ? prefix "\<^isub>,"
fun nth_atom_name thy atomss pool prefix T j =
  let
    val ss = these (triple_lookup (type_match thy) atomss T)
    val m = nth_atom_number pool T j
  in
    if m <= length ss then
      nth ss (m - 1)
    else case T of
      Type (s, _) =>
      let val s' = shortest_name s in
        prefix ^
        (if T = @{typ string} then "s"
         else if String.isPrefix "\\" s' then s'
         else substring (s', 0, 1)) ^ atom_suffix s m
      end
    | TFree (s, _) => prefix ^ perhaps (try (unprefix "'")) s ^ atom_suffix s m
    | _ => raise TYPE ("Nitpick_Model.nth_atom_name", [T], [])
  end
fun nth_atom thy atomss pool for_auto T j =
  if for_auto then
    Free (nth_atom_name thy atomss pool (hd (space_explode "." nitpick_prefix))
                        T j, T)
  else
    Const (nth_atom_name thy atomss pool "" T j, T)

fun extract_real_number (Const (@{const_name divide}, _) $ t1 $ t2) =
    real (snd (HOLogic.dest_number t1)) / real (snd (HOLogic.dest_number t2))
  | extract_real_number t = real (snd (HOLogic.dest_number t))
fun nice_term_ord (Abs (_, _, t1), Abs (_, _, t2)) = nice_term_ord (t1, t2)
  | nice_term_ord tp = Real.compare (pairself extract_real_number tp)
    handle TERM ("dest_number", _) =>
           case tp of
             (t11 $ t12, t21 $ t22) =>
             (case nice_term_ord (t11, t21) of
                EQUAL => nice_term_ord (t12, t22)
              | ord => ord)
           | _ => Term_Ord.fast_term_ord tp

fun register_term_postprocessor_generic T postproc =
  Data.map (cons (T, postproc))
(* TODO: Consider morphism. *)
fun register_term_postprocessor T postproc (_ : morphism) =
  register_term_postprocessor_generic T postproc
val register_term_postprocessor_global =
  Context.theory_map oo register_term_postprocessor_generic

fun unregister_term_postprocessor_generic T = Data.map (AList.delete (op =) T)
(* TODO: Consider morphism. *)
fun unregister_term_postprocessor T (_ : morphism) =
  unregister_term_postprocessor_generic T
val unregister_term_postprocessor_global =
  Context.theory_map o unregister_term_postprocessor_generic

fun tuple_list_for_name rel_table bounds name =
  the (AList.lookup (op =) bounds (the_rel rel_table name)) handle NUT _ => [[]]

fun unarize_unbox_etc_term (Const (@{const_name FunBox}, _) $ t1) =
    unarize_unbox_etc_term t1
  | unarize_unbox_etc_term
        (Const (@{const_name PairBox},
                Type (@{type_name fun}, [T1, Type (@{type_name fun}, [T2, _])]))
         $ t1 $ t2) =
    let val Ts = map uniterize_unarize_unbox_etc_type [T1, T2] in
      Const (@{const_name Pair}, Ts ---> Type (@{type_name prod}, Ts))
      $ unarize_unbox_etc_term t1 $ unarize_unbox_etc_term t2
    end
  | unarize_unbox_etc_term (Const (s, T)) =
    Const (s, uniterize_unarize_unbox_etc_type T)
  | unarize_unbox_etc_term (t1 $ t2) =
    unarize_unbox_etc_term t1 $ unarize_unbox_etc_term t2
  | unarize_unbox_etc_term (Free (s, T)) =
    Free (s, uniterize_unarize_unbox_etc_type T)
  | unarize_unbox_etc_term (Var (x, T)) =
    Var (x, uniterize_unarize_unbox_etc_type T)
  | unarize_unbox_etc_term (Bound j) = Bound j
  | unarize_unbox_etc_term (Abs (s, T, t')) =
    Abs (s, uniterize_unarize_unbox_etc_type T, unarize_unbox_etc_term t')

fun factor_out_types (T1 as Type (@{type_name prod}, [T11, T12]))
                     (T2 as Type (@{type_name prod}, [T21, T22])) =
    let val (n1, n2) = pairself num_factors_in_type (T11, T21) in
      if n1 = n2 then
        let
          val ((T11', opt_T12'), (T21', opt_T22')) = factor_out_types T12 T22
        in
          ((Type (@{type_name prod}, [T11, T11']), opt_T12'),
           (Type (@{type_name prod}, [T21, T21']), opt_T22'))
        end
      else if n1 < n2 then
        case factor_out_types T1 T21 of
          (p1, (T21', NONE)) => (p1, (T21', SOME T22))
        | (p1, (T21', SOME T22')) =>
          (p1, (T21', SOME (Type (@{type_name prod}, [T22', T22]))))
      else
        swap (factor_out_types T2 T1)
    end
  | factor_out_types (Type (@{type_name prod}, [T11, T12])) T2 =
    ((T11, SOME T12), (T2, NONE))
  | factor_out_types T1 (Type (@{type_name prod}, [T21, T22])) =
    ((T1, NONE), (T21, SOME T22))
  | factor_out_types T1 T2 = ((T1, NONE), (T2, NONE))

fun make_plain_fun maybe_opt T1 T2 =
  let
    fun aux T1 T2 [] =
        Const (if maybe_opt then opt_flag else non_opt_flag, T1 --> T2)
      | aux T1 T2 ((t1, t2) :: tps) =
        Const (@{const_name fun_upd}, (T1 --> T2) --> T1 --> T2 --> T1 --> T2)
        $ aux T1 T2 tps $ t1 $ t2
  in aux T1 T2 o rev end
fun is_plain_fun (Const (s, _)) = (s = opt_flag orelse s = non_opt_flag)
  | is_plain_fun (Const (@{const_name fun_upd}, _) $ t0 $ _ $ _) =
    is_plain_fun t0
  | is_plain_fun _ = false
val dest_plain_fun =
  let
    fun aux (Abs (_, _, Const (s, _))) = (s <> irrelevant, ([], []))
      | aux (Const (s, _)) = (s <> non_opt_flag, ([], []))
      | aux (Const (@{const_name fun_upd}, _) $ t0 $ t1 $ t2) =
        let val (maybe_opt, (ts1, ts2)) = aux t0 in
          (maybe_opt, (t1 :: ts1, t2 :: ts2))
        end
      | aux t = raise TERM ("Nitpick_Model.dest_plain_fun", [t])
  in apsnd (pairself rev) o aux end

fun break_in_two T T1 T2 t =
  let
    val ps = HOLogic.flat_tupleT_paths T
    val cut = length (HOLogic.strip_tupleT T1)
    val (ps1, ps2) = pairself HOLogic.flat_tupleT_paths (T1, T2)
    val (ts1, ts2) = t |> HOLogic.strip_ptuple ps |> chop cut
  in (HOLogic.mk_ptuple ps1 T1 ts1, HOLogic.mk_ptuple ps2 T2 ts2) end
fun pair_up (Type (@{type_name prod}, [T1', T2']))
            (t1 as Const (@{const_name Pair},
                          Type (@{type_name fun},
                                [_, Type (@{type_name fun}, [_, T1])]))
             $ t11 $ t12) t2 =
    if T1 = T1' then HOLogic.mk_prod (t1, t2)
    else HOLogic.mk_prod (t11, pair_up T2' t12 t2)
  | pair_up _ t1 t2 = HOLogic.mk_prod (t1, t2)
fun multi_pair_up T1 t1 (ts2, ts3) = map2 (pair o pair_up T1 t1) ts2 ts3

fun typecast_fun (Type (@{type_name fun}, [T1', T2'])) T1 T2 t =
    let
      fun do_curry T1 T1a T1b T2 t =
        let
          val (maybe_opt, tsp) = dest_plain_fun t
          val tps =
            tsp |>> map (break_in_two T1 T1a T1b)
                |> uncurry (map2 (fn (t1a, t1b) => fn t2 => (t1a, (t1b, t2))))
                |> AList.coalesce (op =)
                |> map (apsnd (make_plain_fun maybe_opt T1b T2))
        in make_plain_fun maybe_opt T1a (T1b --> T2) tps end
      and do_uncurry T1 T2 t =
        let
          val (maybe_opt, tsp) = dest_plain_fun t
          val tps =
            tsp |> op ~~
                |> maps (fn (t1, t2) =>
                            multi_pair_up T1 t1 (snd (dest_plain_fun t2)))
        in make_plain_fun maybe_opt T1 T2 tps end
      and do_arrow T1' T2' _ _ (Const (s, _)) = Const (s, T1' --> T2')
        | do_arrow T1' T2' T1 T2
                   (Const (@{const_name fun_upd}, _) $ t0 $ t1 $ t2) =
          Const (@{const_name fun_upd},
                 (T1' --> T2') --> T1' --> T2' --> T1' --> T2')
          $ do_arrow T1' T2' T1 T2 t0 $ do_term T1' T1 t1 $ do_term T2' T2 t2
        | do_arrow _ _ _ _ t =
          raise TERM ("Nitpick_Model.typecast_fun.do_arrow", [t])
      and do_fun T1' T2' T1 T2 t =
        case factor_out_types T1' T1 of
          ((_, NONE), (_, NONE)) => t |> do_arrow T1' T2' T1 T2
        | ((_, NONE), (T1a, SOME T1b)) =>
          t |> do_curry T1 T1a T1b T2 |> do_arrow T1' T2' T1a (T1b --> T2)
        | ((T1a', SOME T1b'), (_, NONE)) =>
          t |> do_arrow T1a' (T1b' --> T2') T1 T2 |> do_uncurry T1' T2'
        | _ => raise TYPE ("Nitpick_Model.typecast_fun.do_fun", [T1, T1'], [])
      and do_term (Type (@{type_name fun}, [T1', T2']))
                  (Type (@{type_name fun}, [T1, T2])) t =
          do_fun T1' T2' T1 T2 t
        | do_term (T' as Type (@{type_name prod}, Ts' as [T1', T2']))
                  (Type (@{type_name prod}, [T1, T2]))
                  (Const (@{const_name Pair}, _) $ t1 $ t2) =
          Const (@{const_name Pair}, Ts' ---> T')
          $ do_term T1' T1 t1 $ do_term T2' T2 t2
        | do_term T' T t =
          if T = T' then t
          else raise TYPE ("Nitpick_Model.typecast_fun.do_term", [T, T'], [])
    in if T1' = T1 andalso T2' = T2 then t else do_fun T1' T2' T1 T2 t end
  | typecast_fun T' _ _ _ =
    raise TYPE ("Nitpick_Model.typecast_fun", [T'], [])

fun truth_const_sort_key @{const True} = "0"
  | truth_const_sort_key @{const False} = "2"
  | truth_const_sort_key _ = "1"

fun mk_tuple (Type (@{type_name prod}, [T1, T2])) ts =
    HOLogic.mk_prod (mk_tuple T1 ts,
        mk_tuple T2 (List.drop (ts, length (HOLogic.flatten_tupleT T1))))
  | mk_tuple _ (t :: _) = t
  | mk_tuple T [] = raise TYPE ("Nitpick_Model.mk_tuple", [T], [])

fun varified_type_match ctxt (candid_T, pat_T) =
  let val thy = Proof_Context.theory_of ctxt in
    strict_type_match thy (candid_T, varify_type ctxt pat_T)
  end

fun all_values_of_type pool wacky_names (scope as {card_assigns, ...} : scope)
                       atomss sel_names rel_table bounds card T =
  let
    val card = if card = 0 then card_of_type card_assigns T else card
    fun nth_value_of_type n =
      let
        fun term unfold =
          reconstruct_term true unfold pool wacky_names scope atomss sel_names
                           rel_table bounds T T (Atom (card, 0)) [[n]]
      in
        case term false of
          t as Const (s, _) =>
          if String.isPrefix (cyclic_const_prefix ()) s then
            HOLogic.mk_eq (t, term true)
          else
            t
        | t => t
      end
  in index_seq 0 card |> map nth_value_of_type |> sort nice_term_ord end
and reconstruct_term maybe_opt unfold pool
        (wacky_names as ((maybe_name, abs_name), _))
        (scope as {hol_ctxt as {thy, ctxt, stds, ...}, binarize, card_assigns,
                   bits, datatypes, ofs, ...})
        atomss sel_names rel_table bounds =
  let
    val for_auto = (maybe_name = "")
    fun value_of_bits jss =
      let
        val j0 = offset_of_type ofs @{typ unsigned_bit}
        val js = map (Integer.add (~ j0) o the_single) jss
      in
        fold (fn j => Integer.add (reasonable_power 2 j |> j = bits ? op ~))
             js 0
      end
    val all_values =
      all_values_of_type pool wacky_names scope atomss sel_names rel_table
                         bounds 0
    fun postprocess_term (Type (@{type_name fun}, _)) = I
      | postprocess_term T =
        case Data.get (Context.Proof ctxt) of
          [] => I
        | postprocs =>
          case AList.lookup (varified_type_match ctxt) postprocs T of
            SOME postproc => postproc ctxt maybe_name all_values T
          | NONE => I
    fun postprocess_subterms Ts (t1 $ t2) =
        let val t = postprocess_subterms Ts t1 $ postprocess_subterms Ts t2 in
          postprocess_term (fastype_of1 (Ts, t)) t
        end
      | postprocess_subterms Ts (Abs (s, T, t')) =
        Abs (s, T, postprocess_subterms (T :: Ts) t')
      | postprocess_subterms Ts t = postprocess_term (fastype_of1 (Ts, t)) t
    fun make_set maybe_opt T1 T2 tps =
      let
        val empty_const = Const (@{const_abbrev Set.empty}, T1 --> T2)
        val insert_const = Const (@{const_name insert},
                                  T1 --> (T1 --> T2) --> T1 --> T2)
        fun aux [] =
            if maybe_opt andalso not (is_complete_type datatypes false T1) then
              insert_const $ Const (unrep (), T1) $ empty_const
            else
              empty_const
          | aux ((t1, t2) :: zs) =
            aux zs
            |> t2 <> @{const False}
               ? curry (op $)
                       (insert_const
                        $ (t1 |> t2 <> @{const True}
                                 ? curry (op $)
                                         (Const (maybe_name, T1 --> T1))))
      in
        if forall (fn (_, t) => t <> @{const True} andalso t <> @{const False})
                  tps then
          Const (unknown, T1 --> T2)
        else
          aux tps
      end
    fun make_map maybe_opt T1 T2 T2' =
      let
        val update_const = Const (@{const_name fun_upd},
                                  (T1 --> T2) --> T1 --> T2 --> T1 --> T2)
        fun aux' [] = Const (@{const_abbrev Map.empty}, T1 --> T2)
          | aux' ((t1, t2) :: tps) =
            (case t2 of
               Const (@{const_name None}, _) => aux' tps
             | _ => update_const $ aux' tps $ t1 $ t2)
        fun aux tps =
          if maybe_opt andalso not (is_complete_type datatypes false T1) then
            update_const $ aux' tps $ Const (unrep (), T1)
            $ (Const (@{const_name Some}, T2' --> T2) $ Const (unknown, T2'))
          else
            aux' tps
      in aux end
    fun polish_funs Ts t =
      (case fastype_of1 (Ts, t) of
         Type (@{type_name fun}, [T1, T2]) =>
         if is_plain_fun t then
           case T2 of
             @{typ bool} =>
             let
               val (maybe_opt, ts_pair) =
                 dest_plain_fun t ||> pairself (map (polish_funs Ts))
             in
               make_set maybe_opt T1 T2
                        (sort_wrt (truth_const_sort_key o snd) (op ~~ ts_pair))
             end
           | Type (@{type_name option}, [T2']) =>
             let
               val (maybe_opt, ts_pair) =
                 dest_plain_fun t ||> pairself (map (polish_funs Ts))
             in make_map maybe_opt T1 T2 T2' (rev (op ~~ ts_pair)) end
           | _ => raise SAME ()
         else
           raise SAME ()
       | _ => raise SAME ())
      handle SAME () =>
             case t of
               (t1 as Const (@{const_name fun_upd}, _) $ t11 $ _)
               $ (t2 as Const (s, _)) =>
               if s = unknown then polish_funs Ts t11
               else polish_funs Ts t1 $ polish_funs Ts t2
             | t1 $ t2 => polish_funs Ts t1 $ polish_funs Ts t2
             | Abs (s, T, t') => Abs (s, T, polish_funs (T :: Ts) t')
             | Const (s, Type (@{type_name fun}, [T1, T2])) =>
               if s = opt_flag orelse s = non_opt_flag then
                 Abs ("x", T1,
                      Const (if is_complete_type datatypes false T1 then
                               irrelevant
                             else
                               unknown, T2))
               else
                 t
             | t => t
    fun make_fun maybe_opt T1 T2 T' ts1 ts2 =
      ts1 ~~ ts2 |> sort (nice_term_ord o pairself fst)
                 |> make_plain_fun maybe_opt T1 T2
                 |> unarize_unbox_etc_term
                 |> typecast_fun (uniterize_unarize_unbox_etc_type T')
                                 (uniterize_unarize_unbox_etc_type T1)
                                 (uniterize_unarize_unbox_etc_type T2)
    fun term_for_atom seen (T as Type (@{type_name fun}, [T1, T2])) T' j _ =
        let
          val k1 = card_of_type card_assigns T1
          val k2 = card_of_type card_assigns T2
        in
          term_for_rep true seen T T' (Vect (k1, Atom (k2, 0)))
                       [nth_combination (replicate k1 (k2, 0)) j]
          handle General.Subscript =>
                 raise ARG ("Nitpick_Model.reconstruct_term.term_for_atom",
                            signed_string_of_int j ^ " for " ^
                            string_for_rep (Vect (k1, Atom (k2, 0))))
        end
      | term_for_atom seen (Type (@{type_name prod}, [T1, T2])) _ j k =
        let
          val k1 = card_of_type card_assigns T1
          val k2 = k div k1
        in
          list_comb (HOLogic.pair_const T1 T2,
                     map3 (fn T => term_for_atom seen T T) [T1, T2]
                          [j div k2, j mod k2] [k1, k2]) (* ### k2 or k1? FIXME *)
        end
      | term_for_atom seen @{typ prop} _ j k =
        HOLogic.mk_Trueprop (term_for_atom seen bool_T bool_T j k)
      | term_for_atom _ @{typ bool} _ j _ =
        if j = 0 then @{const False} else @{const True}
      | term_for_atom seen T _ j k =
        if T = nat_T andalso is_standard_datatype thy stds nat_T then
          HOLogic.mk_number nat_T j
        else if T = int_T then
          HOLogic.mk_number int_T (int_for_atom (k, 0) j)
        else if is_fp_iterator_type T then
          HOLogic.mk_number nat_T (k - j - 1)
        else if T = @{typ bisim_iterator} then
          HOLogic.mk_number nat_T j
        else case datatype_spec datatypes T of
          NONE => nth_atom thy atomss pool for_auto T j
        | SOME {deep = false, ...} => nth_atom thy atomss pool for_auto T j
        | SOME {co, standard, constrs, ...} =>
          let
            fun tuples_for_const (s, T) =
              tuple_list_for_name rel_table bounds (ConstName (s, T, Any))
            fun cyclic_atom () =
              nth_atom thy atomss pool for_auto (Type (cyclic_type_name (), []))
                       j
            fun cyclic_var () =
              Var ((nth_atom_name thy atomss pool "" T j, 0), T)
            val discr_jsss = map (tuples_for_const o discr_for_constr o #const)
                                 constrs
            val real_j = j + offset_of_type ofs T
            val constr_x as (constr_s, constr_T) =
              get_first (fn (jss, {const, ...}) =>
                            if member (op =) jss [real_j] then SOME const
                            else NONE)
                        (discr_jsss ~~ constrs) |> the
            val arg_Ts = curried_binder_types constr_T
            val sel_xs =
              map (binarized_and_boxed_nth_sel_for_constr hol_ctxt binarize
                                                          constr_x)
                  (index_seq 0 (length arg_Ts))
            val sel_Rs =
              map (fn x => get_first
                               (fn ConstName (s', T', R) =>
                                   if (s', T') = x then SOME R else NONE
                                 | u => raise NUT ("Nitpick_Model.reconstruct_\
                                                   \term.term_for_atom", [u]))
                               sel_names |> the) sel_xs
            val arg_Rs = map (snd o dest_Func) sel_Rs
            val sel_jsss = map tuples_for_const sel_xs
            val arg_jsss =
              map (map_filter (fn js => if hd js = real_j then SOME (tl js)
                                        else NONE)) sel_jsss
            val uncur_arg_Ts = binder_types constr_T
            val maybe_cyclic = co orelse not standard
          in
            if maybe_cyclic andalso not (null seen) andalso
               member (op =) (seen |> unfold ? (fst o split_last)) (T, j) then
              cyclic_var ()
            else if constr_s = @{const_name Word} then
              HOLogic.mk_number
                  (if T = @{typ "unsigned_bit word"} then nat_T else int_T)
                  (value_of_bits (the_single arg_jsss))
            else
              let
                val seen = seen |> maybe_cyclic ? cons (T, j)
                val ts =
                  if length arg_Ts = 0 then
                    []
                  else
                    map3 (fn Ts => term_for_rep true seen Ts Ts) arg_Ts arg_Rs
                         arg_jsss
                    |> mk_tuple (HOLogic.mk_tupleT uncur_arg_Ts)
                    |> dest_n_tuple (length uncur_arg_Ts)
                val t =
                  if constr_s = @{const_name Abs_Frac} then
                    case ts of
                      [Const (@{const_name Pair}, _) $ t1 $ t2] =>
                      frac_from_term_pair (body_type T) t1 t2
                    | _ => raise TERM ("Nitpick_Model.reconstruct_term.\
                                       \term_for_atom (Abs_Frac)", ts)
                  else if not for_auto andalso
                          (is_abs_fun ctxt constr_x orelse
                           constr_s = @{const_name Quot}) then
                    Const (abs_name, constr_T) $ the_single ts
                  else
                    list_comb (Const constr_x, ts)
              in
                if maybe_cyclic then
                  let val var = cyclic_var () in
                    if unfold andalso not standard andalso
                       length seen = 1 andalso
                       exists_subterm
                           (fn Const (s, _) =>
                               String.isPrefix (cyclic_const_prefix ()) s
                             | t' => t' = var) t then
                      subst_atomic [(var, cyclic_atom ())] t
                    else if exists_subterm (curry (op =) var) t then
                      if co then
                        Const (@{const_name The}, (T --> bool_T) --> T)
                        $ Abs (cyclic_co_val_name (), T,
                               Const (@{const_name HOL.eq}, T --> T --> bool_T)
                               $ Bound 0 $ abstract_over (var, t))
                      else
                        cyclic_atom ()
                    else
                      t
                  end
                else
                  t
              end
          end
    and term_for_vect seen k R T1 T2 T' js =
      make_fun true T1 T2 T'
               (map (fn j => term_for_atom seen T1 T1 j k) (index_seq 0 k))
               (map (term_for_rep true seen T2 T2 R o single)
                    (batch_list (arity_of_rep R) js))
    and term_for_rep _ seen T T' (R as Atom (k, j0)) [[j]] =
        if j >= j0 andalso j < j0 + k then term_for_atom seen T T' (j - j0) k
        else raise REP ("Nitpick_Model.reconstruct_term.term_for_rep", [R])
      | term_for_rep _ seen (Type (@{type_name prod}, [T1, T2])) _
                     (Struct [R1, R2]) [js] =
        let
          val arity1 = arity_of_rep R1
          val (js1, js2) = chop arity1 js
        in
          list_comb (HOLogic.pair_const T1 T2,
                     map3 (fn T => term_for_rep true seen T T) [T1, T2] [R1, R2]
                          [[js1], [js2]])
        end
      | term_for_rep _ seen (Type (@{type_name fun}, [T1, T2])) T'
                     (Vect (k, R')) [js] =
        term_for_vect seen k R' T1 T2 T' js
      | term_for_rep maybe_opt seen (Type (@{type_name fun}, [T1, T2])) T'
                     (Func (R1, Formula Neut)) jss =
        let
          val jss1 = all_combinations_for_rep R1
          val ts1 = map (term_for_rep true seen T1 T1 R1 o single) jss1
          val ts2 =
            map (fn js => term_for_rep true seen T2 T2 (Atom (2, 0))
                                       [[int_from_bool (member (op =) jss js)]])
                jss1
        in make_fun maybe_opt T1 T2 T' ts1 ts2 end
      | term_for_rep maybe_opt seen (Type (@{type_name fun}, [T1, T2])) T'
                     (Func (R1, R2)) jss =
        let
          val arity1 = arity_of_rep R1
          val jss1 = all_combinations_for_rep R1
          val ts1 = map (term_for_rep false seen T1 T1 R1 o single) jss1
          val grouped_jss2 = AList.group (op =) (map (chop arity1) jss)
          val ts2 = map (term_for_rep false seen T2 T2 R2 o the_default []
                         o AList.lookup (op =) grouped_jss2) jss1
        in make_fun maybe_opt T1 T2 T' ts1 ts2 end
      | term_for_rep _ seen T T' (Opt R) jss =
        if null jss then Const (unknown, T)
        else term_for_rep true seen T T' R jss
      | term_for_rep _ _ T _ R jss =
        raise ARG ("Nitpick_Model.reconstruct_term.term_for_rep",
                   Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R ^ " " ^
                   string_of_int (length jss))
  in
    postprocess_subterms [] o polish_funs [] o unarize_unbox_etc_term
    oooo term_for_rep maybe_opt []
  end

(** Constant postprocessing **)

fun dest_n_tuple_type 1 T = [T]
  | dest_n_tuple_type n (Type (_, [T1, T2])) =
    T1 :: dest_n_tuple_type (n - 1) T2
  | dest_n_tuple_type _ T =
    raise TYPE ("Nitpick_Model.dest_n_tuple_type", [T], [])

fun const_format thy def_tables (x as (s, T)) =
  if String.isPrefix unrolled_prefix s then
    const_format thy def_tables (original_name s, range_type T)
  else if String.isPrefix skolem_prefix s then
    let
      val k = unprefix skolem_prefix s
              |> strip_first_name_sep |> fst |> space_explode "@"
              |> hd |> Int.fromString |> the
    in [k, num_binder_types T - k] end
  else if original_name s <> s then
    [num_binder_types T]
  else case def_of_const thy def_tables x of
    SOME t' => if fixpoint_kind_of_rhs t' <> NoFp then
                 let val k = length (strip_abs_vars t') in
                   [k, num_binder_types T - k]
                 end
               else
                 [num_binder_types T]
  | NONE => [num_binder_types T]
fun intersect_formats _ [] = []
  | intersect_formats [] _ = []
  | intersect_formats ks1 ks2 =
    let val ((ks1', k1), (ks2', k2)) = pairself split_last (ks1, ks2) in
      intersect_formats (ks1' @ (if k1 > k2 then [k1 - k2] else []))
                        (ks2' @ (if k2 > k1 then [k2 - k1] else [])) @
      [Int.min (k1, k2)]
    end

fun lookup_format thy def_tables formats t =
  case AList.lookup (fn (SOME x, SOME y) =>
                        (term_match thy) (x, y) | _ => false)
                    formats (SOME t) of
    SOME format => format
  | NONE => let val format = the (AList.lookup (op =) formats NONE) in
              case t of
                Const x => intersect_formats format
                                             (const_format thy def_tables x)
              | _ => format
            end

fun format_type default_format format T =
  let
    val T = uniterize_unarize_unbox_etc_type T
    val format = format |> filter (curry (op <) 0)
  in
    if forall (curry (op =) 1) format then
      T
    else
      let
        val (binder_Ts, body_T) = strip_type T
        val batched =
          binder_Ts
          |> map (format_type default_format default_format)
          |> rev |> chunk_list_unevenly (rev format)
          |> map (HOLogic.mk_tupleT o rev)
      in List.foldl (op -->) body_T batched end
  end
fun format_term_type thy def_tables formats t =
  format_type (the (AList.lookup (op =) formats NONE))
              (lookup_format thy def_tables formats t) (fastype_of t)

fun repair_special_format js m format =
  m - 1 downto 0 |> chunk_list_unevenly (rev format)
                 |> map (rev o filter_out (member (op =) js))
                 |> filter_out null |> map length |> rev

fun user_friendly_const ({thy, evals, def_tables, skolems, special_funs, ...}
                         : hol_context) (base_name, step_name) formats =
  let
    val default_format = the (AList.lookup (op =) formats NONE)
    fun do_const (x as (s, T)) =
      (if String.isPrefix special_prefix s then
         let
           val do_term = map_aterms (fn Const x => fst (do_const x) | t' => t')
           val (x' as (_, T'), js, ts) =
             AList.find (op =) (!special_funs) (s, unarize_unbox_etc_type T)
             |> the_single
           val max_j = List.last js
           val Ts = List.take (binder_types T', max_j + 1)
           val missing_js = filter_out (member (op =) js) (0 upto max_j)
           val missing_Ts = filter_indices missing_js Ts
           fun nth_missing_var n =
             ((arg_var_prefix ^ nat_subscript (n + 1), 0), nth missing_Ts n)
           val missing_vars = map nth_missing_var (0 upto length missing_js - 1)
           val vars = special_bounds ts @ missing_vars
           val ts' =
             map (fn j =>
                     case AList.lookup (op =) (js ~~ ts) j of
                       SOME t => do_term t
                     | NONE =>
                       Var (nth missing_vars
                                (find_index (curry (op =) j) missing_js)))
                 (0 upto max_j)
           val t = do_const x' |> fst
           val format =
             case AList.lookup (fn (SOME t1, SOME t2) => term_match thy (t1, t2)
                                 | _ => false) formats (SOME t) of
               SOME format =>
               repair_special_format js (num_binder_types T') format
             | NONE =>
               const_format thy def_tables x'
               |> repair_special_format js (num_binder_types T')
               |> intersect_formats default_format
         in
           (list_comb (t, ts') |> fold_rev abs_var vars,
            format_type default_format format T)
         end
       else if String.isPrefix uncurry_prefix s then
         let
           val (ss, s') = unprefix uncurry_prefix s
                          |> strip_first_name_sep |>> space_explode "@"
         in
           if String.isPrefix step_prefix s' then
             do_const (s', T)
           else
             let
               val k = the (Int.fromString (hd ss))
               val j = the (Int.fromString (List.last ss))
               val (before_Ts, (tuple_T, rest_T)) =
                 strip_n_binders j T ||> (strip_n_binders 1 #>> hd)
               val T' = before_Ts ---> dest_n_tuple_type k tuple_T ---> rest_T
             in do_const (s', T') end
         end
       else if String.isPrefix unrolled_prefix s then
         let val t = Const (original_name s, range_type T) in
           (lambda (Free (iter_var_prefix, nat_T)) t,
            format_type default_format
                        (lookup_format thy def_tables formats t) T)
         end
       else if String.isPrefix base_prefix s then
         (Const (base_name, T --> T) $ Const (unprefix base_prefix s, T),
          format_type default_format default_format T)
       else if String.isPrefix step_prefix s then
         (Const (step_name, T --> T) $ Const (unprefix step_prefix s, T),
          format_type default_format default_format T)
       else if String.isPrefix quot_normal_prefix s then
         let val t = Const (nitpick_prefix ^ "quotient normal form", T) in
           (t, format_term_type thy def_tables formats t)
         end
       else if String.isPrefix skolem_prefix s then
         let
           val ss = the (AList.lookup (op =) (!skolems) s)
           val (Ts, Ts') = chop (length ss) (binder_types T)
           val frees = map Free (ss ~~ Ts)
           val s' = original_name s
         in
           (fold lambda frees (Const (s', Ts' ---> T)),
            format_type default_format
                        (lookup_format thy def_tables formats (Const x)) T)
         end
       else if String.isPrefix eval_prefix s then
         let
           val t = nth evals (the (Int.fromString (unprefix eval_prefix s)))
         in (t, format_term_type thy def_tables formats t) end
       else
         (* The selector case can occur in conjunction with fractional types.
            It's not pretty. *)
         let val t = Const (s |> not (is_sel s) ? original_name, T) in
           (t, format_term_type thy def_tables formats t)
         end)
      |>> map_types uniterize_unarize_unbox_etc_type
      |>> shorten_names_in_term |>> Term.map_abs_vars shortest_name
  in do_const end

fun assign_operator_for_const (s, T) =
  if String.isPrefix ubfp_prefix s then
    if is_fun_type T then xsym "\<subseteq>" "<=" ()
    else xsym "\<le>" "<=" ()
  else if String.isPrefix lbfp_prefix s then
    if is_fun_type T then xsym "\<supseteq>" ">=" ()
    else xsym "\<ge>" ">=" ()
  else if original_name s <> s then
    assign_operator_for_const (strip_first_name_sep s |> snd, T)
  else
    "="

(** Model reconstruction **)

fun unfold_outer_the_binders (t as Const (@{const_name The}, _)
                                   $ Abs (s, T, Const (@{const_name HOL.eq}, _)
                                                $ Bound 0 $ t')) =
    betapply (Abs (s, T, t'), t) |> unfold_outer_the_binders
  | unfold_outer_the_binders t = t
fun bisimilar_values _ 0 _ = true
  | bisimilar_values coTs max_depth (t1, t2) =
    let val T = fastype_of t1 in
      if exists_subtype (member (op =) coTs) T then
        let
          val ((head1, args1), (head2, args2)) =
            pairself (strip_comb o unfold_outer_the_binders) (t1, t2)
          val max_depth = max_depth - (if member (op =) coTs T then 1 else 0)
        in
          head1 = head2 andalso
          forall (bisimilar_values coTs max_depth) (args1 ~~ args2)
        end
      else
        t1 = t2
    end

fun reconstruct_hol_model {show_datatypes, show_skolems, show_consts}
        ({hol_ctxt = {thy, ctxt, max_bisim_depth, boxes, stds, wfs, user_axioms,
                      debug, whacks, binary_ints, destroy_constrs, specialize,
                      star_linear_preds, total_consts, needs, tac_timeout,
                      evals, case_names, def_tables, nondef_table, nondefs,
                      simp_table, psimp_table, choice_spec_table, intro_table,
                      ground_thm_table, ersatz_table, skolems, special_funs,
                      unrolled_preds, wf_cache, constr_cache}, binarize,
                      card_assigns, bits, bisim_depth, datatypes, ofs} : scope)
        formats atomss real_frees pseudo_frees free_names sel_names nonsel_names
        rel_table bounds =
  let
    val pool = Unsynchronized.ref []
    val (wacky_names as (_, base_step_names), ctxt) =
      add_wacky_syntax ctxt
    val hol_ctxt =
      {thy = thy, ctxt = ctxt, max_bisim_depth = max_bisim_depth, boxes = boxes,
       stds = stds, wfs = wfs, user_axioms = user_axioms, debug = debug,
       whacks = whacks, binary_ints = binary_ints,
       destroy_constrs = destroy_constrs, specialize = specialize,
       star_linear_preds = star_linear_preds, total_consts = total_consts,
       needs = needs, tac_timeout = tac_timeout, evals = evals,
       case_names = case_names, def_tables = def_tables,
       nondef_table = nondef_table, nondefs = nondefs, simp_table = simp_table,
       psimp_table = psimp_table, choice_spec_table = choice_spec_table,
       intro_table = intro_table, ground_thm_table = ground_thm_table,
       ersatz_table = ersatz_table, skolems = skolems,
       special_funs = special_funs, unrolled_preds = unrolled_preds,
       wf_cache = wf_cache, constr_cache = constr_cache}
    val scope =
      {hol_ctxt = hol_ctxt, binarize = binarize, card_assigns = card_assigns,
       bits = bits, bisim_depth = bisim_depth, datatypes = datatypes, ofs = ofs}
    fun term_for_rep maybe_opt unfold =
      reconstruct_term maybe_opt unfold pool wacky_names scope atomss
                       sel_names rel_table bounds
    val all_values =
      all_values_of_type pool wacky_names scope atomss sel_names rel_table
                         bounds
    fun is_codatatype_wellformed (cos : datatype_spec list)
                                 ({typ, card, ...} : datatype_spec) =
      let
        val ts = all_values card typ
        val max_depth = Integer.sum (map #card cos)
      in
        forall (not o bisimilar_values (map #typ cos) max_depth)
               (all_distinct_unordered_pairs_of ts)
      end
    fun pretty_for_assign name =
      let
        val (oper, (t1, T'), T) =
          case name of
            FreeName (s, T, _) =>
            let val t = Free (s, uniterize_unarize_unbox_etc_type T) in
              ("=", (t, format_term_type thy def_tables formats t), T)
            end
          | ConstName (s, T, _) =>
            (assign_operator_for_const (s, T),
             user_friendly_const hol_ctxt base_step_names formats (s, T), T)
          | _ => raise NUT ("Nitpick_Model.reconstruct_hol_model.\
                            \pretty_for_assign", [name])
        val t2 = if rep_of name = Any then
                   Const (@{const_name undefined}, T')
                 else
                   tuple_list_for_name rel_table bounds name
                   |> term_for_rep (not (is_fully_representable_set name)) false
                                   T T' (rep_of name)
      in
        Pretty.block (Pretty.breaks
            [Syntax.pretty_term (set_show_all_types ctxt) t1,
             Pretty.str oper, Syntax.pretty_term ctxt t2])
      end
    fun pretty_for_datatype ({typ, card, complete, ...} : datatype_spec) =
      Pretty.block (Pretty.breaks
          (pretty_for_type ctxt typ ::
           (case typ of
              Type (@{type_name fun_box}, _) => [Pretty.str "[boxed]"]
            | Type (@{type_name pair_box}, _) => [Pretty.str "[boxed]"]
            | _ => []) @
           [Pretty.str "=",
            Pretty.enum "," "{" "}"
                (map (Syntax.pretty_term ctxt) (all_values card typ) @
                 (if fun_from_pair complete false then []
                  else [Pretty.str (unrep ())]))]))
    fun integer_datatype T =
      [{typ = T, card = card_of_type card_assigns T, co = false,
        standard = true, self_rec = true, complete = (false, false),
        concrete = (true, true), deep = true, constrs = []}]
      handle TYPE ("Nitpick_HOL.card_of_type", _, _) => []
    val (codatatypes, datatypes) =
      datatypes |> filter #deep |> List.partition #co
                ||> append (integer_datatype int_T
                            |> is_standard_datatype thy stds nat_T
                               ? append (integer_datatype nat_T))
    val block_of_datatypes =
      if show_datatypes andalso not (null datatypes) then
        [Pretty.big_list ("Datatype" ^ plural_s_for_list datatypes ^ ":")
                         (map pretty_for_datatype datatypes)]
      else
        []
    val block_of_codatatypes =
      if show_datatypes andalso not (null codatatypes) then
        [Pretty.big_list ("Codatatype" ^ plural_s_for_list codatatypes ^ ":")
                         (map pretty_for_datatype codatatypes)]
      else
        []
    fun block_of_names show title names =
      if show andalso not (null names) then
        Pretty.str (title ^ plural_s_for_list names ^ ":")
        :: map (Pretty.indent indent_size o pretty_for_assign)
               (sort_wrt (original_name o nickname_of) names)
      else
        []
    fun free_name_for_term keep_all (x as (s, T)) =
      case filter (curry (op =) x
                   o pairf nickname_of (uniterize_unarize_unbox_etc_type
                                        o type_of)) free_names of
        [name] => SOME name
      | [] => if keep_all then SOME (FreeName (s, T, Any)) else NONE
      | _ => raise TERM ("Nitpick_Model.reconstruct_hol_model.\
                         \free_name_for_term", [Const x])
    val (skolem_names, nonskolem_nonsel_names) =
      List.partition is_skolem_name nonsel_names
    val (eval_names, noneval_nonskolem_nonsel_names) =
      List.partition (String.isPrefix eval_prefix o nickname_of)
                     nonskolem_nonsel_names
      ||> filter_out (member (op =) [@{const_name bisim},
                                     @{const_name bisim_iterator_max}]
                      o nickname_of)
      ||> append (map_filter (free_name_for_term false) pseudo_frees)
    val real_free_names = map_filter (free_name_for_term true) real_frees
    val chunks = block_of_names true "Free variable" real_free_names @
                 block_of_names show_skolems "Skolem constant" skolem_names @
                 block_of_names true "Evaluated term" eval_names @
                 block_of_datatypes @ block_of_codatatypes @
                 block_of_names show_consts "Constant"
                                noneval_nonskolem_nonsel_names
  in
    (Pretty.chunks (if null chunks then [Pretty.str "Empty assignment"]
                    else chunks),
     bisim_depth >= 0 orelse
     forall (is_codatatype_wellformed codatatypes) codatatypes)
  end

fun term_for_name pool scope atomss sel_names rel_table bounds name =
  let val T = type_of name in
    tuple_list_for_name rel_table bounds name
    |> reconstruct_term (not (is_fully_representable_set name)) false pool
                        (("", ""), ("", "")) scope atomss sel_names rel_table
                        bounds T T (rep_of name)
  end

fun prove_hol_model (scope as {hol_ctxt = {thy, ctxt, debug, ...},
                               card_assigns, ...})
                    auto_timeout free_names sel_names rel_table bounds prop =
  let
    val pool = Unsynchronized.ref []
    val atomss = [(NONE, [])]
    fun free_type_assm (T, k) =
      let
        fun atom j = nth_atom thy atomss pool true T j
        fun equation_for_atom j = HOLogic.eq_const T $ Bound 0 $ atom j
        val eqs = map equation_for_atom (index_seq 0 k)
        val compreh_assm =
          Const (@{const_name All}, (T --> bool_T) --> bool_T)
              $ Abs ("x", T, foldl1 HOLogic.mk_disj eqs)
        val distinct_assm = distinctness_formula T (map atom (index_seq 0 k))
      in s_conj (compreh_assm, distinct_assm) end
    fun free_name_assm name =
      HOLogic.mk_eq (Free (nickname_of name, type_of name),
                     term_for_name pool scope atomss sel_names rel_table bounds
                                   name)
    val freeT_assms = map free_type_assm (filter (is_TFree o fst) card_assigns)
    val model_assms = map free_name_assm free_names
    val assm = foldr1 s_conj (freeT_assms @ model_assms)
    fun try_out negate =
      let
        val concl = (negate ? curry (op $) @{const Not})
                    (Object_Logic.atomize_term thy prop)
        val prop = HOLogic.mk_Trueprop (HOLogic.mk_imp (assm, concl))
                   |> map_types (map_type_tfree
                                     (fn (s, []) => TFree (s, HOLogic.typeS)
                                       | x => TFree x))
       val _ = if debug then
                 Output.urgent_message ((if negate then "Genuineness" else "Spuriousness") ^
                           " goal: " ^ Syntax.string_of_term ctxt prop ^ ".")
               else
                 ()
        val goal = prop |> cterm_of thy |> Goal.init
      in
        (goal |> SINGLE (DETERM_TIMEOUT auto_timeout (auto_tac ctxt))
              |> the |> Goal.finish ctxt; true)
        handle THM _ => false
             | TimeLimit.TimeOut => false
      end
  in
    if try_out false then SOME true
    else if try_out true then SOME false
    else NONE
  end

end;
