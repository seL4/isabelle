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

  type params = {
    show_skolems: bool,
    show_datatypes: bool,
    show_consts: bool}
  type term_postprocessor = Proof.context -> typ -> term -> term

  structure NameTable : TABLE

  val register_term_postprocessor :
    typ -> term_postprocessor -> theory -> theory
  val unregister_term_postprocessor : typ -> theory -> theory
  val tuple_list_for_name :
    nut NameTable.table -> Kodkod.raw_bound list -> nut -> int list list
  val reconstruct_hol_model :
    params -> scope -> (term option * int list) list -> styp list -> nut list
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

type params = {
  show_skolems: bool,
  show_datatypes: bool,
  show_consts: bool}

type term_postprocessor = Proof.context -> typ -> term -> term

structure Data = Theory_Data(
  type T = (typ * term_postprocessor) list
  val empty = []
  val extend = I
  fun merge (ps1, ps2) = AList.merge (op =) (K true) (ps1, ps2))

val unknown = "?"
val unrep = "\<dots>"
val maybe_mixfix = "_\<^sup>?"
val base_mixfix = "_\<^bsub>base\<^esub>"
val step_mixfix = "_\<^bsub>step\<^esub>"
val abs_mixfix = "\<guillemotleft>_\<guillemotright>"
val cyclic_co_val_name = "\<omega>"
val cyclic_const_prefix = "\<xi>"
val cyclic_type_name = nitpick_prefix ^ cyclic_const_prefix
val opt_flag = nitpick_prefix ^ "opt"
val non_opt_flag = nitpick_prefix ^ "non_opt"

type atom_pool = ((string * int) * int list) list

(* atom_pool Unsynchronized.ref -> string -> int -> int -> string *)
fun nth_atom_suffix pool s j k =
  (case AList.lookup (op =) (!pool) (s, k) of
     SOME js =>
     (case find_index (curry (op =) j) js of
        ~1 => (Unsynchronized.change pool (cons ((s, k), j :: js));
               length js + 1)
      | n => length js - n)
   | NONE => (Unsynchronized.change pool (cons ((s, k), [j])); 1))
  |> nat_subscript
  |> (s <> "" andalso Symbol.is_ascii_digit (List.last (explode s)))
     ? prefix "\<^isub>,"
(* atom_pool Unsynchronized.ref -> string -> typ -> int -> int -> string *)
fun nth_atom_name pool prefix (Type (s, _)) j k =
    let val s' = shortest_name s in
      prefix ^ (if String.isPrefix "\\" s' then s' else substring (s', 0, 1)) ^
      nth_atom_suffix pool s j k
    end
  | nth_atom_name pool prefix (TFree (s, _)) j k =
    prefix ^ perhaps (try (unprefix "'")) s ^ nth_atom_suffix pool s j k
  | nth_atom_name _ _ T _ _ =
    raise TYPE ("Nitpick_Model.nth_atom_name", [T], [])
(* atom_pool Unsynchronized.ref -> bool -> typ -> int -> int -> term *)
fun nth_atom pool for_auto T j k =
  if for_auto then
    Free (nth_atom_name pool (hd (space_explode "." nitpick_prefix)) T j k, T)
  else
    Const (nth_atom_name pool "" T j k, T)

(* term -> real *)
fun extract_real_number (Const (@{const_name divide}, _) $ t1 $ t2) =
    real (snd (HOLogic.dest_number t1)) / real (snd (HOLogic.dest_number t2))
  | extract_real_number t = real (snd (HOLogic.dest_number t))
(* term * term -> order *)
fun nice_term_ord (Abs (_, _, t1), Abs (_, _, t2)) = nice_term_ord (t1, t2)
  | nice_term_ord tp = Real.compare (pairself extract_real_number tp)
    handle TERM ("dest_number", _) =>
           case tp of
             (t11 $ t12, t21 $ t22) =>
             (case nice_term_ord (t11, t21) of
                EQUAL => nice_term_ord (t12, t22)
              | ord => ord)
           | _ => Term_Ord.fast_term_ord tp

(* typ -> term_postprocessor -> theory -> theory *)
fun register_term_postprocessor T p = Data.map (cons (T, p))
(* typ -> theory -> theory *)
fun unregister_term_postprocessor T = Data.map (AList.delete (op =) T)

(* nut NameTable.table -> KK.raw_bound list -> nut -> int list list *)
fun tuple_list_for_name rel_table bounds name =
  the (AList.lookup (op =) bounds (the_rel rel_table name)) handle NUT _ => [[]]

(* term -> term *)
fun unarize_unbox_etc_term (Const (@{const_name FinFun}, _) $ t1) =
    unarize_unbox_etc_term t1
  | unarize_unbox_etc_term (Const (@{const_name FunBox}, _) $ t1) =
    unarize_unbox_etc_term t1
  | unarize_unbox_etc_term
        (Const (@{const_name PairBox},
                Type (@{type_name fun}, [T1, Type (@{type_name fun}, [T2, _])]))
         $ t1 $ t2) =
    let val Ts = map uniterize_unarize_unbox_etc_type [T1, T2] in
      Const (@{const_name Pair}, Ts ---> Type (@{type_name "*"}, Ts))
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

(* typ -> typ -> (typ * typ) * (typ * typ) *)
fun factor_out_types (T1 as Type (@{type_name "*"}, [T11, T12]))
                     (T2 as Type (@{type_name "*"}, [T21, T22])) =
    let val (n1, n2) = pairself num_factors_in_type (T11, T21) in
      if n1 = n2 then
        let
          val ((T11', opt_T12'), (T21', opt_T22')) = factor_out_types T12 T22
        in
          ((Type (@{type_name "*"}, [T11, T11']), opt_T12'),
           (Type (@{type_name "*"}, [T21, T21']), opt_T22'))
        end
      else if n1 < n2 then
        case factor_out_types T1 T21 of
          (p1, (T21', NONE)) => (p1, (T21', SOME T22))
        | (p1, (T21', SOME T22')) =>
          (p1, (T21', SOME (Type (@{type_name "*"}, [T22', T22]))))
      else
        swap (factor_out_types T2 T1)
    end
  | factor_out_types (Type (@{type_name "*"}, [T11, T12])) T2 =
    ((T11, SOME T12), (T2, NONE))
  | factor_out_types T1 (Type (@{type_name "*"}, [T21, T22])) =
    ((T1, NONE), (T21, SOME T22))
  | factor_out_types T1 T2 = ((T1, NONE), (T2, NONE))

(* bool -> typ -> typ -> (term * term) list -> term *)
fun make_plain_fun maybe_opt T1 T2 =
  let
    (* typ -> typ -> (term * term) list -> term *)
    fun aux T1 T2 [] =
        Const (if maybe_opt then opt_flag else non_opt_flag, T1 --> T2)
      | aux T1 T2 ((t1, t2) :: ps) =
        Const (@{const_name fun_upd}, (T1 --> T2) --> T1 --> T2 --> T1 --> T2)
        $ aux T1 T2 ps $ t1 $ t2
  in aux T1 T2 o rev end
(* term -> bool *)
fun is_plain_fun (Const (s, _)) = (s = opt_flag orelse s = non_opt_flag)
  | is_plain_fun (Const (@{const_name fun_upd}, _) $ t0 $ _ $ _) =
    is_plain_fun t0
  | is_plain_fun _ = false
(* term -> bool * (term list * term list) *)
val dest_plain_fun =
  let
    (* term -> bool * (term list * term list) *)
    fun aux (Const (s, _)) = (s <> non_opt_flag, ([], []))
      | aux (Const (@{const_name fun_upd}, _) $ t0 $ t1 $ t2) =
        let val (s, (ts1, ts2)) = aux t0 in (s, (t1 :: ts1, t2 :: ts2)) end
      | aux t = raise TERM ("Nitpick_Model.dest_plain_fun", [t])
  in apsnd (pairself rev) o aux end

(* typ -> typ -> typ -> term -> term * term *)
fun break_in_two T T1 T2 t =
  let
    val ps = HOLogic.flat_tupleT_paths T
    val cut = length (HOLogic.strip_tupleT T1)
    val (ps1, ps2) = pairself HOLogic.flat_tupleT_paths (T1, T2)
    val (ts1, ts2) = t |> HOLogic.strip_ptuple ps |> chop cut
  in (HOLogic.mk_ptuple ps1 T1 ts1, HOLogic.mk_ptuple ps2 T2 ts2) end
(* typ -> term -> term -> term *)
fun pair_up (Type (@{type_name "*"}, [T1', T2']))
            (t1 as Const (@{const_name Pair},
                          Type (@{type_name fun},
                                [_, Type (@{type_name fun}, [_, T1])]))
             $ t11 $ t12) t2 =
    if T1 = T1' then HOLogic.mk_prod (t1, t2)
    else HOLogic.mk_prod (t11, pair_up T2' t12 t2)
  | pair_up _ t1 t2 = HOLogic.mk_prod (t1, t2)
(* typ -> term -> term list * term list -> (term * term) list*)
fun multi_pair_up T1 t1 (ts2, ts3) = map2 (pair o pair_up T1 t1) ts2 ts3

(* typ -> typ -> typ -> term -> term *)
fun typecast_fun (Type (@{type_name fun}, [T1', T2'])) T1 T2 t =
    let
      (* typ -> typ -> typ -> typ -> term -> term *)
      fun do_curry T1 T1a T1b T2 t =
        let
          val (maybe_opt, ps) = dest_plain_fun t
          val ps =
            ps |>> map (break_in_two T1 T1a T1b)
               |> uncurry (map2 (fn (t1a, t1b) => fn t2 => (t1a, (t1b, t2))))
               |> AList.coalesce (op =)
               |> map (apsnd (make_plain_fun maybe_opt T1b T2))
        in make_plain_fun maybe_opt T1a (T1b --> T2) ps end
      (* typ -> typ -> term -> term *)
      and do_uncurry T1 T2 t =
        let
          val (maybe_opt, tsp) = dest_plain_fun t
          val ps =
            tsp |> op ~~
                |> maps (fn (t1, t2) =>
                            multi_pair_up T1 t1 (snd (dest_plain_fun t2)))
        in make_plain_fun maybe_opt T1 T2 ps end
      (* typ -> typ -> typ -> typ -> term -> term *)
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
      (* typ -> typ -> term -> term *)
      and do_term (Type (@{type_name fun}, [T1', T2']))
                  (Type (@{type_name fun}, [T1, T2])) t =
          do_fun T1' T2' T1 T2 t
        | do_term (T' as Type (@{type_name "*"}, Ts' as [T1', T2']))
                  (Type (@{type_name "*"}, [T1, T2]))
                  (Const (@{const_name Pair}, _) $ t1 $ t2) =
          Const (@{const_name Pair}, Ts' ---> T')
          $ do_term T1' T1 t1 $ do_term T2' T2 t2
        | do_term T' T t =
          if T = T' then t
          else raise TYPE ("Nitpick_Model.typecast_fun.do_term", [T, T'], [])
    in if T1' = T1 andalso T2' = T2 then t else do_fun T1' T2' T1 T2 t end
  | typecast_fun T' _ _ _ =
    raise TYPE ("Nitpick_Model.typecast_fun", [T'], [])

(* term -> string *)
fun truth_const_sort_key @{const True} = "0"
  | truth_const_sort_key @{const False} = "2"
  | truth_const_sort_key _ = "1"

(* typ -> term list -> term *)
fun mk_tuple (Type (@{type_name "*"}, [T1, T2])) ts =
    HOLogic.mk_prod (mk_tuple T1 ts,
        mk_tuple T2 (List.drop (ts, length (HOLogic.flatten_tupleT T1))))
  | mk_tuple _ (t :: _) = t
  | mk_tuple T [] = raise TYPE ("Nitpick_Model.mk_tuple", [T], [])

(* theory -> typ * typ -> bool *)
fun varified_type_match thy (candid_T, pat_T) =
  strict_type_match thy (candid_T, Logic.varifyT pat_T)
(* Proof.context -> typ -> term -> term *)
fun postprocess_term ctxt T =
  let val thy = ProofContext.theory_of ctxt in
    if null (Data.get thy) then
      I
    else
      (T |> AList.lookup (varified_type_match thy) (Data.get thy)
         |> the_default (K (K I))) ctxt T
  end

(* bool -> atom_pool -> (string * string) * (string * string) -> scope
   -> nut list -> nut list -> nut list -> nut NameTable.table
   -> KK.raw_bound list -> typ -> typ -> rep -> int list list -> term *)
fun reconstruct_term unfold pool ((maybe_name, abs_name), _)
        ({hol_ctxt as {ctxt, thy, stds, ...}, binarize, card_assigns, bits,
          datatypes, ofs, ...} : scope) sel_names rel_table bounds =
  let
    val for_auto = (maybe_name = "")
    (* int list list -> int *)
    fun value_of_bits jss =
      let
        val j0 = offset_of_type ofs @{typ unsigned_bit}
        val js = map (Integer.add (~ j0) o the_single) jss
      in
        fold (fn j => Integer.add (reasonable_power 2 j |> j = bits ? op ~))
             js 0
      end
    (* bool -> typ -> typ -> (term * term) list -> term *)
    fun make_set maybe_opt T1 T2 tps =
      let
        val empty_const = Const (@{const_abbrev Set.empty}, T1 --> T2)
        val insert_const = Const (@{const_name insert},
                                  T1 --> (T1 --> T2) --> T1 --> T2)
        (* (term * term) list -> term *)
        fun aux [] =
            if maybe_opt andalso not (is_complete_type datatypes false T1) then
              insert_const $ Const (unrep, T1) $ empty_const
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
    (* bool -> typ -> typ -> typ -> (term * term) list -> term *)
    fun make_map maybe_opt T1 T2 T2' =
      let
        val update_const = Const (@{const_name fun_upd},
                                  (T1 --> T2) --> T1 --> T2 --> T1 --> T2)
        (* (term * term) list -> term *)
        fun aux' [] = Const (@{const_abbrev Map.empty}, T1 --> T2)
          | aux' ((t1, t2) :: ps) =
            (case t2 of
               Const (@{const_name None}, _) => aux' ps
             | _ => update_const $ aux' ps $ t1 $ t2)
        fun aux ps =
          if maybe_opt andalso not (is_complete_type datatypes false T1) then
            update_const $ aux' ps $ Const (unrep, T1)
            $ (Const (@{const_name Some}, T2' --> T2) $ Const (unknown, T2'))
          else
            aux' ps
      in aux end
    (* typ list -> term -> term *)
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
                 Abs ("x", T1, Const (unknown, T2))
               else
                 t
             | t => t
    (* bool -> typ -> typ -> typ -> term list -> term list -> term *)
    fun make_fun maybe_opt T1 T2 T' ts1 ts2 =
      ts1 ~~ ts2 |> sort (nice_term_ord o pairself fst)
                 |> make_plain_fun maybe_opt T1 T2
                 |> unarize_unbox_etc_term
                 |> typecast_fun (uniterize_unarize_unbox_etc_type T')
                                 (uniterize_unarize_unbox_etc_type T1)
                                 (uniterize_unarize_unbox_etc_type T2)
    (* (typ * int) list -> typ -> typ -> int -> term *)
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
      | term_for_atom seen (Type (@{type_name "*"}, [T1, T2])) _ j k =
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
      | term_for_atom _ @{typ unit} _ _ _ = @{const Unity}
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
          NONE => nth_atom pool for_auto T j k
        | SOME {deep = false, ...} => nth_atom pool for_auto T j k
        | SOME {co, standard, constrs, ...} =>
          let
            (* styp -> int list *)
            fun tuples_for_const (s, T) =
              tuple_list_for_name rel_table bounds (ConstName (s, T, Any))
            (* unit -> term *)
            fun cyclic_atom () =
              nth_atom pool for_auto (Type (cyclic_type_name, [])) j k
            fun cyclic_var () = Var ((nth_atom_name pool "" T j k, 0), T)

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
                    map3 (fn Ts =>
                             term_for_rep (constr_s <> @{const_name FinFun})
                                          seen Ts Ts) arg_Ts arg_Rs arg_jsss
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
                          (is_abs_fun thy constr_x orelse
                           constr_s = @{const_name Quot}) then
                    Const (abs_name, constr_T) $ the_single ts
                  else
                    list_comb (Const constr_x, ts)
              in
                if maybe_cyclic then
                  let val var = cyclic_var () in
                    if unfold andalso not standard andalso
                       length seen = 1 andalso
                       exists_subterm (fn Const (s, _) =>
                                          String.isPrefix cyclic_const_prefix s
                                        | t' => t' = var) t then
                      subst_atomic [(var, cyclic_atom ())] t
                    else if exists_subterm (curry (op =) var) t then
                      if co then
                        Const (@{const_name The}, (T --> bool_T) --> T)
                        $ Abs (cyclic_co_val_name, T,
                               Const (@{const_name "op ="}, T --> T --> bool_T)
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
          |> postprocess_term ctxt T
    (* (typ * int) list -> int -> rep -> typ -> typ -> typ -> int list
       -> term *)
    and term_for_vect seen k R T1 T2 T' js =
      make_fun true T1 T2 T'
               (map (fn j => term_for_atom seen T1 T1 j k) (index_seq 0 k))
               (map (term_for_rep true seen T2 T2 R o single)
                    (batch_list (arity_of_rep R) js))
    (* bool -> (typ * int) list -> typ -> typ -> rep -> int list list -> term *)
    and term_for_rep _ seen T T' Unit [[]] = term_for_atom seen T T' 0 1
      | term_for_rep _ seen T T' (R as Atom (k, j0)) [[j]] =
        if j >= j0 andalso j < j0 + k then term_for_atom seen T T' (j - j0) k
        else raise REP ("Nitpick_Model.reconstruct_term.term_for_rep", [R])
      | term_for_rep _ seen (Type (@{type_name "*"}, [T1, T2])) _
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
      | term_for_rep _ seen (Type (@{type_name fun}, [T1, T2])) T'
                     (Func (R1, Formula Neut)) jss =
        let
          val jss1 = all_combinations_for_rep R1
          val ts1 = map (term_for_rep true seen T1 T1 R1 o single) jss1
          val ts2 =
            map (fn js => term_for_rep true seen T2 T2 (Atom (2, 0))
                                       [[int_from_bool (member (op =) jss js)]])
                jss1
        in make_fun false T1 T2 T' ts1 ts2 end
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
                   Refute.string_of_typ T ^ " " ^ string_for_rep R ^ " " ^
                   string_of_int (length jss))
  in polish_funs [] o unarize_unbox_etc_term oooo term_for_rep true [] end

(* atom_pool -> scope -> nut list -> nut NameTable.table -> KK.raw_bound list
   -> nut -> term *)
fun term_for_name pool scope sel_names rel_table bounds name =
  let val T = type_of name in
    tuple_list_for_name rel_table bounds name
    |> reconstruct_term false pool (("", ""), ("", "")) scope sel_names
                        rel_table bounds T T (rep_of name)
  end

(* Proof.context -> ((string * string) * (string * string)) * Proof.context *)
fun add_wacky_syntax ctxt =
  let
    (* term -> string *)
    val name_of = fst o dest_Const
    val thy = ProofContext.theory_of ctxt |> Context.reject_draft
    val (maybe_t, thy) =
      Sign.declare_const ((@{binding nitpick_maybe}, @{typ "'a => 'a"}),
                          Mixfix (maybe_mixfix, [1000], 1000)) thy
    val (abs_t, thy) =
      Sign.declare_const ((@{binding nitpick_abs}, @{typ "'a => 'b"}),
                          Mixfix (abs_mixfix, [40], 40)) thy
    val (base_t, thy) =
      Sign.declare_const ((@{binding nitpick_base}, @{typ "'a => 'a"}),
                          Mixfix (base_mixfix, [1000], 1000)) thy
    val (step_t, thy) =
      Sign.declare_const ((@{binding nitpick_step}, @{typ "'a => 'a"}),
                          Mixfix (step_mixfix, [1000], 1000)) thy
  in
    (pairself (pairself name_of) ((maybe_t, abs_t), (base_t, step_t)),
     ProofContext.transfer_syntax thy ctxt)
  end

(* term -> term *)
fun unfold_outer_the_binders (t as Const (@{const_name The}, _)
                                   $ Abs (s, T, Const (@{const_name "op ="}, _)
                                                $ Bound 0 $ t')) =
    betapply (Abs (s, T, t'), t) |> unfold_outer_the_binders
  | unfold_outer_the_binders t = t
(* typ list -> int -> term * term -> bool *)
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

(* params -> scope -> (term option * int list) list -> styp list -> nut list
  -> nut list -> nut list -> nut NameTable.table -> KK.raw_bound list
  -> Pretty.T * bool *)
fun reconstruct_hol_model {show_skolems, show_datatypes, show_consts}
        ({hol_ctxt = {thy, ctxt, max_bisim_depth, boxes, stds, wfs, user_axioms,
                      debug, binary_ints, destroy_constrs, specialize,
                      skolemize, star_linear_preds, uncurry, fast_descrs,
                      tac_timeout, evals, case_names, def_table, nondef_table,
                      user_nondefs, simp_table, psimp_table, intro_table,
                      ground_thm_table, ersatz_table, skolems, special_funs,
                      unrolled_preds, wf_cache, constr_cache},
         binarize, card_assigns, bits, bisim_depth, datatypes, ofs} : scope)
        formats all_frees free_names sel_names nonsel_names rel_table bounds =
  let
    val pool = Unsynchronized.ref []
    val (wacky_names as (_, base_step_names), ctxt) =
      add_wacky_syntax ctxt
    val hol_ctxt =
      {thy = thy, ctxt = ctxt, max_bisim_depth = max_bisim_depth, boxes = boxes,
       stds = stds, wfs = wfs, user_axioms = user_axioms, debug = debug,
       binary_ints = binary_ints, destroy_constrs = destroy_constrs,
       specialize = specialize, skolemize = skolemize,
       star_linear_preds = star_linear_preds, uncurry = uncurry,
       fast_descrs = fast_descrs, tac_timeout = tac_timeout, evals = evals,
       case_names = case_names, def_table = def_table,
       nondef_table = nondef_table, user_nondefs = user_nondefs,
       simp_table = simp_table, psimp_table = psimp_table,
       intro_table = intro_table, ground_thm_table = ground_thm_table,
       ersatz_table = ersatz_table, skolems = skolems,
       special_funs = special_funs, unrolled_preds = unrolled_preds,
       wf_cache = wf_cache, constr_cache = constr_cache}
    val scope = {hol_ctxt = hol_ctxt, binarize = binarize,
                 card_assigns = card_assigns, bits = bits,
                 bisim_depth = bisim_depth, datatypes = datatypes, ofs = ofs}
    (* bool -> typ -> typ -> rep -> int list list -> term *)
    fun term_for_rep unfold =
      reconstruct_term unfold pool wacky_names scope sel_names rel_table bounds
    (* nat -> typ -> nat -> term *)
    fun nth_value_of_type card T n =
      let
        (* bool -> term *)
        fun aux unfold = term_for_rep unfold T T (Atom (card, 0)) [[n]]
      in
        case aux false of
          t as Const (s, _) =>
          if String.isPrefix cyclic_const_prefix s then
            HOLogic.mk_eq (t, aux true)
          else
            t
        | t => t
      end
    (* nat -> typ -> typ list *)
    fun all_values_of_type card T =
      index_seq 0 card |> map (nth_value_of_type card T) |> sort nice_term_ord
    (* dtype_spec list -> dtype_spec -> bool *)
    fun is_codatatype_wellformed (cos : dtype_spec list)
                                 ({typ, card, ...} : dtype_spec) =
      let
        val ts = all_values_of_type card typ
        val max_depth = Integer.sum (map #card cos)
      in
        forall (not o bisimilar_values (map #typ cos) max_depth)
               (all_distinct_unordered_pairs_of ts)
      end
    (* string -> Pretty.T *)
    fun pretty_for_assign name =
      let
        val (oper, (t1, T'), T) =
          case name of
            FreeName (s, T, _) =>
            let val t = Free (s, uniterize_unarize_unbox_etc_type T) in
              ("=", (t, format_term_type thy def_table formats t), T)
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
                   |> term_for_rep false T T' (rep_of name)
      in
        Pretty.block (Pretty.breaks
            [setmp_show_all_types (Syntax.pretty_term ctxt) t1,
             Pretty.str oper, Syntax.pretty_term ctxt t2])
      end
    (* dtype_spec -> Pretty.T *)
    fun pretty_for_datatype ({typ, card, complete, ...} : dtype_spec) =
      Pretty.block (Pretty.breaks
          (Syntax.pretty_typ ctxt (uniterize_unarize_unbox_etc_type typ) ::
           (case typ of
              Type (@{type_name fin_fun}, _) => [Pretty.str "[finite]"]
            | Type (@{type_name fun_box}, _) => [Pretty.str "[boxed]"]
            | Type (@{type_name pair_box}, _) => [Pretty.str "[boxed]"]
            | _ => []) @
           [Pretty.str "=",
            Pretty.enum "," "{" "}"
                (map (Syntax.pretty_term ctxt) (all_values_of_type card typ) @
                 (if fun_from_pair complete false then []
                  else [Pretty.str unrep]))]))
    (* typ -> dtype_spec list *)
    fun integer_datatype T =
      [{typ = T, card = card_of_type card_assigns T, co = false,
        standard = true, complete = (false, false), concrete = (true, true),
        deep = true, constrs = []}]
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
    (* bool -> string -> nut list -> Pretty.T list *)
    fun block_of_names show title names =
      if show andalso not (null names) then
        Pretty.str (title ^ plural_s_for_list names ^ ":")
        :: map (Pretty.indent indent_size o pretty_for_assign)
               (sort_wrt (original_name o nickname_of) names)
      else
        []
    val (skolem_names, nonskolem_nonsel_names) =
      List.partition is_skolem_name nonsel_names
    val (eval_names, noneval_nonskolem_nonsel_names) =
      List.partition (String.isPrefix eval_prefix o nickname_of)
                     nonskolem_nonsel_names
      ||> filter_out (member (op =) [@{const_name bisim},
                                     @{const_name bisim_iterator_max}]
                      o nickname_of)
    val free_names =
      map (fn x as (s, T) =>
              case filter (curry (op =) x
                       o pairf nickname_of
                               (uniterize_unarize_unbox_etc_type o type_of))
                       free_names of
                [name] => name
              | [] => FreeName (s, T, Any)
              | _ => raise TERM ("Nitpick_Model.reconstruct_hol_model",
                                 [Const x])) all_frees
    val chunks = block_of_names true "Free variable" free_names @
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

(* scope -> Time.time option -> nut list -> nut list -> nut NameTable.table
   -> KK.raw_bound list -> term -> bool option *)
fun prove_hol_model (scope as {hol_ctxt = {thy, ctxt, debug, ...},
                               card_assigns, ...})
                    auto_timeout free_names sel_names rel_table bounds prop =
  let
    val pool = Unsynchronized.ref []
    (* typ * int -> term *)
    fun free_type_assm (T, k) =
      let
        (* int -> term *)
        fun atom j = nth_atom pool true T j k
        fun equation_for_atom j = HOLogic.eq_const T $ Bound 0 $ atom j
        val eqs = map equation_for_atom (index_seq 0 k)
        val compreh_assm =
          Const (@{const_name All}, (T --> bool_T) --> bool_T)
              $ Abs ("x", T, foldl1 HOLogic.mk_disj eqs)
        val distinct_assm = distinctness_formula T (map atom (index_seq 0 k))
      in s_conj (compreh_assm, distinct_assm) end
    (* nut -> term *)
    fun free_name_assm name =
      HOLogic.mk_eq (Free (nickname_of name, type_of name),
                     term_for_name pool scope sel_names rel_table bounds name)
    val freeT_assms = map free_type_assm (filter (is_TFree o fst) card_assigns)
    val model_assms = map free_name_assm free_names
    val assm = foldr1 s_conj (freeT_assms @ model_assms)
    (* bool -> bool *)
    fun try_out negate =
      let
        val concl = (negate ? curry (op $) @{const Not})
                    (Object_Logic.atomize_term thy prop)
        val prop = HOLogic.mk_Trueprop (HOLogic.mk_imp (assm, concl))
                   |> map_types (map_type_tfree
                                     (fn (s, []) => TFree (s, HOLogic.typeS)
                                       | x => TFree x))
       val _ = if debug then
                 priority ((if negate then "Genuineness" else "Spuriousness") ^
                           " goal: " ^ Syntax.string_of_term ctxt prop ^ ".")
               else
                 ()
        val goal = prop |> cterm_of thy |> Goal.init
      in
        (goal |> SINGLE (DETERM_TIMEOUT auto_timeout
                                        (auto_tac (clasimpset_of ctxt)))
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
