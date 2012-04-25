(*  Title:      HOL/Tools/Nitpick/nitpick_preproc.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Nitpick's HOL preprocessor.
*)

signature NITPICK_PREPROC =
sig
  type hol_context = Nitpick_HOL.hol_context
  val preprocess_formulas :
    hol_context -> term list -> term
    -> term list * term list * term list * bool * bool * bool
end;

structure Nitpick_Preproc : NITPICK_PREPROC =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Mono

fun is_positive_existential polar quant_s =
  (polar = Pos andalso quant_s = @{const_name Ex}) orelse
  (polar = Neg andalso quant_s <> @{const_name Ex})

val is_descr =
  member (op =) [@{const_name The}, @{const_name Eps}, @{const_name safe_The}]

(** Binary coding of integers **)

(* If a formula contains a numeral whose absolute value is more than this
   threshold, the unary coding is likely not to work well and we prefer the
   binary coding. *)
val binary_int_threshold = 3

val may_use_binary_ints =
  let
    fun aux def (Const (@{const_name "=="}, _) $ t1 $ t2) =
        aux def t1 andalso aux false t2
      | aux def (@{const "==>"} $ t1 $ t2) = aux false t1 andalso aux def t2
      | aux def (Const (@{const_name HOL.eq}, _) $ t1 $ t2) =
        aux def t1 andalso aux false t2
      | aux def (@{const HOL.implies} $ t1 $ t2) = aux false t1 andalso aux def t2
      | aux def (t1 $ t2) = aux def t1 andalso aux def t2
      | aux def (t as Const (s, _)) =
        (not def orelse t <> @{const Suc}) andalso
        not (member (op =) [@{const_name Abs_Frac}, @{const_name Rep_Frac},
                            @{const_name nat_gcd}, @{const_name nat_lcm},
                            @{const_name Frac}, @{const_name norm_frac}] s)
      | aux def (Abs (_, _, t')) = aux def t'
      | aux _ _ = true
  in aux end
val should_use_binary_ints =
  let
    fun aux (t1 $ t2) = aux t1 orelse aux t2
      | aux (Const (s, T)) =
        ((s = @{const_name times} orelse s = @{const_name div}) andalso
         is_integer_type (body_type T)) orelse
        (String.isPrefix numeral_prefix s andalso
         let val n = the (Int.fromString (unprefix numeral_prefix s)) in
           n < ~ binary_int_threshold orelse n > binary_int_threshold
         end)
      | aux (Abs (_, _, t')) = aux t'
      | aux _ = false
  in aux end

(** Uncurrying **)

fun add_to_uncurry_table ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    fun aux (t1 $ t2) args table =
        let val table = aux t2 [] table in aux t1 (t2 :: args) table end
      | aux (Abs (_, _, t')) _ table = aux t' [] table
      | aux (t as Const (x as (s, _))) args table =
        if is_built_in_const thy [(NONE, true)] x orelse
           is_constr_like ctxt x orelse
           is_sel s orelse s = @{const_name Sigma} then
          table
        else
          Termtab.map_default (t, 65536) (Integer.min (length args)) table
      | aux _ _ table = table
  in aux t [] end

fun uncurry_prefix_for k j =
  uncurry_prefix ^ string_of_int k ^ "@" ^ string_of_int j ^ name_sep

fun uncurry_term table t =
  let
    fun aux (t1 $ t2) args = aux t1 (aux t2 [] :: args)
      | aux (Abs (s, T, t')) args = s_betapplys [] (Abs (s, T, aux t' []), args)
      | aux (t as Const (s, T)) args =
        (case Termtab.lookup table t of
           SOME n =>
           if n >= 2 then
             let
               val arg_Ts = strip_n_binders n T |> fst
               val j =
                 if is_iterator_type (hd arg_Ts) then
                   1
                 else case find_index (not_equal bool_T) arg_Ts of
                   ~1 => n
                 | j => j
               val ((before_args, tuple_args), after_args) =
                 args |> chop n |>> chop j
               val ((before_arg_Ts, tuple_arg_Ts), rest_T) =
                 T |> strip_n_binders n |>> chop j
               val tuple_T = HOLogic.mk_tupleT tuple_arg_Ts
             in
               if n - j < 2 then
                 s_betapplys [] (t, args)
               else
                 s_betapplys []
                     (Const (uncurry_prefix_for (n - j) j ^ s,
                             before_arg_Ts ---> tuple_T --> rest_T),
                      before_args @ [mk_flat_tuple tuple_T tuple_args] @
                      after_args)
             end
           else
             s_betapplys [] (t, args)
         | NONE => s_betapplys [] (t, args))
      | aux t args = s_betapplys [] (t, args)
  in aux t [] end

(** Boxing **)

fun box_fun_and_pair_in_term (hol_ctxt as {ctxt, thy, stds, ...}) def orig_t =
  let
    fun box_relational_operator_type (Type (@{type_name fun}, Ts)) =
        Type (@{type_name fun}, map box_relational_operator_type Ts)
      | box_relational_operator_type (Type (@{type_name prod}, Ts)) =
        Type (@{type_name prod}, map (box_type hol_ctxt InPair) Ts)
      | box_relational_operator_type T = T
    fun add_boxed_types_for_var (z as (_, T)) (T', t') =
      case t' of
        Var z' => z' = z ? insert (op =) T'
      | Const (@{const_name Pair}, _) $ t1 $ t2 =>
        (case T' of
           Type (_, [T1, T2]) =>
           fold (add_boxed_types_for_var z) [(T1, t1), (T2, t2)]
         | _ => raise TYPE ("Nitpick_Preproc.box_fun_and_pair_in_term.\
                            \add_boxed_types_for_var", [T'], []))
      | _ => exists_subterm (curry (op =) (Var z)) t' ? insert (op =) T
    fun box_var_in_def new_Ts old_Ts t (z as (_, T)) =
      case t of
        @{const Trueprop} $ t1 => box_var_in_def new_Ts old_Ts t1 z
      | Const (s0, _) $ t1 $ _ =>
        if s0 = @{const_name "=="} orelse s0 = @{const_name HOL.eq} then
          let
            val (t', args) = strip_comb t1
            val T' = fastype_of1 (new_Ts, do_term new_Ts old_Ts Neut t')
          in
            case fold (add_boxed_types_for_var z)
                      (fst (strip_n_binders (length args) T') ~~ args) [] of
              [T''] => T''
            | _ => T
          end
        else
          T
      | _ => T
    and do_quantifier new_Ts old_Ts polar quant_s quant_T abs_s abs_T t =
      let
        val abs_T' =
          if polar = Neut orelse is_positive_existential polar quant_s then
            box_type hol_ctxt InFunLHS abs_T
          else
            abs_T
        val body_T = body_type quant_T
      in
        Const (quant_s, (abs_T' --> body_T) --> body_T)
        $ Abs (abs_s, abs_T',
               t |> do_term (abs_T' :: new_Ts) (abs_T :: old_Ts) polar)
      end
    and do_equals new_Ts old_Ts s0 T0 t1 t2 =
      let
        val (t1, t2) = pairself (do_term new_Ts old_Ts Neut) (t1, t2)
        val (T1, T2) = pairself (curry fastype_of1 new_Ts) (t1, t2)
        val T = if def then T1
                else [T1, T2] |> sort (int_ord o pairself size_of_typ) |> hd
      in
        list_comb (Const (s0, T --> T --> body_type T0),
                   map2 (coerce_term hol_ctxt new_Ts T) [T1, T2] [t1, t2])
      end
    and do_descr s T =
      let val T1 = box_type hol_ctxt InFunLHS (range_type T) in
        Const (s, (T1 --> bool_T) --> T1)
      end
    and do_term new_Ts old_Ts polar t =
      case t of
        Const (s0 as @{const_name all}, T0) $ Abs (s1, T1, t1) =>
        do_quantifier new_Ts old_Ts polar s0 T0 s1 T1 t1
      | Const (s0 as @{const_name "=="}, T0) $ t1 $ t2 =>
        do_equals new_Ts old_Ts s0 T0 t1 t2
      | @{const "==>"} $ t1 $ t2 =>
        @{const "==>"} $ do_term new_Ts old_Ts (flip_polarity polar) t1
        $ do_term new_Ts old_Ts polar t2
      | @{const Pure.conjunction} $ t1 $ t2 =>
        @{const Pure.conjunction} $ do_term new_Ts old_Ts polar t1
        $ do_term new_Ts old_Ts polar t2
      | @{const Trueprop} $ t1 =>
        @{const Trueprop} $ do_term new_Ts old_Ts polar t1
      | @{const Not} $ t1 =>
        @{const Not} $ do_term new_Ts old_Ts (flip_polarity polar) t1
      | Const (s0 as @{const_name All}, T0) $ Abs (s1, T1, t1) =>
        do_quantifier new_Ts old_Ts polar s0 T0 s1 T1 t1
      | Const (s0 as @{const_name Ex}, T0) $ Abs (s1, T1, t1) =>
        do_quantifier new_Ts old_Ts polar s0 T0 s1 T1 t1
      | Const (s0 as @{const_name HOL.eq}, T0) $ t1 $ t2 =>
        do_equals new_Ts old_Ts s0 T0 t1 t2
      | @{const HOL.conj} $ t1 $ t2 =>
        @{const HOL.conj} $ do_term new_Ts old_Ts polar t1
        $ do_term new_Ts old_Ts polar t2
      | @{const HOL.disj} $ t1 $ t2 =>
        @{const HOL.disj} $ do_term new_Ts old_Ts polar t1
        $ do_term new_Ts old_Ts polar t2
      | @{const HOL.implies} $ t1 $ t2 =>
        @{const HOL.implies} $ do_term new_Ts old_Ts (flip_polarity polar) t1
        $ do_term new_Ts old_Ts polar t2
      | Const (x as (s, T)) =>
        if is_descr s then
          do_descr s T
        else
          Const (s, if s = @{const_name converse} orelse
                       s = @{const_name trancl} then
                      box_relational_operator_type T
                    else if String.isPrefix quot_normal_prefix s then
                      let val T' = box_type hol_ctxt InFunLHS (domain_type T) in
                        T' --> T'
                      end
                    else if is_built_in_const thy stds x orelse
                            s = @{const_name Sigma} then
                      T
                    else if is_constr_like ctxt x then
                      box_type hol_ctxt InConstr T
                    else if is_sel s orelse is_rep_fun ctxt x then
                      box_type hol_ctxt InSel T
                    else
                      box_type hol_ctxt InExpr T)
      | t1 $ Abs (s, T, t2') =>
        let
          val t1 = do_term new_Ts old_Ts Neut t1
          val T1 = fastype_of1 (new_Ts, t1)
          val (s1, Ts1) = dest_Type T1
          val T' = hd (snd (dest_Type (hd Ts1)))
          val t2 = Abs (s, T', do_term (T' :: new_Ts) (T :: old_Ts) Neut t2')
          val T2 = fastype_of1 (new_Ts, t2)
          val t2 = coerce_term hol_ctxt new_Ts (hd Ts1) T2 t2
        in
          s_betapply new_Ts (if s1 = @{type_name fun} then
                               t1
                             else
                               select_nth_constr_arg ctxt stds
                                   (@{const_name FunBox},
                                    Type (@{type_name fun}, Ts1) --> T1) t1 0
                                   (Type (@{type_name fun}, Ts1)), t2)
        end
      | t1 $ t2 =>
        let
          val t1 = do_term new_Ts old_Ts Neut t1
          val T1 = fastype_of1 (new_Ts, t1)
          val (s1, Ts1) = dest_Type T1
          val t2 = do_term new_Ts old_Ts Neut t2
          val T2 = fastype_of1 (new_Ts, t2)
          val t2 = coerce_term hol_ctxt new_Ts (hd Ts1) T2 t2
        in
          s_betapply new_Ts (if s1 = @{type_name fun} then
                               t1
                             else
                               select_nth_constr_arg ctxt stds
                                   (@{const_name FunBox},
                                    Type (@{type_name fun}, Ts1) --> T1) t1 0
                                   (Type (@{type_name fun}, Ts1)), t2)
        end
      | Free (s, T) => Free (s, box_type hol_ctxt InExpr T)
      | Var (z as (x, T)) =>
        Var (x, if def then box_var_in_def new_Ts old_Ts orig_t z
                else box_type hol_ctxt InExpr T)
      | Bound _ => t
      | Abs (s, T, t') =>
        Abs (s, T, do_term (T :: new_Ts) (T :: old_Ts) Neut t')
  in do_term [] [] Pos orig_t end

(** Destruction of set membership and comprehensions **)

fun destroy_set_Collect (Const (@{const_name Set.member}, _) $ t1
                         $ (Const (@{const_name Collect}, _) $ t2)) =
    destroy_set_Collect (t2 $ t1)
  | destroy_set_Collect (t1 $ t2) =
    destroy_set_Collect t1 $ destroy_set_Collect t2
  | destroy_set_Collect (Abs (s, T, t')) = Abs (s, T, destroy_set_Collect t')
  | destroy_set_Collect t = t

(** Destruction of constructors **)

val val_var_prefix = nitpick_prefix ^ "v"

fun fresh_value_var Ts k n j t =
  Var ((val_var_prefix ^ nat_subscript (n - j), k), fastype_of1 (Ts, t))

fun has_heavy_bounds_or_vars Ts t =
  let
    fun aux [] = false
      | aux [T] = is_fun_or_set_type T orelse is_pair_type T
      | aux _ = true
  in aux (map snd (Term.add_vars t []) @ map (nth Ts) (loose_bnos t)) end

fun pull_out_constr_comb ({ctxt, stds, ...} : hol_context) Ts relax k level t
                         args seen =
  let val t_comb = list_comb (t, args) in
    case t of
      Const x =>
      if not relax andalso is_constr ctxt stds x andalso
         not (is_fun_or_set_type (fastype_of1 (Ts, t_comb))) andalso
         has_heavy_bounds_or_vars Ts t_comb andalso
         not (loose_bvar (t_comb, level)) then
        let
          val (j, seen) = case find_index (curry (op =) t_comb) seen of
                            ~1 => (0, t_comb :: seen)
                          | j => (j, seen)
        in (fresh_value_var Ts k (length seen) j t_comb, seen) end
      else
        (t_comb, seen)
    | _ => (t_comb, seen)
  end

fun equations_for_pulled_out_constrs mk_eq Ts k seen =
  let val n = length seen in
    map2 (fn j => fn t => mk_eq (fresh_value_var Ts k n j t, t))
         (index_seq 0 n) seen
  end

fun pull_out_universal_constrs hol_ctxt def t =
  let
    val k = maxidx_of_term t + 1
    fun do_term Ts def t args seen =
      case t of
        (t0 as Const (@{const_name "=="}, _)) $ t1 $ t2 =>
        do_eq_or_imp Ts true def t0 t1 t2 seen
      | (t0 as @{const "==>"}) $ t1 $ t2 =>
        if def then (t, []) else do_eq_or_imp Ts false def t0 t1 t2 seen
      | (t0 as Const (@{const_name HOL.eq}, _)) $ t1 $ t2 =>
        do_eq_or_imp Ts true def t0 t1 t2 seen
      | (t0 as @{const HOL.implies}) $ t1 $ t2 =>
        do_eq_or_imp Ts false def t0 t1 t2 seen
      | Abs (s, T, t') =>
        let val (t', seen) = do_term (T :: Ts) def t' [] seen in
          (list_comb (Abs (s, T, t'), args), seen)
        end
      | t1 $ t2 =>
        let val (t2, seen) = do_term Ts def t2 [] seen in
          do_term Ts def t1 (t2 :: args) seen
        end
      | _ => pull_out_constr_comb hol_ctxt Ts def k 0 t args seen
    and do_eq_or_imp Ts eq def t0 t1 t2 seen =
      let
        val (t2, seen) = if eq andalso def then (t2, seen)
                         else do_term Ts false t2 [] seen
        val (t1, seen) = do_term Ts false t1 [] seen
      in (t0 $ t1 $ t2, seen) end
    val (concl, seen) = do_term [] def t [] []
  in
    Logic.list_implies (equations_for_pulled_out_constrs Logic.mk_equals [] k
                                                         seen, concl)
  end

fun mk_exists v t =
  HOLogic.exists_const (fastype_of v) $ lambda v (incr_boundvars 1 t)

fun pull_out_existential_constrs hol_ctxt t =
  let
    val k = maxidx_of_term t + 1
    fun aux Ts num_exists t args seen =
      case t of
        (t0 as Const (@{const_name Ex}, _)) $ Abs (s1, T1, t1) =>
        let
          val (t1, seen') = aux (T1 :: Ts) (num_exists + 1) t1 [] []
          val n = length seen'
          fun vars () = map2 (fresh_value_var Ts k n) (index_seq 0 n) seen'
        in
          (equations_for_pulled_out_constrs HOLogic.mk_eq Ts k seen'
           |> List.foldl s_conj t1 |> fold mk_exists (vars ())
           |> curry3 Abs s1 T1 |> curry (op $) t0, seen)
        end
      | t1 $ t2 =>
        let val (t2, seen) = aux Ts num_exists t2 [] seen in
          aux Ts num_exists t1 (t2 :: args) seen
        end
      | Abs (s, T, t') =>
        let
          val (t', seen) = aux (T :: Ts) 0 t' [] (map (incr_boundvars 1) seen)
        in (list_comb (Abs (s, T, t'), args), map (incr_boundvars ~1) seen) end
      | _ =>
        if num_exists > 0 then
          pull_out_constr_comb hol_ctxt Ts false k num_exists t args seen
        else
          (list_comb (t, args), seen)
  in aux [] 0 t [] [] |> fst end

fun destroy_pulled_out_constrs (hol_ctxt as {ctxt, stds, ...}) axiom strong t =
  let
    val num_occs_of_var =
      fold_aterms (fn Var z => (fn f => fn z' => f z' |> z = z' ? Integer.add 1)
                    | _ => I) t (K 0)
    fun aux Ts careful ((t0 as Const (@{const_name "=="}, _)) $ t1 $ t2) =
        aux_eq Ts careful true t0 t1 t2
      | aux Ts careful ((t0 as @{const "==>"}) $ t1 $ t2) =
        t0 $ aux Ts false t1 $ aux Ts careful t2
      | aux Ts careful ((t0 as Const (@{const_name HOL.eq}, _)) $ t1 $ t2) =
        aux_eq Ts careful true t0 t1 t2
      | aux Ts careful ((t0 as @{const HOL.implies}) $ t1 $ t2) =
        t0 $ aux Ts false t1 $ aux Ts careful t2
      | aux Ts careful (Abs (s, T, t')) = Abs (s, T, aux (T :: Ts) careful t')
      | aux Ts careful (t1 $ t2) = aux Ts careful t1 $ aux Ts careful t2
      | aux _ _ t = t
    and aux_eq Ts careful pass1 t0 t1 t2 =
      ((if careful orelse
           not (strong orelse forall (is_constr_pattern ctxt) [t1, t2]) then
          raise SAME ()
        else if axiom andalso is_Var t2 andalso
                num_occs_of_var (dest_Var t2) = 1 then
          @{const True}
        else case strip_comb t2 of
          (* The first case is not as general as it could be. *)
          (Const (@{const_name PairBox}, _),
                  [Const (@{const_name fst}, _) $ Var z1,
                   Const (@{const_name snd}, _) $ Var z2]) =>
          if z1 = z2 andalso num_occs_of_var z1 = 2 then @{const True}
          else raise SAME ()
        | (Const (x as (s, T)), args) =>
          let
            val (arg_Ts, dataT) = strip_type T
            val n = length arg_Ts
          in
            if length args = n andalso
               (is_constr ctxt stds x orelse s = @{const_name Pair} orelse
                x = (@{const_name Suc}, nat_T --> nat_T)) andalso
               (not careful orelse not (is_Var t1) orelse
                String.isPrefix val_var_prefix (fst (fst (dest_Var t1)))) then
                s_let Ts "l" (n + 1) dataT bool_T
                      (fn t1 =>
                          discriminate_value hol_ctxt x t1 ::
                          map3 (sel_eq Ts x t1) (index_seq 0 n) arg_Ts args
                          |> foldr1 s_conj) t1
            else
              raise SAME ()
          end
        | _ => raise SAME ())
       |> body_type (type_of t0) = prop_T ? HOLogic.mk_Trueprop)
      handle SAME () => if pass1 then aux_eq Ts careful false t0 t2 t1
                        else t0 $ aux Ts false t2 $ aux Ts false t1
    and sel_eq Ts x t n nth_T nth_t =
      HOLogic.eq_const nth_T $ nth_t
                             $ select_nth_constr_arg ctxt stds x t n nth_T
      |> aux Ts false
  in aux [] axiom t end

(** Destruction of universal and existential equalities **)

fun curry_assms (@{const "==>"} $ (@{const Trueprop}
                                   $ (@{const HOL.conj} $ t1 $ t2)) $ t3) =
    curry_assms (Logic.list_implies ([t1, t2] |> map HOLogic.mk_Trueprop, t3))
  | curry_assms (@{const "==>"} $ t1 $ t2) =
    @{const "==>"} $ curry_assms t1 $ curry_assms t2
  | curry_assms t = t

val destroy_universal_equalities =
  let
    fun aux prems zs t =
      case t of
        @{const "==>"} $ t1 $ t2 => aux_implies prems zs t1 t2
      | _ => Logic.list_implies (rev prems, t)
    and aux_implies prems zs t1 t2 =
      case t1 of
        Const (@{const_name "=="}, _) $ Var z $ t' => aux_eq prems zs z t' t1 t2
      | @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ Var z $ t') =>
        aux_eq prems zs z t' t1 t2
      | @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ t' $ Var z) =>
        aux_eq prems zs z t' t1 t2
      | _ => aux (t1 :: prems) (Term.add_vars t1 zs) t2
    and aux_eq prems zs z t' t1 t2 =
      if not (member (op =) zs z) andalso
         not (exists_subterm (curry (op =) (Var z)) t') then
        aux prems zs (subst_free [(Var z, t')] t2)
      else
        aux (t1 :: prems) (Term.add_vars t1 zs) t2
  in aux [] [] end

fun find_bound_assign ctxt stds j =
  let
    fun do_term _ [] = NONE
      | do_term seen (t :: ts) =
        let
          fun do_eq pass1 t1 t2 =
            (if loose_bvar1 (t2, j) then
               if pass1 then do_eq false t2 t1 else raise SAME ()
             else case t1 of
               Bound j' => if j' = j then SOME (t2, ts @ seen) else raise SAME ()
             | Const (s, Type (@{type_name fun}, [T1, T2])) $ Bound j' =>
               if j' = j andalso
                  s = nth_sel_name_for_constr_name @{const_name FunBox} 0 then
                 SOME (construct_value ctxt stds
                                       (@{const_name FunBox}, T2 --> T1) [t2],
                       ts @ seen)
               else
                 raise SAME ()
             | _ => raise SAME ())
            handle SAME () => do_term (t :: seen) ts
        in
          case t of
            Const (@{const_name HOL.eq}, _) $ t1 $ t2 => do_eq true t1 t2
          | _ => do_term (t :: seen) ts
        end
  in do_term end

fun subst_one_bound j arg t =
  let
    fun aux (Bound i, lev) =
        if i < lev then raise SAME ()
        else if i = lev then incr_boundvars (lev - j) arg
        else Bound (i - 1)
      | aux (Abs (a, T, body), lev) = Abs (a, T, aux (body, lev + 1))
      | aux (f $ t, lev) =
        (aux (f, lev) $ (aux (t, lev) handle SAME () => t)
         handle SAME () => f $ aux (t, lev))
      | aux _ = raise SAME ()
  in aux (t, j) handle SAME () => t end

fun destroy_existential_equalities ({ctxt, stds, ...} : hol_context) =
  let
    fun kill [] [] ts = foldr1 s_conj ts
      | kill (s :: ss) (T :: Ts) ts =
        (case find_bound_assign ctxt stds (length ss) [] ts of
           SOME (_, []) => @{const True}
         | SOME (arg_t, ts) =>
           kill ss Ts (map (subst_one_bound (length ss)
                                (incr_bv (~1, length ss + 1, arg_t))) ts)
         | NONE =>
           Const (@{const_name Ex}, (T --> bool_T) --> bool_T)
           $ Abs (s, T, kill ss Ts ts))
      | kill _ _ _ = raise ListPair.UnequalLengths
    fun gather ss Ts (Const (@{const_name Ex}, _) $ Abs (s1, T1, t1)) =
        gather (ss @ [s1]) (Ts @ [T1]) t1
      | gather [] [] (Abs (s, T, t1)) = Abs (s, T, gather [] [] t1)
      | gather [] [] (t1 $ t2) = gather [] [] t1 $ gather [] [] t2
      | gather [] [] t = t
      | gather ss Ts t = kill ss Ts (conjuncts_of (gather [] [] t))
  in gather [] [] end

(** Skolemization **)

fun skolem_prefix_for k j =
  skolem_prefix ^ string_of_int k ^ "@" ^ string_of_int j ^ name_sep

fun skolemize_term_and_more (hol_ctxt as {thy, def_tables, skolems, ...})
                            skolem_depth =
  let
    val incrs = map (Integer.add 1)
    fun aux ss Ts js skolemizable polar t =
      let
        fun do_quantifier quant_s quant_T abs_s abs_T t =
          (if not (loose_bvar1 (t, 0)) then
             aux ss Ts js skolemizable polar (incr_boundvars ~1 t)
           else if is_positive_existential polar quant_s then
             let
               val j = length (!skolems) + 1
             in
               if skolemizable andalso length js <= skolem_depth then
                 let
                   val sko_s = skolem_prefix_for (length js) j ^ abs_s
                   val _ = Unsynchronized.change skolems (cons (sko_s, ss))
                   val sko_t = list_comb (Const (sko_s, rev Ts ---> abs_T),
                                          map Bound (rev js))
                   val abs_t = Abs (abs_s, abs_T,
                                    aux ss Ts (incrs js) skolemizable polar t)
                 in
                   if null js then
                     s_betapply Ts (abs_t, sko_t)
                   else
                     Const (@{const_name Let}, abs_T --> quant_T) $ sko_t
                     $ abs_t
                 end
               else
                 raise SAME ()
             end
           else
             raise SAME ())
          handle SAME () =>
                 Const (quant_s, quant_T)
                 $ Abs (abs_s, abs_T,
                        aux (abs_s :: ss) (abs_T :: Ts) (0 :: incrs js)
                            (skolemizable andalso
                             not (is_higher_order_type abs_T)) polar t)
      in
        case t of
          Const (s0 as @{const_name all}, T0) $ Abs (s1, T1, t1) =>
          do_quantifier s0 T0 s1 T1 t1
        | @{const "==>"} $ t1 $ t2 =>
          @{const "==>"} $ aux ss Ts js skolemizable (flip_polarity polar) t1
          $ aux ss Ts js skolemizable polar t2
        | @{const Pure.conjunction} $ t1 $ t2 =>
          @{const Pure.conjunction} $ aux ss Ts js skolemizable polar t1
          $ aux ss Ts js skolemizable polar t2
        | @{const Trueprop} $ t1 =>
          @{const Trueprop} $ aux ss Ts js skolemizable polar t1
        | @{const Not} $ t1 =>
          @{const Not} $ aux ss Ts js skolemizable (flip_polarity polar) t1
        | Const (s0 as @{const_name All}, T0) $ Abs (s1, T1, t1) =>
          do_quantifier s0 T0 s1 T1 t1
        | Const (s0 as @{const_name Ex}, T0) $ Abs (s1, T1, t1) =>
          do_quantifier s0 T0 s1 T1 t1
        | @{const HOL.conj} $ t1 $ t2 =>
          s_conj (pairself (aux ss Ts js skolemizable polar) (t1, t2))
        | @{const HOL.disj} $ t1 $ t2 =>
          s_disj (pairself (aux ss Ts js skolemizable polar) (t1, t2))
        | @{const HOL.implies} $ t1 $ t2 =>
          @{const HOL.implies} $ aux ss Ts js skolemizable (flip_polarity polar) t1
          $ aux ss Ts js skolemizable polar t2
        | (t0 as Const (@{const_name Let}, _)) $ t1 $ t2 =>
          t0 $ t1 $ aux ss Ts js skolemizable polar t2
        | Const (x as (s, T)) =>
          if is_real_inductive_pred hol_ctxt x andalso
             not (is_real_equational_fun hol_ctxt x) andalso
             not (is_well_founded_inductive_pred hol_ctxt x) then
            let
              val gfp = (fixpoint_kind_of_const thy def_tables x = Gfp)
              val (pref, connective) =
                if gfp then (lbfp_prefix, @{const HOL.disj})
                else (ubfp_prefix, @{const HOL.conj})
              fun pos () = unrolled_inductive_pred_const hol_ctxt gfp x
                           |> aux ss Ts js skolemizable polar
              fun neg () = Const (pref ^ s, T)
            in
              case polar |> gfp ? flip_polarity of
                Pos => pos ()
              | Neg => neg ()
              | Neut =>
                let
                  val arg_Ts = binder_types T
                  fun app f =
                    list_comb (f (), map Bound (length arg_Ts - 1 downto 0))
                in
                  fold_rev absdummy arg_Ts (connective $ app pos $ app neg)
                end
            end
          else
            Const x
        | t1 $ t2 =>
          s_betapply Ts (aux ss Ts js false polar t1,
                         aux ss Ts js false Neut t2)
        | Abs (s, T, t1) =>
          Abs (s, T, aux ss Ts (incrs js) skolemizable polar t1)
        | _ => t
      end
  in aux [] [] [] true Pos end

(** Function specialization **)

fun params_in_equation (@{const "==>"} $ _ $ t2) = params_in_equation t2
  | params_in_equation (@{const Trueprop} $ t1) = params_in_equation t1
  | params_in_equation (Const (@{const_name HOL.eq}, _) $ t1 $ _) =
    snd (strip_comb t1)
  | params_in_equation _ = []

fun specialize_fun_axiom x x' fixed_js fixed_args extra_args t =
  let
    val k = fold Integer.max (map maxidx_of_term (fixed_args @ extra_args)) 0
            + 1
    val t = map_aterms (fn Var ((s, i), T) => Var ((s, k + i), T) | t' => t') t
    val fixed_params = filter_indices fixed_js (params_in_equation t)
    fun aux args (Abs (s, T, t)) = list_comb (Abs (s, T, aux [] t), args)
      | aux args (t1 $ t2) = aux (aux [] t2 :: args) t1
      | aux args t =
        if t = Const x then
          list_comb (Const x', extra_args @ filter_out_indices fixed_js args)
        else
          let val j = find_index (curry (op =) t) fixed_params in
            list_comb (if j >= 0 then nth fixed_args j else t, args)
          end
  in aux [] t end

fun static_args_in_term ({ersatz_table, ...} : hol_context) x t =
  let
    fun fun_calls (Abs (_, _, t)) _ = fun_calls t []
      | fun_calls (t1 $ t2) args = fun_calls t2 [] #> fun_calls t1 (t2 :: args)
      | fun_calls t args =
        (case t of
           Const (x' as (s', T')) =>
           x = x' orelse (case AList.lookup (op =) ersatz_table s' of
                            SOME s'' => x = (s'', T')
                          | NONE => false)
         | _ => false) ? cons args
    fun call_sets [] [] vs = [vs]
      | call_sets [] uss vs = vs :: call_sets uss [] []
      | call_sets ([] :: _) _ _ = []
      | call_sets ((t :: ts) :: tss) uss vs =
        Ord_List.insert Term_Ord.term_ord t vs |> call_sets tss (ts :: uss)
    val sets = call_sets (fun_calls t [] []) [] []
    val indexed_sets = sets ~~ (index_seq 0 (length sets))
  in
    fold_rev (fn (set, j) =>
                 case set of
                   [Var _] => AList.lookup (op =) indexed_sets set = SOME j
                              ? cons (j, NONE)
                 | [t as Const _] => cons (j, SOME t)
                 | [t as Free _] => cons (j, SOME t)
                 | _ => I) indexed_sets []
  end
fun static_args_in_terms hol_ctxt x =
  map (static_args_in_term hol_ctxt x)
  #> fold1 (Ord_List.inter (prod_ord int_ord (option_ord Term_Ord.term_ord)))

fun overlapping_indices [] _ = []
  | overlapping_indices _ [] = []
  | overlapping_indices (ps1 as (j1, t1) :: ps1') (ps2 as (j2, t2) :: ps2') =
    if j1 < j2 then overlapping_indices ps1' ps2
    else if j1 > j2 then overlapping_indices ps1 ps2'
    else overlapping_indices ps1' ps2' |> the_default t2 t1 = t2 ? cons j1

fun special_prefix_for j = special_prefix ^ string_of_int j ^ name_sep

(* If a constant's definition is picked up deeper than this threshold, we
   prevent excessive specialization by not specializing it. *)
val special_max_depth = 20

val bound_var_prefix = "b"

fun special_fun_aconv ((x1, js1, ts1), (x2, js2, ts2)) =
  x1 = x2 andalso js1 = js2 andalso length ts1 = length ts2 andalso
  forall (op aconv) (ts1 ~~ ts2)

fun specialize_consts_in_term
        (hol_ctxt as {ctxt, thy, stds, specialize, def_tables, simp_table,
                      special_funs, ...}) def depth t =
  if not specialize orelse depth > special_max_depth then
    t
  else
    let
      val blacklist =
        if def then case term_under_def t of Const x => [x] | _ => [] else []
      fun aux args Ts (Const (x as (s, T))) =
          ((if not (member (op =) blacklist x) andalso not (null args) andalso
               not (String.isPrefix special_prefix s) andalso
               not (is_built_in_const thy stds x) andalso
               (is_equational_fun_but_no_plain_def hol_ctxt x orelse
                (is_some (def_of_const thy def_tables x) andalso
                 not (is_of_class_const thy x) andalso
                 not (is_constr ctxt stds x) andalso
                 not (is_choice_spec_fun hol_ctxt x))) then
              let
                val eligible_args =
                  filter (is_special_eligible_arg true Ts o snd)
                         (index_seq 0 (length args) ~~ args)
                val _ = not (null eligible_args) orelse raise SAME ()
                val old_axs = equational_fun_axioms hol_ctxt x
                              |> map (destroy_existential_equalities hol_ctxt)
                val static_params = static_args_in_terms hol_ctxt x old_axs
                val fixed_js = overlapping_indices static_params eligible_args
                val _ = not (null fixed_js) orelse raise SAME ()
                val fixed_args = filter_indices fixed_js args
                val vars = fold Term.add_vars fixed_args []
                           |> sort (Term_Ord.fast_indexname_ord o pairself fst)
                val bound_js = fold (fn t => fn js => add_loose_bnos (t, 0, js))
                                    fixed_args []
                               |> sort int_ord
                val live_args = filter_out_indices fixed_js args
                val extra_args = map Var vars @ map Bound bound_js @ live_args
                val extra_Ts = map snd vars @ filter_indices bound_js Ts
                val k = maxidx_of_term t + 1
                fun var_for_bound_no j =
                  Var ((bound_var_prefix ^
                        nat_subscript (find_index (curry (op =) j) bound_js
                                       + 1), k),
                       nth Ts j)
                val fixed_args_in_axiom =
                  map (curry subst_bounds
                             (map var_for_bound_no (index_seq 0 (length Ts))))
                      fixed_args
              in
                case AList.lookup special_fun_aconv (!special_funs)
                                  (x, fixed_js, fixed_args_in_axiom) of
                  SOME x' => list_comb (Const x', extra_args)
                | NONE =>
                  let
                    val extra_args_in_axiom =
                      map Var vars @ map var_for_bound_no bound_js
                    val x' as (s', _) =
                      (special_prefix_for (length (!special_funs) + 1) ^ s,
                       extra_Ts @ filter_out_indices fixed_js (binder_types T)
                       ---> body_type T)
                    val new_axs =
                      map (specialize_fun_axiom x x' fixed_js
                               fixed_args_in_axiom extra_args_in_axiom) old_axs
                    val _ =
                      Unsynchronized.change special_funs
                          (cons ((x, fixed_js, fixed_args_in_axiom), x'))
                    val _ = add_simps simp_table s' new_axs
                  in list_comb (Const x', extra_args) end
              end
            else
              raise SAME ())
           handle SAME () => list_comb (Const x, args))
        | aux args Ts (Abs (s, T, t)) =
          list_comb (Abs (s, T, aux [] (T :: Ts) t), args)
        | aux args Ts (t1 $ t2) = aux (aux [] Ts t2 :: args) Ts t1
        | aux args _ t = list_comb (t, args)
    in aux [] [] t end

type special_triple = int list * term list * styp

val cong_var_prefix = "c"

fun special_congruence_axiom T (js1, ts1, x1) (js2, ts2, x2) =
  let
    val (bounds1, bounds2) = pairself (map Var o special_bounds) (ts1, ts2)
    val Ts = binder_types T
    val max_j = fold (fold Integer.max) [js1, js2] ~1
    val (eqs, (args1, args2)) =
      fold (fn j => case pairself (fn ps => AList.lookup (op =) ps j)
                                  (js1 ~~ ts1, js2 ~~ ts2) of
                      (SOME t1, SOME t2) => apfst (cons (t1, t2))
                    | (SOME t1, NONE) => apsnd (apsnd (cons t1))
                    | (NONE, SOME t2) => apsnd (apfst (cons t2))
                    | (NONE, NONE) =>
                      let val v = Var ((cong_var_prefix ^ nat_subscript j, 0),
                                       nth Ts j) in
                        apsnd (pairself (cons v))
                      end) (max_j downto 0) ([], ([], []))
  in
    Logic.list_implies (eqs |> filter_out (op aconv) |> distinct (op =)
                            |> map Logic.mk_equals,
                        Logic.mk_equals (list_comb (Const x1, bounds1 @ args1),
                                         list_comb (Const x2, bounds2 @ args2)))
  end

fun special_congruence_axioms (hol_ctxt as {special_funs, ...}) ts =
  let
    val groups =
      !special_funs
      |> map (fn ((x, js, ts), x') => (x, (js, ts, x')))
      |> AList.group (op =)
      |> filter_out (is_equational_fun_surely_complete hol_ctxt o fst)
      |> map (fn (x, zs) =>
                 (x, zs |> member (op =) ts (Const x) ? cons ([], [], x)))
    fun generality (js, _, _) = ~(length js)
    fun is_more_specific (j1, t1, x1) (j2, t2, x2) =
      x1 <> x2 andalso length j2 < length j1 andalso
      Ord_List.subset (prod_ord int_ord Term_Ord.term_ord) (j2 ~~ t2, j1 ~~ t1)
    fun do_pass_1 _ [] [_] [_] = I
      | do_pass_1 T skipped _ [] = do_pass_2 T skipped
      | do_pass_1 T skipped all (z :: zs) =
        case filter (is_more_specific z) all
             |> sort (int_ord o pairself generality) of
          [] => do_pass_1 T (z :: skipped) all zs
        | (z' :: _) => cons (special_congruence_axiom T z z')
                       #> do_pass_1 T skipped all zs
    and do_pass_2 _ [] = I
      | do_pass_2 T (z :: zs) =
        fold (cons o special_congruence_axiom T z) zs #> do_pass_2 T zs
  in fold (fn ((_, T), zs) => do_pass_1 T [] zs zs) groups [] end

(** Axiom selection **)

fun defined_free_by_assumption t =
  let
    fun do_equals u def =
      if exists_subterm (curry (op aconv) u) def then NONE else SOME u
  in
    case t of
      Const (@{const_name "=="}, _) $ (u as Free _) $ def => do_equals u def
    | @{const Trueprop}
      $ (Const (@{const_name HOL.eq}, _) $ (u as Free _) $ def) =>
      do_equals u def
    | _ => NONE
  end

fun assumption_exclusively_defines_free assm_ts t =
  case defined_free_by_assumption t of
    SOME u =>
    length (filter ((fn SOME u' => u aconv u' | NONE => false)
                     o defined_free_by_assumption) assm_ts) = 1
  | NONE => false

fun all_table_entries table = Symtab.fold (append o snd) table []
fun extra_table tables s =
  Symtab.make [(s, pairself all_table_entries tables |> op @)]

fun eval_axiom_for_term j t =
  Logic.mk_equals (Const (eval_prefix ^ string_of_int j, fastype_of t), t)

val is_trivial_equation = the_default false o try (op aconv o Logic.dest_equals)

(* Prevents divergence in case of cyclic or infinite axiom dependencies. *)
val axioms_max_depth = 255

fun axioms_for_term
        (hol_ctxt as {thy, ctxt, max_bisim_depth, stds, user_axioms,
                      evals, def_tables, nondef_table, choice_spec_table,
                      nondefs, ...}) assm_ts neg_t =
  let
    val (def_assm_ts, nondef_assm_ts) =
      List.partition (assumption_exclusively_defines_free assm_ts) assm_ts
    val def_assm_table = map (`(the o defined_free_by_assumption)) def_assm_ts
    type accumulator = styp list * (term list * term list)
    fun add_axiom get app def depth t (accum as (seen, axs)) =
      let
        val t = t |> unfold_defs_in_term hol_ctxt
                  |> skolemize_term_and_more hol_ctxt ~1 (* FIXME: why ~1? *)
      in
        if is_trivial_equation t then
          accum
        else
          let val t' = t |> specialize_consts_in_term hol_ctxt def depth in
            if exists (member (op aconv) (get axs)) [t, t'] then accum
            else add_axioms_for_term (depth + 1) t' (seen, app (cons t') axs)
          end
      end
    and add_def_axiom depth = add_axiom fst apfst true depth
    and add_nondef_axiom depth = add_axiom snd apsnd false depth
    and add_maybe_def_axiom depth t =
      (if head_of t <> @{const "==>"} then add_def_axiom
       else add_nondef_axiom) depth t
    and add_eq_axiom depth t =
      (if is_constr_pattern_formula ctxt t then add_def_axiom
       else add_nondef_axiom) depth t
    and add_axioms_for_term depth t (accum as (seen, axs)) =
      case t of
        t1 $ t2 => accum |> fold (add_axioms_for_term depth) [t1, t2]
      | Const (x as (s, T)) =>
        (if member (op aconv) seen t orelse is_built_in_const thy stds x then
           accum
         else
           let val accum = (t :: seen, axs) in
             if depth > axioms_max_depth then
               raise TOO_LARGE ("Nitpick_Preproc.axioms_for_term.\
                                \add_axioms_for_term",
                                "too many nested axioms (" ^
                                string_of_int depth ^ ")")
             else if is_of_class_const thy x then
               let
                 val class = Logic.class_of_const s
                 val of_class = Logic.mk_of_class (TVar (("'a", 0), [class]),
                                                   class)
                 val ax1 = try (specialize_type thy x) of_class
                 val ax2 = Option.map (specialize_type thy x o snd)
                                      (get_class_def thy class)
               in
                 fold (add_maybe_def_axiom depth) (map_filter I [ax1, ax2])
                      accum
               end
             else if is_constr ctxt stds x then
               accum
             else if is_descr (original_name s) then
               fold (add_nondef_axiom depth) (equational_fun_axioms hol_ctxt x)
                    accum
             else if is_equational_fun_but_no_plain_def hol_ctxt x then
               fold (add_eq_axiom depth) (equational_fun_axioms hol_ctxt x)
                    accum
             else if is_choice_spec_fun hol_ctxt x then
               fold (add_nondef_axiom depth)
                    (nondef_props_for_const thy true choice_spec_table x) accum
             else if is_abs_fun ctxt x then
               accum |> fold (add_nondef_axiom depth)
                             (nondef_props_for_const thy false nondef_table x)
                     |> (is_funky_typedef ctxt (range_type T) orelse
                         range_type T = nat_T)
                        ? fold (add_maybe_def_axiom depth)
                               (nondef_props_for_const thy true
                                    (extra_table def_tables s) x)
             else if is_rep_fun ctxt x then
               accum |> fold (add_nondef_axiom depth)
                             (nondef_props_for_const thy false nondef_table x)
                     |> (is_funky_typedef ctxt (range_type T) orelse
                         range_type T = nat_T)
                        ? fold (add_maybe_def_axiom depth)
                               (nondef_props_for_const thy true
                                    (extra_table def_tables s) x)
                     |> add_axioms_for_term depth
                                            (Const (mate_of_rep_fun ctxt x))
                     |> fold (add_def_axiom depth)
                             (inverse_axioms_for_rep_fun ctxt x)
             else if s = @{const_name TYPE} then
               accum
             else case def_of_const thy def_tables x of
               SOME _ =>
               fold (add_eq_axiom depth) (equational_fun_axioms hol_ctxt x)
                    accum
             | NONE =>
               accum |> user_axioms <> SOME false
                        ? fold (add_nondef_axiom depth)
                               (nondef_props_for_const thy false nondef_table x)
           end)
        |> add_axioms_for_type depth T
      | Free (_, T) =>
        (if member (op aconv) seen t then
           accum
         else case AList.lookup (op =) def_assm_table t of
           SOME t => add_def_axiom depth t accum
         | NONE => accum)
        |> add_axioms_for_type depth T
      | Var (_, T) => add_axioms_for_type depth T accum
      | Bound _ => accum
      | Abs (_, T, t) => accum |> add_axioms_for_term depth t
                               |> add_axioms_for_type depth T
    and add_axioms_for_type depth T =
      case T of
        Type (@{type_name fun}, Ts) => fold (add_axioms_for_type depth) Ts
      | Type (@{type_name prod}, Ts) => fold (add_axioms_for_type depth) Ts
      | Type (@{type_name set}, Ts) => fold (add_axioms_for_type depth) Ts
      | @{typ prop} => I
      | @{typ bool} => I
      | TFree (_, S) => add_axioms_for_sort depth T S
      | TVar (_, S) => add_axioms_for_sort depth T S
      | Type (z as (_, Ts)) =>
        fold (add_axioms_for_type depth) Ts
        #> (if is_pure_typedef ctxt T then
              fold (add_maybe_def_axiom depth) (optimized_typedef_axioms ctxt z)
            else if is_quot_type ctxt T then
              fold (add_def_axiom depth)
                   (optimized_quot_type_axioms ctxt stds z)
            else if max_bisim_depth >= 0 andalso is_codatatype ctxt T then
              fold (add_maybe_def_axiom depth)
                   (codatatype_bisim_axioms hol_ctxt T)
            else
              I)
    and add_axioms_for_sort depth T S =
      let
        val supers = Sign.complete_sort thy S
        val class_axioms =
          maps (fn class => map prop_of (AxClass.get_info thy class |> #axioms
                                         handle ERROR _ => [])) supers
        val monomorphic_class_axioms =
          map (fn t => case Term.add_tvars t [] of
                         [] => t
                       | [(x, S)] =>
                         monomorphic_term (Vartab.make [(x, (S, T))]) t
                       | _ => raise TERM ("Nitpick_Preproc.axioms_for_term.\
                                          \add_axioms_for_sort", [t]))
              class_axioms
      in fold (add_nondef_axiom depth) monomorphic_class_axioms end
    val (mono_nondefs, poly_nondefs) =
      List.partition (null o Term.hidden_polymorphism) nondefs
    val eval_axioms = map2 eval_axiom_for_term (index_seq 0 (length evals))
                           evals
    val (seen, (defs, nondefs)) =
      ([], ([], []))
      |> add_axioms_for_term 1 neg_t
      |> fold_rev (add_nondef_axiom 1) nondef_assm_ts
      |> fold_rev (add_def_axiom 1) eval_axioms
      |> user_axioms = SOME true ? fold (add_nondef_axiom 1) mono_nondefs
    val defs = defs @ special_congruence_axioms hol_ctxt seen
    val got_all_mono_user_axioms =
      (user_axioms = SOME true orelse null mono_nondefs)
  in (neg_t :: nondefs, defs, got_all_mono_user_axioms, null poly_nondefs) end

(** Simplification of constructor/selector terms **)

fun simplify_constrs_and_sels ctxt t =
  let
    fun is_nth_sel_on t' n (Const (s, _) $ t) =
        (t = t' andalso is_sel_like_and_no_discr s andalso
         sel_no_from_name s = n)
      | is_nth_sel_on _ _ _ = false
    fun do_term (Const (@{const_name Rep_Frac}, _)
                 $ (Const (@{const_name Abs_Frac}, _) $ t1)) [] = do_term t1 []
      | do_term (Const (@{const_name Abs_Frac}, _)
                 $ (Const (@{const_name Rep_Frac}, _) $ t1)) [] = do_term t1 []
      | do_term (t1 $ t2) args = do_term t1 (do_term t2 [] :: args)
      | do_term (t as Const (x as (s, T))) (args as _ :: _) =
        ((if is_constr_like ctxt x then
            if length args = num_binder_types T then
              case hd args of
                Const (_, T') $ t' =>
                if domain_type T' = body_type T andalso
                   forall (uncurry (is_nth_sel_on t'))
                          (index_seq 0 (length args) ~~ args) then
                  t'
                else
                  raise SAME ()
              | _ => raise SAME ()
            else
              raise SAME ()
          else if is_sel_like_and_no_discr s then
            case strip_comb (hd args) of
              (Const (x' as (s', T')), ts') =>
              if is_constr_like ctxt x' andalso
                 constr_name_for_sel_like s = s' andalso
                 not (exists is_pair_type (binder_types T')) then
                list_comb (nth ts' (sel_no_from_name s), tl args)
              else
                raise SAME ()
            | _ => raise SAME ()
          else
            raise SAME ())
         handle SAME () => s_betapplys [] (t, args))
      | do_term (Abs (s, T, t')) args =
        s_betapplys [] (Abs (s, T, do_term t' []), args)
      | do_term t args = s_betapplys [] (t, args)
  in do_term t [] end

(** Quantifier massaging: Distributing quantifiers **)

fun distribute_quantifiers t =
  case t of
    (t0 as Const (@{const_name All}, T0)) $ Abs (s, T1, t1) =>
    (case t1 of
       (t10 as @{const HOL.conj}) $ t11 $ t12 =>
       t10 $ distribute_quantifiers (t0 $ Abs (s, T1, t11))
           $ distribute_quantifiers (t0 $ Abs (s, T1, t12))
     | (t10 as @{const Not}) $ t11 =>
       t10 $ distribute_quantifiers (Const (@{const_name Ex}, T0)
                                     $ Abs (s, T1, t11))
     | t1 =>
       if not (loose_bvar1 (t1, 0)) then
         distribute_quantifiers (incr_boundvars ~1 t1)
       else
         t0 $ Abs (s, T1, distribute_quantifiers t1))
  | (t0 as Const (@{const_name Ex}, T0)) $ Abs (s, T1, t1) =>
    (case distribute_quantifiers t1 of
       (t10 as @{const HOL.disj}) $ t11 $ t12 =>
       t10 $ distribute_quantifiers (t0 $ Abs (s, T1, t11))
           $ distribute_quantifiers (t0 $ Abs (s, T1, t12))
     | (t10 as @{const HOL.implies}) $ t11 $ t12 =>
       t10 $ distribute_quantifiers (Const (@{const_name All}, T0)
                                     $ Abs (s, T1, t11))
           $ distribute_quantifiers (t0 $ Abs (s, T1, t12))
     | (t10 as @{const Not}) $ t11 =>
       t10 $ distribute_quantifiers (Const (@{const_name All}, T0)
                                     $ Abs (s, T1, t11))
     | t1 =>
       if not (loose_bvar1 (t1, 0)) then
         distribute_quantifiers (incr_boundvars ~1 t1)
       else
         t0 $ Abs (s, T1, distribute_quantifiers t1))
  | t1 $ t2 => distribute_quantifiers t1 $ distribute_quantifiers t2
  | Abs (s, T, t') => Abs (s, T, distribute_quantifiers t')
  | _ => t

(** Quantifier massaging: Pushing quantifiers inward **)

fun renumber_bounds j n f t =
  case t of
    t1 $ t2 => renumber_bounds j n f t1 $ renumber_bounds j n f t2
  | Abs (s, T, t') => Abs (s, T, renumber_bounds (j + 1) n f t')
  | Bound j' =>
    Bound (if j' >= j andalso j' < j + n then f (j' - j) + j else j')
  | _ => t

(* Maximum number of quantifiers in a cluster for which the exponential
   algorithm is used. Larger clusters use a heuristic inspired by Claessen &
   Soerensson's polynomial binary splitting procedure (p. 5 of their MODEL 2003
   paper). *)
val quantifier_cluster_threshold = 7

val push_quantifiers_inward =
  let
    fun aux quant_s ss Ts t =
      (case t of
         Const (s0, _) $ Abs (s1, T1, t1 as _ $ _) =>
         if s0 = quant_s then
           aux s0 (s1 :: ss) (T1 :: Ts) t1
         else if quant_s = "" andalso
                 (s0 = @{const_name All} orelse s0 = @{const_name Ex}) then
           aux s0 [s1] [T1] t1
         else
           raise SAME ()
       | _ => raise SAME ())
      handle SAME () =>
             case t of
               t1 $ t2 =>
               if quant_s = "" then
                 aux "" [] [] t1 $ aux "" [] [] t2
               else
                 let
                   fun big_union proj ps =
                     fold (fold (insert (op =)) o proj) ps []
                   val (ts, connective) = strip_any_connective t
                   val T_costs = map typical_card_of_type Ts
                   val t_costs = map size_of_term ts
                   val num_Ts = length Ts
                   val flip = curry (op -) (num_Ts - 1)
                   val t_boundss = map (map flip o loose_bnos) ts
                   fun merge costly_boundss [] = costly_boundss
                     | merge costly_boundss (j :: js) =
                       let
                         val (yeas, nays) =
                           List.partition (fn (bounds, _) =>
                                              member (op =) bounds j)
                                          costly_boundss
                         val yeas_bounds = big_union fst yeas
                         val yeas_cost = Integer.sum (map snd yeas)
                                         * nth T_costs j
                       in merge ((yeas_bounds, yeas_cost) :: nays) js end
                   val cost = Integer.sum o map snd oo merge
                   fun heuristically_best_permutation _ [] = []
                     | heuristically_best_permutation costly_boundss js =
                       let
                         val (costly_boundss, (j, js)) =
                           js |> map (`(merge costly_boundss o single))
                              |> sort (int_ord
                                       o pairself (Integer.sum o map snd o fst))
                              |> split_list |>> hd ||> pairf hd tl
                       in
                         j :: heuristically_best_permutation costly_boundss js
                       end
                   val js =
                     if length Ts <= quantifier_cluster_threshold then
                       all_permutations (index_seq 0 num_Ts)
                       |> map (`(cost (t_boundss ~~ t_costs)))
                       |> sort (int_ord o pairself fst) |> hd |> snd
                     else
                       heuristically_best_permutation (t_boundss ~~ t_costs)
                                                      (index_seq 0 num_Ts)
                   val back_js = map (fn j => find_index (curry (op =) j) js)
                                     (index_seq 0 num_Ts)
                   val ts = map (renumber_bounds 0 num_Ts (nth back_js o flip))
                                ts
                   fun mk_connection [] =
                       raise ARG ("Nitpick_Preproc.push_quantifiers_inward.aux.\
                                  \mk_connection", "")
                     | mk_connection ts_cum_bounds =
                       ts_cum_bounds |> map fst
                       |> foldr1 (fn (t1, t2) => connective $ t1 $ t2)
                   fun build ts_cum_bounds [] = ts_cum_bounds |> mk_connection
                     | build ts_cum_bounds (j :: js) =
                       let
                         val (yeas, nays) =
                           List.partition (fn (_, bounds) =>
                                              member (op =) bounds j)
                                          ts_cum_bounds
                           ||> map (apfst (incr_boundvars ~1))
                       in
                         if null yeas then
                           build nays js
                         else
                           let val T = nth Ts (flip j) in
                             build ((Const (quant_s, (T --> bool_T) --> bool_T)
                                     $ Abs (nth ss (flip j), T,
                                            mk_connection yeas),
                                      big_union snd yeas) :: nays) js
                           end
                       end
                 in build (ts ~~ t_boundss) js end
             | Abs (s, T, t') => Abs (s, T, aux "" [] [] t')
             | _ => t
  in aux "" [] [] end

(** Preprocessor entry point **)

val max_skolem_depth = 3

fun preprocess_formulas
        (hol_ctxt as {thy, ctxt, stds, binary_ints, destroy_constrs, boxes,
                      needs, ...}) assm_ts neg_t =
  let
    val (nondef_ts, def_ts, got_all_mono_user_axioms, no_poly_user_axioms) =
      neg_t |> unfold_defs_in_term hol_ctxt
            |> close_form
            |> skolemize_term_and_more hol_ctxt max_skolem_depth
            |> specialize_consts_in_term hol_ctxt false 0
            |> axioms_for_term hol_ctxt assm_ts
    val binarize =
      is_standard_datatype thy stds nat_T andalso
      case binary_ints of
        SOME false => false
      | _ => forall (may_use_binary_ints false) nondef_ts andalso
             forall (may_use_binary_ints true) def_ts andalso
             (binary_ints = SOME true orelse
              exists should_use_binary_ints (nondef_ts @ def_ts))
    val box = exists (not_equal (SOME false) o snd) boxes
    val table =
      Termtab.empty
      |> box ? fold (add_to_uncurry_table ctxt) (nondef_ts @ def_ts)
    fun do_middle def =
      binarize ? binarize_nat_and_int_in_term
      #> box ? uncurry_term table
      #> box ? box_fun_and_pair_in_term hol_ctxt def
    fun do_tail def =
      destroy_set_Collect
      #> destroy_constrs ? (pull_out_universal_constrs hol_ctxt def
                            #> pull_out_existential_constrs hol_ctxt)
      #> destroy_pulled_out_constrs hol_ctxt def destroy_constrs
      #> curry_assms
      #> destroy_universal_equalities
      #> destroy_existential_equalities hol_ctxt
      #> simplify_constrs_and_sels ctxt
      #> distribute_quantifiers
      #> push_quantifiers_inward
      #> close_form
      #> Term.map_abs_vars shortest_name
    val nondef_ts = nondef_ts |> map (do_middle false)
    val need_ts =
      case needs of
        SOME needs =>
        needs |> map (unfold_defs_in_term hol_ctxt #> do_middle false)
      | NONE => [] (* FIXME: Implement inference. *)
    val nondef_ts = nondef_ts |> map (do_tail false)
    val def_ts = def_ts |> map (do_middle true #> do_tail true)
  in
    (nondef_ts, def_ts, need_ts, got_all_mono_user_axioms, no_poly_user_axioms,
     binarize)
  end

end;
