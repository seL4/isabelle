(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_fun.ML
    Author:     Lukas Bulwahn, TU Muenchen

Preprocessing functions to predicates.
*)

signature PREDICATE_COMPILE_FUN =
sig
  val define_predicates : (string * thm list) list -> theory -> (string * thm list) list * theory
  val rewrite_intro : theory -> thm -> thm list
  val pred_of_function : theory -> string -> string option
  val add_function_predicate_translation : (term * term) -> theory -> theory
end;

structure Predicate_Compile_Fun : PREDICATE_COMPILE_FUN =
struct

open Predicate_Compile_Aux;

(* Table from function to inductive predicate *)
structure Fun_Pred = Theory_Data
(
  type T = (term * term) Item_Net.T;
  val empty = Item_Net.init ((op aconv o pairself fst) : (term * term) * (term * term) -> bool)
    (single o fst);
  val extend = I;
  val merge = Item_Net.merge;
)

fun lookup thy net t =
  case Item_Net.retrieve net t of
    [] => NONE
  | [(f, p)] =>
    let
      val subst = Pattern.match thy (f, t) (Vartab.empty, Vartab.empty)
    in
      SOME (Envir.subst_term subst p)
    end
  | _ => NONE

fun pred_of_function thy name =
  case Item_Net.retrieve (Fun_Pred.get thy) (Const (name, Term.dummyT)) of
    [] => NONE
  | [(f, p)] => SOME (fst (dest_Const p))
  | _ => error ("Multiple matches possible for lookup of constant " ^ name)

fun defined_const thy name = is_some (pred_of_function thy name)

fun add_function_predicate_translation (f, p) =
  Fun_Pred.map (Item_Net.update (f, p))

fun transform_ho_typ (T as Type ("fun", _)) =
  let
    val (Ts, T') = strip_type T
  in if T' = @{typ "bool"} then T else (Ts @ [T']) ---> HOLogic.boolT end
| transform_ho_typ t = t

fun transform_ho_arg arg = 
  case (fastype_of arg) of
    (T as Type ("fun", _)) =>
      (case arg of
        Free (name, _) => Free (name, transform_ho_typ T)
      | _ => raise Fail "A non-variable term at a higher-order position")
  | _ => arg

fun pred_type T =
  let
    val (Ts, T') = strip_type T
    val Ts' = map transform_ho_typ Ts
  in
    (Ts' @ [T']) ---> HOLogic.boolT
  end;

(* FIXME: create new predicate name -- does not avoid nameclashing *)
fun pred_of f =
  let
    val (name, T) = dest_Const f
  in
    if (body_type T = @{typ bool}) then
      (Free (Long_Name.base_name name ^ "P", T))
    else
      (Free (Long_Name.base_name name ^ "P", pred_type T))
  end

(* creates the list of premises for every intro rule *)
(* theory -> term -> (string list, term list list) *)

fun dest_code_eqn eqn = let
  val (lhs, rhs) = Logic.dest_equals (Logic.unvarify_global (Thm.prop_of eqn))
  val (func, args) = strip_comb lhs
in ((func, args), rhs) end;

(* TODO: does not work with higher order functions yet *)
fun mk_rewr_eq (func, pred) =
  let
    val (argTs, resT) = (strip_type (fastype_of func))
    val nctxt =
      Name.make_context (Term.fold_aterms (fn Free (x, _) => insert (op =) x | _ => I) (func $ pred) [])
    val (argnames, nctxt') = Name.variants (replicate (length argTs) "a") nctxt
    val ([resname], nctxt'') = Name.variants ["r"] nctxt'
    val args = map Free (argnames ~~ argTs)
    val res = Free (resname, resT)
  in Logic.mk_equals
      (HOLogic.mk_eq (res, list_comb (func, args)), list_comb (pred, args @ [res]))
  end;

fun folds_map f xs y =
  let
    fun folds_map' acc [] y = [(rev acc, y)]
      | folds_map' acc (x :: xs) y =
        maps (fn (x, y) => folds_map' (x :: acc) xs y) (f x y)
    in
      folds_map' [] xs y
    end;

fun keep_functions thy t =
  case try dest_Const (fst (strip_comb t)) of
    SOME (c, _) => Predicate_Compile_Data.keep_function thy c
  | _ => false

fun flatten thy lookup_pred t (names, prems) =
  let
    fun lift t (names, prems) =
      case lookup_pred (Envir.eta_contract t) of
        SOME pred => [(pred, (names, prems))]
      | NONE =>
        let
          val (vars, body) = strip_abs t
          val _ = assert (fastype_of body = body_type (fastype_of body))
          val absnames = Name.variant_list names (map fst vars)
          val frees = map2 (curry Free) absnames (map snd vars)
          val body' = subst_bounds (rev frees, body)
          val resname = Name.variant (absnames @ names) "res"
          val resvar = Free (resname, fastype_of body)
          val t = flatten' body' ([], [])
            |> map (fn (res, (inner_names, inner_prems)) =>
              let
                fun mk_exists (x, T) t = HOLogic.mk_exists (x, T, t)
                val vTs = 
                  fold Term.add_frees inner_prems []
                  |> filter (fn (x, T) => member (op =) inner_names x)
                val t = 
                  fold mk_exists vTs
                  (foldr1 HOLogic.mk_conj (HOLogic.mk_eq (res, resvar) ::
                    map HOLogic.dest_Trueprop inner_prems))
              in
                t
              end)
              |> foldr1 HOLogic.mk_disj
              |> fold lambda (resvar :: rev frees)
        in
          [(t, (names, prems))]
        end
    and flatten_or_lift (t, T) (names, prems) =
      if fastype_of t = T then
        flatten' t (names, prems)
      else
        (* note pred_type might be to general! *)
        if (pred_type (fastype_of t) = T) then
          lift t (names, prems)
        else
          error ("unexpected input for flatten or lift" ^ Syntax.string_of_term_global thy t ^
          ", " ^  Syntax.string_of_typ_global thy T)
    and flatten' (t as Const (name, T)) (names, prems) = [(t, (names, prems))]
      | flatten' (t as Free (f, T)) (names, prems) = [(t, (names, prems))]
      | flatten' (t as Abs _) (names, prems) = [(t, (names, prems))]
      | flatten' (t as _ $ _) (names, prems) =
      if Predicate_Compile_Aux.is_constrt thy t orelse keep_functions thy t then
        [(t, (names, prems))]
      else
        case (fst (strip_comb t)) of
          Const (@{const_name "If"}, _) =>
            (let
              val (_, [B, x, y]) = strip_comb t
            in
              flatten' B (names, prems)
              |> maps (fn (B', (names, prems)) =>
                (flatten' x (names, prems)
                |> map (fn (res, (names, prems)) => (res, (names, (HOLogic.mk_Trueprop B') :: prems))))
                @ (flatten' y (names, prems)
                |> map (fn (res, (names, prems)) =>
                  (* in general unsound! *)
                  (res, (names, (HOLogic.mk_Trueprop (HOLogic.mk_not B')) :: prems)))))
            end)
        | Const (@{const_name "Let"}, _) => 
            (let
              val (_, [f, g]) = strip_comb t
            in
              flatten' f (names, prems)
              |> maps (fn (res, (names, prems)) =>
                flatten' (betapply (g, res)) (names, prems))
            end)
        | Const (@{const_name "split"}, _) => 
            (let
              val (_, g :: res :: args) = strip_comb t
              val [res1, res2] = Name.variant_list names ["res1", "res2"]
              val (T1, T2) = HOLogic.dest_prodT (fastype_of res)
              val (resv1, resv2) = (Free (res1, T1), Free (res2, T2))
            in
              flatten' (betapplys (g, (resv1 :: resv2 :: args)))
              (res1 :: res2 :: names,
              HOLogic.mk_Trueprop (HOLogic.mk_eq (res, HOLogic.mk_prod (resv1, resv2))) :: prems)
            end)
        | _ =>
        case find_split_thm thy (fst (strip_comb t)) of
          SOME raw_split_thm =>
          let
            val (f, args) = strip_comb t
            val split_thm = prepare_split_thm (ProofContext.init thy) raw_split_thm
            val (assms, concl) = Logic.strip_horn (prop_of split_thm)
            val (P, [split_t]) = strip_comb (HOLogic.dest_Trueprop concl) 
            val subst = Pattern.match thy (split_t, t) (Vartab.empty, Vartab.empty)
            val (_, split_args) = strip_comb split_t
            val match = split_args ~~ args
            fun flatten_of_assm assm =
              let
                val (vTs, assm') = strip_all (Envir.beta_norm (Envir.subst_term subst assm))
                val var_names = Name.variant_list names (map fst vTs)
                val vars = map Free (var_names ~~ (map snd vTs))
                val (prems', pre_res) = Logic.strip_horn (subst_bounds (rev vars, assm'))
                val (_, [inner_t]) = strip_comb (HOLogic.dest_Trueprop pre_res)
                val (lhss : term list, rhss) =
                  split_list (map (HOLogic.dest_eq o HOLogic.dest_Trueprop) prems')
              in
                folds_map flatten' lhss (var_names @ names, prems)
                |> map (fn (ress, (names, prems)) =>
                  let
                    val prems' = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (ress ~~ rhss)
                  in (names, prems' @ prems) end)
                |> maps (flatten' inner_t)
              end
          in
            maps flatten_of_assm assms
          end
      | NONE =>
          let
            val (f, args) = strip_comb t
            val args = map (Pattern.eta_long []) args
            val _ = assert (fastype_of t = body_type (fastype_of t))
            val f' = lookup_pred f
            val Ts = case f' of
              SOME pred => (fst (split_last (binder_types (fastype_of pred))))
            | NONE => binder_types (fastype_of f)
          in
            folds_map flatten_or_lift (args ~~ Ts) (names, prems) |>
            (case f' of
              NONE =>
                map (fn (argvs, (names', prems')) => (list_comb (f, argvs), (names', prems')))
            | SOME pred =>
                map (fn (argvs, (names', prems')) =>
                  let
                    fun lift_arg T t =
                      if (fastype_of t) = T then t
                      else
                        let
                          val _ = assert (T =
                            (binder_types (fastype_of t) @ [@{typ bool}] ---> @{typ bool}))
                          fun mk_if T (b, t, e) =
                            Const (@{const_name If}, @{typ bool} --> T --> T --> T) $ b $ t $ e
                          val Ts = binder_types (fastype_of t)
                        in
                          list_abs (map (pair "x") Ts @ [("b", @{typ bool})],
                            mk_if @{typ bool} (list_comb (t, map Bound (length Ts downto 1)),
                            HOLogic.mk_eq (@{term True}, Bound 0),
                            HOLogic.mk_eq (@{term False}, Bound 0)))
                        end
                    val argvs' = map2 lift_arg Ts argvs
                    val resname = Name.variant names' "res"
                    val resvar = Free (resname, body_type (fastype_of t))
                    val prem = HOLogic.mk_Trueprop (list_comb (pred, argvs' @ [resvar]))
                  in (resvar, (resname :: names', prem :: prems')) end))
          end
  in
    map (apfst Envir.eta_contract) (flatten' (Pattern.eta_long [] t) (names, prems))
  end;

(* assumption: mutual recursive predicates all have the same parameters. *)
fun define_predicates specs thy =
  if forall (fn (const, _) => defined_const thy const) specs then
    ([], thy)
  else
    let
      val consts = map fst specs
      val eqns = maps snd specs
      (* create prednames *)
      val ((funs, argss), rhss) = map_split dest_code_eqn eqns |>> split_list
      val argss' = map (map transform_ho_arg) argss
      fun is_lifted (t1, t2) = (fastype_of t2 = pred_type (fastype_of t1))
     (* FIXME: higher order arguments also occur in tuples! *)
      val lifted_args = distinct (op =) (filter is_lifted (flat argss ~~ flat argss'))
      val preds = map pred_of funs
      (* mapping from term (Free or Const) to term *)
      val net = fold Item_Net.update
        ((funs ~~ preds) @ lifted_args)
          (Fun_Pred.get thy)
      fun lookup_pred t = lookup thy net t
      (* create intro rules *)
      fun mk_intros ((func, pred), (args, rhs)) =
        if (body_type (fastype_of func) = @{typ bool}) then
         (* TODO: preprocess predicate definition of rhs *)
          [Logic.list_implies ([HOLogic.mk_Trueprop rhs], HOLogic.mk_Trueprop (list_comb (pred, args)))]
        else
          let
            val names = Term.add_free_names rhs []
          in flatten thy lookup_pred rhs (names, [])
            |> map (fn (resultt, (names', prems)) =>
              Logic.list_implies (prems, HOLogic.mk_Trueprop (list_comb (pred, args @ [resultt]))))
          end
      fun mk_rewr_thm (func, pred) = @{thm refl}
      val intr_ts = maps mk_intros ((funs ~~ preds) ~~ (argss' ~~ rhss))
      val (ind_result, thy') =
        thy
        |> Sign.map_naming Name_Space.conceal
        |> Inductive.add_inductive_global
          {quiet_mode = false, verbose = false, alt_name = Binding.empty, coind = false,
            no_elim = false, no_ind = false, skip_mono = false, fork_mono = false}
          (map (fn (s, T) =>
            ((Binding.name s, T), NoSyn)) (distinct (op =) (map dest_Free preds)))
          (map (dest_Free o snd) lifted_args)
          (map (fn x => (Attrib.empty_binding, x)) intr_ts)
          []
        ||> Sign.restore_naming thy
      val prednames = map (fst o dest_Const) (#preds ind_result)
      (* add constants to my table *)
      val specs = map (fn predname => (predname, filter (Predicate_Compile_Aux.is_intro predname)
        (#intrs ind_result))) prednames
      val thy'' = Fun_Pred.map
        (fold Item_Net.update (map (apfst Logic.varify_global)
          (distinct (op =) funs ~~ (#preds ind_result)))) thy'
    in
      (specs, thy'')
    end

fun rewrite_intro thy intro =
  let
    (*val _ = tracing ("Rewriting intro with registered mapping for: " ^
      commas (Symtab.keys (Pred_Compile_Preproc.get thy)))*)
    fun lookup_pred t = lookup thy (Fun_Pred.get thy) t
    val intro_t = Logic.unvarify_global (prop_of intro)
    val (prems, concl) = Logic.strip_horn intro_t
    val frees = map fst (Term.add_frees intro_t [])
    fun rewrite prem names =
      let
        (*val _ = tracing ("Rewriting premise " ^ Syntax.string_of_term_global thy prem ^ "...")*)
        val t = (HOLogic.dest_Trueprop prem)
        val (lit, mk_lit) = case try HOLogic.dest_not t of
            SOME t => (t, HOLogic.mk_not)
          | NONE => (t, I)
        val (P, args) = (strip_comb lit)
      in
        folds_map (flatten thy lookup_pred) args (names, [])
        |> map (fn (resargs, (names', prems')) =>
          let
            val prem' = HOLogic.mk_Trueprop (mk_lit (list_comb (P, resargs)))
          in (prem'::prems', names') end)
      end
    val intro_ts' = folds_map rewrite prems frees
      |> maps (fn (prems', frees') =>
        rewrite concl frees'
        |> map (fn (concl'::conclprems, _) =>
          Logic.list_implies ((flat prems') @ conclprems, concl')))
  in
    map (Drule.export_without_context o Skip_Proof.make_thm thy) intro_ts'
  end

end;
