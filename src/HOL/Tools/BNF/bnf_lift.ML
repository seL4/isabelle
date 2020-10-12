(*  Title:      HOL/Tools/BNF/bnf_lift.ML
    Author:     Julian Biendarra, TU Muenchen
    Author:     Basil Fürer, ETH Zurich
    Author:     Joshua Schneider, ETH Zurich
    Author:     Dmitriy Traytel, ETH Zurich
    Copyright   2015, 2019

Lifting of BNFs through typedefs.
*)

signature BNF_LIFT =
sig
  datatype lift_bnf_option =
    Plugins_Option of Proof.context -> Plugin_Name.filter
  | No_Warn_Wits
  | No_Warn_Transfer
  val copy_bnf:
    (((lift_bnf_option list * (binding option * (string * sort option)) list) *
      string) * thm option) * (binding * binding * binding) ->
      local_theory -> local_theory
  val copy_bnf_cmd:
    (((lift_bnf_option list * (binding option * (string * string option)) list) *
      string) * (Facts.ref * Token.src list) option) * (binding * binding * binding) ->
      local_theory -> local_theory
  val lift_bnf:
    ((((lift_bnf_option list * (binding option * (string * sort option)) list) *
      string) * term list option) * thm list option) * (binding * binding * binding) ->
      ({context: Proof.context, prems: thm list} -> tactic) list ->
      local_theory -> local_theory
  val lift_bnf_cmd:
     ((((lift_bnf_option list * (binding option * (string * string option)) list) *
       string) * string list) * (Facts.ref * Token.src list) list option) *
       (binding * binding * binding) -> local_theory -> Proof.state
end

structure BNF_Lift : BNF_LIFT =
struct

open Ctr_Sugar_Tactics
open BNF_Util
open BNF_Comp
open BNF_Def


datatype lift_bnf_option =
  Plugins_Option of Proof.context -> Plugin_Name.filter
| No_Warn_Wits
| No_Warn_Transfer;

datatype equiv_thm = Typedef | Quotient of thm

(** Util **)

fun last2 [x, y] = ([], (x, y))
  | last2 (x :: xs) = last2 xs |>> (fn y => x :: y)
  | last2 [] = raise Match;

fun strip3 thm = (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.prop_of thm)) of
    (_, [x1, x2, x3]) => (x1, x2, x3)
  | _ => error "strip3: wrong number of arguments");

val mk_Free = yield_singleton o mk_Frees;

fun TWICE t = t THEN' t;

fun prove lthy fvars tm tac =
  Goal.prove_sorry lthy (map (fst o dest_Free) fvars) [] tm (fn {context, ...} => tac context);

(** Term construction **)

fun mk_relT aT bT = aT --> bT --> HOLogic.boolT;
fun mk_relcompp r s = let
    val (rT, sT) = apply2 fastype_of (r, s);
    val ((xT, _), (_, zTs)) = apply2 dest_funT (rT, sT);
    val T = rT --> sT --> mk_relT xT (fst (dest_funT zTs));
  in Const (@{const_name relcompp}, T) $ r $ s end;
val mk_OO = fold_rev mk_relcompp;

(* option from sum *)
fun mk_MaybeT T = mk_sumT (HOLogic.unitT, T);
fun mk_Nothing T = BNF_FP_Util.mk_Inl T HOLogic.unit;
val Just_const = BNF_FP_Util.Inr_const HOLogic.unitT;
fun mk_Just tm = Just_const (fastype_of tm) $ tm;
fun Maybe_map_const T =
  let val (xT, yT) = dest_funT T in
    Const (@{const_name map_sum}, (HOLogic.unitT --> HOLogic.unitT) --> T --> mk_MaybeT xT --> mk_MaybeT yT) $
      HOLogic.id_const HOLogic.unitT
  end;
fun mk_Maybe_map tm = Maybe_map_const (fastype_of tm) $ tm;
fun fromJust_const T = Const (@{const_name sum.projr}, mk_MaybeT T --> T)

fun rel_Maybe_const T U =
  Const (@{const_name rel_sum}, (HOLogic.unitT --> HOLogic.unitT --> HOLogic.boolT) -->
    (T --> U --> HOLogic.boolT) --> mk_MaybeT T --> mk_MaybeT U --> HOLogic.boolT) $
  HOLogic.eq_const HOLogic.unitT
fun set_Maybe_const T = Const (@{const_name Basic_BNFs.setr}, mk_MaybeT T --> HOLogic.mk_setT T)

fun Inf_const T = Const (@{const_name Inf}, HOLogic.mk_setT T --> T);

fun Image_const T =
  let
    val relT = HOLogic.mk_setT (HOLogic.mk_prodT (T, T));
    val setT = HOLogic.mk_setT T;
  in Const (@{const_name Image}, relT --> setT --> setT) end;

fun bot_const T = Const (@{const_name bot}, T);

fun mk_insert x S =
  Const (@{const_name Set.insert}, fastype_of x --> fastype_of S --> fastype_of S) $ x $ S;

fun mk_vimage f s =
  let val (xT, yT) = dest_funT (fastype_of f) in
    Const (@{const_name vimage}, (xT --> yT) --> HOLogic.mk_setT yT --> HOLogic.mk_setT xT) $ f $ s
  end;

fun mk_case_prod (x, y) tm = let
     val ((x, xT), (y, yT)) = apply2 dest_Free (x, y);
     val prodT = HOLogic.mk_prodT (xT, yT);
   in HOLogic.Collect_const prodT $ (Const (@{const_name case_prod},
       (xT --> yT --> HOLogic.boolT) --> prodT --> HOLogic.boolT) $ absfree (x, xT)
       (absfree (y, yT) tm)) end;

fun mk_Trueprop_implies (ps, c) =
  Logic.list_implies (map HOLogic.mk_Trueprop ps, HOLogic.mk_Trueprop c);

fun mk_Collect (v, tm) = let val (n, T) = dest_Free v in
  HOLogic.mk_Collect (n, T, tm) end;


(** witnesses **)
fun prepare_wits is_quotient RepT wits opts alphas wits_F var_as var_as' sets lthy =
  let
    fun binder_types_until_eq V T =
      let
        fun strip (TU as Type ("fun", [T, U])) = if V = TU then [] else T :: strip U
          | strip T = if V = T then [] else
              error ("Bad type for witness: " ^ quote (Syntax.string_of_typ lthy T));
      in strip T end;

    val Iwits = the_default wits_F (Option.map (map (`(map (fn T =>
      find_index (fn U => T = U) alphas) o binder_types_until_eq RepT o fastype_of))) wits);

    val Iwits = if is_quotient then
        let
          val subsumed_Iwits =
            filter (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) wits_F) Iwits;
          val _ =  if null subsumed_Iwits orelse exists (fn No_Warn_Wits => true | _ => false) opts
            then ()
            else
              let
                val (suffix1, suffix2, be) =
                  (if length subsumed_Iwits = 1 then ("", "", "is") else ("s", "es", "are"))
              in
                subsumed_Iwits
                |> map (Syntax.pretty_typ lthy o fastype_of o snd)
                |> Pretty.big_list
                  ("The following type" ^ suffix1 ^ " of nonemptiness witness" ^ suffix2 ^
                    " of the raw type's BNF " ^ be ^ " subsumed by the existing raw witnesses:")
                |> (fn pt => Pretty.chunks [pt,
                  Pretty.para ("You do not need to lift these subsumed witnesses.")])
                |> Pretty.string_of
                |> warning
              end;
        in
          filter_out (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) wits_F) Iwits
        end
      else Iwits;

    val wit_goals = maps (BNF_Def.mk_wit_goals var_as var_as' sets) Iwits;

    val lost_wits = if is_quotient then [] else
      filter_out (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) Iwits) wits_F;

    val _ =
      if null lost_wits orelse exists (fn No_Warn_Wits => true | _ => false) opts then ()
      else
        let
          val what = (if is_quotient then "quotient type" else "typedef");
          val (suffix1, suffix2, be) =
            (if length lost_wits = 1 then ("", "", "was") else ("s", "es", "were"))
        in
          lost_wits
          |> map (Syntax.pretty_typ lthy o fastype_of o snd)
          |> Pretty.big_list
            ("The following type" ^ suffix1 ^ " of nonemptiness witness" ^ suffix2 ^
              " of the raw type's BNF " ^ be ^ " lost:")
          |> (fn pt => Pretty.chunks [pt,
            Pretty.para ("You can specify a liftable witness (e.g., a term of one of the above types\
              \ that satisfies the " ^ what ^ "'s invariant)\
              \ using the annotation [wits: <term>].")])
          |> Pretty.string_of
          |> warning
        end;
  in (Iwits, wit_goals) end;


(** transfer theorems **)

fun mk_transfer_thms' bnf_F bnf_G name consts Tss crel_def pcrel_def defs lthy = let

    val live = length (#alphas Tss);

    val (pcrel_tm, crel_tm) = apply2 (Thm.prop_of #> Logic.dest_equals #> fst #> head_of)
      (pcrel_def, crel_def);

    val (var_Qs, var_Rs) = fold Variable.declare_typ (#alphas Tss @ #deads Tss) lthy
      |> mk_Frees "Q" (map2 mk_relT (#alphas Tss) (#betas Tss))
      ||>> mk_Frees "R" (map2 mk_relT (#gammas Tss) (#deltas Tss))
      |> fst;

    (* get the "pcrel :: args_raw => rep => abs \<Rightarrow> bool" term and instantiate types *)
    val (args_raw, (rep, abs)) = pcrel_tm
      |> fastype_of
      |> binder_types
      |> last2;
    val thy = Proof_Context.theory_of lthy;
    val tyenv_match = Vartab.empty
      |> Sign.typ_match thy ((rep, #rep Tss))
      |> Sign.typ_match thy ((abs, #abs Tss));
    val args = map (Envir.subst_type tyenv_match) args_raw;
    val (pcrel_a, pcrel_b) = Envir.subst_term (tyenv_match, Vartab.empty) pcrel_tm
      |> `(subst_atomic_types (#alphas Tss @ #betas Tss ~~ #gammas Tss @ #deltas Tss));

    (* match "crel :: {?a F} \<Rightarrow> a G" with "rep_G :: {a F}" *)
    val tyenv_match = Vartab.empty |> Sign.typ_match thy
      (crel_tm |> fastype_of |> binder_types |> hd, #rep Tss);
    val crel_b = Envir.subst_term (tyenv_match, Vartab.empty) crel_tm
      |> subst_atomic_types (#alphas Tss ~~ #betas Tss)
    val crel_d = subst_atomic_types (#betas Tss ~~ #deltas Tss) crel_b;

    (* instantiate pcrel with Qs and Rs*)
    val dead_args = map binder_types args
      |> map (fn [T,U] => if T = U then SOME T else NONE | _ => NONE);
    val parametrize = let
        fun go (SOME T :: dTs) tms = HOLogic.eq_const T :: go dTs tms
          | go (_ :: dTs) (tm :: tms) = tm :: go dTs tms
          | go (_ :: dTs) tms = go dTs tms
          | go _ _ = [];
      in go dead_args end;

    val pcrel_Qs = list_comb (pcrel_b, parametrize var_Qs);
    val pcrel_Rs = list_comb (pcrel_a, parametrize var_Rs);

    (* get the order of the dead variables right *)
    val Ds0 = maps the_list dead_args;
    val permute_Ds = (mk_T_of_bnf Ds0 (#betas Tss) bnf_G, nth (binder_types (type_of pcrel_Qs)) 1)
      |> apply2 (fn Type (_, Ts) => Ts | _ => []) |> op~~ |> typ_subst_atomic;
    val Ds0 = map permute_Ds Ds0;

    (* terms for sets of the set_transfer thms *)
    val rel_sets_Q = @{map 3} (fn aT => fn bT => fn Q =>
      mk_rel 1 [aT] [bT] @{term rel_set} $ Q) (#alphas Tss) (#betas Tss) var_Qs;

    (* rewrite rules for pcrel and BNF's relator: "pcrel Q = rel_F OO crel" *)
    fun mk_pcr_rel_F_eq Ts Us pcrel vs crel =
      let
        val thm = HOLogic.mk_Trueprop (HOLogic.mk_eq (pcrel, mk_relcompp (list_comb
          (mk_rel_of_bnf (#deads Tss) (Ts Tss) (Us Tss) bnf_F, vs)) crel));
        fun tac ctxt = unfold_thms_tac ctxt (pcrel_def :: defs @ @{thm id_bnf_apply} ::
          Transfer.get_relator_eq ctxt) THEN (HEADGOAL (rtac ctxt refl))
      in prove lthy vs thm tac |> mk_abs_def end;

    val pcr_rel_F_eqs =
      [mk_pcr_rel_F_eq #alphas #betas pcrel_Qs var_Qs crel_b,
       mk_pcr_rel_F_eq #gammas #deltas pcrel_Rs var_Rs crel_d];

    (* create transfer-relations from term('s type) *)
    fun mk_transfer_rel' i tm =
      let
        fun go T' (n, q) = case T' of
            Type ("fun", [T as Type ("fun", _), U]) =>
              go U (n+1, q) |>> mk_rel_fun (fst (go T (n, q)))
          | Type ("fun", [T, U]) =>
              go T (n, q) |-> (fn x => fn st => go U st |>> mk_rel_fun x)
          | Type (@{type_name bool}, _) => (HOLogic.eq_const HOLogic.boolT, (n, q))
          | Type (@{type_name set}, _) => (nth rel_sets_Q n, (n, q))
          | Type _ => (if q then pcrel_Qs else pcrel_Rs, (n, not q))
          | TFree _ => (nth (if q then var_Qs else var_Rs) n, (n, not q))
          | _ => raise Match
      in go (fastype_of tm) (i, true) |> fst end;

    (* prove transfer rules *)
    fun prove_transfer_thm' i vars new_tm const =
      let
        val tm = HOLogic.mk_Trueprop (mk_transfer_rel' i new_tm $ #raw const $ new_tm);
        val tac = (fn ctxt => unfold_thms_tac ctxt (pcr_rel_F_eqs @ [crel_def]) THEN
          #tac const {Rs=var_Rs,Qs=var_Qs} ctxt);
      in prove lthy vars tm tac end;
    val prove_transfer_thm = prove_transfer_thm' 0;

    (* map transfer: "((Q ===> R) ===> pcr_G Q ===> pcr_G R) map_F' map_G" *)
    val map_G = mk_map_of_bnf Ds0 (#betas Tss) (#deltas Tss) bnf_G;
    val map_transfer = prove_transfer_thm (var_Qs @ var_Rs) map_G (#map consts);

    (* pred_transfer: "((Q ===> (=)) ===> pcr_G Q ===> (=)) pred_F' pred_G" *)
    val pred_G = mk_pred_of_bnf Ds0 (#betas Tss) bnf_G;
    val pred_transfer = #pred consts |> Option.map (fn p =>
      ("pred", [prove_transfer_thm (var_Qs @ var_Rs) pred_G p]));

    (* rel_transfer: "((Q ===> R ===> (=)) ===> pcr_G Q ===> pcr_G R ===> (=)) rel_F' rel_G" *)
    val rel_G = mk_rel_of_bnf Ds0 (#betas Tss) (#deltas Tss) bnf_G;
    val rel_transfer = prove_transfer_thm (var_Qs @ var_Rs) rel_G (#rel consts);

    (* set_transfer: "(pcr_G Q ===> rel_set Q) set_F' set_G" *)
    val sets_G = mk_sets_of_bnf (replicate live Ds0) (replicate live (#betas Tss)) bnf_G;
    fun mk_set_transfer i set_G raw tac = prove_transfer_thm' i var_Qs set_G {raw=raw, tac=tac};
    val sets_transfer = @{map 4} mk_set_transfer
      (0 upto (live-1)) sets_G (#raws (#sets consts)) (#tacs (#sets consts));

    (* export transfer theorems *)
    val transform = Morphism.thm (Morphism.thm_morphism "BNF" (unfold_thms lthy defs)) |> map;
    val b = Binding.qualified_name name;
    val qualify =
      let val qs = Binding.path_of b;
      in fold_rev (fn (s, mand) => Binding.qualify mand s) qs end;
    fun mk_binding n = Binding.name (n ^ "_transfer_raw")
      |> Binding.qualify true (Binding.name_of b) |> qualify;
    val notes = [("map", [map_transfer]), ("rel", [rel_transfer])] @ the_list pred_transfer @
      [("set", sets_transfer)] |> map (fn (n, thms) =>
        ((mk_binding n, []), [(transform thms, @{attributes [transfer_rule]})]));

  in lthy |> Local_Theory.notes notes |> snd end;

(* transfer theorems for map, pred (in case of a typedef), rel and sets *)
fun mk_transfer_thms quiet bnf_F bnf_G name consts thm Tss defs lthy = let

    fun mk_crel_def quot_thm =
      (case thm of
        Quotient equiv => @{thm Quotient_crel_quotient} OF [quot_thm, equiv]
      | Typedef => hd ([quot_thm] RL @{thms Quotient_crel_typedef Quotient_crel_typecopy}));
    fun no_quotient _ = [Pretty.para ("No quotient theorem has been registered for " ^
        Binding.name_of (name_of_bnf bnf_G) ^ "."),
      Pretty.para "Use setup_lifting to register a quotient or type definition theorem."];
    fun wrong_quotient T lthy = [Pretty.para ("A wrong quotient theorem has been registered for " ^
        Binding.name_of (name_of_bnf bnf_G) ^ "."),
      Pretty.para ("Expected raw type " ^
        Pretty.string_of (Syntax.pretty_typ lthy (T_of_bnf bnf_F)) ^
        " but the quotient theorem has raw type " ^
        Pretty.string_of (Syntax.pretty_typ lthy T) ^ "."),
      Pretty.para "Use setup_lifting to register a different quotient or type definition theorem."];
    fun pcr_why _ = [Pretty.para ("The pcr_" ^ Binding.name_of (name_of_bnf bnf_G) ^
      " relator has not been defined.")];
    fun warn_transfer why lthy =
      (Pretty.para "The transfer theorems can't be generated:" ::  why lthy)
      |> Pretty.chunks |> Pretty.string_of |> warning |> K lthy;
    fun maybe_warn_transfer why = not quiet ? warn_transfer why;
  in
    case Lifting_Info.lookup_quotients lthy name of
      SOME {pcr_info, quot_thm} =>
        (let
          val crel_def = mk_crel_def quot_thm;
          val rty = Lifting_Util.quot_thm_rty_qty quot_thm |> fst;
          val thy = Proof_Context.theory_of lthy;
        in
          if Sign.typ_instance thy (rty, T_of_bnf bnf_F) then
          (case pcr_info of
            SOME {pcrel_def, ...} =>
              mk_transfer_thms' bnf_F bnf_G name consts Tss crel_def pcrel_def defs lthy
          | _ => maybe_warn_transfer pcr_why lthy)
          else maybe_warn_transfer (wrong_quotient rty) lthy
        end)
    | _ => maybe_warn_transfer no_quotient lthy
  end;


(** typedef_bnf **)

fun mk_typedef_transfer_tacs bnf_F bnf_G thms old_defs
  map_raw rel_raw pred_raw sets_raw = let

    val live = live_of_bnf bnf_G;
    val Abs_G_inverse = @{thm type_definition.Abs_inverse} OF [#typedef thms];
    val Rep_G = @{thm type_definition.Rep} OF [#typedef thms];

    fun common_tac addefs tac = (fn _ => fn ctxt =>
      HEADGOAL (EVERY' [SELECT_GOAL (unfold_thms_tac ctxt addefs),
        REPEAT_DETERM o rtac ctxt rel_funI,
        SELECT_GOAL (unfold_thms_tac ctxt @{thms o_apply}),
        REPEAT_DETERM o eresolve_tac ctxt @{thms relcomppE exE conjE},
        hyp_subst_tac ctxt]) THEN tac ctxt)

    fun map_tac ctxt = (HEADGOAL o EVERY')
      [rtac ctxt @{thm relcomppI},
      etac ctxt (mk_rel_funDN (live+1) (map_transfer_of_bnf bnf_F)),
      REPEAT_DETERM_N live o assume_tac ctxt,
      SELECT_GOAL (unfold_thms_tac ctxt [Abs_G_inverse OF [#map_closed thms] OF [Rep_G]]),
      REPEAT_DETERM o rtac ctxt refl];
    val map_tac = common_tac [#map old_defs] map_tac;

    fun rel_tac ctxt =
      HEADGOAL (etac ctxt (mk_rel_funDN (live+2) (rel_transfer_of_bnf bnf_F)) THEN'
        REPEAT_DETERM_N (live+1) o assume_tac ctxt);
    val rel_tac = common_tac (#rel old_defs :: @{thms vimage2p_def}) rel_tac;

    fun pred_tac ctxt =
      HEADGOAL (etac ctxt (mk_rel_funDN (live+1) (pred_transfer_of_bnf bnf_F)) THEN'
        REPEAT_DETERM_N live o (assume_tac ctxt));
    val pred_tac = common_tac [#pred old_defs] pred_tac;

    fun set_tac set_transfer_thm ctxt =
      HEADGOAL (etac ctxt (rel_funD OF [set_transfer_thm]));
    fun mk_set_tac set_def set_transfer = common_tac [set_def] (set_tac set_transfer);
    val set_tacs = map2 mk_set_tac (#sets old_defs) (set_transfer_of_bnf bnf_F);

  in {map={raw=map_raw,tac=map_tac},rel={raw=rel_raw,tac=rel_tac},
      sets={raws=sets_raw,tacs=set_tacs},pred=SOME{raw=pred_raw,tac=pred_tac}} end;

fun typedef_bnf thm wits specs map_b rel_b pred_b opts lthy =
  let
    val plugins =
      get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts)
        |> the_default Plugin_Name.default_filter;

    (* extract Rep Abs F RepT AbsT *)
    val (Rep_G, Abs_G, F) = strip3 thm;
    val typ_Abs_G = dest_funT (fastype_of Abs_G);
    val RepT = fst typ_Abs_G; (* F *)
    val AbsT = snd typ_Abs_G; (* G *)
    val AbsT_name = fst (dest_Type AbsT);
    val tvs = AbsT |> dest_Type |> snd |> map (fst o dest_TVar);
    val alpha0s = map (TFree o snd) specs;

    val _ = length tvs = length alpha0s orelse
      error ("Expected " ^ string_of_int (length tvs) ^ " type argument(s) to " ^ quote AbsT_name);

    (* instantiate the new type variables newtvs to oldtvs *)
    val subst = subst_TVars (tvs ~~ alpha0s);
    val typ_subst = typ_subst_TVars (tvs ~~ alpha0s);

    val Rep_G = subst Rep_G;
    val Abs_G = subst Abs_G;
    val F = subst F;
    val RepT = typ_subst RepT;
    val AbsT = typ_subst AbsT;

    fun flatten_tyargs Ass =
      map dest_TFree alpha0s
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);

    val Ds0 = filter (is_none o fst) specs |> map snd;

    (* get the bnf for RepT *)
    val ((bnf_F, (deads, alphas)), ((_, unfolds), lthy)) =
      bnf_of_typ true Dont_Inline (Binding.qualify true AbsT_name) flatten_tyargs []
        Ds0 RepT ((empty_comp_cache, empty_unfolds), lthy);

    val set_bs =
      map (fn T => find_index (fn U => T = U) alpha0s) alphas
      |> map (the_default Binding.empty o fst o nth specs);

    val _ = (case alphas of [] => error "No live variables" | _ => ());

    val defs = #map_unfolds unfolds @ flat (#set_unfoldss unfolds) @ #rel_unfolds unfolds @ #pred_unfolds unfolds;

    (* number of live variables *)
    val live = length alphas;

    (* state the three required properties *)
    val sorts = map Type.sort_of_atyp alphas;
    val names_lthy = fold Variable.declare_typ (alphas @ deads) lthy;
    val (((alphas', betas), betas'), names_lthy) = names_lthy
      |> mk_TFrees' sorts
      ||>> mk_TFrees' sorts
      ||>> mk_TFrees' sorts;

    val map_F = mk_map_of_bnf deads alphas betas bnf_F;

    val (typ_fs, typ_aF) = fastype_of map_F |> strip_typeN live ||> domain_type;
    val typ_pairs = map HOLogic.mk_prodT (alphas ~~ alphas');
    val typ_subst_pair = typ_subst_atomic (alphas ~~ typ_pairs);
    val typ_pair = typ_subst_pair RepT;
    val subst_b = subst_atomic_types (alphas ~~ betas);
    val subst_a' = subst_atomic_types (alphas ~~ alphas');
    val subst_pair = subst_atomic_types (alphas ~~ typ_pairs);
    val aF_set = F;
    val aF_set' = subst_a' F;
    val pairF_set = subst_pair F;
    val bF_set = subst_b F;
    val map_F_fst = mk_map_of_bnf deads typ_pairs alphas bnf_F;
    val map_F_snd = mk_map_of_bnf deads typ_pairs alphas' bnf_F
    val sets_F_pairs = mk_sets_of_bnf (replicate live deads) (replicate live typ_pairs) bnf_F
    val wits_F = mk_wits_of_bnf
      (replicate (nwits_of_bnf bnf_F) deads)
      (replicate (nwits_of_bnf bnf_F) alphas) bnf_F;

    (* val map_closed_F = @{term "\<And>f x. x \<in> F \<Longrightarrow> map_F f x \<in> F"}; *)
    val (var_fs, names_lthy) = mk_Frees "f" typ_fs names_lthy;
    val (var_x, names_lthy) = mk_Frees "x" [typ_aF] names_lthy |>> the_single;
    val mem_x = HOLogic.mk_Trueprop (HOLogic.mk_mem (var_x, aF_set));
    val map_f = list_comb (map_F, var_fs);
    val mem_map = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_f $ var_x, bF_set));
    val imp_map = Logic.mk_implies (mem_x, mem_map);
    val map_closed_F = fold_rev Logic.all var_fs (Logic.all var_x imp_map);

    (* val zip_closed_F =
      @{term "\<And>z. \<lbrakk>map_F fst z \<in> F; map_F snd z \<in> F\<rbrakk> \<Longrightarrow>
        \<exists>z' \<in> F. set_F z' \<subseteq> set_F z \<and> map_F fst z' = map_F fst z \<and> map_F snd z' = map_F snd z"}; *)
    val (var_z, names_lthy) = mk_Free "z" typ_pair names_lthy;
    val (var_z', names_lthy) = mk_Free "z'" typ_pair names_lthy;
    val (pairs, names_lthy) = mk_Frees "tmp" typ_pairs names_lthy;

    fun mk_map mfs f z = Term.list_comb (mfs, map (fst o Term.strip_comb o f) pairs) $ z;
    fun mk_set var = map (fn t => t $ var) sets_F_pairs;

    val (map_fst', map_fst) = apply2 (mk_map map_F_fst HOLogic.mk_fst) (var_z', var_z);
    val (map_snd', map_snd) = apply2 (mk_map map_F_snd HOLogic.mk_snd) (var_z', var_z);
    val mem_map_fst = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_fst, aF_set));
    val mem_map_snd = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_snd, aF_set'));
    val ex_conj = foldr1 HOLogic.mk_conj (map2 mk_leq (mk_set var_z') (mk_set var_z) @
      [HOLogic.mk_eq (map_fst', map_fst), HOLogic.mk_eq (map_snd', map_snd)]);
    val zip_concl = HOLogic.mk_Trueprop (mk_Bex pairF_set (absfree (dest_Free var_z') ex_conj));
    val zip_closed_F = Logic.all var_z (Logic.list_implies ([mem_map_fst, mem_map_snd], zip_concl));

    (* val wit_closed_F = @{term "wit_F a \<in> F"}; *)
    val (var_as, names_lthy) = mk_Frees "a" alphas names_lthy;
    val (var_bs, _) = mk_Frees "a" alphas names_lthy;
    val sets = mk_sets_of_bnf (replicate live deads) (replicate live alphas) bnf_F;
    val (Iwits, wit_goals) =
      prepare_wits false RepT wits opts alphas wits_F var_as var_bs sets lthy;
    val wit_closed_Fs =
      Iwits |> map (fn (I, wit_F) =>
        let
          val vars = map (nth var_as) I;
          val wit_a = list_comb (wit_F, vars);
        in fold_rev Logic.all vars (HOLogic.mk_Trueprop (HOLogic.mk_mem (wit_a, aF_set))) end);

    val goals = [map_closed_F, zip_closed_F] @ wit_closed_Fs @
      (case wits of NONE => [] | _ => wit_goals);

    fun after_qed ([map_closed_thm] :: [zip_closed_thm] :: wit_thmss) lthy =
          let
            val (wit_closed_thms, wit_thms) =
              (case wits of
                NONE => (map the_single wit_thmss, wit_thms_of_bnf bnf_F)
              | _ => chop (length wit_closed_Fs) (map the_single wit_thmss))

            (*  construct map set bd rel wit *)
            (* val map_G = @{term "\<lambda>f. Abs_G o map_F f o Rep_G"}; *)
            val Abs_Gb = subst_b Abs_G;
            val map_G = fold_rev lambda var_fs
                (HOLogic.mk_comp (HOLogic.mk_comp (Abs_Gb, map_f), Rep_G));
            val map_raw = fold_rev lambda var_fs map_f;

            (* val sets_G = [@{term "set_F o Rep_G"}]; *)
            val sets_F = mk_sets_of_bnf (replicate live deads) (replicate live alphas) bnf_F;
            val sets_G = map (fn set_F => HOLogic.mk_comp (set_F, Rep_G)) sets_F;

            (* val bd_G = @{term "bd_F"}; *)
            val bd_F = mk_bd_of_bnf deads alphas bnf_F;
            val bd_G = bd_F;

            (* val rel_G = @{term "\<lambda>R. BNF_Def.vimage2p Rep_G Rep_G (rel_F R)"}; *)
            val rel_F = mk_rel_of_bnf deads alphas betas bnf_F;
            val (typ_Rs, _) = strip_typeN live (fastype_of rel_F);

            val (var_Rs, names_lthy) = mk_Frees "R" typ_Rs lthy;
            val Rep_Gb = subst_b Rep_G;
            val rel_G = fold_rev absfree (map dest_Free var_Rs)
              (mk_vimage2p Rep_G Rep_Gb $ list_comb (rel_F, var_Rs));
            val rel_raw = fold_rev absfree (map dest_Free var_Rs) (list_comb (rel_F, var_Rs));

            (* val pred_G = @{term "\<lambda>P. pred_F P o Rep_G"}; *)
            val pred_F = mk_pred_of_bnf deads alphas bnf_F;
            val (typ_Ps, _) = strip_typeN live (fastype_of pred_F);

            val (var_Ps, names_lthy) = mk_Frees "P" typ_Ps names_lthy;
            val pred_G = fold_rev absfree (map dest_Free var_Ps)
              (HOLogic.mk_comp (list_comb (pred_F, var_Ps), Rep_G));
            val pred_raw = fold_rev absfree (map dest_Free var_Ps) (list_comb (pred_F, var_Ps));

            (* val wits_G = [@{term "Abs_G o wit_F"}]; *)
            val (var_as, _) = mk_Frees "a" alphas names_lthy;
            val wits_G =
              map (fn (I, wit_F) =>
                let
                  val vs = map (nth var_as) I;
                in fold_rev absfree (map dest_Free vs) (Abs_G $ (list_comb (wit_F, vs))) end)
              Iwits;

            (* tactics *)
            val Rep_thm = thm RS @{thm type_definition.Rep};
            val Abs_inverse_thm = thm RS @{thm type_definition.Abs_inverse};
            val Abs_inject_thm = thm RS @{thm type_definition.Abs_inject};
            val Rep_cases_thm = thm RS @{thm type_definition.Rep_cases};
            val Rep_inverse_thm = thm RS @{thm type_definition.Rep_inverse};

            fun map_id0_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt ext,
                SELECT_GOAL (unfold_thms_tac ctxt [map_id0_of_bnf bnf_F, id_apply, o_apply,
                  Rep_inverse_thm]),
                rtac ctxt refl]);

            fun map_comp0_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt ext,
                SELECT_GOAL (unfold_thms_tac ctxt [map_comp0_of_bnf bnf_F, o_apply,
                  Rep_thm RS (map_closed_thm RS Abs_inverse_thm)]),
                rtac ctxt refl]);

            fun map_cong0_tac ctxt =
              HEADGOAL (EVERY' ([SELECT_GOAL (unfold_thms_tac ctxt [o_apply]),
                rtac ctxt (([Rep_thm RS map_closed_thm, Rep_thm RS map_closed_thm] MRS
                  Abs_inject_thm) RS iffD2),
                rtac ctxt (map_cong0_of_bnf bnf_F)] @ replicate live (Goal.assume_rule_tac ctxt)));

            val set_map0s_tac =
              map (fn set_map => fn ctxt =>
                HEADGOAL (EVERY' [rtac ctxt ext,
                  SELECT_GOAL (unfold_thms_tac ctxt [set_map, o_apply,
                    Rep_thm RS (map_closed_thm RS Abs_inverse_thm)]),
                  rtac ctxt refl]))
              (set_map_of_bnf bnf_F);

            fun card_order_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_card_order_of_bnf bnf_F));

            fun cinfinite_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_cinfinite_of_bnf bnf_F));

            val set_bds_tac =
              map (fn set_bd => fn ctxt =>
                HEADGOAL (EVERY' [SELECT_GOAL (unfold_thms_tac ctxt [o_apply]), rtac ctxt set_bd]))
              (set_bd_of_bnf bnf_F);

            fun le_rel_OO_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt @{thm vimage2p_relcompp_mono},
                rtac ctxt ((rel_OO_of_bnf bnf_F RS sym) RS @{thm ord_eq_le_trans}),
                rtac ctxt @{thm order_refl}]);

            fun rel_OO_Grp_tac ctxt =
              HEADGOAL (EVERY' ([SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt ext))),
                SELECT_GOAL (unfold_thms_tac ctxt [@{thm OO_Grp_alt}, mem_Collect_eq,
                  o_apply, @{thm vimage2p_def}, in_rel_of_bnf bnf_F, Bex_def, mem_Collect_eq]),
                rtac ctxt iffI,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [exE, conjE]))),
                forward_tac ctxt
                  [zip_closed_thm OF (replicate 2 (Rep_thm RSN (2, @{thm ssubst_mem})))],
                assume_tac ctxt,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [bexE, conjE]))),
                etac ctxt Rep_cases_thm,
                hyp_subst_tac ctxt,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt exI))),
                rtac ctxt conjI] @
                replicate live
                  (EVERY' [TRY o rtac ctxt conjI, etac ctxt @{thm order_trans}, assume_tac ctxt]) @
                [SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt conjI))),
                REPEAT_DETERM_N 2 o EVERY'
                  [rtac ctxt (trans OF [iffD2 OF [Abs_inject_thm OF
                      [map_closed_thm OF [Rep_thm], Rep_thm]], Rep_inverse_thm]),
                  etac ctxt trans, assume_tac ctxt],
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [exE, conjE]))),
                rtac ctxt exI,
                rtac ctxt conjI] @
                replicate (live-1) (rtac ctxt conjI THEN' assume_tac ctxt) @
                [assume_tac ctxt,
                rtac ctxt conjI,
                REPEAT_DETERM_N 2 o EVERY'
                  [rtac ctxt (iffD1 OF [Abs_inject_thm OF [map_closed_thm OF [Rep_thm], Rep_thm]]),
                  etac ctxt (Rep_inverse_thm RS sym RSN (2, trans))]]));

            fun pred_set_tac ctxt =
              HEADGOAL (EVERY'
                [rtac ctxt (pred_set_of_bnf bnf_F RS @{thm arg_cong[of _ _ "\<lambda>f. f \<circ> _"]} RS trans),
                SELECT_GOAL (unfold_thms_tac ctxt (@{thms Ball_comp_iff conj_comp_iff})),
                rtac ctxt refl]);

            fun wit_tac ctxt =
              HEADGOAL (EVERY'
                (map (fn thm => (EVERY'
                  [SELECT_GOAL (unfold_thms_tac ctxt (o_apply ::
                    (wit_closed_thms RL [Abs_inverse_thm]))),
                  dtac ctxt thm, assume_tac ctxt]))
                wit_thms));

            val tactics = [map_id0_tac, map_comp0_tac, map_cong0_tac] @ set_map0s_tac @
              [card_order_bd_tac, cinfinite_bd_tac] @ set_bds_tac @
              [le_rel_OO_tac, rel_OO_Grp_tac, pred_set_tac];

            val (bnf_G, lthy) = bnf_def Dont_Inline (user_policy Note_Some) true I
              tactics wit_tac NONE map_b rel_b pred_b set_bs
              (((((((Binding.empty, AbsT), map_G), sets_G), bd_G), wits_G), SOME rel_G), SOME pred_G)
              lthy;

            val old_defs =
              {sets = set_defs_of_bnf bnf_G, map = map_def_of_bnf bnf_G, rel = rel_def_of_bnf bnf_G,
               pred = pred_def_of_bnf bnf_G};

            val unfold_morphism = Morphism.thm_morphism "BNF" (unfold_thms lthy defs);
            val (bnf_G, lthy) = morph_bnf_defs unfold_morphism bnf_G
              |> (fn bnf => note_bnf_defs bnf lthy);

            val quiet = exists (fn No_Warn_Transfer => true | _ => false) opts;

            val transfer_consts = mk_typedef_transfer_tacs bnf_F bnf_G
              {map_closed=map_closed_thm,typedef=thm} old_defs map_raw rel_raw pred_raw sets_F;
          in
            lthy |> BNF_Def.register_bnf plugins AbsT_name bnf_G |>
              mk_transfer_thms quiet bnf_F bnf_G AbsT_name transfer_consts Typedef
              {abs=typ_subst_atomic (alphas ~~ alphas') AbsT, rep=RepT, Ds0=map TFree Ds0,
               deads = deads, alphas=alphas, betas=alphas', gammas=betas, deltas=betas'} defs
          end
      | after_qed _ _ = raise Match;
  in
    (goals, after_qed, defs, lthy)
  end;


(** quotient_bnf **)

fun mk_quotient_transfer_tacs bnf_F Tss live qthms thms set_F'_thmss old_defs
  inst_REL_pos_distrI map_raw rel_raw sets_raw = let

    fun common_tac ctxt addefs = unfold_thms_tac ctxt (#REL qthms :: addefs) THEN
      (REPEAT_DETERM o HEADGOAL) (rtac ctxt rel_funI);

    (* quotient.map_transfer tactic *)
    val map_F_transfer = map_transfer_of_bnf bnf_F |> mk_rel_funDN (live+1);
    fun map_transfer_q _ ctxt =
      common_tac ctxt (#map old_defs :: @{thms o_def}) THEN
      (HEADGOAL o EVERY') [REPEAT_DETERM o eresolve_tac ctxt @{thms relcomppE},
        rtac ctxt @{thm relcomppI[rotated]}, hyp_subst_tac ctxt THEN' EVERY'
        (map (rtac ctxt) [#rel_abs qthms, #map_F_rsp thms, (#rep_abs_rsp qthms), (#reflp qthms)]),
        hyp_subst_tac ctxt, rtac ctxt map_F_transfer, REPEAT_DETERM_N (live+1) o assume_tac ctxt];

    (* quotient.rel_transfer tactic *)
    val rel_F_maps = rel_map_of_bnf bnf_F;
    val rel_F_map_iffD2s = map (fn thm => thm RS @{thm iffD2}) rel_F_maps;
    fun inst_REL_pos_distrI_order_refls vs aTs bTs ctxt = inst_REL_pos_distrI live vs aTs bTs ctxt
      OF (replicate (live+1) asm_rl @ replicate live @{thm order_refl});
    fun rel_transfer_q {Qs, Rs} ctxt = EVERY
      [common_tac ctxt [#rel old_defs, @{thm vimage2p_def}],
      HEADGOAL (rtac ctxt iffI),
      (REPEAT_DETERM o ALLGOALS)
        (eresolve_tac ctxt @{thms exE conjE relcomppE} ORELSE' hyp_subst_tac ctxt),
      (HEADGOAL o EVERY')
        [REPEAT_DETERM o dtac ctxt @{thm rel_fun_rel_OO1},
        rtac ctxt (inst_REL_pos_distrI 0 (map mk_conversep Qs) (#betas Tss) (#alphas Tss) ctxt),
        rtac ctxt @{thm relcomppI},
        rtac ctxt (#symp qthms),
        rtac ctxt (#map_F_rsp thms),
        rtac ctxt (#rep_abs_rsp qthms),
        rtac ctxt (#reflp qthms),
        rtac ctxt @{thm relcomppI},
        rtac ctxt (rel_flip_of_bnf bnf_F RS @{thm iffD1}),
        rtac ctxt (nth rel_F_map_iffD2s 0),
        rtac ctxt (nth rel_F_map_iffD2s 1),
        etac ctxt (#rel_monoD_rotated thms)],
      (REPEAT_DETERM_N live o HEADGOAL o EVERY')
        [rtac ctxt @{thm predicate2I},
        rtac ctxt @{thm conversepI},
        rtac ctxt @{thm Basic_BNFs.rel_sum_simps(4)[THEN iffD2]},
        etac ctxt @{thm conversepI}],
      (HEADGOAL o EVERY')
        [rtac ctxt (inst_REL_pos_distrI_order_refls Rs (#gammas Tss) (#deltas Tss) ctxt),
        (SELECT_GOAL o REPEAT_DETERM o HEADGOAL) (etac ctxt @{thm relcomppI}),
        rtac ctxt @{thm relcomppI[rotated]},
        rtac ctxt (#map_F_rsp thms),
        rtac ctxt (#rep_abs_rsp qthms OF [#reflp qthms]),
        SELECT_GOAL (unfold_thms_tac ctxt (@{thms rel_sum_simps} @ rel_F_maps)),
        assume_tac ctxt],
      (REPEAT_DETERM_N (2*live) o HEADGOAL)
        (rtac ctxt @{thm rel_sum_eq2_nonempty} ORELSE' rtac ctxt @{thm rel_sum_eq3_nonempty}),
      (REPEAT_DETERM_N live)
        (unfold_thms_tac ctxt @{thms sum.rel_compp[symmetric] eq_OO} THEN
        HEADGOAL (etac ctxt @{thm sum.rel_mono[OF order_refl]})),
      (HEADGOAL o EVERY')
        [(SELECT_GOAL o REPEAT_DETERM o HEADGOAL) (dtac ctxt @{thm rel_fun_rel_OO2}),
        rtac ctxt (inst_REL_pos_distrI 0 Qs (#alphas Tss) (#betas Tss) ctxt),
        rtac ctxt @{thm relcomppI},
        rtac ctxt (#reflp qthms),
        rtac ctxt @{thm relcomppI},
        rtac ctxt (nth rel_F_map_iffD2s 0),
        rtac ctxt (nth rel_F_map_iffD2s 1),
        etac ctxt (#rel_monoD_rotated thms)],
      (REPEAT_DETERM_N live o HEADGOAL o EVERY')
        [rtac ctxt @{thm predicate2I}, rtac ctxt @{thm rel_sum.intros(2)}, assume_tac ctxt],
      (HEADGOAL o EVERY')
        [rtac ctxt
          (inst_REL_pos_distrI_order_refls (map mk_conversep Rs) (#deltas Tss) (#gammas Tss) ctxt),
        rtac ctxt @{thm relcomppI},
        etac ctxt (rotate_prems 1 (#transp qthms)),
        rtac ctxt (#map_F_rsp thms),
        rtac ctxt (#rep_abs_rsp qthms OF [#reflp qthms]),
        etac ctxt @{thm relcomppI},
        rtac ctxt @{thm relcomppI},
        etac ctxt (#transp qthms),
        rtac ctxt (#symp qthms),
        rtac ctxt (#map_F_rsp thms),
        rtac ctxt (#rep_abs_rsp qthms),
        rtac ctxt (#reflp qthms),
        rtac ctxt @{thm relcomppI[rotated]},
        rtac ctxt (#reflp qthms),
        rtac ctxt (rel_flip_of_bnf bnf_F RS @{thm iffD1}),
        rtac ctxt (nth rel_F_map_iffD2s 0),
        rtac ctxt (nth rel_F_map_iffD2s 1),
        etac ctxt (#rel_monoD_rotated thms)],
      (REPEAT_DETERM_N live o HEADGOAL o EVERY')
        [rtac ctxt @{thm predicate2I},
        rtac ctxt @{thm conversepI},
        rtac ctxt @{thm rel_sum.intros(2)},
        etac ctxt @{thm conversepI}],
      (REPEAT_DETERM_N (2*live) o HEADGOAL)
        (rtac ctxt @{thm rel_sum_eq2_nonempty} ORELSE' rtac ctxt @{thm rel_sum_eq3_nonempty}),
      (REPEAT_DETERM_N live o EVERY)
        [unfold_thms_tac ctxt @{thms sum.rel_compp[symmetric] eq_OO},
        HEADGOAL (etac ctxt @{thm sum.rel_mono[OF order_refl]})]];

    (* quotient.set_transfer tactics *)
    fun set_transfer_q set_G_def set_F'_thms _ ctxt =
      let val set_F'_rsp = mk_rel_funDN 1 (#set_F'_respect set_F'_thms) in
        common_tac ctxt (set_G_def :: @{thms o_def}) THEN
        (HEADGOAL o EVERY')
          [etac ctxt @{thm relcomppE}, hyp_subst_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt
            [set_F'_rsp OF [#rep_abs qthms] OF [#reflp qthms], @{thm rel_set_def}]),
          dtac ctxt (#rel_F_rel_F' thms), rtac ctxt conjI] THEN
        (REPEAT_DETERM_N 2 o HEADGOAL o EVERY')
          [SELECT_GOAL (unfold_thms_tac ctxt [#rel_F'_set thms]),
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          REPEAT_DETERM o dtac ctxt (mk_sym set_F'_rsp),
          SELECT_GOAL (unfold_thms_tac ctxt [#set_map_F' set_F'_thms]),
          rtac ctxt ballI, dtac ctxt @{thm equalityD1[THEN subsetD]}, assume_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms image_iff}),
          etac ctxt bexE, dtac ctxt set_mp, assume_tac ctxt,
          SELECT_GOAL (unfold_thms_tac ctxt @{thms mem_Collect_eq case_prod_beta}),
          rtac ctxt bexI, hyp_subst_tac ctxt, assume_tac ctxt, etac ctxt @{thm hypsubst},
          etac ctxt @{thm imageI}, assume_tac ctxt]
      end;
  in
     {map={raw=map_raw, tac=map_transfer_q},
      rel={raw=rel_raw, tac=rel_transfer_q},
      sets={raws=sets_raw,tacs=map2 set_transfer_q (#sets old_defs) set_F'_thmss},
      pred=NONE}
  end;


fun quotient_bnf (equiv_thm, quot_thm) wits specs map_b rel_b pred_b opts lthy =
  let
    (* extract rep_G and abs_G *)
    val (equiv_rel, abs_G, rep_G) = strip3 quot_thm;
    val (repT, absT) = dest_funT (fastype_of abs_G); (* ("?'a F", "?'a G") *)
    val absT_name = fst (dest_Type absT);

    val tvs = map (fst o dest_TVar) (snd (dest_Type absT));
    val _ = length tvs = length specs orelse
      error ("Expected " ^ string_of_int (length tvs) ^
        " type argument" ^ (if (length tvs) = 1 then "" else "s") ^ " to " ^ quote absT_name);

    (* instantiate TVars *)
    val alpha0s = map (TFree o snd) specs;
    val typ_subst = typ_subst_TVars (tvs ~~ alpha0s);
    val (repT, absT) = apply2 typ_subst (repT, absT);

    (* get the bnf for RepT *)
    val Ds0 = filter (is_none o fst) specs |> map snd;

    fun flatten_tyargs Ass =
      map dest_TFree alpha0s |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);

    val ((bnf_F, (deads, alphas)), ((_, unfolds), lthy)) =
      bnf_of_typ true Dont_Inline (Binding.qualify true absT_name) flatten_tyargs
        [] Ds0 repT ((empty_comp_cache, empty_unfolds), lthy);
    val live = length alphas;
    val _ = (if live = 0 then error "No live variables" else ());

    val defs = #map_unfolds unfolds @ flat (#set_unfoldss unfolds) @ #rel_unfolds unfolds;
    val set_bs =
      map (fn T => find_index (fn U => T = U) alpha0s) alphas
      |> map (the_default Binding.empty o fst o nth specs);

    (* create and instantiate all the needed type variables *)
    val subst = subst_TVars (tvs ~~ alpha0s);
    val (abs_G, rep_G) = apply2 subst (abs_G, rep_G);

    val sorts = map Type.sort_of_atyp alphas;
    val (((betas, gammas), deltas), names_lthy) = fold Variable.declare_typ (alphas @ deads) lthy
      |> mk_TFrees' sorts
      ||>> mk_TFrees' sorts
      ||>> mk_TFrees' sorts;

    fun subst_Ts tm Ts = subst_atomic_types (alphas ~~ Ts) tm;
    val subst_b = subst_atomic_types (alphas ~~ betas);
    val subst_Maybe = subst_atomic_types o map (swap o `mk_MaybeT);
    val equiv_rel_a = subst equiv_rel;
    val map_F = mk_map_of_bnf deads alphas betas bnf_F;
    val rel_F_ab = mk_rel_of_bnf deads alphas betas bnf_F;
    val rel_F_bc = mk_rel_of_bnf deads betas gammas bnf_F;
    val rel_F_ac = mk_rel_of_bnf deads alphas gammas bnf_F;
    val rel_F_option = mk_rel_of_bnf deads (map mk_MaybeT alphas) (map mk_MaybeT betas) bnf_F;
    val sets_F = mk_sets_of_bnf (replicate live deads) (replicate live alphas) bnf_F;
    val wits_F = mk_wits_of_bnf
      (replicate (nwits_of_bnf bnf_F) deads) (replicate (nwits_of_bnf bnf_F) alphas) bnf_F;

    val (typ_fs, (typ_aF, typ_bF)) = strip_typeN live (fastype_of map_F) ||> dest_funT;
    val typ_MaybeF = typ_subst_atomic (alphas ~~ map mk_MaybeT alphas) typ_aF;
    val typ_a_sets = map HOLogic.mk_setT alphas;
    val typ_pairs = map HOLogic.mk_prodT (alphas ~~ betas);
    val typ_fs' = map (typ_subst_atomic (map (swap o `mk_MaybeT) betas)) typ_fs;

    (* create all the needed variables *)
    val ((((((((((((((((((((((var_Ps, var_Qs), var_Rs), var_x), var_x'), var_y), var_y'), var_mx),
      var_As), var_As'), var_Ss), var_Bs), var_as), var_as'), var_bs), var_bs'), var_R), var_fs),
      var_fs'), var_gs), var_gs'), var_z), var_ts) = names_lthy
        |> mk_Frees "Ps" (map2 mk_relT alphas betas)
        ||>> mk_Frees "Qs" (map2 mk_relT betas gammas)
        ||>> mk_Frees "Rs" (map2 mk_relT alphas gammas)
        ||>> mk_Free "x" typ_aF
        ||>> mk_Free "x'" typ_aF
        ||>> mk_Free "y" typ_bF
        ||>> mk_Free "y'" (typ_subst_atomic (alphas ~~ gammas) typ_aF)
        ||>> mk_Free "mx" typ_MaybeF
        ||>> mk_Frees "As" typ_a_sets
        ||>> mk_Frees "As'" typ_a_sets
        ||>> mk_Frees "Ss" (map HOLogic.mk_setT typ_a_sets)
        ||>> mk_Frees "Bs" (map HOLogic.mk_setT betas)
        ||>> mk_Frees "as" alphas
        ||>> mk_Frees "as'" alphas
        ||>> mk_Frees "bs" betas
        ||>> mk_Frees "bs'" betas
        ||>> mk_Free "R" (typ_aF --> typ_bF --> HOLogic.boolT)
        ||>> mk_Frees "fs" typ_fs
        ||>> mk_Frees "fs'" typ_fs'
        ||>> mk_Frees "gs" typ_fs
        ||>> mk_Frees "gs'" typ_fs'
        ||>> mk_Free "z" (typ_subst_atomic (alphas ~~ typ_pairs) typ_aF)
        ||>> mk_Frees "ts" typ_pairs
        |> fst;

    (* create local definitions `b = tm` with n arguments *)
    fun suffix tm s = (dest_Const tm |> fst |> Long_Name.base_name) ^ s;
    fun define lthy b n tm =
      let
        val b = Binding.qualify true absT_name (Binding.qualified_name b);
        val ((tm, (_, def)), (lthy, lthy_old)) = lthy
          |> (snd o Local_Theory.begin_nested)
          |> Local_Theory.define_internal (((Binding.concealed b, NoSyn), (Binding.empty_atts, tm)))
          ||> `Local_Theory.end_nested;
        val phi = Proof_Context.export_morphism lthy_old lthy;
        val tm = Term.subst_atomic_types
          (map (`(Morphism.typ phi)) (alphas @ betas @ gammas @ map TFree Ds0))
          (Morphism.term phi tm);
        val def = mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi def));
      in ({def=def, tm=tm}, lthy) end;

    (* internally use REL, not the user-provided definition *)
    val (REL, lthy) = define lthy "REL" 0 equiv_rel_a;
    val REL_def = sym RS eq_reflection OF [#def REL];
    fun REL_rewr_all ctxt thm = Conv.fconv_rule
      (Conv.top_conv (fn _ => Conv.try_conv (Conv.rewr_conv REL_def)) ctxt) thm;

    val equiv_rel_a' = equiv_rel_a;
    val equiv_rel_a  = #tm REL;
    val (equiv_rel_b, equiv_rel_c) = apply2 (subst_Ts equiv_rel_a) (betas, gammas);

    (* rel_pos_distr: @{term "\<And>A B.
      A \<circ>\<circ> B \<noteq> bot \<Longrightarrow> REL \<circ>\<circ> rel_F A \<circ>\<circ> REL \<circ>\<circ> rel_F B \<circ>\<circ> REL \<le> REL \<circ>\<circ> rel_F (A \<circ>\<circ> B) \<circ>\<circ> REL"} *)
    fun compp_not_bot comp aT cT = let
        val T = mk_relT aT cT;
        val mk_eq = HOLogic.eq_const T;
      in HOLogic.mk_not (mk_eq $ comp $ bot_const T) end;
    val ab_comps = map2 mk_relcompp var_Ps var_Qs;
    val ne_comps = (@{map 3} compp_not_bot ab_comps alphas gammas);
    val ab_prem = foldr1 HOLogic.mk_conj ne_comps;

    val REL_pos_distrI_tm = let
        val le_relcomps = map2 mk_leq ab_comps var_Rs;
        val assm = mk_OO [equiv_rel_a, list_comb (rel_F_ab, var_Ps),
                    equiv_rel_b, list_comb (rel_F_bc, var_Qs)] equiv_rel_c;
        val concl = mk_OO [equiv_rel_a, list_comb (rel_F_ac, var_Rs)] equiv_rel_c;
      in
        mk_Trueprop_implies
          ([assm $ var_x $ var_y'] @ ne_comps @ le_relcomps, concl $ var_x $ var_y')
      end;

    val ab_concl = mk_leq
      (mk_OO [list_comb (rel_F_ab, var_Ps), equiv_rel_b] (list_comb (rel_F_bc, var_Qs)))
      (mk_OO [equiv_rel_a, list_comb (rel_F_ac, ab_comps)] (equiv_rel_c));
    val ab_imp = Logic.mk_implies (apply2 HOLogic.mk_Trueprop (ab_prem, ab_concl));
    val rel_pos_distr = fold_rev Logic.all (var_Ps @ var_Qs) ab_imp;

    (* {(x, y) . REL x y} *)
    fun mk_rel_pairs rel = mk_case_prod (var_x, var_x') (rel $ var_x $ var_x')
    val rel_pairs = mk_rel_pairs equiv_rel_a;

    (* rel_Inter: \<And>S. \<lbrakk> S \<noteq> {}; \<Inter>S \<noteq> {} \<rbrakk> \<Longrightarrow>
      (\<Inter>A\<in>S. {(x, y). REL x y} `` {x. set_F x \<subseteq> A}) \<subseteq> {(x, y). REL x y} `` {x. set_F x \<subseteq> \<Inter>S} *)
    fun rel_Inter_from_set_F (var_A, var_S) set_F = let

      val typ_aset = fastype_of var_A;

      (* \<Inter>S *)
      val inter_S = Inf_const typ_aset $ var_S;

      (* [S \<noteq> {}, \<Inter>S \<noteq> {}] *)
      fun not_empty x = let val ty = fastype_of x
        in HOLogic.mk_not (HOLogic.mk_eq (x, bot_const ty)) end;
      val prems = map (HOLogic.mk_Trueprop o not_empty) [var_S, inter_S];

      (* {x. set_F x \<subseteq> A} *)
      val setF_sub_A = mk_in [var_A] [set_F] typ_aF;

      (* {x. set_F x \<subseteq> \<Inter>S} *)
      val setF_sub_S = mk_in [inter_S] [set_F] typ_aF;

      val lhs = Inf_const (HOLogic.mk_setT typ_aF) $ (mk_image
        (absfree (dest_Free var_A) (Image_const typ_aF $ rel_pairs $ setF_sub_A)) $ var_S);
      val rhs = Image_const typ_aF $ rel_pairs $ setF_sub_S;
      val concl = HOLogic.mk_Trueprop (mk_leq lhs rhs);

     in Logic.all var_S (Logic.list_implies (prems, concl)) end;

    val rel_Inters = map2 rel_Inter_from_set_F (var_As ~~ var_Ss) sets_F;

    (* map_F_Just = map_F Just *)
    val map_F_Just = let
        val option_tys = map mk_MaybeT alphas;
        val somes = map Just_const alphas;
      in list_comb (subst_atomic_types (betas ~~ option_tys) map_F, somes) end;

    fun mk_set_F'_tm typ_a set_F =
      let
        val typ_aset = HOLogic.mk_setT typ_a;

        (* set_F' x = (\<Inter>y\<in>{y. REL (map_F Just x) y}. UNION (set_F y) set_Maybe) *)
        val sbind = mk_UNION (subst_Maybe alphas set_F $ var_mx) (set_Maybe_const typ_a);
        val collection = HOLogic.Collect_const typ_MaybeF $ absfree (dest_Free var_mx)
          (subst_Maybe alphas equiv_rel_a $ (map_F_Just $ var_x) $ var_mx);
        val set_F'_tm = lambda var_x
          (Inf_const typ_aset $ (mk_image (absfree (dest_Free var_mx) sbind) $ collection));
      in
        set_F'_tm
      end

    val sets = mk_sets_of_bnf (replicate live deads) (replicate live alphas) bnf_F;
    val sets' = map2 mk_set_F'_tm alphas sets;

    val (Iwits, wit_goals) =
      prepare_wits true repT wits opts alphas wits_F var_as var_as' sets' lthy;

    val goals = rel_pos_distr :: rel_Inters @
      (case wits of NONE => [] | _ => wit_goals);

    val plugins =
      get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts) |>
      the_default Plugin_Name.default_filter;

    fun after_qed thmss lthy =
      (case thmss of [rel_pos_distr_thm0] :: thmss =>
        let
          val equiv_thm' = REL_rewr_all lthy equiv_thm;
          val rel_pos_distr_thm =
            @{thm equivp_add_relconj} OF [equiv_thm', equiv_thm', rel_pos_distr_thm0];

          val (rel_Inter_thms, wit_thmss) = apply2 (fn f => flat (f live thmss)) (take, drop);

          (* construct map_G, sets_G, bd_G, rel_G and wits_G *)

          (* map_G f = abs_G o map_F f o rep_G *)
          val map_G = fold_rev lambda var_fs (HOLogic.mk_comp (HOLogic.mk_comp
            (subst_Ts abs_G betas, list_comb (map_F, var_fs)), rep_G));
          val map_raw = fold_rev lambda var_fs (list_comb (map_F, var_fs))
            |> subst_atomic_types (betas ~~ gammas);

          (* Define set_G and the three auxiliary definitions (set_F', F_in, F_in') *)
          fun mk_set_G var_A set_F lthy = let
              val typ_a = HOLogic.dest_setT (fastype_of var_A);
              val set_F'_tm = mk_set_F'_tm typ_a set_F

              val (set_F', lthy) = define lthy (suffix set_F "'") 1 set_F'_tm;

              (* set_G = set_F' o rep_G *)
              val set_G = HOLogic.mk_comp (#tm set_F', rep_G);

              (* F_in A = {x. set_F x \<subseteq> A} *)
              val F_in_tm = lambda var_A (mk_in [var_A] [set_F] typ_aF);
              val (F_in, lthy) = define lthy (suffix set_F "_in") 1 F_in_tm;

              (* F_in' A = map_F Inr -` ({(x, y). REL x y} `` F_in (insert (Inl ()) (Inr ` A))) *)
              val F_in' = lambda var_A (mk_vimage map_F_Just (Image_const typ_MaybeF $
                subst_Maybe alphas rel_pairs $ (subst_Maybe alphas (#tm F_in) $ mk_insert
                  (mk_Nothing typ_a) (mk_image (Just_const typ_a) $ var_A))));
              val (F_in', lthy) = define lthy (suffix set_F "_in'") 1 F_in';

            in ((set_G, {set_F'=set_F', F_in=F_in, F_in'=F_in'}), lthy) end;

          val ((sets_G, set_F'_aux_defs), lthy) =
            @{fold_map 2} mk_set_G var_As sets_F lthy |>> split_list;

          (* bd_G = bd_F *)
          val bd_G = mk_bd_of_bnf deads alphas bnf_F;

          (* rel_F' A =
               BNF_Def.vimage2p (map_F Just) (map_F Just) ((\<cong>) OO rel_F (rel_Maybe A) OO (\<cong>)) *)
          val rel_Maybes = @{map 3} (fn v => fn aT => fn bT => rel_Maybe_const aT bT $ v);
          val rel_F'_tm = let val equiv_equiv_rel_option = subst_Ts equiv_rel_a' o map mk_MaybeT in
            mk_vimage2p map_F_Just (subst_atomic_types (alphas ~~ betas) map_F_Just) $
              mk_OO [equiv_equiv_rel_option alphas, list_comb (rel_F_option, rel_Maybes var_Ps alphas betas)]
              (equiv_equiv_rel_option betas) end;

          val (rel_F', lthy) =
            define lthy (suffix rel_F_ab "'") (live+2) (fold_rev lambda var_Ps rel_F'_tm);

          (* rel_G A = vimage2p rep_G rep_G (rel_F' A) *)
          val rel_G = fold_rev lambda var_Ps (mk_vimage2p rep_G (subst_Ts rep_G betas) $ rel_F'_tm);
          val rel_raw = fold_rev lambda var_Ps rel_F'_tm
            |> subst_atomic_types (betas ~~ gammas);

          (* auxiliary lemmas *)
          val bd_card_order = bd_card_order_of_bnf bnf_F;
          val bd_cinfinite = bd_cinfinite_of_bnf bnf_F;
          val in_rel = in_rel_of_bnf bnf_F;
          val map_F_comp = map_comp_of_bnf bnf_F;
          val map_F_comp0 = map_comp0_of_bnf bnf_F;
          val map_F_cong = map_cong_of_bnf bnf_F;
          val map_F_id0 = map_id0_of_bnf bnf_F;
          val map_F_id = map_id_of_bnf bnf_F;
          val rel_conversep = rel_conversep_of_bnf bnf_F;
          val rel_flip = rel_flip_of_bnf bnf_F;
          val rel_eq_onp = rel_eq_onp_of_bnf bnf_F;
          val rel_Grp = rel_Grp_of_bnf bnf_F;
          val rel_OO = rel_OO_of_bnf bnf_F;
          val rel_map = rel_map_of_bnf bnf_F;
          val rel_refl_strong = rel_refl_strong_of_bnf bnf_F;
          val set_bd_thms = set_bd_of_bnf bnf_F;
          val set_map_thms = set_map_of_bnf bnf_F;



          (* map_F_respect: @{term "((=) ===> REL ===> REL) map_F map_F"} *)
          val map_F_respect = HOLogic.mk_Trueprop (fold_rev mk_rel_fun (map2 (fn xT => fn yT =>
            HOLogic.eq_const (xT --> yT)) alphas betas @ [equiv_rel_a]) (equiv_rel_b) $ map_F $ map_F);

          fun map_F_respect_tac ctxt =
            HEADGOAL (EVERY'
             [REPEAT_DETERM_N (live + 1) o rtac ctxt @{thm rel_funI}, hyp_subst_tac ctxt,
              rtac ctxt (BNF_FP_Util.split_conj_prems live rel_pos_distr_thm0 OF
                replicate live @{thm Grp_conversep_nonempty} RS rev_mp),
              rtac ctxt impI, dtac ctxt @{thm predicate2D}, etac ctxt @{thm relcomppI2[rotated]},
              rtac ctxt (rel_Grp RS @{thm predicate2_eqD} RS iffD2), rtac ctxt @{thm GrpI[OF refl]},
              REPEAT_DETERM o resolve_tac ctxt [CollectI, conjI, subset_UNIV],
              rtac ctxt (rel_flip RS iffD2),
              rtac ctxt (rel_Grp RS @{thm predicate2_eqD} RS iffD2), rtac ctxt @{thm GrpI[OF refl]},
              REPEAT_DETERM o resolve_tac ctxt [CollectI, conjI, subset_UNIV],
              SELECT_GOAL (unfold_thms_tac ctxt (rel_eq_onp :: @{thms Grp_conversep_eq_onp})),
              etac ctxt @{thm predicate2D[OF rel_conj_eq_onp, rotated]},
              rtac ctxt equiv_thm']);

          val map_F_respect_thm = prove lthy [] map_F_respect map_F_respect_tac;

          val rel_funD = mk_rel_funDN (live+1);
          val map_F_rsp = (rel_funD map_F_respect_thm) OF (replicate live refl);
          fun map_F_rsp_of tms ctxt = (infer_instantiate' ctxt (NONE :: NONE
            :: map (SOME o Thm.cterm_of ctxt) tms) map_F_rsp)

          val qthms = let
              fun equivp_THEN thm = REL_rewr_all lthy equiv_thm RS thm;
              fun Quotient3_THEN thm = REL_rewr_all lthy quot_thm RS thm;
            in
              {abs_rep = Quotient3_THEN @{thm Quotient3_abs_rep},
               rel_abs = Quotient3_THEN @{thm Quotient3_rel_abs},
               rep_abs = Quotient3_THEN @{thm Quotient3_rep_abs},
               rep_reflp = Quotient3_THEN @{thm Quotient3_rep_reflp},
               rep_abs_rsp = Quotient3_THEN @{thm rep_abs_rsp},
               reflp = equivp_THEN @{thm equivp_reflp},
               symp = equivp_THEN @{thm equivp_symp},
               transp = equivp_THEN @{thm equivp_transp},
               REL = REL_def}
            end;

          (* lemma REL_OO_REL_left: REL OO REL OO R = REL OO R *)
          val REL_OO_REL_left_thm = let
              val tm = mk_Trueprop_eq
                (mk_OO [equiv_rel_a, equiv_rel_a] var_R, mk_relcompp equiv_rel_a var_R)
              fun tac ctxt = HEADGOAL (EVERY'
                [rtac ctxt ext,
                rtac ctxt ext,
                rtac ctxt iffI,
                TWICE (etac ctxt @{thm relcomppE}),
                rtac ctxt @{thm relcomppI},
                etac ctxt (#transp qthms),
                TWICE (assume_tac ctxt),
                etac ctxt @{thm relcomppE},
                etac ctxt @{thm relcomppI},
                rtac ctxt @{thm relcomppI},
                rtac ctxt (#reflp qthms),
                assume_tac ctxt]);
            in prove lthy [var_R] tm tac end;

          (* Generate theorems related to the setters *)
          val map_F_fs = list_comb (map_F, var_fs);

          (* aset aset asetset bset typ_b typ_b *)
          fun mk_set_F'_thmss (((((var_A, var_A'), var_S), var_B), var_b), var_b')
                set_F {set_F', F_in, F_in'} rel_Inter_thm set_map_F_thm (idx, vf) =
            let
              val (var_f, var_fs') = case vf of
                (f :: fs) => (f, fs)
                | _ => error "won't happen";

              val typ_a = fastype_of var_f |> dest_funT |> fst;
              val typ_b = fastype_of var_b;
              val (typ_asetset, typ_aset) = `HOLogic.mk_setT (fastype_of var_A);

              val map_F_fs_x = map_F_fs $ var_x;

              (* F_in'_mono: A \<subseteq> B \<Longrightarrow> F_in' A \<subseteq> F_in' B *)
              val F_in'_mono_tm = mk_Trueprop_implies
                ([mk_leq var_A var_A'], mk_leq (#tm F_in' $ var_A) (#tm F_in' $ var_A'));
              fun F_in'_mono_tac ctxt =
                unfold_thms_tac ctxt [#def F_in', #def F_in] THEN
                HEADGOAL (EVERY'
                  [rtac ctxt subsetI,
                  etac ctxt vimageE,
                  etac ctxt @{thm ImageE},
                  etac ctxt CollectE,
                  etac ctxt CollectE,
                  dtac ctxt @{thm case_prodD},
                  hyp_subst_tac ctxt,
                  rtac ctxt (vimageI OF [refl]),
                  rtac ctxt @{thm ImageI},
                  rtac ctxt CollectI,
                  rtac ctxt @{thm case_prodI},
                  assume_tac ctxt ORELSE' rtac ctxt refl,
                  rtac ctxt CollectI,
                  etac ctxt subset_trans,
                  etac ctxt (@{thm insert_mono} OF [@{thm image_mono}])]);
              val F_in'_mono_thm = prove lthy [var_A, var_A'] F_in'_mono_tm F_in'_mono_tac;

              (* F_in'_Inter: F_in' (\<Inter>S) = (\<Inter>A\<in>S. F_in' A) *)
              val F_in'_Inter_tm = mk_Trueprop_eq ((#tm F_in' $ (Inf_const typ_aset $ var_S)),
                (Inf_const (HOLogic.mk_setT typ_aF) $ (mk_image (#tm F_in') $ var_S)));
              fun F_in'_Inter_tac ctxt =
                Local_Defs.unfold_tac ctxt [#def F_in', #def F_in]
                THEN HEADGOAL (rtac ctxt (infer_instantiate' ctxt
                  [SOME (Thm.cterm_of ctxt (HOLogic.mk_eq (var_S, bot_const typ_asetset)))] @{thm case_split})
                  THEN' EVERY' [
                    hyp_subst_tac ctxt,
                    SELECT_GOAL
                      (unfold_thms_tac ctxt @{thms Inter_empty INT_empty UNIV_sum_unit_conv}),
                    rtac ctxt @{thm set_eqI},
                    rtac ctxt iffI,
                    rtac ctxt UNIV_I,
                    rtac ctxt (vimageI OF [refl]),
                    rtac ctxt @{thm ImageI},
                    rtac ctxt CollectI,
                    rtac ctxt @{thm case_prodI},
                    rtac ctxt (#reflp qthms),
                    rtac ctxt CollectI,
                    rtac ctxt subset_UNIV,
                    etac ctxt @{thm exE[OF ex_in_conv[THEN iffD2]]},
                    EqSubst.eqsubst_tac ctxt [0] @{thms image_INT[of _ UNIV _ id, simplified]},
                    rtac ctxt @{thm inj_Inr},
                    assume_tac ctxt,
                    SELECT_GOAL (unfold_thms_tac ctxt @{thms INT_extend_simps vimage_INT[symmetric]}),
                    rtac ctxt @{thm arg_cong2[where f=vimage, OF refl]},
                    rtac ctxt equalityI,
                    rtac ctxt subsetI,
                    rtac ctxt @{thm InterI},
                    etac ctxt imageE,
                    etac ctxt @{thm ImageE},
                    etac ctxt CollectE,
                    etac ctxt CollectE,
                    dtac ctxt @{thm case_prodD},
                    hyp_subst_tac ctxt,
                    rtac ctxt @{thm ImageI[OF CollectI]},
                    etac ctxt @{thm case_prodI} ORELSE' (SELECT_GOAL
                      (unfold_thms_tac ctxt @{thms prod.case}) THEN' rtac ctxt @{thm refl}),
                    rtac ctxt CollectI,
                    etac ctxt subset_trans,
                    etac ctxt @{thm INT_lower[OF imageI]},
                    rtac ctxt (@{thm subset_trans} OF [asm_rl, rel_Inter_thm]),
                    K (unfold_thms_tac ctxt @{thms image_image}),
                    rtac ctxt subset_refl,
                    K (unfold_thms_tac ctxt @{thms INT_extend_simps ex_in_conv[symmetric]}),
                    rtac ctxt exI,
                    rtac ctxt imageI,
                    assume_tac ctxt,
                    rtac ctxt exI,
                    rtac ctxt @{thm InterI},
                    etac ctxt imageE,
                    hyp_subst_tac ctxt,
                    rtac ctxt @{thm insertI1}]);

              val F_in'_Inter_thm = prove lthy [var_S] F_in'_Inter_tm F_in'_Inter_tac;

              (* set_F'_respect: (REL ===> (=)) set_F' set_F' *)
              val set_F'_respect_tm = HOLogic.mk_Trueprop (mk_rel_fun equiv_rel_a
                (HOLogic.eq_const typ_aset) $ #tm set_F' $ #tm set_F');
              fun set_F'_respect_tac ctxt = unfold_thms_tac ctxt (#def set_F' :: @{thms rel_fun_def})
                THEN HEADGOAL (EVERY'
                  [TWICE (rtac ctxt allI),
                  rtac ctxt impI,
                  dtac ctxt (map_F_rsp_of (map Just_const alphas) ctxt),
                  rtac ctxt @{thm INF_cong},
                  rtac ctxt @{thm Collect_eqI},
                  rtac ctxt iffI,
                  etac ctxt (#transp qthms OF [#symp qthms]),
                  assume_tac ctxt,
                  etac ctxt (#transp qthms),
                  assume_tac ctxt,
                  rtac ctxt refl]);

              (* F_in'_alt2: F_in' A = {x. set_F' x \<subseteq> A} *)
              val F_in'_alt2_tm = mk_Trueprop_eq
                (#tm F_in' $ var_A, mk_in [var_A] [#tm set_F'] typ_aF);
              fun F_in'_alt2_tac ctxt = HEADGOAL (rtac ctxt equalityI THEN'
                (Subgoal.FOCUS o K) (unfold_thms_tac ctxt (map #def [set_F', F_in', F_in])) ctxt
                THEN' EVERY'
                  [rtac ctxt subsetI,
                  rtac ctxt CollectI,
                  rtac ctxt subsetI,
                  dtac ctxt vimageD,
                  etac ctxt @{thm ImageE},
                  etac ctxt CollectE,
                  etac ctxt CollectE,
                  dtac ctxt @{thm case_prodD},
                  dtac ctxt @{thm InterD},
                  rtac ctxt @{thm imageI[OF CollectI]},
                  etac ctxt (#symp qthms),
                  etac ctxt @{thm UnionE},
                  etac ctxt imageE,
                  hyp_subst_tac ctxt,
                  etac ctxt @{thm subset_lift_sum_unitD},
                  etac ctxt @{thm setr.cases},
                  hyp_subst_tac ctxt,
                  assume_tac ctxt])
                THEN unfold_thms_tac ctxt [#def set_F'] THEN
                (HEADGOAL o EVERY')
                  [rtac ctxt subsetI,
                  etac ctxt CollectE,
                  etac ctxt (subsetD OF [F_in'_mono_thm]),
                  EqSubst.eqsubst_tac ctxt [0] [F_in'_Inter_thm],
                  rtac ctxt @{thm InterI}] THEN
                REPEAT_DETERM (HEADGOAL (etac ctxt @{thm imageE} THEN' hyp_subst_tac ctxt)) THEN
                (HEADGOAL o EVERY')
                  [etac ctxt CollectE,
                  SELECT_GOAL (unfold_thms_tac ctxt (map #def [F_in', F_in])),
                  rtac ctxt @{thm vimageI[OF refl]},
                  rtac ctxt @{thm ImageI},
                  rtac ctxt CollectI,
                  rtac ctxt @{thm case_prodI},
                  etac ctxt (#symp qthms),
                  rtac ctxt CollectI,
                  rtac ctxt subsetI,
                  rtac ctxt @{thm sum_insert_Inl_unit},
                  assume_tac ctxt,
                  hyp_subst_tac ctxt,
                  rtac ctxt imageI,
                  rtac ctxt @{thm UnionI},
                  rtac ctxt imageI,
                  assume_tac ctxt,
                  rtac ctxt @{thm setr.intros[OF refl]}];
              val F_in'_alt2_thm = prove lthy [var_A] F_in'_alt2_tm F_in'_alt2_tac;

              (* set_F'_alt: set_F' x = \<Inter>{A. x \<in> F_in' A} *)
              val set_F'_alt_tm = mk_Trueprop_eq (#tm set_F' $ var_x,
                Inf_const typ_aset $ mk_Collect (var_A, HOLogic.mk_mem (var_x, #tm F_in' $ var_A)));
              fun set_F'_alt_tac ctxt = unfold_thms_tac ctxt [F_in'_alt2_thm]
                THEN HEADGOAL (EVERY'
                  [rtac ctxt @{thm set_eqI},
                  rtac ctxt iffI,
                  rtac ctxt @{thm InterI},
                  etac ctxt CollectE,
                  etac ctxt CollectE,
                  dtac ctxt subsetD,
                  assume_tac ctxt,
                  assume_tac ctxt,
                  etac ctxt @{thm InterD},
                  rtac ctxt CollectI,
                  rtac ctxt CollectI,
                  rtac ctxt subset_refl]);
              val set_F'_alt_thm = prove lthy [var_x] set_F'_alt_tm set_F'_alt_tac;

              (* map_F_in_F_in'I: x \<in> F_in' B \<Longrightarrow> map_F f x \<in> F_in' (f ` B) *)
              val map_F_in_F_in'I_tm = mk_Trueprop_implies ([HOLogic.mk_mem (var_x, #tm F_in' $ var_A')],
                HOLogic.mk_mem (map_F_fs_x, subst_b (#tm F_in') $ (mk_image var_f $ var_A')));
              fun map_F_in_F_in'I_tac ctxt =
                Local_Defs.unfold_tac ctxt ([#def F_in', #def F_in, Bex_def] @ @{thms vimage_def Image_iff}) THEN
                HEADGOAL (EVERY'
                  [etac ctxt @{thm CollectE},
                  etac ctxt exE,
                  etac ctxt conjE,
                  etac ctxt @{thm CollectE},
                  etac ctxt @{thm CollectE},
                  dtac ctxt @{thm case_prodD},
                  rtac ctxt @{thm CollectI},
                  rtac ctxt exI,
                  rtac ctxt @{thm conjI[rotated]},
                  rtac ctxt @{thm CollectI},
                  rtac ctxt @{thm case_prodI},
                  dtac ctxt (map_F_rsp_of (map mk_Maybe_map var_fs) ctxt),
                  SELECT_GOAL (unfold_thms_tac ctxt (map_F_comp :: @{thms o_def map_sum.simps})),
                  assume_tac ctxt,
                  rtac ctxt CollectI,
                  SELECT_GOAL (unfold_thms_tac ctxt set_map_thms),
                  etac ctxt @{thm image_map_sum_unit_subset}]);
              val map_F_in_F_in'I_thm =
                prove lthy (var_A' :: var_x :: var_fs) map_F_in_F_in'I_tm map_F_in_F_in'I_tac;

              (* REL_preimage_eq: C \<inter> range f \<noteq> {} \<Longrightarrow>
                    {(a, b). REL a b} `` {x. set_F x \<subseteq> f -` C} =
                        map_F f -` {(a, b). REL a b} `` {x. set_F x \<subseteq> C} *)
              val REL_preimage_eq_tm = mk_Trueprop_implies ([HOLogic.mk_not (HOLogic.mk_eq
                  (HOLogic.mk_binop @{const_name inf} (var_B, mk_image var_f $ HOLogic.mk_UNIV typ_a),
                    bot_const (HOLogic.mk_setT typ_b)))], HOLogic.mk_eq (Image_const typ_aF $
                    rel_pairs $ mk_in [mk_vimage var_f var_B] [set_F] typ_aF, mk_vimage map_F_fs
                    (Image_const typ_bF $ subst_b rel_pairs $ mk_in [var_B] [subst_b set_F] typ_bF)));

              (* Bs \<inter> range fs \<noteq> {} \<Longrightarrow> set_F xb \<subseteq> Bs \<Longrightarrow> REL xb (map_F fs x)
                    \<Longrightarrow> x \<in> {(x, x'). REL x x'} `` {x. set_F x \<subseteq> fs -` Bs}              *)
              fun subgoal_tac {context = ctxt, params, ...} = let
                  val (x, y) = case params of
                    [(_, x), _, (_, y)] => (x, y)
                    | _ => error "won't happen";
                  val cond = HOLogic.mk_conj (apply2 HOLogic.mk_mem ((var_b, var_B), (var_b', var_B)));

                  (* ["\<lambda>x y. x \<in> B \<and> y \<in> B", "(Grp UNIV f_1)\<inverse>\<inverse>"] *)
                  val cvars = var_fs |> maps (fn f => let val fT = fastype_of f in
                    map (SOME o Thm.cterm_of ctxt)
                      [if f = var_f then
                        fold_rev lambda [var_b, var_b'] cond else HOLogic.eq_const (range_type fT),
                      mk_conversep (mk_Grp (HOLogic.mk_UNIV (domain_type fT)) f)] end);
                  val rel_pos_distr_thm_inst = infer_instantiate' ctxt (cvars @ [SOME y,SOME x])
                    (@{thm predicate2D} OF [rel_pos_distr_thm]);

                  (* GrpI[of "map_F f1 .. fN" x, OF refl CollectI, OF "B1 \<subseteq> UNIV \<and> ... \<and> Bn \<subseteq> UNIV"] *)
                  fun subset_UNIVs n = fold (fn a => fn b => conjI OF [a, b]) (replicate (n-1)
                    @{thm subset_UNIV}) @{thm subset_UNIV};
                  val GrpI_inst = infer_instantiate' ctxt (map SOME [Thm.cterm_of ctxt map_F_fs, x])
                    @{thm GrpI} OF [refl, CollectI] OF [subset_UNIVs live];

                in EVERY [
                  HEADGOAL (Method.insert_tac ctxt [rel_pos_distr_thm_inst]),
                  unfold_thms_tac ctxt [rel_conversep, rel_OO, rel_Grp],
                  HEADGOAL (etac ctxt @{thm meta_impE}),
                  REPEAT_DETERM_N (live-1) (HEADGOAL (rtac ctxt @{thm conjI[rotated]})),
                  REPEAT_DETERM_N live (HEADGOAL (etac ctxt @{thm relcompp_mem_Grp_neq_bot} ORELSE'
                      rtac ctxt @{thm relcompp_eq_Grp_neq_bot})),
                  HEADGOAL (EVERY' [etac ctxt @{thm meta_impE},
                    rtac ctxt @{thm relcomppI},
                    rtac ctxt (#reflp qthms),
                    rtac ctxt @{thm relcomppI},
                    rtac ctxt rel_refl_strong]),
                  REPEAT_DETERM_N idx (HEADGOAL (rtac ctxt refl)),
                  HEADGOAL (rtac ctxt conjI THEN' TWICE (etac ctxt subsetD THEN' assume_tac ctxt)),
                  REPEAT_DETERM_N (live-idx-1) (HEADGOAL (rtac ctxt refl)),
                  HEADGOAL (EVERY'
                    [rtac ctxt @{thm relcomppI},
                    assume_tac ctxt,
                    rtac ctxt @{thm relcomppI},
                    rtac ctxt @{thm conversepI},
                    rtac ctxt GrpI_inst,
                    rtac ctxt (#reflp qthms),
                    etac ctxt @{thm relcomppE},
                    etac ctxt @{thm relcomppE},
                    etac ctxt @{thm relcomppE},
                    etac ctxt @{thm conversepE},
                    etac ctxt @{thm GrpE},
                    hyp_subst_tac ctxt,
                    rtac ctxt @{thm ImageI},
                    rtac ctxt CollectI,
                    rtac ctxt @{thm case_prodI},
                    assume_tac ctxt,
                    EqSubst.eqsubst_asm_tac ctxt [1] rel_map,
                    EqSubst.eqsubst_asm_tac ctxt [1] [in_rel_of_bnf bnf_F],
                    etac ctxt exE,
                    etac ctxt CollectE,
                    etac ctxt conjE,
                    etac ctxt conjE,
                    etac ctxt CollectE,
                    hyp_subst_tac ctxt,
                    rtac ctxt CollectI]),
                  unfold_thms_tac ctxt set_map_thms,
                  HEADGOAL (rtac ctxt (subsetI OF [vimageI] OF [refl]) THEN'
                            etac ctxt @{thm imageE} THEN' hyp_subst_tac ctxt),
                  REPEAT_DETERM_N 6 (HEADGOAL (etac ctxt Drule.thin_rl)),
                  REPEAT_DETERM_N (live-1) (HEADGOAL (etac ctxt conjE)),
                  HEADGOAL (EVERY' [dtac ctxt subsetD, assume_tac ctxt, etac ctxt CollectE]),
                  unfold_thms_tac ctxt @{thms split_beta},
                  HEADGOAL (etac ctxt conjunct2)] end;

              fun REL_preimage_eq_tac ctxt = HEADGOAL (EVERY'
                [rtac ctxt @{thm set_eqI},
                rtac ctxt iffI,
                etac ctxt @{thm ImageE},
                etac ctxt CollectE,
                etac ctxt CollectE,
                dtac ctxt @{thm case_prodD},
                rtac ctxt (vimageI OF [refl]),
                rtac ctxt @{thm ImageI},
                rtac ctxt CollectI,
                rtac ctxt @{thm case_prodI},
                etac ctxt map_F_rsp,
                rtac ctxt CollectI,
                EqSubst.eqsubst_tac ctxt [0] [set_map_F_thm],
                etac ctxt @{thm subset_vimage_image_subset},
                etac ctxt vimageE,
                etac ctxt @{thm ImageE},
                TWICE (etac ctxt CollectE),
                dtac ctxt @{thm case_prodD},
                hyp_subst_tac ctxt,
                Subgoal.FOCUS_PARAMS subgoal_tac ctxt]);

              val REL_preimage_eq_thm = prove lthy (var_B :: var_fs) REL_preimage_eq_tm REL_preimage_eq_tac;

              (* set_map_F': set_F' (map_F f x) = f ` set_F' x *)
              val set_map_F'_tm = mk_Trueprop_eq (subst_b (#tm set_F')
                $ map_F_fs_x, mk_image var_f $ (#tm set_F' $ var_x));
              fun set_map_F'_tac ctxt = HEADGOAL (EVERY'
                  [rtac ctxt @{thm set_eqI},
                  rtac ctxt iffI,
                  EqSubst.eqsubst_asm_tac ctxt [0] [set_F'_alt_thm],
                  etac ctxt @{thm InterD},
                  rtac ctxt CollectI,
                  rtac ctxt map_F_in_F_in'I_thm,
                  SELECT_GOAL (unfold_thms_tac ctxt [F_in'_alt2_thm]),
                  rtac ctxt CollectI,
                  rtac ctxt subset_refl,
                  SELECT_GOAL (unfold_thms_tac ctxt [set_F'_alt_thm]),
                  rtac ctxt @{thm InterI},
                  etac ctxt imageE,
                  etac ctxt CollectE,
                  hyp_subst_tac ctxt,
                  etac ctxt @{thm vimageD[OF InterD]},
                  rtac ctxt CollectI]) THEN
                  (* map_F f x \<in> F_in' X \<Longrightarrow> x \<in> F_in' (f -` X) *)
                  HEADGOAL (Subgoal.FOCUS_PARAMS (fn {context = ctxt, params, ...} =>
                    let
                      val X = nth params 1 |> snd |> Thm.term_of;
                      val Inr_img = mk_image (Just_const (HOLogic.dest_setT (fastype_of X))) $ X;
                      fun cvars_of ctxt = map (SOME o Thm.cterm_of ctxt);
                      val cut_thm = infer_instantiate' ctxt (cvars_of ctxt [Inr_img, var_f])
                        @{thm insert_Inl_int_map_sum_unit};
                      val preimage_thm = infer_instantiate' ctxt (cvars_of ctxt
                          (filter (fn f => var_f <> f) var_fs |> map mk_Maybe_map))
                        (cut_thm RS REL_preimage_eq_thm);
                    in EVERY [
                      unfold_thms_tac ctxt (map #def [F_in', F_in] @ preimage_thm :: map_F_comp ::
                          @{thms lift_sum_unit_vimage_commute vimage_comp o_def map_sum.simps}),
                      unfold_thms_tac ctxt [@{thm o_def[symmetric]}, map_F_comp0],
                      Local_Defs.fold_tac ctxt @{thms vimage_comp},
                      HEADGOAL (etac ctxt (vimageI OF [refl]))] end) ctxt);

              (* set_F'_subset: set_F' x \<subseteq> set_F x *)
              val set_F'_subset_tm = HOLogic.mk_Trueprop (mk_leq (#tm set_F' $ var_x) (set_F $ var_x));
              fun set_F'_subset_tac ctxt =
                let val int_e_thm = infer_instantiate' ctxt
                  (replicate 3 NONE @ [SOME (Thm.cterm_of ctxt (map_F_Just $ var_x))]) @{thm INT_E};
                in HEADGOAL (EVERY' [SELECT_GOAL (Local_Defs.unfold_tac ctxt [#def set_F']),
                  rtac ctxt subsetI,
                  etac ctxt int_e_thm,
                  SELECT_GOAL (unfold_thms_tac ctxt [set_map_F_thm]),
                  etac ctxt @{thm UN_E},
                  etac ctxt imageE,
                  hyp_subst_tac ctxt,
                  SELECT_GOAL (unfold_thms_tac ctxt @{thms sum_set_simps singleton_iff}),
                  hyp_subst_tac ctxt,
                  assume_tac ctxt,
                  etac ctxt notE,
                  rtac ctxt CollectI,
                  rtac ctxt (#reflp qthms)])
                end;
            in
              ({F_in'_mono = F_in'_mono_thm,
                F_in'_Inter = F_in'_Inter_thm,
                set_F'_respect = prove lthy [] set_F'_respect_tm set_F'_respect_tac,
                F_in'_alt2 = F_in'_alt2_thm,
                set_F'_alt = set_F'_alt_thm,
                map_F_in_F_in'I = map_F_in_F_in'I_thm,
                set_map_F' = prove lthy (var_x :: var_fs) set_map_F'_tm set_map_F'_tac,
                set_F'_subset = prove lthy [var_x] set_F'_subset_tm set_F'_subset_tac,
                set_F'_def = #def set_F',
                F_in_def = #def F_in,
                F_in'_def = #def F_in'}, (idx + 1, var_fs'))
            end;

          val set_F'_thmss = @{fold_map 5} mk_set_F'_thmss
            (var_As ~~ var_As' ~~ var_Ss ~~ var_Bs ~~ var_bs ~~ var_bs') sets_F set_F'_aux_defs
            rel_Inter_thms set_map_thms (0, var_fs)
            |> fst;

          (* F_in'D: x \<in> F_in' A \<Longrightarrow> \<forall>a\<in>A. f a = g a \<Longrightarrow> REL (map_F f x) (map_F g x) *)
          fun rel_map_F_fs_map_F_gs subst fs gs = subst equiv_rel_b $
            (list_comb (subst map_F, fs) $ var_x) $ (list_comb (subst map_F, gs) $ var_x);
          val F_in'D_thm = let
              fun mk_prem var_a var_Aset {F_in', ...} var_f var_g =
                [HOLogic.mk_mem (var_x, #tm F_in' $ var_Aset), mk_Ball var_Aset
                  ((absfree (dest_Free var_a)) (HOLogic.mk_eq (var_f $ var_a, var_g $ var_a)))];
              val prems = @{map 5} mk_prem var_as var_As set_F'_aux_defs var_fs' var_gs';
              val F_in'D_tm = mk_Trueprop_implies (flat prems,
                rel_map_F_fs_map_F_gs (subst_Maybe betas) var_fs' var_gs');

              fun map_F_rsp_of_case_sums fs ctxt = map_F_rsp_of
                (@{map 2} (fn f => fn T => BNF_FP_Util.mk_case_sum
                  (Term.absdummy HOLogic.unitT (mk_Nothing T), f)) fs betas) ctxt;

              fun mk_var_fgs n = take n var_gs' @ drop n var_fs';
              fun F_in'D_tac ctxt = EVERY
                (unfold_thms_tac ctxt
                  (maps (fn {F_in'_def, F_in_def, ...} => [F_in'_def, F_in_def]) set_F'_thmss) ::
                map (REPEAT_DETERM_N live o HEADGOAL)
                  [etac ctxt vimageE,
                  etac ctxt @{thm ImageE},
                  etac ctxt CollectE THEN' etac ctxt CollectE,
                  dtac ctxt @{thm case_prodD}] @
                HEADGOAL (hyp_subst_tac ctxt THEN' rotate_tac (~live)) ::
                map (fn i => (HEADGOAL o EVERY')
                  [if i < live then rtac ctxt (#transp qthms) else K all_tac,
                  Ctr_Sugar_Tactics.select_prem_tac ctxt live (dresolve_tac ctxt [asm_rl]) i,
                  rtac ctxt (#transp qthms),
                  dtac ctxt (map_F_rsp_of_case_sums (mk_var_fgs (i-1)) ctxt),
                  SELECT_GOAL (unfold_thms_tac ctxt (map_F_comp :: @{thms case_sum_o_inj(2)})),
                  etac ctxt (#symp qthms),
                  dtac ctxt (map_F_rsp_of_case_sums (mk_var_fgs i) ctxt),
                  SELECT_GOAL (unfold_thms_tac ctxt (map_F_comp :: @{thms case_sum_o_inj(2)})),
                  EqSubst.eqsubst_tac ctxt [0] [map_F_cong OF replicate i refl @ asm_rl :: replicate (live-i) refl],
                  rtac ctxt @{thm sum.case_cong[OF refl refl]},
                  etac ctxt bspec,
                  hyp_subst_tac ctxt,
                  etac ctxt @{thm subset_lift_sum_unitD},
                  assume_tac ctxt,
                  assume_tac ctxt]) (1 upto live));

            in prove lthy (var_x :: var_As @ var_fs' @ var_gs') F_in'D_tm F_in'D_tac end;

          (* map_F_cong': (\<And>a. a \<in> set_F' x \<Longrightarrow> f a = g a) \<Longrightarrow> REL (map_F f x) (map_F g x) *)
          val map_F_cong'_thm = let
              fun mk_prem {set_F', ...} var_a var_f var_g = Logic.all var_a
                (mk_Trueprop_implies ([HOLogic.mk_mem (var_a, #tm set_F' $ var_x)],
                  HOLogic.mk_eq (var_f $ var_a, var_g $ var_a)));
              val map_F_cong'_tm = Logic.list_implies
                (@{map 4} mk_prem set_F'_aux_defs var_as var_fs var_gs, HOLogic.mk_Trueprop
                  (rel_map_F_fs_map_F_gs I var_fs var_gs));
              fun Just_o_fun bT f = HOLogic.mk_comp (Just_const bT, f);
              fun map_F_Just_o_funs fs = list_comb
                (subst_Maybe betas map_F, map2 Just_o_fun betas fs) $ var_x;
              fun map_F_cong'_tac ctxt = let
                  val map_F_respect_inst = map_F_rsp
                    |> infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt)
                      (map map_F_Just_o_funs [var_fs, var_gs] @ map fromJust_const betas))
                    |> Local_Defs.unfold ctxt (map_F_comp :: @{thms o_assoc
                      Fun.o_apply[where f=projr and g=Inr, unfolded sum.sel] id_def[symmetric]})
                    |> Local_Defs.unfold ctxt @{thms id_comp};
                in
                  HEADGOAL (rtac ctxt map_F_respect_inst THEN' rtac ctxt F_in'D_thm) THEN
                  EVERY (map (fn {F_in'_alt2, ...} =>
                    unfold_thms_tac ctxt [F_in'_alt2] THEN
                    HEADGOAL (EVERY'
                      [rtac ctxt CollectI,
                      rtac ctxt subset_refl,
                      rtac ctxt ballI,
                      SELECT_GOAL (unfold_thms_tac ctxt [o_apply]),
                      rtac ctxt @{thm arg_cong[where f=Inr]},
                      asm_full_simp_tac ctxt])) set_F'_thmss) end;
                in prove lthy (var_x :: var_fs @ var_gs) map_F_cong'_tm map_F_cong'_tac end;

          (* rel_F'_set: "rel_F' P x y \<longleftrightarrow>
            (\<exists>z. set_F' z \<subseteq> {(x, y). P x y} \<and> REL (map_F fst z) x \<and> REL (map_F snd z) y)" *)
          val rel_F'_set_thm = let
            val lhs = list_comb (#tm rel_F', var_Ps) $ var_x $ var_y;
            fun mk_subset_A var_a var_b var_P {set_F', ...} = let
                val collect_A = mk_case_prod (var_a, var_b) (var_P $ var_a $ var_b);
              in mk_leq (subst_atomic_types (alphas ~~ typ_pairs) (#tm set_F') $ var_z) collect_A end;
            val subset_As = @{map 4} mk_subset_A var_as var_bs var_Ps set_F'_aux_defs;
            fun mk_map mfs f z =
              Term.list_comb (mfs, map (fst o Term.strip_comb o f) var_ts) $ z;
            val map_F_fst = mk_map_of_bnf deads typ_pairs alphas bnf_F;
            val map_F_snd = mk_map_of_bnf deads typ_pairs betas bnf_F;
            val map_fst = equiv_rel_a $ (mk_map map_F_fst HOLogic.mk_fst var_z) $ var_x;
            val map_snd = equiv_rel_b $ (mk_map map_F_snd HOLogic.mk_snd var_z) $ var_y;
            val rhs = let val (z, T) = dest_Free var_z in
              HOLogic.mk_exists (z, T, fold_rev (fn a => fn b => HOLogic.mk_conj (a, b))
                (subset_As @ [map_fst]) map_snd) end;
            val rel_F'_set_tm = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));

            val maybePairsTs = map HOLogic.mk_prodT (map mk_MaybeT alphas ~~ map mk_MaybeT betas)
            fun mk_map_prod_projr aT bT = let
                val (mabT, (maT, mbT)) = `HOLogic.mk_prodT (apply2 mk_MaybeT (aT, bT));
                val map_prod_const = Const (@{const_name map_prod},
                  (maT --> aT) --> (mbT --> bT) --> mabT --> HOLogic.mk_prodT (aT, bT));
              in map_prod_const $ fromJust_const aT $ fromJust_const bT end;

            fun exI_OF_tac ctxt tm = rtac ctxt
              (infer_instantiate' ctxt (NONE :: [SOME (Thm.cterm_of ctxt tm)]) exI);

            (* REL (map_F Inr x) (map_F fst z) \<Longrightarrow> REL (map_F snd z) (map_F Inr y) \<Longrightarrow>
                 set_F z \<subseteq> {(x, y). rel_sum (=) P x y} \<Longrightarrow>
                 \<exists>z. set_F' z \<subseteq> {(x, y). P x y} \<and> REL (map_F fst z) x \<and> REL (map_F snd z) y *)
            fun subgoal1_tac {context = ctxt, params, ...} =
              let
                val z = (case params of
                    (_ :: _ :: (_, ct) :: _) => Thm.term_of ct
                  | _ => error "won't happen");
                val map_F_projr_z = list_comb (mk_map_of_bnf deads maybePairsTs typ_pairs bnf_F,
                  map2 mk_map_prod_projr alphas betas) $ z;
              in
                HEADGOAL (exI_OF_tac ctxt map_F_projr_z) THEN
                HEADGOAL (EVERY' (maps (fn {set_F'_subset, set_F'_respect, set_map_F', ...} =>
                  [rtac ctxt conjI,
                  dtac ctxt (set_F'_subset RS @{thm order_trans}),
                  TWICE (dtac ctxt (set_F'_respect RS @{thm rel_funD})),
                  SELECT_GOAL (unfold_thms_tac ctxt [set_map_F']),
                  etac ctxt @{thm in_rel_sum_in_image_projr},
                  TWICE (assume_tac ctxt)]) set_F'_thmss)) THEN
                HEADGOAL (EVERY' (map (fn Ts => FIRST'
                  [dtac ctxt (map_F_rsp_of (map fromJust_const Ts) ctxt),
                  etac ctxt sym , assume_tac ctxt]) [alphas, betas])) THEN
                unfold_thms_tac ctxt (map_F_comp ::
                  @{thms fst_comp_map_prod snd_comp_map_prod comp_projr_Inr} @ [map_F_id]) THEN
                HEADGOAL (rtac ctxt conjI) THEN
                HEADGOAL (etac ctxt (#symp qthms) THEN' assume_tac ctxt
                  ORELSE' (EVERY' (maps (fn Ts =>
                    [dtac ctxt (map_F_rsp_of (map fromJust_const Ts) ctxt),
                    SELECT_GOAL (unfold_thms_tac ctxt (map_F_comp ::
                      @{thms fst_comp_map_prod snd_comp_map_prod comp_projr_Inr} @ [map_F_id])),
                    assume_tac ctxt]) [alphas, betas]))) end;

            (* set_F' z \<subseteq> {(x, y). P x y} \<Longrightarrow> REL (map_F fst z) x \<Longrightarrow> REL (map_F snd z) y \<Longrightarrow>
                 \<exists>b. REL (map_F Inr x) b \<and> (\<exists>ba. rel_F (rel_sum (=) P) b ba \<and> REL ba (map_F Inr y)) *)
            fun subgoal2_tac {context = ctxt, params, ...} = let
                val z = (case params of
                  ((_, ct) :: _) => Thm.term_of ct
                | _ => error "won't happen");

                fun exI_map_Ifs_tac mk_proj Ts = exI_OF_tac ctxt (list_comb
                  (mk_map_of_bnf deads typ_pairs (map mk_MaybeT Ts) bnf_F, @{map 3}
                    (fn var_t => fn {set_F', ...} => fn T => lambda var_t (BNF_FP_Util.mk_If
                      (HOLogic.mk_mem (var_t, subst_Ts (#tm set_F') typ_pairs $ z))
                      (mk_Just (mk_proj var_t)) (mk_Nothing T))) var_ts set_F'_aux_defs Ts) $ z)

                fun mk_REL_trans_map_F n = (rotate_prems n (#transp qthms) OF
                  [rel_funD map_F_respect_thm] OF (replicate live refl @ [#symp qthms]));
              in
                HEADGOAL (EVERY'
                  [exI_map_Ifs_tac HOLogic.mk_fst alphas,
                  rtac ctxt conjI,
                  etac ctxt (mk_REL_trans_map_F 0)]) THEN
                unfold_thms_tac ctxt [map_F_comp, @{thm o_def}] THEN
                HEADGOAL (rtac ctxt map_F_cong'_thm) THEN
                REPEAT_DETERM_N live (HEADGOAL (etac ctxt @{thm if_P[symmetric]})) THEN
                HEADGOAL (EVERY' [exI_map_Ifs_tac HOLogic.mk_snd betas, rtac ctxt conjI]) THEN
                unfold_thms_tac ctxt rel_map THEN
                HEADGOAL (rtac ctxt rel_refl_strong) THEN
                REPEAT_DETERM_N live (HEADGOAL (etac ctxt @{thm subset_rel_sumI})) THEN
                HEADGOAL (etac ctxt (mk_REL_trans_map_F 1 OF [#symp qthms])) THEN
                unfold_thms_tac ctxt [map_F_comp, @{thm o_def}] THEN
                HEADGOAL (rtac ctxt map_F_cong'_thm) THEN
                REPEAT_DETERM_N live (HEADGOAL (etac ctxt @{thm if_P})) end;

            fun rel_F'_set_tac ctxt = EVERY
              ([unfold_thms_tac ctxt (#def rel_F' :: #REL qthms :: @{thms vimage2p_def relcompp_apply}),
              HEADGOAL (rtac ctxt iffI),
              (HEADGOAL o TWICE) (etac ctxt exE THEN' etac ctxt conjE),
              HEADGOAL (EVERY'
                [dtac ctxt (in_rel RS iffD1),
                etac ctxt exE,
                TWICE (etac ctxt conjE),
                etac ctxt CollectE,
                hyp_subst_tac ctxt]),
              (REPEAT_DETERM_N (live-1) o HEADGOAL) (etac ctxt conjE),
              HEADGOAL (Subgoal.FOCUS_PARAMS subgoal1_tac ctxt THEN' etac ctxt exE),
              (REPEAT_DETERM_N (live+1) o HEADGOAL) (etac ctxt conjE),
              HEADGOAL (Subgoal.FOCUS_PARAMS subgoal2_tac ctxt)]);

            in prove lthy (var_x :: var_y :: var_Ps) rel_F'_set_tm rel_F'_set_tac end;

          (* tactics *)

          (* map_G_id0: abs_G \<circ> map_F id \<circ> rep_G = id *)
          fun map_G_id0_tac ctxt = HEADGOAL (EVERY' [SELECT_GOAL (unfold_thms_tac ctxt
            [@{thm fun_eq_iff}, o_apply, map_F_id0, id_apply, #abs_rep qthms]),
            rtac ctxt allI, rtac ctxt refl]);

          (* map_G (g \<circ> f) = map_G g \<circ> map_G f *)
          fun map_G_comp0_tac ctxt = HEADGOAL (EVERY' [rtac ctxt ext, rtac ctxt sym,
            SELECT_GOAL (unfold_thms_tac ctxt [o_apply, map_F_comp0]), rtac ctxt (#rel_abs qthms),
            rtac ctxt map_F_rsp, rtac ctxt (#rep_abs qthms), rtac ctxt (#reflp qthms)]);

          (* map_G_cong: (\<And>z. z \<in> set_G x \<Longrightarrow> f z = g z) \<Longrightarrow> map_G f x = map_G g x *)
          fun map_G_cong_tac ctxt = EVERY
            [Local_Defs.fold_tac ctxt (map #set_F'_def set_F'_thmss),
            unfold_thms_tac ctxt [o_apply],
            HEADGOAL (rtac ctxt (#rel_abs qthms) THEN' rtac ctxt map_F_cong'_thm),
            REPEAT_DETERM_N live (HEADGOAL (asm_full_simp_tac ctxt))];

          (* set_G_map0_G: set_G \<circ> map_G f = f ` set_G *)
          fun mk_set_G_map0_G_tac thms ctxt =
            HEADGOAL (rtac ctxt ext) THEN
            EVERY [unfold_thms_tac ctxt [o_apply],
              Local_Defs.fold_tac ctxt [#set_F'_def thms]] THEN
            HEADGOAL (EVERY' (map (rtac ctxt)
              [trans OF [#set_map_F' thms RS sym, sym] RS sym,
               @{thm rel_funD} OF [#set_F'_respect thms],
               #rep_abs qthms,
               map_F_rsp,
               #rep_reflp qthms]));

          (* bd_card_order: card_order bd_F *)
          fun bd_card_order_tac ctxt = HEADGOAL (rtac ctxt bd_card_order);

          (* bd_cinfinite: BNF_Cardinal_Arithmetic.cinfinite bd_F *)
          fun bd_cinfinite_tac ctxt = HEADGOAL (rtac ctxt bd_cinfinite);

          (*target: ordLeq3 (card_of (set_F' (rep_G x_))) bd_F*)
          fun mk_set_G_bd_tac thms set_bd_thm ctxt = EVERY
            [Local_Defs.fold_tac ctxt [#set_F'_def thms],
            unfold_thms_tac ctxt [o_apply],
            HEADGOAL (rtac ctxt (@{thm ordLeq_transitive} OF
              [@{thm card_of_mono1} OF [#set_F'_subset thms], set_bd_thm]))];

          (* rel_compp: rel_G R OO rel_G S \<le> rel_G (R OO S) *)
          fun rel_compp_tac ctxt = EVERY
            [unfold_thms_tac ctxt [#REL qthms],
            HEADGOAL (TWICE (rtac ctxt @{thm vimage2p_relcompp_mono})),
            (unfold_thms_tac ctxt (REL_OO_REL_left_thm :: @{thms relcompp_assoc})),
            (unfold_thms_tac ctxt [Local_Defs.unfold ctxt @{thms eq_OO}
              (infer_instantiate' ctxt [HOLogic.eq_const HOLogic.unitT |> Thm.cterm_of ctxt |> SOME]
                @{thm sum.rel_compp})]),
            HEADGOAL (rtac ctxt rel_pos_distr_thm),
            unfold_thms_tac ctxt
              @{thms fun_eq_iff bot_apply bot_bool_def not_all eq_False not_not OO_def},
            REPEAT_DETERM (HEADGOAL (resolve_tac ctxt [exI, conjI, @{thm rel_sum.intros(1)}, refl]))];

          (* rel_G R_ = (\<lambda>x y. \<exists>z. set_G z \<subseteq> {(x, y). R x y} \<and> map_G fst z = x \<and> map_G snd z = y) *)
          fun rel_compp_Grp_tac ctxt = let
              val _ = ()
            in EVERY [Local_Defs.fold_tac ctxt (@{thm Grp_def} :: map #set_F'_def set_F'_thmss),
              unfold_thms_tac ctxt
                [o_apply, @{thm mem_Collect_eq}, @{thm OO_Grp_alt}, @{thm vimage2p_def}],
              Local_Defs.fold_tac ctxt [Local_Defs.unfold ctxt @{thms vimage2p_def} (#def rel_F')],
              unfold_thms_tac ctxt [rel_F'_set_thm],
              HEADGOAL (TWICE (rtac ctxt ext)),
              HEADGOAL (rtac ctxt iffI),
              REPEAT_DETERM (ALLGOALS (eresolve_tac ctxt [exE, conjE])),
              HEADGOAL (rtac ctxt exI),
              REPEAT_FIRST (resolve_tac ctxt [conjI]),
              HEADGOAL (EVERY' (maps (fn {set_F'_respect, ...} =>
                [etac ctxt @{thm subset_trans[rotated]},
                rtac ctxt equalityD1,
                rtac ctxt (@{thm rel_funD} OF [set_F'_respect]),
                rtac ctxt (#rep_abs qthms),
                rtac ctxt (#reflp qthms)]) set_F'_thmss)),
              (HEADGOAL o TWICE o EVERY')
                [rtac ctxt (trans OF [asm_rl, #abs_rep qthms]),
                rtac ctxt (#rel_abs qthms),
                etac ctxt (rotate_prems 1 (#transp qthms)),
                rtac ctxt map_F_rsp,
                rtac ctxt (#rep_abs qthms),
                rtac ctxt (#reflp qthms)
                ],
              HEADGOAL (rtac ctxt exI THEN' rtac ctxt conjI),
              (REPEAT_DETERM_N live o HEADGOAL o EVERY')
                [assume_tac ctxt, rtac ctxt conjI],
              (HEADGOAL o TWICE o EVERY') [
                hyp_subst_tac ctxt,
                rtac ctxt (#rep_abs_rsp qthms),
                rtac ctxt map_F_rsp,
                rtac ctxt (#rep_reflp qthms)]]
            end;

          fun pred_G_set_G_tac ctxt = HEADGOAL (rtac ctxt refl);

          val tactics = map_G_id0_tac :: map_G_comp0_tac :: map_G_cong_tac ::
            map mk_set_G_map0_G_tac set_F'_thmss @
            bd_card_order_tac :: bd_cinfinite_tac ::
            map2 mk_set_G_bd_tac set_F'_thmss set_bd_thms @
            rel_compp_tac :: rel_compp_Grp_tac :: [pred_G_set_G_tac];

          (* val wits_G = [abs_G o wit_F] *)
          val (wits_G, wit_thms) =
            let
              val wit_F_thmss = map (map2 (fn set_F' => fn wit =>
                    (#set_F'_subset set_F' RS set_mp RS wit)
                    |> unfold_thms lthy [#set_F'_def set_F']) set_F'_thmss)
                (wit_thmss_of_bnf bnf_F);
              val (wits_F, wit_F_thmss) = split_list
                (filter_out (fn ((J, _), _) => exists (fn (I, _) => subset (op =) (I, J)) Iwits)
                  (wits_F ~~ wit_F_thmss));
              fun mk_wit (I, wit) = let val vars = (map (fn n => nth var_as n) I)
                in fold_rev lambda vars (abs_G $ list_comb (wit, vars)) end;
            in
              (map mk_wit (Iwits @ wits_F), wit_thmss @ flat wit_F_thmss)
            end;

          fun mk_wit_tacs ({set_F'_def, set_F'_respect, ...} :: set_F'_thmss) (w :: ws) ctxt =
                EVERY [unfold_thms_tac ctxt [@{thm o_def},
                    set_F'_respect RS @{thm rel_funD} OF [#rep_abs qthms OF [(#reflp qthms)]]],
                  unfold_thms_tac ctxt [set_F'_def],
                  HEADGOAL (etac ctxt w)]
                THEN mk_wit_tacs set_F'_thmss ws ctxt
            | mk_wit_tacs [] ws ctxt = mk_wit_tacs set_F'_thmss ws ctxt
            | mk_wit_tacs _ _ _ = all_tac;

          val (bnf_G, lthy) = bnf_def Dont_Inline (user_policy Note_Some) true I
            tactics (mk_wit_tacs [] wit_thms) NONE map_b rel_b pred_b set_bs
            (((((((Binding.empty, absT), map_G), sets_G), bd_G), wits_G), SOME rel_G), NONE) lthy;

          val old_defs =
            {sets = set_defs_of_bnf bnf_G, map = map_def_of_bnf bnf_G, rel = rel_def_of_bnf bnf_G};

          val set_F'_defs = map (mk_abs_def o #set_F'_def) set_F'_thmss;
          val unfold_morphism = Morphism.thm_morphism "BNF"
            (unfold_thms lthy (defs @ #def REL :: set_F'_defs));
          val (bnf_G, lthy) = morph_bnf_defs unfold_morphism bnf_G
            |> (fn bnf => note_bnf_defs bnf lthy);

          (* auxiliary lemmas transfer for transfer *)
          val rel_monoD_rotated = rotate_prems ~1 (rel_mono_of_bnf bnf_F RS @{thm predicate2D});

          val REL_pos_distrI = let
              fun tac ctxt = EVERY
                [HEADGOAL (dtac ctxt (rotate_prems ~1 (rel_pos_distr_thm RS @{thm predicate2D}))),
                (REPEAT_DETERM o HEADGOAL) (rtac ctxt conjI ORELSE' assume_tac ctxt),
                (REPEAT_DETERM o HEADGOAL) (etac ctxt @{thm relcomppE}),
                HEADGOAL (dtac ctxt rel_monoD_rotated),
                (REPEAT_DETERM o HEADGOAL)
                  (assume_tac ctxt ORELSE' rtac ctxt @{thm relcomppI})];
            in prove lthy (var_x :: var_y' :: var_Ps @ var_Qs @ var_Rs) REL_pos_distrI_tm tac end;

          val rel_F_rel_F' = let
              val rel_F = mk_rel_of_bnf deads alphas betas bnf_F;
              val rel_F_rel_F'_tm = (rel_F, #tm rel_F')
                |> apply2 (fn R => HOLogic.mk_Trueprop (list_comb (R, var_Ps) $ var_x $ var_y))
                |> Logic.mk_implies;
              fun rel_F_rel_F'_tac ctxt = EVERY
                [HEADGOAL (dtac ctxt (in_rel_of_bnf bnf_F RS iffD1)),
                unfold_thms_tac ctxt (rel_F'_set_thm :: @{thms mem_Collect_eq}),
                (REPEAT_DETERM o HEADGOAL) (eresolve_tac ctxt [exE, conjE]),
                HEADGOAL (rtac ctxt exI),
                HEADGOAL (EVERY' (maps (fn thms =>
                  [rtac ctxt conjI,
                  rtac ctxt subsetI,
                  dtac ctxt (set_mp OF [#set_F'_subset thms]),
                  dtac ctxt subsetD,
                  assume_tac ctxt, assume_tac ctxt]) set_F'_thmss)),
                (REPEAT_DETERM o HEADGOAL)
                  (rtac ctxt conjI ORELSE' hyp_subst_tac ctxt THEN' rtac ctxt (#reflp qthms))]
            in prove lthy (var_x :: var_y :: var_Ps) rel_F_rel_F'_tm rel_F_rel_F'_tac end;

          fun inst_REL_pos_distrI n vs aTs bTs ctxt =
            infer_instantiate' ctxt (replicate n NONE @ (rel_Maybes vs aTs bTs
              |> map (SOME o Thm.cterm_of ctxt))) REL_pos_distrI;

          val Tss = {abs = typ_subst_atomic (alphas ~~ betas) absT, rep = repT, Ds0 = map TFree Ds0,
            deads = deads, alphas = alphas, betas = betas, gammas = gammas, deltas = deltas};

          val thms =
            {map_F_rsp = map_F_rsp,
             rel_F'_def = #def rel_F',
             rel_F_rel_F' = rel_F_rel_F',
             rel_F'_set = rel_F'_set_thm,
             rel_monoD_rotated = rel_monoD_rotated}

          val transfer_consts = mk_quotient_transfer_tacs bnf_F Tss live
            qthms thms set_F'_thmss old_defs inst_REL_pos_distrI
            map_raw rel_raw (map (#tm o #set_F') set_F'_aux_defs);
          val quiet = exists (fn No_Warn_Transfer => true | _ => false) opts;
        in
          lthy |> BNF_Def.register_bnf plugins absT_name bnf_G |>
            mk_transfer_thms quiet bnf_F bnf_G absT_name transfer_consts (Quotient equiv_thm) Tss
              (defs @ #def REL :: set_F'_defs)
        end
      | _ => raise Match);

  in (goals, after_qed, #def REL :: defs, lthy) end;


(** main commands **)

local

fun prepare_common prepare_name prepare_sort prepare_term prepare_thm
    (((((plugins, raw_specs), raw_absT_name), raw_wits), xthms_opt), (map_b, rel_b, pred_b)) lthy =
  let
    val absT_name = prepare_name lthy raw_absT_name;

    fun bad_input input =
      Pretty.chunks [Pretty.para ("Expected theorem(s) of either form:"),
      Pretty.item [Pretty.enum "," "" "" [Syntax.pretty_term lthy @{term "Quotient R Abs Rep T"},
        Syntax.pretty_term lthy @{term "reflp R"}]],
      Pretty.item [Syntax.pretty_term lthy @{term "Quotient R Abs Rep T"}],
      Pretty.item [Syntax.pretty_term lthy @{term "type_definition Rep Abs A"}],
      Pretty.para ("Got"), Pretty.enum "," "" "" (map (Thm.pretty_thm lthy) input)]
      |> Pretty.string_of
      |> error;

    fun no_refl qthm =
      Pretty.chunks [Pretty.para ("Could not find a reflexivity rule for the Quotient theorem:"),
      Pretty.item [Thm.pretty_thm lthy qthm],
      Pretty.para ("Try supplying a reflexivity theorem manually or registering it in setup_lifting.")]
      |> Pretty.string_of
      |> error;

    fun find_equiv_thm_via_Quotient qthm =
      let
        val refl_thms = Lifting_Info.get_reflexivity_rules lthy
         |> map (unfold_thms lthy @{thms reflp_eq[symmetric]});
      in
        (case refl_thms RL [qthm RS @{thm Quotient_reflp_imp_equivp}] of
          [] => no_refl qthm
        | thm :: _ => thm)
      end;

    val (lift_thm, equiv_thm) =
      (case Option.map (prepare_thm lthy) xthms_opt of
        SOME (thms as [qthm, _]) =>
          (case try (fn thms => @{thm Quotient_reflp_imp_equivp} OF thms) thms of
            SOME equiv_thm => (qthm RS @{thm Quotient_Quotient3}, Quotient equiv_thm)
          | NONE => bad_input thms)
      | SOME [thm] =>
          (case try (fn thm => thm RS @{thm Quotient_Quotient3}) thm of
            SOME qthm => (qthm, Quotient (find_equiv_thm_via_Quotient thm))
          | NONE => if can (fn thm => thm RS @{thm type_definition.Rep}) thm
              then (thm, Typedef)
              else bad_input [thm])
      | NONE => (case Lifting_Info.lookup_quotients lthy absT_name of
            SOME {quot_thm = qthm, ...} =>
              (case [qthm] RL @{thms Quotient_eq_onp_typedef Quotient_eq_onp_type_copy} of
                thm :: _ => (thm, Typedef)
              | _ => (qthm RS @{thm Quotient_Quotient3},
                 Quotient (find_equiv_thm_via_Quotient qthm)))
          | NONE => (Typedef.get_info lthy absT_name |> hd |> snd |> #type_definition, Typedef))
      | SOME thms => bad_input thms);
    val wits = (Option.map o map) (prepare_term lthy) raw_wits;
    val specs =
      map (apsnd (apsnd (the_default @{sort type} o Option.map (prepare_sort lthy)))) raw_specs;

    val which_bnf = (case equiv_thm of
        Quotient thm => quotient_bnf (thm, lift_thm)
      | Typedef => typedef_bnf lift_thm);
  in
    which_bnf wits specs map_b rel_b pred_b plugins lthy
  end;

fun prepare_lift_bnf prepare_name prepare_sort prepare_term prepare_thm =
  (fn (goals, after_qed, definitions, lthy) =>
    lthy
    |> Proof.theorem NONE after_qed (map (single o rpair []) goals)
    |> Proof.refine_singleton
        (Method.Basic (fn ctxt => SIMPLE_METHOD (unfold_thms_tac ctxt definitions)))
    |> Proof.refine_singleton (Method.primitive_text (K I))) oo
  prepare_common prepare_name prepare_sort prepare_term prepare_thm o apfst (apfst (apsnd SOME));

fun prepare_solve prepare_name prepare_typ prepare_sort prepare_thm tacs =
  (fn (goals, after_qed, definitions, lthy) =>
    lthy
    |> after_qed (map2 (fn goal => fn tac => [Goal.prove_sorry lthy [] [] goal
        (fn (ctxtprems as {context = ctxt, prems = _}) =>
          unfold_thms_tac ctxt definitions THEN tac ctxtprems)])
      goals (tacs (length goals)))) oo
  prepare_common prepare_name prepare_typ prepare_sort prepare_thm;

in

val lift_bnf_cmd =
  prepare_lift_bnf
    (fst o dest_Type oo Proof_Context.read_type_name {proper = true, strict = false})
    Syntax.read_sort Syntax.read_term Attrib.eval_thms;

fun lift_bnf args tacs =
  prepare_solve (K I) (K I) (K I) (K I) (K tacs) args;

fun copy_bnf_tac {context = ctxt, prems = _} =
  REPEAT_DETERM (resolve_tac ctxt [bexI, conjI, UNIV_I, refl, subset_refl] 1);

val copy_bnf =
  apfst (apfst (rpair NONE))
  #> apfst (apsnd (Option.map single))
  #> prepare_solve (K I) (K I) (K I) (K I)
    (fn n => replicate n copy_bnf_tac);

val copy_bnf_cmd =
  apfst (apfst (rpair NONE))
  #> apfst (apsnd (Option.map single))
  #> prepare_solve
    (fst o dest_Type oo Proof_Context.read_type_name {proper = true, strict = false})
    Syntax.read_sort Syntax.read_term Attrib.eval_thms
    (fn n => replicate n copy_bnf_tac);

end;

(** outer syntax **)

local

(* parsers *)

val parse_wits =
  @{keyword "["} |-- (Parse.name --| @{keyword ":"} -- Scan.repeat Parse.term >>
    (fn ("wits", Ts) => Ts
      | (s, _) => error ("Unknown label " ^ quote s ^ " (expected \"wits\")"))) --|
  @{keyword "]"} || Scan.succeed [];

fun parse_common_opts p =
  Scan.optional (@{keyword "("} |--
    Parse.list1 (Parse.group (K "option")
      (Scan.first (p :: [Plugin_Name.parse_filter >> Plugins_Option,
          Parse.reserved "no_warn_transfer" >> K No_Warn_Transfer])))
    --| @{keyword ")"}) [];

val parse_lift_opts = Parse.reserved "no_warn_wits" >> K No_Warn_Wits |> parse_common_opts;

val parse_copy_opts = parse_common_opts Scan.fail;

val parse_xthm = Scan.option (Parse.reserved "via" |-- Parse.thm);
val parse_xthms = Scan.option (Parse.reserved "via" |-- Parse.thms1);

in

(* exposed commands *)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword lift_bnf}
    "register a quotient type/subtype of a bounded natural functor (BNF) as a BNF"
    ((parse_lift_opts -- parse_type_args_named_constrained -- Parse.type_const -- parse_wits --
      parse_xthms -- parse_map_rel_pred_bindings) >> lift_bnf_cmd);

val _ =
  Outer_Syntax.local_theory @{command_keyword copy_bnf}
    "register a type copy of a bounded natural functor (BNF) as a BNF"
    ((parse_copy_opts -- parse_type_args_named_constrained -- Parse.type_const --
      parse_xthm -- parse_map_rel_pred_bindings) >> copy_bnf_cmd);

end;

end;
