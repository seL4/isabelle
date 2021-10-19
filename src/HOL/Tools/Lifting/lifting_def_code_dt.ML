(*  Title:      HOL/Tools/Lifting/lifting_def_code_dt.ML
    Author:     Ondrej Kuncar

Workaround that allows us to execute lifted constants that have
as a return type a datatype containing a subtype; lift_definition command
*)

signature LIFTING_DEF_CODE_DT =
sig
  type rep_isom_data
  val isom_of_rep_isom_data: rep_isom_data -> term
  val transfer_of_rep_isom_data: rep_isom_data -> thm
  val bundle_name_of_rep_isom_data: rep_isom_data -> string
  val pointer_of_rep_isom_data: rep_isom_data -> string

  type code_dt
  val rty_of_code_dt: code_dt -> typ
  val qty_of_code_dt: code_dt -> typ
  val wit_of_code_dt: code_dt -> term
  val wit_thm_of_code_dt: code_dt -> thm
  val rep_isom_data_of_code_dt: code_dt -> rep_isom_data option
  val morph_code_dt: morphism -> code_dt -> code_dt
  val mk_witness_of_code_dt: typ -> code_dt -> term
  val mk_rep_isom_of_code_dt: typ -> code_dt -> term option

  val code_dt_of: Proof.context -> typ * typ -> code_dt option
  val code_dt_of_global: theory -> typ * typ -> code_dt option
  val all_code_dt_of: Proof.context -> code_dt list
  val all_code_dt_of_global: theory -> code_dt list

  type config_code_dt = { code_dt: bool, lift_config: Lifting_Def.config }
  val default_config_code_dt: config_code_dt

  val add_lift_def_code_dt:
    config_code_dt -> binding * mixfix -> typ -> term -> thm -> thm list -> local_theory ->
      Lifting_Def.lift_def * local_theory

  val lift_def_code_dt:
    config_code_dt -> binding * mixfix -> typ -> term -> (Proof.context -> tactic) -> thm list ->
    local_theory -> Lifting_Def.lift_def * local_theory

  val lift_def_cmd:
    string list * (binding * string option * mixfix) * string * (Facts.ref * Token.src list) list ->
    local_theory -> Proof.state
end

structure Lifting_Def_Code_Dt: LIFTING_DEF_CODE_DT =
struct
                                                                       
open Ctr_Sugar_Util BNF_Util BNF_FP_Util BNF_FP_Def_Sugar Lifting_Def Lifting_Util

infix 0 MRSL

(** data structures **)

(* all type variables in qty are in rty *)
datatype rep_isom_data = REP_ISOM of { isom: term, transfer: thm, bundle_name: string, pointer: string }
fun isom_of_rep_isom_data (REP_ISOM rep_isom) = #isom rep_isom;
fun transfer_of_rep_isom_data (REP_ISOM rep_isom) = #transfer rep_isom;
fun bundle_name_of_rep_isom_data (REP_ISOM rep_isom) = #bundle_name rep_isom;
fun pointer_of_rep_isom_data (REP_ISOM rep_isom) = #pointer rep_isom;

datatype code_dt = CODE_DT of { rty: typ, qty: typ, wit: term, wit_thm: thm,
  rep_isom_data: rep_isom_data option };
fun rty_of_code_dt (CODE_DT code_dt) = #rty code_dt;
fun qty_of_code_dt (CODE_DT code_dt) = #qty code_dt;
fun wit_of_code_dt (CODE_DT code_dt) = #wit code_dt;
fun wit_thm_of_code_dt (CODE_DT code_dt) = #wit_thm code_dt;
fun rep_isom_data_of_code_dt (CODE_DT code_dt) = #rep_isom_data code_dt;
fun ty_alpha_equiv (T, U) = Type.raw_instance (T, U) andalso Type.raw_instance (U, T);
fun code_dt_eq c = (ty_alpha_equiv o apply2 rty_of_code_dt) c 
  andalso (ty_alpha_equiv o apply2 qty_of_code_dt) c;
fun term_of_code_dt code_dt = code_dt |> `rty_of_code_dt ||> qty_of_code_dt |> HOLogic.mk_prodT
  |> Net.encode_type |> single;

(* modulo renaming, typ must contain TVars *)
fun is_code_dt_of_type (rty, qty) code_dt = code_dt |> `rty_of_code_dt ||> qty_of_code_dt
  |> HOLogic.mk_prodT |> curry ty_alpha_equiv (HOLogic.mk_prodT (rty, qty));

fun mk_rep_isom_data isom transfer bundle_name pointer =
  REP_ISOM { isom = isom, transfer = transfer, bundle_name = bundle_name, pointer = pointer}

fun mk_code_dt rty qty wit wit_thm rep_isom_data =
  CODE_DT { rty = rty, qty = qty, wit = wit, wit_thm = wit_thm, rep_isom_data = rep_isom_data };

fun map_rep_isom_data f1 f2 f3 f4
  (REP_ISOM { isom = isom, transfer = transfer, bundle_name = bundle_name, pointer = pointer }) =
  REP_ISOM { isom = f1 isom, transfer = f2 transfer, bundle_name = f3 bundle_name, pointer = f4 pointer };

fun map_code_dt f1 f2 f3 f4 f5 f6 f7 f8
  (CODE_DT {rty = rty, qty = qty, wit = wit, wit_thm = wit_thm, rep_isom_data = rep_isom_data}) =
  CODE_DT {rty = f1 rty, qty = f2 qty, wit = f3 wit, wit_thm = f4 wit_thm,
    rep_isom_data = Option.map (map_rep_isom_data f5 f6 f7 f8) rep_isom_data};

fun update_rep_isom isom transfer binding pointer i = mk_code_dt (rty_of_code_dt i) (qty_of_code_dt i)
  (wit_of_code_dt i) (wit_thm_of_code_dt i) (SOME (mk_rep_isom_data isom transfer binding pointer))

fun morph_code_dt phi =
  let
    val mty = Morphism.typ phi
    val mterm = Morphism.term phi
    val mthm = Morphism.thm phi
  in
    map_code_dt mty mty mterm mthm mterm mthm I I
  end

val transfer_code_dt = morph_code_dt o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = code_dt Item_Net.T
  val empty = Item_Net.init code_dt_eq term_of_code_dt
  val extend = I
  val merge = Item_Net.merge
);

fun code_dt_of_generic context (rty, qty) =
  let
    val typ = HOLogic.mk_prodT (rty, qty)
    val prefiltred = Item_Net.retrieve_matching (Data.get context) (Net.encode_type typ)
  in
    prefiltred |> filter (is_code_dt_of_type (rty, qty))
    |> map (transfer_code_dt (Context.theory_of context)) |> find_first (fn _ => true)
  end;

fun code_dt_of ctxt (rty, qty) =
  let
    val sch_rty = Logic.type_map (singleton (Variable.polymorphic ctxt)) rty
    val sch_qty = Logic.type_map (singleton (Variable.polymorphic ctxt)) qty
  in
    code_dt_of_generic (Context.Proof ctxt) (sch_rty, sch_qty)
  end;

fun code_dt_of_global thy (rty, qty) =
  let
    val sch_rty = Logic.varifyT_global rty
    val sch_qty = Logic.varifyT_global qty
  in
    code_dt_of_generic (Context.Theory thy) (sch_rty, sch_qty)
  end;

fun all_code_dt_of_generic context =
    Item_Net.content (Data.get context) |> map (transfer_code_dt (Context.theory_of context));

val all_code_dt_of = all_code_dt_of_generic o Context.Proof;
val all_code_dt_of_global = all_code_dt_of_generic o Context.Theory;

fun update_code_dt code_dt =
  (snd o Local_Theory.begin_nested)
  #> Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Item_Net.update (morph_code_dt phi code_dt)))
  #> Local_Theory.end_nested

fun mk_match_of_code_dt qty code_dt = Vartab.empty |> Type.raw_match (qty_of_code_dt code_dt, qty)
  |> Vartab.dest |> map (fn (x, (S, T)) => (TVar (x, S), T));

fun mk_witness_of_code_dt qty code_dt =
  Term.subst_atomic_types (mk_match_of_code_dt qty code_dt) (wit_of_code_dt code_dt)

fun mk_rep_isom_of_code_dt qty code_dt = Option.map
  (isom_of_rep_isom_data #> Term.subst_atomic_types (mk_match_of_code_dt qty code_dt))
    (rep_isom_data_of_code_dt code_dt)


(** unique name for a type **)

fun var_name name sort = if sort = \<^sort>\<open>{type}\<close> orelse sort = [] then ["x" ^ name]
  else "x" ^ name :: "x_" :: sort @ ["x_"];

fun concat_Tnames (Type (name, ts)) = name :: maps concat_Tnames ts
  | concat_Tnames (TFree (name, sort)) = var_name name sort
  | concat_Tnames (TVar ((name, _), sort)) = var_name name sort;

fun unique_Tname (rty, qty) =
  let
    val Tnames = map Long_Name.base_name (concat_Tnames rty @ ["x_x"] @ concat_Tnames qty);
  in
    fold (Binding.qualify false) (tl Tnames) (Binding.name (hd Tnames))
  end;

(** witnesses **)

fun mk_undefined T = Const (\<^const_name>\<open>undefined\<close>, T);

fun mk_witness quot_thm =
  let
    val wit_thm = quot_thm RS @{thm type_definition_Quotient_not_empty_witness}
    val wit = quot_thm_rep quot_thm $ mk_undefined (quot_thm_rty_qty quot_thm |> snd)
  in
    (wit, wit_thm)
  end

(** config **)

type config_code_dt = { code_dt: bool, lift_config: config }
val default_config_code_dt = { code_dt = false, lift_config = default_config }


(** Main code **)

val ld_no_notes = { notes = false }

fun comp_lift_error _ _ = error "Composition of abstract types has not been implemented yet."

fun lift qty (quot_thm, (lthy, rel_eq_onps)) =
  let
    val quot_thm = Lifting_Term.force_qty_type lthy qty quot_thm
    val (rty, qty) = quot_thm_rty_qty quot_thm;
  in
    if is_none (code_dt_of lthy (rty, qty)) then
      let
        val (wit, wit_thm) = (mk_witness quot_thm
          handle THM _ => error ("code_dt: " ^ quote (Tname qty) ^ " was not defined as a subtype."))
        val code_dt = mk_code_dt rty qty wit wit_thm NONE
      in
        (quot_thm, (update_code_dt code_dt lthy, rel_eq_onps))
      end
    else
      (quot_thm, (lthy, rel_eq_onps))
  end;

fun case_tac rule =
  Subgoal.FOCUS_PARAMS (fn {context = ctxt, params, ...} =>
    HEADGOAL (rtac ctxt (infer_instantiate' ctxt [SOME (snd (hd params))] rule)));

fun bundle_name_of_bundle_binding binding phi context  =
  Name_Space.full_name (Name_Space.naming_of context) (Morphism.binding phi binding);

fun prove_schematic_quot_thm actions ctxt =
  Lifting_Term.prove_schematic_quot_thm actions (Lifting_Info.get_quotients ctxt) ctxt

fun prove_code_dt (rty, qty) lthy =
  let
    val (fold_quot_thm: (local_theory * thm list) Lifting_Term.fold_quot_thm) =
      { constr = constr, lift = lift, comp_lift = comp_lift_error };
  in prove_schematic_quot_thm fold_quot_thm lthy (rty, qty) (lthy, []) |> snd end
and add_lift_def_code_dt config var qty rhs rsp_thm par_thms lthy =
  let
    fun binop_conv2 cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
    fun ret_rel_conv conv ctm =
      case (Thm.term_of ctm) of
        Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _ =>
          binop_conv2 Conv.all_conv conv ctm
        | _ => conv ctm
    fun R_conv rel_eq_onps ctxt =
      Conv.top_sweep_rewrs_conv @{thms eq_onp_top_eq_eq[symmetric, THEN eq_reflection]} ctxt
      then_conv Conv.bottom_rewrs_conv rel_eq_onps ctxt

    val (ret_lift_def, lthy1) = add_lift_def (#lift_config config) var qty rhs rsp_thm par_thms lthy
  in
    if (not (#code_dt config) orelse (code_eq_of_lift_def ret_lift_def <> NONE_EQ)
      andalso (code_eq_of_lift_def ret_lift_def <> UNKNOWN_EQ))
      (* Let us try even in case of UNKNOWN_EQ. If this leads to problems, the user can always
        say that they do not want this workaround. *)
    then (ret_lift_def, lthy1)
    else
      let
        val lift_def = inst_of_lift_def lthy1 qty ret_lift_def
        val rty = rty_of_lift_def lift_def
        val rty_ret = body_type rty
        val qty_ret = body_type qty

        val (lthy2, rel_eq_onps) = prove_code_dt (rty_ret, qty_ret) lthy1
        val code_dt = code_dt_of lthy2 (rty_ret, qty_ret)
      in
        if is_none code_dt orelse is_none (rep_isom_data_of_code_dt (the code_dt))
        then (ret_lift_def, lthy2)
        else
          let
            val code_dt = the code_dt
            val rhs = dest_comb (rhs_of_lift_def lift_def) |> snd
            val rep_isom_data = code_dt |> rep_isom_data_of_code_dt |> the
            val pointer = pointer_of_rep_isom_data rep_isom_data
            val quot_active = 
              Lifting_Info.lookup_restore_data lthy2 pointer |> the |> #quotient |> #quot_thm
              |> Lifting_Info.lookup_quot_thm_quotients lthy2 |> is_some
            val qty_code_dt_bundle_name = bundle_name_of_rep_isom_data rep_isom_data
            val rep_isom = mk_rep_isom_of_code_dt qty_ret code_dt |> the
            val lthy3 = if quot_active then lthy2 else Bundle.includes [qty_code_dt_bundle_name] lthy2
            fun qty_isom_of_rep_isom rep = rep |> dest_Const |> snd |> domain_type
            val qty_isom = qty_isom_of_rep_isom rep_isom
            val f'_var = (Binding.suffix_name "_aux" (fst var), NoSyn);
            val f'_qty = strip_type qty |> fst |> rpair qty_isom |> op --->
            val f'_rsp_rel = Lifting_Term.equiv_relation lthy3 (rty, f'_qty);
            val rsp = rsp_thm_of_lift_def lift_def
            val rel_eq_onps_conv =
              HOLogic.Trueprop_conv (Conv.fun2_conv (ret_rel_conv (R_conv rel_eq_onps lthy3)))
            val rsp_norm = Conv.fconv_rule rel_eq_onps_conv rsp
            val f'_rsp_goal = HOLogic.mk_Trueprop (f'_rsp_rel $ rhs $ rhs);
            val f'_rsp = Goal.prove_sorry lthy3 [] [] f'_rsp_goal
              (fn {context = ctxt, prems = _} =>
                HEADGOAL (CONVERSION (rel_eq_onps_conv) THEN' rtac ctxt rsp_norm))
              |> Thm.close_derivation \<^here>
            val (f'_lift_def, lthy4) = add_lift_def ld_no_notes f'_var f'_qty rhs f'_rsp [] lthy3
            val f'_lift_def = inst_of_lift_def lthy4 f'_qty f'_lift_def
            val f'_lift_const = mk_lift_const_of_lift_def f'_qty f'_lift_def
            val (args, args_ctxt) = mk_Frees "x" (binder_types qty) lthy4
            val f_alt_def_goal_lhs = list_comb (lift_const_of_lift_def lift_def, args);
            val f_alt_def_goal_rhs = rep_isom $ list_comb (f'_lift_const, args);
            val f_alt_def_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (f_alt_def_goal_lhs, f_alt_def_goal_rhs));
            fun f_alt_def_tac ctxt i =
              EVERY' [Transfer.gen_frees_tac [] ctxt, DETERM o Transfer.transfer_tac true ctxt,
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt [id_apply]), rtac ctxt refl] i;
            val rep_isom_transfer = transfer_of_rep_isom_data rep_isom_data
            val (_, transfer_ctxt) = args_ctxt
              |> Proof_Context.note_thms ""
                  (Binding.empty_atts, [([rep_isom_transfer], [Transfer.transfer_add])])
            val f_alt_def =
              Goal.prove_sorry transfer_ctxt [] [] f_alt_def_goal
                (fn {context = goal_ctxt, ...} => HEADGOAL (f_alt_def_tac goal_ctxt))
              |> Thm.close_derivation \<^here>
              |> singleton (Variable.export transfer_ctxt lthy4)
            val lthy5 = lthy4
              |> Local_Theory.note ((Binding.empty, @{attributes [code]}), [f_alt_def])
              |> snd
              (* if processing a mutual datatype (there is a cycle!) the corresponding quotient 
                 will be needed later and will be forgotten later *)
              |> (if quot_active then I else Lifting_Setup.lifting_forget pointer)
          in
            (ret_lift_def, lthy5)
          end
       end
    end
and mk_rep_isom qty_isom_bundle (rty, qty, qty_isom) lthy0 =
  let
    (* logical definition of qty qty_isom isomorphism *) 
    val uTname = unique_Tname (rty, qty)
    fun eq_onp_to_top_tac ctxt = SELECT_GOAL (Local_Defs.unfold0_tac ctxt 
      (@{thm eq_onp_top_eq_eq[symmetric]} :: Lifting_Info.get_relator_eq_onp_rules ctxt))
    fun lift_isom_tac ctxt = HEADGOAL (eq_onp_to_top_tac ctxt
      THEN' (rtac ctxt @{thm id_transfer}));

    val (rep_isom_lift_def, lthy1) = lthy0
      |> (snd o Local_Theory.begin_nested)
      |> lift_def ld_no_notes (Binding.qualify_name true uTname "Rep_isom", NoSyn)
        (qty_isom --> qty) (HOLogic.id_const rty) lift_isom_tac []
      |>> inst_of_lift_def lthy0 (qty_isom --> qty);
    val (abs_isom, lthy2) = lthy1
      |> lift_def ld_no_notes (Binding.qualify_name true uTname "Abs_isom", NoSyn)
        (qty --> qty_isom) (HOLogic.id_const rty) lift_isom_tac []
      |>> mk_lift_const_of_lift_def (qty --> qty_isom);
    val rep_isom = lift_const_of_lift_def rep_isom_lift_def

    val pointer = Lifting_Setup.pointer_of_bundle_binding lthy2 qty_isom_bundle
    fun code_dt phi context =
      code_dt_of lthy2 (rty, qty) |> the
      |> update_rep_isom rep_isom (transfer_rules_of_lift_def rep_isom_lift_def |> hd)
          (bundle_name_of_bundle_binding qty_isom_bundle phi context) pointer;
    val lthy3 = lthy2  
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => fn context => Data.map (Item_Net.update (morph_code_dt phi (code_dt phi context))) context)
      |> Local_Theory.end_nested

    (* in order to make the qty qty_isom isomorphism executable we have to define discriminators 
      and selectors for qty_isom *)
    val (rty_name, typs) = dest_Type rty
    val (_, qty_typs) = dest_Type qty
    val fp = BNF_FP_Def_Sugar.fp_sugar_of lthy3 rty_name
    val fp = if is_some fp then the fp
      else error ("code_dt: " ^ quote rty_name ^ " is not a datatype.")
    val ctr_sugar = fp |> #fp_ctr_sugar |> #ctr_sugar
    val ctrs = map (Ctr_Sugar.mk_ctr typs) (#ctrs ctr_sugar);
    val qty_ctrs = map (Ctr_Sugar.mk_ctr qty_typs) (#ctrs ctr_sugar);
    val ctr_Tss = map (dest_Const #> snd #> binder_types) ctrs;
    val qty_ctr_Tss = map (dest_Const #> snd #> binder_types) qty_ctrs;

    val n = length ctrs;
    val ks = 1 upto n;
    val (xss, _) = mk_Freess "x" ctr_Tss lthy3;

    fun sel_retT (rty' as Type (s, rtys'), qty' as Type (s', qtys')) =
        if (rty', qty') = (rty, qty) then qty_isom else (if s = s'
          then Type (s, map sel_retT (rtys' ~~ qtys')) else qty')
      | sel_retT (_, qty') = qty';

    val sel_retTs = map2 (map2 (sel_retT oo pair)) ctr_Tss qty_ctr_Tss

    fun lazy_prove_code_dt (rty, qty) lthy =
      if is_none (code_dt_of lthy (rty, qty)) then prove_code_dt (rty, qty) lthy |> fst else lthy;

    val lthy4 = fold2 (fold2 (lazy_prove_code_dt oo pair)) ctr_Tss sel_retTs lthy3

    val sel_argss = @{map 4} (fn k => fn xs => @{map 2} (fn x => fn qty_ret => 
      (k, qty_ret, (xs, x)))) ks xss xss sel_retTs;

    fun mk_sel_casex (_, _, (_, x)) = Ctr_Sugar.mk_case typs (x |> dest_Free |> snd) (#casex ctr_sugar);
    val dis_casex = Ctr_Sugar.mk_case typs HOLogic.boolT (#casex ctr_sugar);
    fun mk_sel_case_args lthy ctr_Tss ks (k, qty_ret, (xs, x)) =
      let
        val T = x |> dest_Free |> snd;
        fun gen_undef_wit Ts wits =
          case code_dt_of lthy (T, qty_ret) of
            SOME code_dt =>
              (fold_rev (Term.lambda o curry Free Name.uu) Ts (mk_witness_of_code_dt qty_ret code_dt),
                wit_thm_of_code_dt code_dt :: wits)
            | NONE => (fold_rev (Term.lambda o curry Free Name.uu) Ts (mk_undefined T), wits)
      in
        @{fold_map 2} (fn Ts => fn k' => fn wits =>
          (if k = k' then (fold_rev Term.lambda xs x, wits) else gen_undef_wit Ts wits)) ctr_Tss ks []
      end;
    fun mk_sel_rhs arg =
      let val (sel_rhs, wits) = mk_sel_case_args lthy4 ctr_Tss ks arg
      in (arg |> #2, wits, list_comb (mk_sel_casex arg, sel_rhs)) end;
    fun mk_dis_case_args args k  = map (fn (k', arg) => (if k = k'
      then fold_rev Term.lambda arg \<^Const>\<open>True\<close> else fold_rev Term.lambda arg \<^Const>\<open>False\<close>)) args;
    val sel_rhs = map (map mk_sel_rhs) sel_argss
    val dis_rhs = map (fn k => list_comb (dis_casex, mk_dis_case_args (ks ~~ xss) k)) ks
    val dis_qty = qty_isom --> HOLogic.boolT;
    val dis_names = map (fn k => Binding.qualify_name true uTname ("dis" ^ string_of_int k)) ks;

    val (diss, lthy5) = @{fold_map 2} (fn b => fn rhs => fn lthy =>
      lift_def ld_no_notes (b, NoSyn) dis_qty rhs (K all_tac) [] lthy
      |>> mk_lift_const_of_lift_def dis_qty) dis_names dis_rhs lthy4

    val unfold_lift_sel_rsp = @{lemma "(\<And>x. P1 x \<Longrightarrow> P2 (f x)) \<Longrightarrow> (rel_fun (eq_onp P1) (eq_onp P2)) f f"
      by (simp add: eq_onp_same_args rel_fun_eq_onp_rel)}

    fun lift_sel_tac exhaust_rule dt_rules wits ctxt i =
        (Method.insert_tac ctxt wits THEN' 
         eq_onp_to_top_tac ctxt THEN' (* normalize *)
         rtac ctxt unfold_lift_sel_rsp THEN'
         case_tac exhaust_rule ctxt THEN_ALL_NEW (
        EVERY' [hyp_subst_tac ctxt, (* does not kill wits because = was rewritten to eq_onp top *)
        Raw_Simplifier.rewrite_goal_tac ctxt (map safe_mk_meta_eq dt_rules), 
        REPEAT_DETERM o etac ctxt conjE, assume_tac ctxt])) i
    val pred_simps = Transfer.lookup_pred_data lthy5 (Tname rty) |> the |> Transfer.pred_simps
    val sel_tac = lift_sel_tac (#exhaust ctr_sugar) (#case_thms ctr_sugar @ pred_simps)
    val sel_names =
      map (fn (k, xs) =>
        map (fn k' => Binding.qualify_name true uTname ("sel" ^ string_of_int k ^ string_of_int k'))
          (1 upto length xs)) (ks ~~ ctr_Tss);
    val (selss, lthy6) = @{fold_map 2} (@{fold_map 2} (fn b => fn (qty_ret, wits, rhs) => fn lthy =>
        lift_def_code_dt { code_dt = true, lift_config = ld_no_notes }
        (b, NoSyn) (qty_isom --> qty_ret) rhs (HEADGOAL o sel_tac wits) [] lthy
      |>> mk_lift_const_of_lift_def (qty_isom --> qty_ret))) sel_names sel_rhs lthy5

    (* now we can execute the qty qty_isom isomorphism *)
    fun mk_type_definition newT oldT RepC AbsC A =
      let
        val typedefC =
          Const (\<^const_name>\<open>type_definition\<close>,
            (newT --> oldT) --> (oldT --> newT) --> HOLogic.mk_setT oldT --> HOLogic.boolT);
      in typedefC $ RepC $ AbsC $ A end;
    val typedef_goal = mk_type_definition qty_isom qty rep_isom abs_isom (HOLogic.mk_UNIV qty) |>
      HOLogic.mk_Trueprop;
    fun typ_isom_tac ctxt i =
      EVERY' [ SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms type_definition_def}),
        DETERM o Transfer.transfer_tac true ctxt,
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms eq_onp_top_eq_eq}) (* normalize *), 
          Raw_Simplifier.rewrite_goal_tac ctxt 
          (map safe_mk_meta_eq @{thms id_apply simp_thms Ball_def}),
         rtac ctxt TrueI] i;

    val (_, transfer_ctxt) =
      Proof_Context.note_thms ""
        (Binding.empty_atts,
          [(@{thms right_total_UNIV_transfer}, [Transfer.transfer_add]),
           (@{thms Domain_eq_top}, [Transfer.transfer_domain_add])]) lthy6;

    val quot_thm_isom =
      Goal.prove_sorry transfer_ctxt [] [] typedef_goal
        (fn {context = goal_ctxt, ...} => typ_isom_tac goal_ctxt 1)
      |> Thm.close_derivation \<^here>
      |> singleton (Variable.export transfer_ctxt lthy6)
      |> (fn thm => @{thm UNIV_typedef_to_Quotient} OF [thm, @{thm reflexive}])
    val qty_isom_name = Tname qty_isom;
    val quot_isom_rep =
      let
        val (quotients : Lifting_Term.quotients) =
          Symtab.insert (Lifting_Info.quotient_eq)
            (qty_isom_name, {quot_thm = quot_thm_isom, pcr_info = NONE}) Symtab.empty
        val id_actions = { constr = K I, lift = K I, comp_lift = K I }
      in
        fn ctxt => fn (rty, qty) => Lifting_Term.prove_schematic_quot_thm id_actions quotients
          ctxt (rty, qty) () |> fst |> Lifting_Term.force_qty_type ctxt qty
          |> quot_thm_rep
      end;
    val (x, x_ctxt) = yield_singleton (mk_Frees "x") qty_isom lthy6;

    fun mk_ctr ctr ctr_Ts sels =
      let
        val sel_ret_Ts = map (dest_Const #> snd #> body_type) sels;

        fun rep_isom lthy t (rty, qty) =
          let
            val rep = quot_isom_rep lthy (rty, qty)
          in
            if is_Const rep andalso (rep |> dest_Const |> fst) = \<^const_name>\<open>id\<close> then
              t else rep $ t
          end;
      in
        @{fold 3} (fn sel => fn ctr_T => fn sel_ret_T => fn ctr =>
          ctr $ rep_isom x_ctxt (sel $ x) (ctr_T, sel_ret_T)) sels ctr_Ts sel_ret_Ts ctr
      end;

    (* stolen from Metis *)
    exception BREAK_LIST
    fun break_list (x :: xs) = (x, xs)
      | break_list _ = raise BREAK_LIST

    val (ctr, ctrs) = qty_ctrs |> rev |> break_list;
    val (ctr_Ts, ctr_Tss) = qty_ctr_Tss |> rev |> break_list;
    val (sel, rselss) = selss |> rev |> break_list;
    val rdiss = rev diss |> tl;

    val first_ctr = mk_ctr ctr ctr_Ts sel;

    fun mk_If_ctr dis ctr ctr_Ts sel elsex = mk_If (dis$x) (mk_ctr ctr ctr_Ts sel) elsex;

    val rhs = @{fold 4} mk_If_ctr rdiss ctrs ctr_Tss rselss first_ctr;

    val rep_isom_code_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (rep_isom$x, rhs));

    local
      val rep_isom_code_tac_rules = map safe_mk_meta_eq @{thms refl id_apply if_splits simp_thms}
    in
      fun rep_isom_code_tac (ctr_sugar:Ctr_Sugar.ctr_sugar) ctxt i =
        let
          val exhaust = ctr_sugar |> #exhaust
          val cases = ctr_sugar |> #case_thms
          val map_ids = fp |> #fp_nesting_bnfs |> map BNF_Def.map_id0_of_bnf
          val simp_rules = map safe_mk_meta_eq (cases @ map_ids) @ rep_isom_code_tac_rules
        in
          EVERY' [Transfer.gen_frees_tac [] ctxt, DETERM o (Transfer.transfer_tac true ctxt),
            case_tac exhaust ctxt THEN_ALL_NEW EVERY' [hyp_subst_tac ctxt,
              Raw_Simplifier.rewrite_goal_tac ctxt simp_rules, rtac ctxt TrueI ]] i
        end
    end
    
    (* stolen from bnf_fp_n2m.ML *)
    fun force_typ ctxt T =
      Term.map_types Type_Infer.paramify_vars
      #> Type.constraint T
      #> singleton (Type_Infer_Context.infer_types ctxt);

    (* The following tests that types in rty have corresponding arities imposed by constraints of
       the datatype fp. Otherwise rep_isom_code_tac could fail (especially transfer in it) is such
       a way that it is not easy to infer the problem with sorts.
    *)
    val _ = yield_singleton (mk_Frees "x") (#T fp) x_ctxt |> fst |> force_typ x_ctxt qty

    val rep_isom_code =
      Goal.prove_sorry x_ctxt [] [] rep_isom_code_goal
        (fn {context = goal_ctxt, ...} => rep_isom_code_tac ctr_sugar goal_ctxt 1)
      |> Thm.close_derivation \<^here>
      |> singleton(Variable.export x_ctxt lthy6)
  in
    lthy6
    |> snd o Local_Theory.note ((Binding.empty, @{attributes [code]}), [rep_isom_code])
    |> Lifting_Setup.lifting_forget pointer
    |> pair (selss, diss, rep_isom_code)
  end
and constr qty (quot_thm, (lthy0, rel_eq_onps)) =
  let
    val quot_thm = Lifting_Term.force_qty_type lthy0 qty quot_thm
    val (rty, qty) = quot_thm_rty_qty quot_thm
    val rty_name = Tname rty;
    val pred_data = Transfer.lookup_pred_data lthy0 rty_name
    val pred_data = if is_some pred_data then the pred_data
      else error ("code_dt: " ^ quote rty_name ^ " is not a datatype.")
    val rel_eq_onp = safe_mk_meta_eq (Transfer.rel_eq_onp pred_data);
    val rel_eq_onps = insert Thm.eq_thm rel_eq_onp rel_eq_onps
    fun R_conv ctxt =
      Conv.top_sweep_rewrs_conv @{thms eq_onp_top_eq_eq[symmetric, THEN eq_reflection]} ctxt
      then_conv Conv.rewr_conv rel_eq_onp
    val quot_thm =
      Conv.fconv_rule (HOLogic.Trueprop_conv (Quotient_R_conv (R_conv lthy0))) quot_thm;
  in
    if is_none (code_dt_of lthy0 (rty, qty)) then
      let
        val non_empty_pred = quot_thm RS @{thm type_definition_Quotient_not_empty}
        val pred = quot_thm_rel quot_thm |> dest_comb |> snd;
        val (pred, lthy1) = lthy0
          |> (snd o Local_Theory.begin_nested)
          |> yield_singleton (Variable.import_terms true) pred;
        val TFrees = Term.add_tfreesT qty []

        fun non_empty_typedef_tac non_empty_pred ctxt i =
          (Method.insert_tac ctxt [non_empty_pred] THEN' 
            SELECT_GOAL (Local_Defs.unfold0_tac ctxt [mem_Collect_eq]) THEN' assume_tac ctxt) i
        val uTname = unique_Tname (rty, qty)
        val Tdef_set = HOLogic.mk_Collect ("x", rty, pred $ Free("x", rty));
        val ((_, tcode_dt), lthy2) = lthy1
          |> conceal_naming_result
            (typedef (Binding.concealed uTname, TFrees, NoSyn)
              Tdef_set NONE (fn lthy => HEADGOAL (non_empty_typedef_tac non_empty_pred lthy)));
        val type_definition_thm = tcode_dt |> snd |> #type_definition;
        val qty_isom = tcode_dt |> fst |> #abs_type;

        val (binding, lthy3) = lthy2
          |> conceal_naming_result
            (Lifting_Setup.setup_by_typedef_thm {notes = false} type_definition_thm)
          ||> Local_Theory.end_nested
        val (wit, wit_thm) = mk_witness quot_thm;
        val code_dt = mk_code_dt rty qty wit wit_thm NONE;
        val lthy4 = lthy3
          |> update_code_dt code_dt
          |> mk_rep_isom binding (rty, qty, qty_isom) |> snd
      in
        (quot_thm, (lthy4, rel_eq_onps))
      end
    else
      (quot_thm, (lthy0, rel_eq_onps))
  end
and lift_def_code_dt config = gen_lift_def (add_lift_def_code_dt config)


(** from parsed parameters to the config record **)

fun map_config_code_dt f1 f2 ({code_dt = code_dt, lift_config = lift_config}: config_code_dt) =
  {code_dt = f1 code_dt, lift_config = f2 lift_config}

fun update_config_code_dt nval = map_config_code_dt (K nval) I

val config_flags = [("code_dt", update_config_code_dt true)]

fun evaluate_params params =
  let
    fun eval_param param config =
      case AList.lookup (op =) config_flags param of
        SOME update => update config
        | NONE => error ("Unknown parameter: " ^ (quote param))
  in
    fold eval_param params default_config_code_dt
  end

(**

  lift_definition command. It opens a proof of a corresponding respectfulness
  theorem in a user-friendly, readable form. Then add_lift_def_code_dt is called internally.

**)

local
  val eq_onp_assms_tac_fixed_rules = map (Transfer.prep_transfer_domain_thm \<^context>)
    [@{thm pcr_Domainp_total}, @{thm pcr_Domainp_par_left_total}, @{thm pcr_Domainp_par}, 
      @{thm pcr_Domainp}]
in
fun mk_readable_rsp_thm_eq tm ctxt =
  let
    val ctm = Thm.cterm_of ctxt tm
    
    fun assms_rewr_conv tactic rule ct =
      let
        fun prove_extra_assms thm =
          let
            val assms = cprems_of thm
            fun finish thm = if Thm.no_prems thm then SOME (Goal.conclude thm) else NONE
            fun prove ctm = Option.mapPartial finish (SINGLE tactic (Goal.init ctm))
          in
            map_interrupt prove assms
          end
    
        fun cconl_of thm = Drule.strip_imp_concl (Thm.cprop_of thm)
        fun lhs_of thm = fst (Thm.dest_equals (cconl_of thm))
        fun rhs_of thm = snd (Thm.dest_equals (cconl_of thm))
        val rule1 = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
        val lhs = lhs_of rule1;
        val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1;
        val rule3 =
          Thm.instantiate (Thm.match (lhs, ct)) rule2
            handle Pattern.MATCH => raise CTERM ("assms_rewr_conv", [lhs, ct]);
        val proved_assms = prove_extra_assms rule3
      in
        case proved_assms of
          SOME proved_assms =>
            let
              val rule3 = proved_assms MRSL rule3
              val rule4 =
                if lhs_of rule3 aconvc ct then rule3
                else
                  let val ceq = Thm.dest_fun2 (Thm.cprop_of rule3)
                  in rule3 COMP Thm.trivial (Thm.mk_binop ceq ct (rhs_of rule3)) end
            in Thm.transitive rule4 (Thm.beta_conversion true (rhs_of rule4)) end
          | NONE => Conv.no_conv ct
      end

    fun assms_rewrs_conv tactic rules = Conv.first_conv (map (assms_rewr_conv tactic) rules)

    fun simp_arrows_conv ctm =
      let
        val unfold_conv = Conv.rewrs_conv 
          [@{thm rel_fun_eq_eq_onp[THEN eq_reflection]}, 
            @{thm rel_fun_eq_onp_rel[THEN eq_reflection]},
            @{thm rel_fun_eq[THEN eq_reflection]},
            @{thm rel_fun_eq_rel[THEN eq_reflection]}, 
            @{thm rel_fun_def[THEN eq_reflection]}]
        fun binop_conv2 cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
        val eq_onp_assms_tac_rules = @{thm left_unique_OO} :: 
            eq_onp_assms_tac_fixed_rules @ (Transfer.get_transfer_raw ctxt)
        val intro_top_rule = @{thm eq_onp_top_eq_eq[symmetric, THEN eq_reflection]}
        val kill_tops = Conv.top_sweep_rewrs_conv @{thms eq_onp_top_eq_eq[THEN eq_reflection]} ctxt
        val eq_onp_assms_tac = (CONVERSION kill_tops THEN' 
          TRY o REPEAT_ALL_NEW (resolve_tac ctxt eq_onp_assms_tac_rules) 
          THEN_ALL_NEW (DETERM o Transfer.eq_tac ctxt)) 1
        val relator_eq_onp_conv = Conv.bottom_conv
          (K (Conv.try_conv (assms_rewrs_conv eq_onp_assms_tac
            (intro_top_rule :: Lifting_Info.get_relator_eq_onp_rules ctxt)))) ctxt
          then_conv kill_tops
        val relator_eq_conv = Conv.bottom_conv
          (K (Conv.try_conv (Conv.rewrs_conv (Transfer.get_relator_eq ctxt)))) ctxt
      in
        case (Thm.term_of ctm) of
          Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _ => 
            (binop_conv2 simp_arrows_conv simp_arrows_conv then_conv unfold_conv) ctm
          | _ => (relator_eq_onp_conv then_conv relator_eq_conv) ctm
      end
    
    val unfold_ret_val_invs = Conv.bottom_conv 
      (K (Conv.try_conv (Conv.rewr_conv @{thm eq_onp_same_args[THEN eq_reflection]}))) ctxt
    val unfold_inv_conv = 
      Conv.top_sweep_rewrs_conv @{thms eq_onp_def[THEN eq_reflection]} ctxt
    val simp_conv = HOLogic.Trueprop_conv (Conv.fun2_conv simp_arrows_conv)
    val univq_conv = Conv.rewr_conv @{thm HOL.all_simps(6)[symmetric, THEN eq_reflection]}
    val univq_prenex_conv = Conv.top_conv (K (Conv.try_conv univq_conv)) ctxt
    val beta_conv = Thm.beta_conversion true
    val eq_thm = 
      (simp_conv then_conv univq_prenex_conv then_conv beta_conv then_conv unfold_ret_val_invs
         then_conv unfold_inv_conv) ctm
  in
    Object_Logic.rulify ctxt (eq_thm RS Drule.equal_elim_rule2)
  end
end

fun rename_to_tnames ctxt term =
  let
    fun all_typs (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, T, t)) = T :: all_typs t
      | all_typs _ = []

    fun rename (Const (\<^const_name>\<open>Pure.all\<close>, T1) $ Abs (_, T2, t)) (new_name :: names) = 
        (Const (\<^const_name>\<open>Pure.all\<close>, T1) $ Abs (new_name, T2, rename t names)) 
      | rename t _ = t

    val (fixed_def_t, _) = yield_singleton (Variable.importT_terms) term ctxt
    val new_names = Old_Datatype_Prop.make_tnames (all_typs fixed_def_t)
  in
    rename term new_names
  end

fun quot_thm_err ctxt (rty, qty) pretty_msg =
  let
    val error_msg = cat_lines
       ["Lifting failed for the following types:",
        Pretty.string_of (Pretty.block
         [Pretty.str "Raw type:", Pretty.brk 2, Syntax.pretty_typ ctxt rty]),
        Pretty.string_of (Pretty.block
         [Pretty.str "Abstract type:", Pretty.brk 2, Syntax.pretty_typ ctxt qty]),
        "",
        (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:", Pretty.brk 2, pretty_msg]))]
  in
    error error_msg
  end

fun check_rty_err ctxt (rty_schematic, rty_forced) (raw_var, rhs_raw) =
  let
    val (_, ctxt') = Proof_Context.read_var raw_var ctxt
    val rhs = Syntax.read_term ctxt' rhs_raw
    val error_msg = cat_lines
       ["Lifting failed for the following term:",
        Pretty.string_of (Pretty.block
         [Pretty.str "Term:", Pretty.brk 2, Syntax.pretty_term ctxt rhs]),
        Pretty.string_of (Pretty.block
         [Pretty.str "Type:", Pretty.brk 2, Syntax.pretty_typ ctxt rty_schematic]),
        "",
        (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:",
          Pretty.brk 2,
          Pretty.str "The type of the term cannot be instantiated to",
          Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt rty_forced),
          Pretty.str "."]))]
    in
      error error_msg
    end

fun lift_def_cmd (params, raw_var, rhs_raw, par_xthms) lthy0 =
  let
    val config = evaluate_params params
    val ((binding, SOME qty, mx), lthy1) = Proof_Context.read_var raw_var lthy0
    val var = (binding, mx)
    val rhs = Syntax.read_term lthy1 rhs_raw
    val par_thms = Attrib.eval_thms lthy1 par_xthms
    val (goal, after_qed) = lthy1
      |> prepare_lift_def (add_lift_def_code_dt config) var qty rhs par_thms
    val (goal, after_qed) =
      case goal of
        NONE => (goal, K (after_qed Drule.dummy_thm))
        | SOME prsp_tm =>
          let
            val readable_rsp_thm_eq = mk_readable_rsp_thm_eq prsp_tm lthy1
            val (readable_rsp_tm, _) = Logic.dest_implies (Thm.prop_of readable_rsp_thm_eq)
            val readable_rsp_tm_tnames = rename_to_tnames lthy1 readable_rsp_tm
        
            fun after_qed' [[thm]] lthy = 
              let
                val internal_rsp_thm =
                  Goal.prove lthy [] [] prsp_tm (fn {context = goal_ctxt, ...} =>
                    rtac goal_ctxt readable_rsp_thm_eq 1 THEN
                    Proof_Context.fact_tac goal_ctxt [thm] 1)
              in after_qed internal_rsp_thm lthy end
          in (SOME readable_rsp_tm_tnames, after_qed') end
    fun after_qed_with_err_handling thmss ctxt = (after_qed thmss ctxt
      handle Lifting_Term.QUOT_THM (rty, qty, msg) => quot_thm_err lthy1 (rty, qty) msg)
      handle Lifting_Term.CHECK_RTY (rty_schematic, rty_forced) =>
        check_rty_err lthy1 (rty_schematic, rty_forced) (raw_var, rhs_raw);
  in
    lthy1
    |> Proof.theorem NONE (snd oo after_qed_with_err_handling) [map (rpair []) (the_list goal)]
  end

fun lift_def_cmd_with_err_handling (params, (raw_var, rhs_raw, par_xthms)) lthy =
  (lift_def_cmd (params, raw_var, rhs_raw, par_xthms) lthy
    handle Lifting_Term.QUOT_THM (rty, qty, msg) => quot_thm_err lthy (rty, qty) msg)
    handle Lifting_Term.CHECK_RTY (rty_schematic, rty_forced) =>
      check_rty_err lthy (rty_schematic, rty_forced) (raw_var, rhs_raw);

val parse_param = Parse.name
val parse_params = Scan.optional (Args.parens (Parse.list parse_param)) [];


(* command syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>lift_definition\<close>
    "definition for constants over the quotient type"
    (parse_params --
      (((Parse.binding -- (\<^keyword>\<open>::\<close> |-- (Parse.typ >> SOME) -- Parse.opt_mixfix')
          >> Scan.triple2) --
        (\<^keyword>\<open>is\<close> |-- Parse.term) --
        Scan.optional (\<^keyword>\<open>parametric\<close> |-- Parse.!!! Parse.thms1) []) >> Scan.triple1)
     >> lift_def_cmd_with_err_handling);

end
