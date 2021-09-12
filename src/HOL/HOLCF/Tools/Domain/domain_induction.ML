(*  Title:      HOL/HOLCF/Tools/Domain/domain_induction.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Proofs of high-level (co)induction rules for domain command.
*)

signature DOMAIN_INDUCTION =
sig
  val comp_theorems :
      binding list ->
      Domain_Take_Proofs.take_induct_info ->
      Domain_Constructors.constr_info list ->
      theory -> thm list * theory

  val quiet_mode: bool Unsynchronized.ref
  val trace_domain: bool Unsynchronized.ref
end

structure Domain_Induction : DOMAIN_INDUCTION =
struct

val quiet_mode = Unsynchronized.ref false
val trace_domain = Unsynchronized.ref false

fun message s = if !quiet_mode then () else writeln s
fun trace s = if !trace_domain then tracing s else ()

open HOLCF_Library

(******************************************************************************)
(***************************** proofs about take ******************************)
(******************************************************************************)

fun take_theorems
    (dbinds : binding list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (constr_infos : Domain_Constructors.constr_info list)
    (thy : theory) : thm list list * theory =
let
  val {take_consts, take_Suc_thms, deflation_take_thms, ...} = take_info
  val deflation_thms = Domain_Take_Proofs.get_deflation_thms thy

  val n = Free ("n", \<^typ>\<open>nat\<close>)
  val n' = \<^Const>\<open>Suc for n\<close>

  local
    val newTs = map (#absT o #iso_info) constr_infos
    val subs = newTs ~~ map (fn t => t $ n) take_consts
    fun is_ID \<^Const_>\<open>ID _\<close> = true
      | is_ID _ = false
  in
    fun map_of_arg thy v T =
      let val m = Domain_Take_Proofs.map_of_typ thy subs T
      in if is_ID m then v else mk_capply (m, v) end
  end

  fun prove_take_apps
      ((dbind, take_const), constr_info) thy =
    let
      val {iso_info, con_specs, con_betas, ...} : Domain_Constructors.constr_info = constr_info
      val {abs_inverse, ...} = iso_info
      fun prove_take_app (con_const, args) =
        let
          val Ts = map snd args
          val ns = Name.variant_list ["n"] (Old_Datatype_Prop.make_tnames Ts)
          val vs = map Free (ns ~~ Ts)
          val lhs = mk_capply (take_const $ n', list_ccomb (con_const, vs))
          val rhs = list_ccomb (con_const, map2 (map_of_arg thy) vs Ts)
          val goal = mk_trp (mk_eq (lhs, rhs))
          val rules =
              [abs_inverse] @ con_betas @ @{thms take_con_rules}
              @ take_Suc_thms @ deflation_thms @ deflation_take_thms
          fun tac ctxt = simp_tac (put_simpset HOL_basic_ss ctxt addsimps rules) 1
        in
          Goal.prove_global thy [] [] goal (tac o #context)
        end
      val take_apps = map prove_take_app con_specs
    in
      yield_singleton Global_Theory.add_thmss
        ((Binding.qualify_name true dbind "take_rews", take_apps),
        [Simplifier.simp_add]) thy
    end
in
  fold_map prove_take_apps
    (dbinds ~~ take_consts ~~ constr_infos) thy
end

(******************************************************************************)
(****************************** induction rules *******************************)
(******************************************************************************)

val case_UU_allI =
    @{lemma "(\<And>x. x \<noteq> UU \<Longrightarrow> P x) \<Longrightarrow> P UU \<Longrightarrow> \<forall>x. P x" by metis}

fun prove_induction
    (comp_dbind : binding)
    (constr_infos : Domain_Constructors.constr_info list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (take_rews : thm list)
    (thy : theory) =
let
  val comp_dname = Binding.name_of comp_dbind

  val iso_infos = map #iso_info constr_infos
  val exhausts = map #exhaust constr_infos
  val con_rews = maps #con_rews constr_infos
  val {take_consts, take_induct_thms, ...} = take_info

  val newTs = map #absT iso_infos
  val P_names = Old_Datatype_Prop.indexify_names (map (K "P") newTs)
  val x_names = Old_Datatype_Prop.indexify_names (map (K "x") newTs)
  val P_types = map (fn T => T --> \<^Type>\<open>bool\<close>) newTs
  val Ps = map Free (P_names ~~ P_types)
  val xs = map Free (x_names ~~ newTs)
  val n = Free ("n", \<^Type>\<open>nat\<close>)

  fun con_assm defined p (con, args) =
    let
      val Ts = map snd args
      val ns = Name.variant_list P_names (Old_Datatype_Prop.make_tnames Ts)
      val vs = map Free (ns ~~ Ts)
      val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs))
      fun ind_hyp (v, T) t =
          case AList.lookup (op =) (newTs ~~ Ps) T of NONE => t
          | SOME p' => Logic.mk_implies (mk_trp (p' $ v), t)
      val t1 = mk_trp (p $ list_ccomb (con, vs))
      val t2 = fold_rev ind_hyp (vs ~~ Ts) t1
      val t3 = Logic.list_implies (map (mk_trp o mk_defined) nonlazy, t2)
    in fold_rev Logic.all vs (if defined then t3 else t2) end
  fun eq_assms ((p, T), cons) =
      mk_trp (p $ HOLCF_Library.mk_bottom T) :: map (con_assm true p) cons
  val assms = maps eq_assms (Ps ~~ newTs ~~ map #con_specs constr_infos)

  fun quant_tac ctxt i = EVERY
    (map (fn name =>
      Rule_Insts.res_inst_tac ctxt [((("x", 0), Position.none), name)] [] spec i) x_names)

  (* FIXME: move this message to domain_take_proofs.ML *)
  val is_finite = #is_finite take_info
  val _ = if is_finite
          then message ("Proving finiteness rule for domain "^comp_dname^" ...")
          else ()

  val _ = trace " Proving finite_ind..."
  val finite_ind =
    let
      val concls =
          map (fn ((P, t), x) => P $ mk_capply (t $ n, x))
              (Ps ~~ take_consts ~~ xs)
      val goal = mk_trp (foldr1 mk_conj concls)

      fun tacf {prems, context = ctxt} =
        let
          val take_ctxt = put_simpset HOL_ss ctxt addsimps (@{thm Rep_cfun_strict1} :: take_rews)

          (* Prove stronger prems, without definedness side conditions *)
          fun con_thm p (con, args) =
            let
              val subgoal = con_assm false p (con, args)
              val rules = prems @ con_rews @ @{thms simp_thms}
              val simplify = asm_simp_tac (put_simpset HOL_basic_ss ctxt addsimps rules)
              fun arg_tac (lazy, _) =
                  resolve_tac ctxt [if lazy then allI else case_UU_allI] 1
              fun tacs ctxt =
                  rewrite_goals_tac ctxt @{thms atomize_all atomize_imp} ::
                  map arg_tac args @
                  [REPEAT (resolve_tac ctxt [impI] 1), ALLGOALS simplify]
            in
              Goal.prove ctxt [] [] subgoal (EVERY o tacs o #context)
            end
          fun eq_thms (p, cons) = map (con_thm p) cons
          val conss = map #con_specs constr_infos
          val prems' = maps eq_thms (Ps ~~ conss)

          val tacs1 = [
            quant_tac ctxt 1,
            simp_tac (put_simpset HOL_ss ctxt) 1,
            Induct_Tacs.induct_tac ctxt [[SOME "n"]] NONE 1,
            simp_tac (take_ctxt addsimps prems) 1,
            TRY (safe_tac (put_claset HOL_cs ctxt))]
          fun con_tac _ = 
            asm_simp_tac take_ctxt 1 THEN
            (resolve_tac ctxt prems' THEN_ALL_NEW eresolve_tac ctxt [spec]) 1
          fun cases_tacs (cons, exhaust) =
            Rule_Insts.res_inst_tac ctxt [((("y", 0), Position.none), "x")] [] exhaust 1 ::
            asm_simp_tac (take_ctxt addsimps prems) 1 ::
            map con_tac cons
          val tacs = tacs1 @ maps cases_tacs (conss ~~ exhausts)
        in
          EVERY (map DETERM tacs)
        end
    in Goal.prove_global thy [] assms goal tacf end

  val _ = trace " Proving ind..."
  val ind =
    let
      val concls = map (op $) (Ps ~~ xs)
      val goal = mk_trp (foldr1 mk_conj concls)
      val adms = if is_finite then [] else map (mk_trp o mk_adm) Ps
      fun tacf {prems, context = ctxt} =
        let
          fun finite_tac (take_induct, fin_ind) =
              resolve_tac ctxt [take_induct] 1 THEN
              (if is_finite then all_tac else resolve_tac ctxt prems 1) THEN
              (resolve_tac ctxt [fin_ind] THEN_ALL_NEW solve_tac ctxt prems) 1
          val fin_inds = Project_Rule.projections ctxt finite_ind
        in
          TRY (safe_tac (put_claset HOL_cs ctxt)) THEN
          EVERY (map finite_tac (take_induct_thms ~~ fin_inds))
        end
    in Goal.prove_global thy [] (adms @ assms) goal tacf end

  (* case names for induction rules *)
  val dnames = map (fst o dest_Type) newTs
  val case_ns =
    let
      val adms =
          if is_finite then [] else
          if length dnames = 1 then ["adm"] else
          map (fn s => "adm_" ^ Long_Name.base_name s) dnames
      val bottoms =
          if length dnames = 1 then ["bottom"] else
          map (fn s => "bottom_" ^ Long_Name.base_name s) dnames
      fun one_eq bot (constr_info : Domain_Constructors.constr_info) =
        let fun name_of (c, _) = Long_Name.base_name (fst (dest_Const c))
        in bot :: map name_of (#con_specs constr_info) end
    in adms @ flat (map2 one_eq bottoms constr_infos) end

  val inducts = Project_Rule.projections (Proof_Context.init_global thy) ind
  fun ind_rule (dname, rule) =
      ((Binding.empty, rule),
       [Rule_Cases.case_names case_ns, Induct.induct_type dname])

in
  thy
  |> snd o Global_Theory.add_thms [
     ((Binding.qualify_name true comp_dbind "finite_induct", finite_ind), []),
     ((Binding.qualify_name true comp_dbind "induct", ind), [])]
  |> (snd o Global_Theory.add_thms (map ind_rule (dnames ~~ inducts)))
end (* prove_induction *)

(******************************************************************************)
(************************ bisimulation and coinduction ************************)
(******************************************************************************)

fun prove_coinduction
    (comp_dbind : binding, dbinds : binding list)
    (constr_infos : Domain_Constructors.constr_info list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (take_rews : thm list list)
    (thy : theory) : theory =
let
  val iso_infos = map #iso_info constr_infos
  val newTs = map #absT iso_infos

  val {take_consts, take_0_thms, take_lemma_thms, ...} = take_info

  val R_names = Old_Datatype_Prop.indexify_names (map (K "R") newTs)
  val R_types = map (fn T => T --> T --> \<^Type>\<open>bool\<close>) newTs
  val Rs = map Free (R_names ~~ R_types)
  val n = Free ("n", \<^Type>\<open>nat\<close>)
  val reserved = "x" :: "y" :: R_names

  (* declare bisimulation predicate *)
  val bisim_bind = Binding.suffix_name "_bisim" comp_dbind
  val bisim_type = R_types ---> \<^Type>\<open>bool\<close>
  val (bisim_const, thy) =
      Sign.declare_const_global ((bisim_bind, bisim_type), NoSyn) thy

  (* define bisimulation predicate *)
  local
    fun one_con T (con, args) =
      let
        val Ts = map snd args
        val ns1 = Name.variant_list reserved (Old_Datatype_Prop.make_tnames Ts)
        val ns2 = map (fn n => n^"'") ns1
        val vs1 = map Free (ns1 ~~ Ts)
        val vs2 = map Free (ns2 ~~ Ts)
        val eq1 = mk_eq (Free ("x", T), list_ccomb (con, vs1))
        val eq2 = mk_eq (Free ("y", T), list_ccomb (con, vs2))
        fun rel ((v1, v2), T) =
            case AList.lookup (op =) (newTs ~~ Rs) T of
              NONE => mk_eq (v1, v2) | SOME r => r $ v1 $ v2
        val eqs = foldr1 mk_conj (map rel (vs1 ~~ vs2 ~~ Ts) @ [eq1, eq2])
      in
        Library.foldr mk_ex (vs1 @ vs2, eqs)
      end
    fun one_eq ((T, R), cons) =
      let
        val x = Free ("x", T)
        val y = Free ("y", T)
        val disj1 = mk_conj (mk_eq (x, mk_bottom T), mk_eq (y, mk_bottom T))
        val disjs = disj1 :: map (one_con T) cons
      in
        mk_all (x, mk_all (y, mk_imp (R $ x $ y, foldr1 mk_disj disjs)))
      end
    val conjs = map one_eq (newTs ~~ Rs ~~ map #con_specs constr_infos)
    val bisim_rhs = lambdas Rs (Library.foldr1 mk_conj conjs)
    val bisim_eqn = Logic.mk_equals (bisim_const, bisim_rhs)
  in
    val (bisim_def_thm, thy) = thy |>
        yield_singleton (Global_Theory.add_defs false)
         ((Binding.qualify_name true comp_dbind "bisim_def", bisim_eqn), [])
  end (* local *)

  (* prove coinduction lemma *)
  val coind_lemma =
    let
      val assm = mk_trp (list_comb (bisim_const, Rs))
      fun one ((T, R), take_const) =
        let
          val x = Free ("x", T)
          val y = Free ("y", T)
          val lhs = mk_capply (take_const $ n, x)
          val rhs = mk_capply (take_const $ n, y)
        in
          mk_all (x, mk_all (y, mk_imp (R $ x $ y, mk_eq (lhs, rhs))))
        end
      val goal =
          mk_trp (foldr1 mk_conj (map one (newTs ~~ Rs ~~ take_consts)))
      val rules = @{thm Rep_cfun_strict1} :: take_0_thms
      fun tacf {prems, context = ctxt} =
        let
          val prem' = rewrite_rule ctxt [bisim_def_thm] (hd prems)
          val prems' = Project_Rule.projections ctxt prem'
          val dests = map (fn th => th RS spec RS spec RS mp) prems'
          fun one_tac (dest, rews) =
              dresolve_tac ctxt [dest] 1 THEN safe_tac (put_claset HOL_cs ctxt) THEN
              ALLGOALS (asm_simp_tac (put_simpset HOL_basic_ss ctxt addsimps rews))
        in
          resolve_tac ctxt @{thms nat.induct} 1 THEN
          simp_tac (put_simpset HOL_ss ctxt addsimps rules) 1 THEN
          safe_tac (put_claset HOL_cs ctxt) THEN
          EVERY (map one_tac (dests ~~ take_rews))
        end
    in
      Goal.prove_global thy [] [assm] goal tacf
    end

  (* prove individual coinduction rules *)
  fun prove_coind ((T, R), take_lemma) =
    let
      val x = Free ("x", T)
      val y = Free ("y", T)
      val assm1 = mk_trp (list_comb (bisim_const, Rs))
      val assm2 = mk_trp (R $ x $ y)
      val goal = mk_trp (mk_eq (x, y))
      fun tacf {prems, context = ctxt} =
        let
          val rule = hd prems RS coind_lemma
        in
          resolve_tac ctxt [take_lemma] 1 THEN
          asm_simp_tac (put_simpset HOL_basic_ss ctxt addsimps (rule :: prems)) 1
        end
    in
      Goal.prove_global thy [] [assm1, assm2] goal tacf
    end
  val coinds = map prove_coind (newTs ~~ Rs ~~ take_lemma_thms)
  val coind_binds = map (fn b => Binding.qualify_name true b "coinduct") dbinds

in
  thy |> snd o Global_Theory.add_thms
    (map Thm.no_attributes (coind_binds ~~ coinds))
end (* let *)

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun comp_theorems
    (dbinds : binding list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (constr_infos : Domain_Constructors.constr_info list)
    (thy : theory) =
let

val comp_dbind = Binding.conglomerate dbinds
val comp_dname = Binding.name_of comp_dbind

(* Test for emptiness *)
(* FIXME: reimplement emptiness test
local
  open Domain_Library
  val dnames = map (fst o fst) eqs
  val conss = map snd eqs
  fun rec_to ns lazy_rec (n,cons) = forall (exists (fn arg => 
        is_rec arg andalso not (member (op =) ns (rec_of arg)) andalso
        ((rec_of arg =  n andalso not (lazy_rec orelse is_lazy arg)) orelse 
          rec_of arg <> n andalso rec_to (rec_of arg::ns) 
            (lazy_rec orelse is_lazy arg) (n, nth conss (rec_of arg)))
        ) o snd) cons
  fun warn (n,cons) =
    if rec_to [] false (n,cons)
    then (warning ("domain " ^ nth dnames n ^ " is empty!") true)
    else false
in
  val n__eqs = mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs
  val is_emptys = map warn n__eqs
end
*)

(* Test for indirect recursion *)
local
  val newTs = map (#absT o #iso_info) constr_infos
  fun indirect_typ (Type (_, Ts)) =
      exists (fn T => member (op =) newTs T orelse indirect_typ T) Ts
    | indirect_typ _ = false
  fun indirect_arg (_, T) = indirect_typ T
  fun indirect_con (_, args) = exists indirect_arg args
  fun indirect_eq cons = exists indirect_con cons
in
  val is_indirect = exists indirect_eq (map #con_specs constr_infos)
  val _ =
      if is_indirect
      then message "Indirect recursion detected, skipping proofs of (co)induction rules"
      else message ("Proving induction properties of domain "^comp_dname^" ...")
end

(* theorems about take *)

val (take_rewss, thy) =
    take_theorems dbinds take_info constr_infos thy

val {take_0_thms, take_strict_thms, ...} = take_info

val take_rews = take_0_thms @ take_strict_thms @ flat take_rewss

(* prove induction rules, unless definition is indirect recursive *)
val thy =
    if is_indirect then thy else
    prove_induction comp_dbind constr_infos take_info take_rews thy

val thy =
    if is_indirect then thy else
    prove_coinduction (comp_dbind, dbinds) constr_infos take_info take_rewss thy

in
  (take_rews, thy)
end (* let *)
end (* struct *)
