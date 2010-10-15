(*  Title:      HOLCF/Tools/Domain/domain_theorems.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Proof generator for domain command.
*)

val HOLCF_ss = @{simpset};

signature DOMAIN_THEOREMS =
sig
  val comp_theorems :
      binding * Domain_Library.eq list ->
      binding list ->
      Domain_Take_Proofs.take_induct_info ->
      Domain_Constructors.constr_info list ->
      theory -> thm list * theory

  val quiet_mode: bool Unsynchronized.ref;
  val trace_domain: bool Unsynchronized.ref;
end;

structure Domain_Theorems :> DOMAIN_THEOREMS =
struct

val quiet_mode = Unsynchronized.ref false;
val trace_domain = Unsynchronized.ref false;

fun message s = if !quiet_mode then () else writeln s;
fun trace s = if !trace_domain then tracing s else ();

open HOLCF_Library;
infixr 0 ===>;
infix 0 == ; 
infix 1 ===;
infix 9 `   ;

(* ----- general proof facilities ------------------------------------------- *)

local

fun map_typ f g (Type (c, Ts)) = Type (g c, map (map_typ f g) Ts)
  | map_typ f _ (TFree (x, S)) = TFree (x, map f S)
  | map_typ f _ (TVar (xi, S)) = TVar (xi, map f S);

fun map_term f g h (Const (c, T)) = Const (h c, map_typ f g T)
  | map_term f g _ (Free (x, T)) = Free (x, map_typ f g T)
  | map_term f g _ (Var (xi, T)) = Var (xi, map_typ f g T)
  | map_term _ _ _ (t as Bound _) = t
  | map_term f g h (Abs (x, T, t)) = Abs (x, map_typ f g T, map_term f g h t)
  | map_term f g h (t $ u) = map_term f g h t $ map_term f g h u;

in

fun intern_term thy =
  map_term (Sign.intern_class thy) (Sign.intern_type thy) (Sign.intern_const thy);

end;

fun legacy_infer_term thy t =
  let val ctxt = ProofContext.set_mode ProofContext.mode_schematic (ProofContext.init_global thy)
  in singleton (Syntax.check_terms ctxt) (intern_term thy t) end;

fun pg'' thy defs t tacs =
  let
    val t' = legacy_infer_term thy t;
    val asms = Logic.strip_imp_prems t';
    val prop = Logic.strip_imp_concl t';
    fun tac {prems, context} =
      rewrite_goals_tac defs THEN
      EVERY (tacs {prems = map (rewrite_rule defs) prems, context = context})
  in Goal.prove_global thy [] asms prop tac end;

fun pg' thy defs t tacsf =
  let
    fun tacs {prems, context} =
      if null prems then tacsf context
      else cut_facts_tac prems 1 :: tacsf context;
  in pg'' thy defs t tacs end;

(******************************************************************************)
(***************************** proofs about take ******************************)
(******************************************************************************)

fun take_theorems
    (dbinds : binding list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (constr_infos : Domain_Constructors.constr_info list)
    (thy : theory) : thm list list * theory =
let
  val {take_consts, take_Suc_thms, deflation_take_thms, ...} = take_info;
  val deflation_thms = Domain_Take_Proofs.get_deflation_thms thy;

  val n = Free ("n", @{typ nat});
  val n' = @{const Suc} $ n;

  local
    val newTs = map (#absT o #iso_info) constr_infos;
    val subs = newTs ~~ map (fn t => t $ n) take_consts;
    fun is_ID (Const (c, _)) = (c = @{const_name ID})
      | is_ID _              = false;
  in
    fun map_of_arg v T =
      let val m = Domain_Take_Proofs.map_of_typ thy subs T;
      in if is_ID m then v else mk_capply (m, v) end;
  end

  fun prove_take_apps
      ((dbind, take_const), constr_info) thy =
    let
      val {iso_info, con_specs, con_betas, ...} = constr_info;
      val {abs_inverse, ...} = iso_info;
      fun prove_take_app (con_const, args) =
        let
          val Ts = map snd args;
          val ns = Name.variant_list ["n"] (Datatype_Prop.make_tnames Ts);
          val vs = map Free (ns ~~ Ts);
          val lhs = mk_capply (take_const $ n', list_ccomb (con_const, vs));
          val rhs = list_ccomb (con_const, map2 map_of_arg vs Ts);
          val goal = mk_trp (mk_eq (lhs, rhs));
          val rules =
              [abs_inverse] @ con_betas @ @{thms take_con_rules}
              @ take_Suc_thms @ deflation_thms @ deflation_take_thms;
          val tac = simp_tac (HOL_basic_ss addsimps rules) 1;
        in
          Goal.prove_global thy [] [] goal (K tac)
        end;
      val take_apps = map prove_take_app con_specs;
    in
      yield_singleton Global_Theory.add_thmss
        ((Binding.qualified true "take_rews" dbind, take_apps),
        [Simplifier.simp_add]) thy
    end;
in
  fold_map prove_take_apps
    (dbinds ~~ take_consts ~~ constr_infos) thy
end;

(* ----- general proofs ----------------------------------------------------- *)

val all2E = @{lemma "!x y . P x y ==> (P x y ==> R) ==> R" by simp}

val case_UU_allI =
    @{lemma "(!!x. x ~= UU ==> P x) ==> P UU ==> ALL x. P x" by metis};

(******************************************************************************)
(****************************** induction rules *******************************)
(******************************************************************************)

fun prove_induction
    (comp_dbind : binding, eqs : Domain_Library.eq list)
    (constr_infos : Domain_Constructors.constr_info list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (take_rews : thm list)
    (thy : theory) =
let
  val comp_dname = Sign.full_name thy comp_dbind;
  val dnames = map (fst o fst) eqs;
  val conss  = map  snd        eqs;

  val iso_infos = map #iso_info constr_infos;
  val axs_rep_iso = map #rep_inverse iso_infos;
  val axs_abs_iso = map #abs_inverse iso_infos;
  val exhausts = map #exhaust constr_infos;
  val con_rews = maps #con_rews constr_infos;

  val {take_consts, ...} = take_info;
  val {take_0_thms, take_Suc_thms, chain_take_thms, ...} = take_info;
  val {lub_take_thms, finite_defs, reach_thms, ...} = take_info;
  val {take_induct_thms, ...} = take_info;

  val newTs = map #absT iso_infos;
  val P_names = Datatype_Prop.indexify_names (map (K "P") dnames);
  val x_names = Datatype_Prop.indexify_names (map (K "x") dnames);
  val P_types = map (fn T => T --> HOLogic.boolT) newTs;
  val Ps = map Free (P_names ~~ P_types);
  val xs = map Free (x_names ~~ newTs);
  val n = Free ("n", HOLogic.natT);
  val taken = "n" :: P_names @ x_names;

  fun con_assm defined p (con, args) =
    let
      val Ts = map snd args;
      val ns = Name.variant_list P_names (Datatype_Prop.make_tnames Ts);
      val vs = map Free (ns ~~ Ts);
      val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs));
      fun ind_hyp (v, T) t =
          case AList.lookup (op =) (newTs ~~ Ps) T of NONE => t
          | SOME p' => Logic.mk_implies (mk_trp (p' $ v), t);
      val t1 = mk_trp (p $ list_ccomb (con, vs));
      val t2 = fold_rev ind_hyp (vs ~~ Ts) t1;
      val t3 = Logic.list_implies (map (mk_trp o mk_defined) nonlazy, t2);
    in fold_rev Logic.all vs (if defined then t3 else t2) end;
  fun eq_assms ((p, T), cons) =
      mk_trp (p $ HOLCF_Library.mk_bottom T) :: map (con_assm true p) cons;
  val assms = maps eq_assms (Ps ~~ newTs ~~ map #con_specs constr_infos);

  fun ind_term concls =
    Logic.list_implies (assms, mk_trp (foldr1 mk_conj concls));

  val take_ss = HOL_ss addsimps (@{thm Rep_CFun_strict1} :: take_rews);
  fun quant_tac ctxt i = EVERY
    (map (fn name => res_inst_tac ctxt [(("x", 0), name)] spec i) x_names);

  local
    open Domain_Library;
    fun rec_to ns lazy_rec (n,cons) = forall (exists (fn arg => 
          is_rec arg andalso not (member (op =) ns (rec_of arg)) andalso
          ((rec_of arg =  n andalso not (lazy_rec orelse is_lazy arg)) orelse 
            rec_of arg <> n andalso rec_to (rec_of arg::ns) 
              (lazy_rec orelse is_lazy arg) (n, (List.nth(conss,rec_of arg))))
          ) o snd) cons;
    fun warn (n,cons) =
      if rec_to [] false (n,cons)
      then (warning ("domain "^List.nth(dnames,n)^" is empty!"); true)
      else false;

  in
    val n__eqs = mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs;
    val is_emptys = map warn n__eqs;
    val is_finite = #is_finite take_info;
    val _ = if is_finite
            then message ("Proving finiteness rule for domain "^comp_dname^" ...")
            else ();
  end;
  val _ = trace " Proving finite_ind...";
  val finite_ind =
    let
      val concls =
          map (fn ((P, t), x) => P $ HOLCF_Library.mk_capply (t $ n, x))
              (Ps ~~ #take_consts take_info ~~ xs);
      val goal = mk_trp (foldr1 mk_conj concls);

      fun tacf {prems, context} =
        let
          (* Prove stronger prems, without definedness side conditions *)
          fun con_thm p (con, args) =
            let
              val subgoal = con_assm false p (con, args);
              val rules = prems @ con_rews @ simp_thms;
              val simplify = asm_simp_tac (HOL_basic_ss addsimps rules);
              fun arg_tac (lazy, _) =
                  rtac (if lazy then allI else case_UU_allI) 1;
              val tacs =
                  rewrite_goals_tac @{thms atomize_all atomize_imp} ::
                  map arg_tac args @
                  [REPEAT (rtac impI 1), ALLGOALS simplify];
            in
              Goal.prove context [] [] subgoal (K (EVERY tacs))
            end;
          fun eq_thms (p, cons) = map (con_thm p) cons;
          val conss = map #con_specs constr_infos;
          val prems' = maps eq_thms (Ps ~~ conss);

          val tacs1 = [
            quant_tac context 1,
            simp_tac HOL_ss 1,
            InductTacs.induct_tac context [[SOME "n"]] 1,
            simp_tac (take_ss addsimps prems) 1,
            TRY (safe_tac HOL_cs)];
          fun con_tac _ = 
            asm_simp_tac take_ss 1 THEN
            (resolve_tac prems' THEN_ALL_NEW etac spec) 1;
          fun cases_tacs (cons, exhaust) =
            res_inst_tac context [(("y", 0), "x")] exhaust 1 ::
            asm_simp_tac (take_ss addsimps prems) 1 ::
            map con_tac cons;
          val tacs = tacs1 @ maps cases_tacs (conss ~~ exhausts)
        in
          EVERY (map DETERM tacs)
        end;
    in Goal.prove_global thy [] assms goal tacf end;

(* ----- theorems concerning finiteness and induction ----------------------- *)

  val global_ctxt = ProofContext.init_global thy;

  val _ = trace " Proving ind...";
  val ind =
    let
      val concls = map (op $) (Ps ~~ xs);
      val goal = mk_trp (foldr1 mk_conj concls);
      val adms = if is_finite then [] else map (mk_trp o mk_adm) Ps;
      fun tacf {prems, context} =
        let
          fun finite_tac (take_induct, fin_ind) =
              rtac take_induct 1 THEN
              (if is_finite then all_tac else resolve_tac prems 1) THEN
              (rtac fin_ind THEN_ALL_NEW solve_tac prems) 1;
          val fin_inds = Project_Rule.projections context finite_ind;
        in
          TRY (safe_tac HOL_cs) THEN
          EVERY (map finite_tac (take_induct_thms ~~ fin_inds))
        end;
    in Goal.prove_global thy [] (adms @ assms) goal tacf end

val case_ns =
  let
    val adms =
        if is_finite then [] else
        if length dnames = 1 then ["adm"] else
        map (fn s => "adm_" ^ Long_Name.base_name s) dnames;
    val bottoms =
        if length dnames = 1 then ["bottom"] else
        map (fn s => "bottom_" ^ Long_Name.base_name s) dnames;
    fun one_eq bot (_,cons) =
          bot :: map (fn (c,_) => Long_Name.base_name c) cons;
  in adms @ flat (map2 one_eq bottoms eqs) end;

val inducts = Project_Rule.projections (ProofContext.init_global thy) ind;
fun ind_rule (dname, rule) =
    ((Binding.empty, [rule]),
     [Rule_Cases.case_names case_ns, Induct.induct_type dname]);

in
  thy
  |> snd o Global_Theory.add_thmss [
     ((Binding.qualified true "finite_induct" comp_dbind, [finite_ind]), []),
     ((Binding.qualified true "induct"        comp_dbind, [ind]       ), [])]
  |> (snd o Global_Theory.add_thmss (map ind_rule (dnames ~~ inducts)))
end; (* prove_induction *)

(******************************************************************************)
(************************ bisimulation and coinduction ************************)
(******************************************************************************)

fun prove_coinduction
    (comp_dbind : binding, eqs : Domain_Library.eq list)
    (take_rews : thm list)
    (take_lemmas : thm list)
    (thy : theory) : theory =
let
open Domain_Library;

val dnames = map (fst o fst) eqs;
val comp_dname = Sign.full_name thy comp_dbind;
fun dc_take dn = %%:(dn^"_take");
val x_name = idx_name dnames "x"; 
val n_eqs = length eqs;

(* ----- define bisimulation predicate -------------------------------------- *)

local
  open HOLCF_Library
  val dtypes  = map (Type o fst) eqs;
  val relprod = mk_tupleT (map (fn tp => tp --> tp --> boolT) dtypes);
  val bisim_bind = Binding.suffix_name "_bisim" comp_dbind;
  val bisim_type = relprod --> boolT;
in
  val (bisim_const, thy) =
      Sign.declare_const ((bisim_bind, bisim_type), NoSyn) thy;
end;

local

  fun legacy_infer_term thy t =
      singleton (Syntax.check_terms (ProofContext.init_global thy)) (intern_term thy t);
  fun legacy_infer_prop thy t = legacy_infer_term thy (Type.constraint propT t);
  fun infer_props thy = map (apsnd (legacy_infer_prop thy));
  fun add_defs_i x = Global_Theory.add_defs false (map Thm.no_attributes x);
  fun add_defs_infer defs thy = add_defs_i (infer_props thy defs) thy;

  fun one_con (con, args) =
    let
      val nonrec_args = filter_out is_rec args;
      val    rec_args = filter is_rec args;
      val    recs_cnt = length rec_args;
      val allargs     = nonrec_args @ rec_args
                        @ map (upd_vname (fn s=> s^"'")) rec_args;
      val allvns      = map vname allargs;
      fun vname_arg s arg = if is_rec arg then vname arg^s else vname arg;
      val vns1        = map (vname_arg "" ) args;
      val vns2        = map (vname_arg "'") args;
      val allargs_cnt = length nonrec_args + 2*recs_cnt;
      val rec_idxs    = (recs_cnt-1) downto 0;
      val nonlazy_idxs = map snd (filter_out (fn (arg,_) => is_lazy arg)
                                             (allargs~~((allargs_cnt-1) downto 0)));
      fun rel_app i ra = proj (Bound(allargs_cnt+2)) eqs (rec_of ra) $ 
                              Bound (2*recs_cnt-i) $ Bound (recs_cnt-i);
      val capps =
          List.foldr
            mk_conj
            (mk_conj(
             Bound(allargs_cnt+1)===list_ccomb(%%:con,map (bound_arg allvns) vns1),
             Bound(allargs_cnt+0)===list_ccomb(%%:con,map (bound_arg allvns) vns2)))
            (mapn rel_app 1 rec_args);
    in
      List.foldr
        mk_ex
        (Library.foldr mk_conj
                       (map (defined o Bound) nonlazy_idxs,capps)) allvns
    end;
  fun one_comp n (_,cons) =
      mk_all (x_name(n+1),
      mk_all (x_name(n+1)^"'",
      mk_imp (proj (Bound 2) eqs n $ Bound 1 $ Bound 0,
      foldr1 mk_disj (mk_conj(Bound 1 === UU,Bound 0 === UU)
                      ::map one_con cons))));
  val bisim_eqn =
      %%:(comp_dname^"_bisim") ==
         mk_lam("R", foldr1 mk_conj (mapn one_comp 0 eqs));

in
  val (ax_bisim_def, thy) =
      yield_singleton add_defs_infer
        (Binding.qualified true "bisim_def" comp_dbind, bisim_eqn) thy;
end; (* local *)

(* ----- theorem concerning coinduction ------------------------------------- *)

local
  val pg = pg' thy;
  val xs = mapn (fn n => K (x_name n)) 1 dnames;
  fun bnd_arg n i = Bound(2*(n_eqs - n)-i-1);
  val take_ss = HOL_ss addsimps (@{thm Rep_CFun_strict1} :: take_rews);
  val sproj = prj (fn s => K("fst("^s^")")) (fn s => K("snd("^s^")"));
  val _ = trace " Proving coind_lemma...";
  val coind_lemma =
    let
      fun mk_prj n _ = proj (%:"R") eqs n $ bnd_arg n 0 $ bnd_arg n 1;
      fun mk_eqn n dn =
        (dc_take dn $ %:"n" ` bnd_arg n 0) ===
        (dc_take dn $ %:"n" ` bnd_arg n 1);
      fun mk_all2 (x,t) = mk_all (x, mk_all (x^"'", t));
      val goal =
        mk_trp (mk_imp (%%:(comp_dname^"_bisim") $ %:"R",
          Library.foldr mk_all2 (xs,
            Library.foldr mk_imp (mapn mk_prj 0 dnames,
              foldr1 mk_conj (mapn mk_eqn 0 dnames)))));
      fun x_tacs ctxt n x = [
        rotate_tac (n+1) 1,
        etac all2E 1,
        eres_inst_tac ctxt [(("P", 1), sproj "R" eqs n^" "^x^" "^x^"'")] (mp RS disjE) 1,
        TRY (safe_tac HOL_cs),
        REPEAT (CHANGED (asm_simp_tac take_ss 1))];
      fun tacs ctxt = [
        rtac impI 1,
        InductTacs.induct_tac ctxt [[SOME "n"]] 1,
        simp_tac take_ss 1,
        safe_tac HOL_cs] @
        flat (mapn (x_tacs ctxt) 0 xs);
    in pg [ax_bisim_def] goal tacs end;
in
  val _ = trace " Proving coind...";
  val coind = 
    let
      fun mk_prj n x = mk_trp (proj (%:"R") eqs n $ %:x $ %:(x^"'"));
      fun mk_eqn x = %:x === %:(x^"'");
      val goal =
        mk_trp (%%:(comp_dname^"_bisim") $ %:"R") ===>
          Logic.list_implies (mapn mk_prj 0 xs,
            mk_trp (foldr1 mk_conj (map mk_eqn xs)));
      val tacs =
        TRY (safe_tac HOL_cs) ::
        maps (fn take_lemma => [
          rtac take_lemma 1,
          cut_facts_tac [coind_lemma] 1,
          fast_tac HOL_cs 1])
        take_lemmas;
    in pg [] goal (K tacs) end;
end; (* local *)

in thy |> snd o Global_Theory.add_thmss
    [((Binding.qualified true "coinduct" comp_dbind, [coind]), [])]
end; (* let *)

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun comp_theorems
    (comp_dbind : binding, eqs : Domain_Library.eq list)
    (dbinds : binding list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (constr_infos : Domain_Constructors.constr_info list)
    (thy : theory) =
let
val map_tab = Domain_Take_Proofs.get_map_tab thy;

val dnames = map (fst o fst) eqs;
val comp_dname = Sign.full_name thy comp_dbind;

(* ----- getting the composite axiom and definitions ------------------------ *)

(* Test for indirect recursion *)
local
  open Domain_Library;
  fun indirect_arg arg =
      rec_of arg = ~1 andalso Datatype_Aux.is_rec_type (dtyp_of arg);
  fun indirect_con (_, args) = exists indirect_arg args;
  fun indirect_eq (_, cons) = exists indirect_con cons;
in
  val is_indirect = exists indirect_eq eqs;
  val _ =
      if is_indirect
      then message "Indirect recursion detected, skipping proofs of (co)induction rules"
      else message ("Proving induction properties of domain "^comp_dname^" ...");
end;

(* theorems about take *)

val (take_rewss, thy) =
    take_theorems dbinds take_info constr_infos thy;

val {take_lemma_thms, take_0_thms, take_strict_thms, ...} = take_info;

val take_rews = take_0_thms @ take_strict_thms @ flat take_rewss;

(* prove induction rules, unless definition is indirect recursive *)
val thy =
    if is_indirect then thy else
    prove_induction (comp_dbind, eqs) constr_infos take_info take_rews thy;

val thy =
    if is_indirect then thy else
    prove_coinduction (comp_dbind, eqs) take_rews take_lemma_thms thy;

in
  (take_rews, thy)
end; (* let *)
end; (* struct *)
