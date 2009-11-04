(*  Title:      HOLCF/Tools/Domain/domain_theorems.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Proof generator for domain command.
*)

val HOLCF_ss = @{simpset};

signature DOMAIN_THEOREMS =
sig
  val theorems: Domain_Library.eq * Domain_Library.eq list -> theory -> thm list * theory;
  val comp_theorems: bstring * Domain_Library.eq list -> theory -> thm list * theory;
  val quiet_mode: bool Unsynchronized.ref;
  val trace_domain: bool Unsynchronized.ref;
end;

structure Domain_Theorems :> DOMAIN_THEOREMS =
struct

val quiet_mode = Unsynchronized.ref false;
val trace_domain = Unsynchronized.ref false;

fun message s = if !quiet_mode then () else writeln s;
fun trace s = if !trace_domain then tracing s else ();

local

val adm_impl_admw = @{thm adm_impl_admw};
val adm_all = @{thm adm_all};
val adm_conj = @{thm adm_conj};
val adm_subst = @{thm adm_subst};
val antisym_less_inverse = @{thm below_antisym_inverse};
val beta_cfun = @{thm beta_cfun};
val cfun_arg_cong = @{thm cfun_arg_cong};
val ch2ch_fst = @{thm ch2ch_fst};
val ch2ch_snd = @{thm ch2ch_snd};
val ch2ch_Rep_CFunL = @{thm ch2ch_Rep_CFunL};
val ch2ch_Rep_CFunR = @{thm ch2ch_Rep_CFunR};
val chain_iterate = @{thm chain_iterate};
val compact_ONE = @{thm compact_ONE};
val compact_sinl = @{thm compact_sinl};
val compact_sinr = @{thm compact_sinr};
val compact_spair = @{thm compact_spair};
val compact_up = @{thm compact_up};
val contlub_cfun_arg = @{thm contlub_cfun_arg};
val contlub_cfun_fun = @{thm contlub_cfun_fun};
val contlub_fst = @{thm contlub_fst};
val contlub_snd = @{thm contlub_snd};
val contlubE = @{thm contlubE};
val cont_const = @{thm cont_const};
val cont_id = @{thm cont_id};
val cont2cont_fst = @{thm cont2cont_fst};
val cont2cont_snd = @{thm cont2cont_snd};
val cont2cont_Rep_CFun = @{thm cont2cont_Rep_CFun};
val fix_def2 = @{thm fix_def2};
val injection_eq = @{thm injection_eq};
val injection_less = @{thm injection_below};
val lub_equal = @{thm lub_equal};
val monofun_cfun_arg = @{thm monofun_cfun_arg};
val retraction_strict = @{thm retraction_strict};
val spair_eq = @{thm spair_eq};
val spair_less = @{thm spair_below};
val sscase1 = @{thm sscase1};
val ssplit1 = @{thm ssplit1};
val strictify1 = @{thm strictify1};
val wfix_ind = @{thm wfix_ind};

val iso_intro       = @{thm iso.intro};
val iso_abs_iso     = @{thm iso.abs_iso};
val iso_rep_iso     = @{thm iso.rep_iso};
val iso_abs_strict  = @{thm iso.abs_strict};
val iso_rep_strict  = @{thm iso.rep_strict};
val iso_abs_defin'  = @{thm iso.abs_defin'};
val iso_rep_defin'  = @{thm iso.rep_defin'};
val iso_abs_defined = @{thm iso.abs_defined};
val iso_rep_defined = @{thm iso.rep_defined};
val iso_compact_abs = @{thm iso.compact_abs};
val iso_compact_rep = @{thm iso.compact_rep};
val iso_iso_swap    = @{thm iso.iso_swap};

val exh_start = @{thm exh_start};
val ex_defined_iffs = @{thms ex_defined_iffs};
val exh_casedist0 = @{thm exh_casedist0};
val exh_casedists = @{thms exh_casedists};

open Domain_Library;
infixr 0 ===>;
infixr 0 ==>;
infix 0 == ; 
infix 1 ===;
infix 1 ~= ;
infix 1 <<;
infix 1 ~<<;
infix 9 `   ;
infix 9 `% ;
infix 9 `%%;
infixr 9 oo;

(* ----- general proof facilities ------------------------------------------- *)

fun legacy_infer_term thy t =
  let val ctxt = ProofContext.set_mode ProofContext.mode_schematic (ProofContext.init thy)
  in singleton (Syntax.check_terms ctxt) (Sign.intern_term thy t) end;

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

fun case_UU_tac ctxt rews i v =
  InductTacs.case_tac ctxt (v^"=UU") i THEN
  asm_simp_tac (HOLCF_ss addsimps rews) i;

val chain_tac =
  REPEAT_DETERM o resolve_tac 
    [chain_iterate, ch2ch_Rep_CFunR, ch2ch_Rep_CFunL, ch2ch_fst, ch2ch_snd];

(* ----- general proofs ----------------------------------------------------- *)

val all2E = @{lemma "!x y . P x y ==> (P x y ==> R) ==> R" by simp}

val dist_eqI = @{lemma "!!x::'a::po. ~ x << y ==> x ~= y" by (blast dest!: below_antisym_inverse)}

in

fun theorems (((dname, _), cons) : eq, eqs : eq list) thy =
let

val _ = message ("Proving isomorphism properties of domain "^dname^" ...");
val pg = pg' thy;

(* ----- getting the axioms and definitions --------------------------------- *)

local
  fun ga s dn = PureThy.get_thm thy (dn ^ "." ^ s);
in
  val ax_abs_iso  = ga "abs_iso"  dname;
  val ax_rep_iso  = ga "rep_iso"  dname;
  val ax_when_def = ga "when_def" dname;
  fun get_def mk_name (con,_) = ga (mk_name con^"_def") dname;
  val axs_con_def = map (get_def extern_name) cons;
  val axs_dis_def = map (get_def dis_name) cons;
  val axs_mat_def = map (get_def mat_name) cons;
  val axs_pat_def = map (get_def pat_name) cons;
  val axs_sel_def =
    let
      fun def_of_sel sel = ga (sel^"_def") dname;
      fun def_of_arg arg = Option.map def_of_sel (sel_of arg);
      fun defs_of_con (_, args) = map_filter def_of_arg args;
    in
      maps defs_of_con cons
    end;
  val ax_copy_def = ga "copy_def" dname;
end; (* local *)

(* ----- theorems concerning the isomorphism -------------------------------- *)

val dc_abs  = %%:(dname^"_abs");
val dc_rep  = %%:(dname^"_rep");
val dc_copy = %%:(dname^"_copy");
val x_name = "x";

val iso_locale = iso_intro OF [ax_abs_iso, ax_rep_iso];
val abs_strict = ax_rep_iso RS (allI RS retraction_strict);
val rep_strict = ax_abs_iso RS (allI RS retraction_strict);
val abs_defin' = iso_locale RS iso_abs_defin';
val rep_defin' = iso_locale RS iso_rep_defin';
val iso_rews = map Drule.standard [ax_abs_iso,ax_rep_iso,abs_strict,rep_strict];

(* ----- generating beta reduction rules from definitions-------------------- *)

val _ = trace " Proving beta reduction rules...";

local
  fun arglist (Const _ $ Abs (s, _, t)) =
    let
      val (vars,body) = arglist t;
    in (s :: vars, body) end
    | arglist t = ([], t);
  fun bind_fun vars t = Library.foldr mk_All (vars, t);
  fun bound_vars 0 = []
    | bound_vars i = Bound (i-1) :: bound_vars (i - 1);
in
  fun appl_of_def def =
    let
      val (_ $ con $ lam) = concl_of def;
      val (vars, rhs) = arglist lam;
      val lhs = list_ccomb (con, bound_vars (length vars));
      val appl = bind_fun vars (lhs == rhs);
      val cs = ContProc.cont_thms lam;
      val betas = map (fn c => mk_meta_eq (c RS beta_cfun)) cs;
    in pg (def::betas) appl (K [rtac reflexive_thm 1]) end;
end;

val _ = trace "Proving when_appl...";
val when_appl = appl_of_def ax_when_def;
val _ = trace "Proving con_appls...";
val con_appls = map appl_of_def axs_con_def;

local
  fun arg2typ n arg =
    let val t = TVar (("'a", n), pcpoS)
    in (n + 1, if is_lazy arg then mk_uT t else t) end;

  fun args2typ n [] = (n, oneT)
    | args2typ n [arg] = arg2typ n arg
    | args2typ n (arg::args) =
    let
      val (n1, t1) = arg2typ n arg;
      val (n2, t2) = args2typ n1 args
    in (n2, mk_sprodT (t1, t2)) end;

  fun cons2typ n [] = (n,oneT)
    | cons2typ n [con] = args2typ n (snd con)
    | cons2typ n (con::cons) =
    let
      val (n1, t1) = args2typ n (snd con);
      val (n2, t2) = cons2typ n1 cons
    in (n2, mk_ssumT (t1, t2)) end;
in
  fun cons2ctyp cons = ctyp_of thy (snd (cons2typ 1 cons));
end;

local 
  val iso_swap = iso_locale RS iso_iso_swap;
  fun one_con (con, args) =
    let
      val vns = map vname args;
      val eqn = %:x_name === con_app2 con %: vns;
      val conj = foldr1 mk_conj (eqn :: map (defined o %:) (nonlazy args));
    in Library.foldr mk_ex (vns, conj) end;

  val conj_assoc = @{thm conj_assoc};
  val exh = foldr1 mk_disj ((%:x_name === UU) :: map one_con cons);
  val thm1 = instantiate' [SOME (cons2ctyp cons)] [] exh_start;
  val thm2 = rewrite_rule (map mk_meta_eq ex_defined_iffs) thm1;
  val thm3 = rewrite_rule [mk_meta_eq @{thm conj_assoc}] thm2;

  (* first 3 rules replace "x = UU \/ P" with "rep$x = UU \/ P" *)
  val tacs = [
    rtac disjE 1,
    etac (rep_defin' RS disjI1) 2,
    etac disjI2 2,
    rewrite_goals_tac [mk_meta_eq iso_swap],
    rtac thm3 1];
in
  val _ = trace " Proving exhaust...";
  val exhaust = pg con_appls (mk_trp exh) (K tacs);
  val _ = trace " Proving casedist...";
  val casedist =
    Drule.standard (rewrite_rule exh_casedists (exhaust RS exh_casedist0));
end;

local 
  fun bind_fun t = Library.foldr mk_All (when_funs cons, t);
  fun bound_fun i _ = Bound (length cons - i);
  val when_app = list_ccomb (%%:(dname^"_when"), mapn bound_fun 1 cons);
in
  val _ = trace " Proving when_strict...";
  val when_strict =
    let
      val axs = [when_appl, mk_meta_eq rep_strict];
      val goal = bind_fun (mk_trp (strict when_app));
      val tacs = [resolve_tac [sscase1, ssplit1, strictify1] 1];
    in pg axs goal (K tacs) end;

  val _ = trace " Proving when_apps...";
  val when_apps =
    let
      fun one_when n (con,args) =
        let
          val axs = when_appl :: con_appls;
          val goal = bind_fun (lift_defined %: (nonlazy args, 
                mk_trp (when_app`(con_app con args) ===
                       list_ccomb (bound_fun n 0, map %# args))));
          val tacs = [asm_simp_tac (HOLCF_ss addsimps [ax_abs_iso]) 1];
        in pg axs goal (K tacs) end;
    in mapn one_when 1 cons end;
end;
val when_rews = when_strict :: when_apps;

(* ----- theorems concerning the constructors, discriminators and selectors - *)

local
  fun dis_strict (con, _) =
    let
      val goal = mk_trp (strict (%%:(dis_name con)));
    in pg axs_dis_def goal (K [rtac when_strict 1]) end;

  fun dis_app c (con, args) =
    let
      val lhs = %%:(dis_name c) ` con_app con args;
      val rhs = if con = c then TT else FF;
      val goal = lift_defined %: (nonlazy args, mk_trp (lhs === rhs));
      val tacs = [asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
    in pg axs_dis_def goal (K tacs) end;

  val _ = trace " Proving dis_apps...";
  val dis_apps = maps (fn (c,_) => map (dis_app c) cons) cons;

  fun dis_defin (con, args) =
    let
      val goal = defined (%:x_name) ==> defined (%%:(dis_name con) `% x_name);
      val tacs =
        [rtac casedist 1,
         contr_tac 1,
         DETERM_UNTIL_SOLVED (CHANGED
          (asm_simp_tac (HOLCF_ss addsimps dis_apps) 1))];
    in pg [] goal (K tacs) end;

  val _ = trace " Proving dis_stricts...";
  val dis_stricts = map dis_strict cons;
  val _ = trace " Proving dis_defins...";
  val dis_defins = map dis_defin cons;
in
  val dis_rews = dis_stricts @ dis_defins @ dis_apps;
end;

local
  fun mat_strict (con, _) =
    let
      val goal = mk_trp (%%:(mat_name con) ` UU ` %:"rhs" === UU);
      val tacs = [asm_simp_tac (HOLCF_ss addsimps [when_strict]) 1];
    in pg axs_mat_def goal (K tacs) end;

  val _ = trace " Proving mat_stricts...";
  val mat_stricts = map mat_strict cons;

  fun one_mat c (con, args) =
    let
      val lhs = %%:(mat_name c) ` con_app con args ` %:"rhs";
      val rhs =
        if con = c
        then list_ccomb (%:"rhs", map %# args)
        else mk_fail;
      val goal = lift_defined %: (nonlazy args, mk_trp (lhs === rhs));
      val tacs = [asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
    in pg axs_mat_def goal (K tacs) end;

  val _ = trace " Proving mat_apps...";
  val mat_apps =
    maps (fn (c,_) => map (one_mat c) cons) cons;
in
  val mat_rews = mat_stricts @ mat_apps;
end;

local
  fun ps args = mapn (fn n => fn _ => %:("pat" ^ string_of_int n)) 1 args;

  fun pat_lhs (con,args) = mk_branch (list_comb (%%:(pat_name con), ps args));

  fun pat_rhs (con,[]) = mk_return ((%:"rhs") ` HOLogic.unit)
    | pat_rhs (con,args) =
        (mk_branch (mk_ctuple_pat (ps args)))
          `(%:"rhs")`(mk_ctuple (map %# args));

  fun pat_strict c =
    let
      val axs = @{thm branch_def} :: axs_pat_def;
      val goal = mk_trp (strict (pat_lhs c ` (%:"rhs")));
      val tacs = [simp_tac (HOLCF_ss addsimps [when_strict]) 1];
    in pg axs goal (K tacs) end;

  fun pat_app c (con, args) =
    let
      val axs = @{thm branch_def} :: axs_pat_def;
      val lhs = (pat_lhs c)`(%:"rhs")`(con_app con args);
      val rhs = if con = fst c then pat_rhs c else mk_fail;
      val goal = lift_defined %: (nonlazy args, mk_trp (lhs === rhs));
      val tacs = [asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
    in pg axs goal (K tacs) end;

  val _ = trace " Proving pat_stricts...";
  val pat_stricts = map pat_strict cons;
  val _ = trace " Proving pat_apps...";
  val pat_apps = maps (fn c => map (pat_app c) cons) cons;
in
  val pat_rews = pat_stricts @ pat_apps;
end;

local
  fun con_strict (con, args) = 
    let
      val rules = abs_strict :: @{thms con_strict_rules};
      fun one_strict vn =
        let
          fun f arg = if vname arg = vn then UU else %# arg;
          val goal = mk_trp (con_app2 con f args === UU);
          val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1];
        in pg con_appls goal (K tacs) end;
    in map one_strict (nonlazy args) end;

  fun con_defin (con, args) =
    let
      fun iff_disj (t, []) = HOLogic.mk_not t
        | iff_disj (t, ts) = t === foldr1 HOLogic.mk_disj ts;
      val lhs = con_app con args === UU;
      val rhss = map (fn x => %:x === UU) (nonlazy args);
      val goal = mk_trp (iff_disj (lhs, rhss));
      val rule1 = iso_locale RS @{thm iso.abs_defined_iff};
      val rules = rule1 :: @{thms con_defined_iff_rules};
      val tacs = [simp_tac (HOL_ss addsimps rules) 1];
    in pg con_appls goal (K tacs) end;
in
  val _ = trace " Proving con_stricts...";
  val con_stricts = maps con_strict cons;
  val _ = trace " Proving con_defins...";
  val con_defins = map con_defin cons;
  val con_rews = con_stricts @ con_defins;
end;

local
  val rules =
    [compact_sinl, compact_sinr, compact_spair, compact_up, compact_ONE];
  fun con_compact (con, args) =
    let
      val concl = mk_trp (mk_compact (con_app con args));
      val goal = lift (fn x => mk_compact (%#x)) (args, concl);
      val tacs = [
        rtac (iso_locale RS iso_compact_abs) 1,
        REPEAT (resolve_tac rules 1 ORELSE atac 1)];
    in pg con_appls goal (K tacs) end;
in
  val _ = trace " Proving con_compacts...";
  val con_compacts = map con_compact cons;
end;

local
  fun one_sel sel =
    pg axs_sel_def (mk_trp (strict (%%:sel)))
      (K [simp_tac (HOLCF_ss addsimps when_rews) 1]);

  fun sel_strict (_, args) =
    map_filter (Option.map one_sel o sel_of) args;
in
  val _ = trace " Proving sel_stricts...";
  val sel_stricts = maps sel_strict cons;
end;

local
  fun sel_app_same c n sel (con, args) =
    let
      val nlas = nonlazy args;
      val vns = map vname args;
      val vnn = List.nth (vns, n);
      val nlas' = filter (fn v => v <> vnn) nlas;
      val lhs = (%%:sel)`(con_app con args);
      val goal = lift_defined %: (nlas', mk_trp (lhs === %:vnn));
      fun tacs1 ctxt =
        if vnn mem nlas
        then [case_UU_tac ctxt (when_rews @ con_stricts) 1 vnn]
        else [];
      val tacs2 = [asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
    in pg axs_sel_def goal (fn ctxt => (tacs1 ctxt @ tacs2)) end;

  fun sel_app_diff c n sel (con, args) =
    let
      val nlas = nonlazy args;
      val goal = mk_trp (%%:sel ` con_app con args === UU);
      fun tacs1 ctxt = map (case_UU_tac ctxt (when_rews @ con_stricts) 1) nlas;
      val tacs2 = [asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
    in pg axs_sel_def goal (fn ctxt => (tacs1 ctxt @ tacs2)) end;

  fun sel_app c n sel (con, args) =
    if con = c
    then sel_app_same c n sel (con, args)
    else sel_app_diff c n sel (con, args);

  fun one_sel c n sel = map (sel_app c n sel) cons;
  fun one_sel' c n arg = Option.map (one_sel c n) (sel_of arg);
  fun one_con (c, args) =
    flat (map_filter I (mapn (one_sel' c) 0 args));
in
  val _ = trace " Proving sel_apps...";
  val sel_apps = maps one_con cons;
end;

local
  fun sel_defin sel =
    let
      val goal = defined (%:x_name) ==> defined (%%:sel`%x_name);
      val tacs = [
        rtac casedist 1,
        contr_tac 1,
        DETERM_UNTIL_SOLVED (CHANGED
          (asm_simp_tac (HOLCF_ss addsimps sel_apps) 1))];
    in pg [] goal (K tacs) end;
in
  val _ = trace " Proving sel_defins...";
  val sel_defins =
    if length cons = 1
    then map_filter (fn arg => Option.map sel_defin (sel_of arg))
                 (filter_out is_lazy (snd (hd cons)))
    else [];
end;

val sel_rews = sel_stricts @ sel_defins @ sel_apps;

val _ = trace " Proving dist_les...";
val distincts_le =
  let
    fun dist (con1, args1) (con2, args2) =
      let
        val goal = lift_defined %: (nonlazy args1,
                        mk_trp (con_app con1 args1 ~<< con_app con2 args2));
        fun tacs ctxt = [
          rtac @{thm rev_contrapos} 1,
          eres_inst_tac ctxt [(("f", 0), dis_name con1)] monofun_cfun_arg 1]
          @ map (case_UU_tac ctxt (con_stricts @ dis_rews) 1) (nonlazy args2)
          @ [asm_simp_tac (HOLCF_ss addsimps dis_rews) 1];
      in pg [] goal tacs end;

    fun distinct (con1, args1) (con2, args2) =
        let
          val arg1 = (con1, args1);
          val arg2 =
            (con2, ListPair.map (fn (arg,vn) => upd_vname (K vn) arg)
              (args2, Name.variant_list (map vname args1) (map vname args2)));
        in [dist arg1 arg2, dist arg2 arg1] end;
    fun distincts []      = []
      | distincts (c::cs) = (map (distinct c) cs) :: distincts cs;
  in distincts cons end;
val dist_les = flat (flat distincts_le);

val _ = trace " Proving dist_eqs...";
val dist_eqs =
  let
    fun distinct (_,args1) ((_,args2), leqs) =
      let
        val (le1,le2) = (hd leqs, hd(tl leqs));
        val (eq1,eq2) = (le1 RS dist_eqI, le2 RS dist_eqI)
      in
        if nonlazy args1 = [] then [eq1, eq1 RS not_sym] else
        if nonlazy args2 = [] then [eq2, eq2 RS not_sym] else
          [eq1, eq2]
      end;
    fun distincts []      = []
      | distincts ((c,leqs)::cs) =
        flat
          (ListPair.map (distinct c) ((map #1 cs),leqs)) @
        distincts cs;
  in map Drule.standard (distincts (cons ~~ distincts_le)) end;

local 
  fun pgterm rel con args =
    let
      fun append s = upd_vname (fn v => v^s);
      val (largs, rargs) = (args, map (append "'") args);
      val concl =
        foldr1 mk_conj (ListPair.map rel (map %# largs, map %# rargs));
      val prem = rel (con_app con largs, con_app con rargs);
      val sargs = case largs of [_] => [] | _ => nonlazy args;
      val prop = lift_defined %: (sargs, mk_trp (prem === concl));
    in pg con_appls prop end;
  val cons' = filter (fn (_,args) => args<>[]) cons;
in
  val _ = trace " Proving inverts...";
  val inverts =
    let
      val abs_less = ax_abs_iso RS (allI RS injection_less);
      val tacs =
        [asm_full_simp_tac (HOLCF_ss addsimps [abs_less, spair_less]) 1];
    in map (fn (con, args) => pgterm (op <<) con args (K tacs)) cons' end;

  val _ = trace " Proving injects...";
  val injects =
    let
      val abs_eq = ax_abs_iso RS (allI RS injection_eq);
      val tacs = [asm_full_simp_tac (HOLCF_ss addsimps [abs_eq, spair_eq]) 1];
    in map (fn (con, args) => pgterm (op ===) con args (K tacs)) cons' end;
end;

(* ----- theorems concerning one induction step ----------------------------- *)

val copy_strict =
  let
    val _ = trace " Proving copy_strict...";
    val goal = mk_trp (strict (dc_copy `% "f"));
    val rules = [abs_strict, rep_strict] @ @{thms domain_fun_stricts};
    val tacs = [asm_simp_tac (HOLCF_ss addsimps rules) 1];
  in pg [ax_copy_def] goal (K tacs) end;

local
  fun copy_app (con, args) =
    let
      val lhs = dc_copy`%"f"`(con_app con args);
      fun one_rhs arg =
          if DatatypeAux.is_rec_type (dtyp_of arg)
          then Domain_Axioms.copy_of_dtyp (proj (%:"f") eqs) (dtyp_of arg) ` (%# arg)
          else (%# arg);
      val rhs = con_app2 con one_rhs args;
      val goal = lift_defined %: (nonlazy_rec args, mk_trp (lhs === rhs));
      val args' = filter_out (fn a => is_rec a orelse is_lazy a) args;
      val stricts = abs_strict :: rep_strict :: @{thms domain_fun_stricts};
      fun tacs1 ctxt = map (case_UU_tac ctxt stricts 1 o vname) args';
      val rules = [ax_abs_iso] @ @{thms domain_fun_simps};
      val tacs2 = [asm_simp_tac (HOLCF_ss addsimps rules) 1];
    in pg (ax_copy_def::con_appls) goal (fn ctxt => (tacs1 ctxt @ tacs2)) end;
in
  val _ = trace " Proving copy_apps...";
  val copy_apps = map copy_app cons;
end;

local
  fun one_strict (con, args) = 
    let
      val goal = mk_trp (dc_copy`UU`(con_app con args) === UU);
      val rews = copy_strict :: copy_apps @ con_rews;
      fun tacs ctxt = map (case_UU_tac ctxt rews 1) (nonlazy args) @
        [asm_simp_tac (HOLCF_ss addsimps rews) 1];
    in pg [] goal tacs end;

  fun has_nonlazy_rec (_, args) = exists is_nonlazy_rec args;
in
  val _ = trace " Proving copy_stricts...";
  val copy_stricts = map one_strict (filter has_nonlazy_rec cons);
end;

val copy_rews = copy_strict :: copy_apps @ copy_stricts;

in
  thy
    |> Sign.add_path (Long_Name.base_name dname)
    |> snd o PureThy.add_thmss [
        ((Binding.name "iso_rews"  , iso_rews    ), [Simplifier.simp_add]),
        ((Binding.name "exhaust"   , [exhaust]   ), []),
        ((Binding.name "casedist"  , [casedist]  ), [Induct.cases_type dname]),
        ((Binding.name "when_rews" , when_rews   ), [Simplifier.simp_add]),
        ((Binding.name "compacts"  , con_compacts), [Simplifier.simp_add]),
        ((Binding.name "con_rews"  , con_rews    ),
         [Simplifier.simp_add, Fixrec.fixrec_simp_add]),
        ((Binding.name "sel_rews"  , sel_rews    ), [Simplifier.simp_add]),
        ((Binding.name "dis_rews"  , dis_rews    ), [Simplifier.simp_add]),
        ((Binding.name "pat_rews"  , pat_rews    ), [Simplifier.simp_add]),
        ((Binding.name "dist_les"  , dist_les    ), [Simplifier.simp_add]),
        ((Binding.name "dist_eqs"  , dist_eqs    ), [Simplifier.simp_add]),
        ((Binding.name "inverts"   , inverts     ), [Simplifier.simp_add]),
        ((Binding.name "injects"   , injects     ), [Simplifier.simp_add]),
        ((Binding.name "copy_rews" , copy_rews   ), [Simplifier.simp_add]),
        ((Binding.name "match_rews", mat_rews    ),
         [Simplifier.simp_add, Fixrec.fixrec_simp_add])]
    |> Sign.parent_path
    |> pair (iso_rews @ when_rews @ con_rews @ sel_rews @ dis_rews @
        pat_rews @ dist_les @ dist_eqs @ copy_rews)
end; (* let *)

fun comp_theorems (comp_dnam, eqs: eq list) thy =
let
val global_ctxt = ProofContext.init thy;

val dnames = map (fst o fst) eqs;
val conss  = map  snd        eqs;
val comp_dname = Sign.full_bname thy comp_dnam;

val _ = message ("Proving induction properties of domain "^comp_dname^" ...");
val pg = pg' thy;

(* ----- getting the composite axiom and definitions ------------------------ *)

local
  fun ga s dn = PureThy.get_thm thy (dn ^ "." ^ s);
in
  val axs_reach      = map (ga "reach"     ) dnames;
  val axs_take_def   = map (ga "take_def"  ) dnames;
  val axs_finite_def = map (ga "finite_def") dnames;
  val ax_copy2_def   =      ga "copy_def"  comp_dnam;
  val ax_bisim_def   =      ga "bisim_def" comp_dnam;
end;

local
  fun gt  s dn = PureThy.get_thm  thy (dn ^ "." ^ s);
  fun gts s dn = PureThy.get_thms thy (dn ^ "." ^ s);
in
  val cases = map (gt  "casedist" ) dnames;
  val con_rews  = maps (gts "con_rews" ) dnames;
  val copy_rews = maps (gts "copy_rews") dnames;
end;

fun dc_take dn = %%:(dn^"_take");
val x_name = idx_name dnames "x"; 
val P_name = idx_name dnames "P";
val n_eqs = length eqs;

(* ----- theorems concerning finite approximation and finite induction ------ *)

local
  val iterate_Cprod_ss = global_simpset_of @{theory Fix};
  val copy_con_rews  = copy_rews @ con_rews;
  val copy_take_defs =
    (if n_eqs = 1 then [] else [ax_copy2_def]) @ axs_take_def;
  val _ = trace " Proving take_stricts...";
  val take_stricts =
    let
      fun one_eq ((dn, args), _) = strict (dc_take dn $ %:"n");
      val goal = mk_trp (foldr1 mk_conj (map one_eq eqs));
      fun tacs ctxt = [
        InductTacs.induct_tac ctxt [[SOME "n"]] 1,
        simp_tac iterate_Cprod_ss 1,
        asm_simp_tac (iterate_Cprod_ss addsimps copy_rews) 1];
    in pg copy_take_defs goal tacs end;

  val take_stricts' = rewrite_rule copy_take_defs take_stricts;
  fun take_0 n dn =
    let
      val goal = mk_trp ((dc_take dn $ %%:"HOL.zero") `% x_name n === UU);
    in pg axs_take_def goal (K [simp_tac iterate_Cprod_ss 1]) end;
  val take_0s = mapn take_0 1 dnames;
  fun c_UU_tac ctxt = case_UU_tac ctxt (take_stricts'::copy_con_rews) 1;
  val _ = trace " Proving take_apps...";
  val take_apps =
    let
      fun mk_eqn dn (con, args) =
        let
          fun mk_take n = dc_take (List.nth (dnames, n)) $ %:"n";
          fun one_rhs arg =
              if DatatypeAux.is_rec_type (dtyp_of arg)
              then Domain_Axioms.copy_of_dtyp mk_take (dtyp_of arg) ` (%# arg)
              else (%# arg);
          val lhs = (dc_take dn $ (%%:"Suc" $ %:"n"))`(con_app con args);
          val rhs = con_app2 con one_rhs args;
        in Library.foldr mk_all (map vname args, lhs === rhs) end;
      fun mk_eqns ((dn, _), cons) = map (mk_eqn dn) cons;
      val goal = mk_trp (foldr1 mk_conj (maps mk_eqns eqs));
      val simps = filter (has_fewer_prems 1) copy_rews;
      fun con_tac ctxt (con, args) =
        if nonlazy_rec args = []
        then all_tac
        else EVERY (map (c_UU_tac ctxt) (nonlazy_rec args)) THEN
          asm_full_simp_tac (HOLCF_ss addsimps copy_rews) 1;
      fun eq_tacs ctxt ((dn, _), cons) = map (con_tac ctxt) cons;
      fun tacs ctxt =
        simp_tac iterate_Cprod_ss 1 ::
        InductTacs.induct_tac ctxt [[SOME "n"]] 1 ::
        simp_tac (iterate_Cprod_ss addsimps copy_con_rews) 1 ::
        asm_full_simp_tac (HOLCF_ss addsimps simps) 1 ::
        TRY (safe_tac HOL_cs) ::
        maps (eq_tacs ctxt) eqs;
    in pg copy_take_defs goal tacs end;
in
  val take_rews = map Drule.standard
    (atomize global_ctxt take_stricts @ take_0s @ atomize global_ctxt take_apps);
end; (* local *)

local
  fun one_con p (con,args) =
    let
      fun ind_hyp arg = %:(P_name (1 + rec_of arg)) $ bound_arg args arg;
      val t1 = mk_trp (%:p $ con_app2 con (bound_arg args) args);
      val t2 = lift ind_hyp (filter is_rec args, t1);
      val t3 = lift_defined (bound_arg (map vname args)) (nonlazy args, t2);
    in Library.foldr mk_All (map vname args, t3) end;

  fun one_eq ((p, cons), concl) =
    mk_trp (%:p $ UU) ===> Logic.list_implies (map (one_con p) cons, concl);

  fun ind_term concf = Library.foldr one_eq
    (mapn (fn n => fn x => (P_name n, x)) 1 conss,
     mk_trp (foldr1 mk_conj (mapn concf 1 dnames)));
  val take_ss = HOL_ss addsimps take_rews;
  fun quant_tac ctxt i = EVERY
    (mapn (fn n => fn _ => res_inst_tac ctxt [(("x", 0), x_name n)] spec i) 1 dnames);

  fun ind_prems_tac prems = EVERY
    (maps (fn cons =>
      (resolve_tac prems 1 ::
        maps (fn (_,args) => 
          resolve_tac prems 1 ::
          map (K(atac 1)) (nonlazy args) @
          map (K(atac 1)) (filter is_rec args))
        cons))
      conss);
  local 
    (* check whether every/exists constructor of the n-th part of the equation:
       it has a possibly indirectly recursive argument that isn't/is possibly 
       indirectly lazy *)
    fun rec_to quant nfn rfn ns lazy_rec (n,cons) = quant (exists (fn arg => 
          is_rec arg andalso not(rec_of arg mem ns) andalso
          ((rec_of arg =  n andalso nfn(lazy_rec orelse is_lazy arg)) orelse 
            rec_of arg <> n andalso rec_to quant nfn rfn (rec_of arg::ns) 
              (lazy_rec orelse is_lazy arg) (n, (List.nth(conss,rec_of arg))))
          ) o snd) cons;
    fun all_rec_to ns  = rec_to forall not all_rec_to  ns;
    fun warn (n,cons) =
      if all_rec_to [] false (n,cons)
      then (warning ("domain "^List.nth(dnames,n)^" is empty!"); true)
      else false;
    fun lazy_rec_to ns = rec_to exists I  lazy_rec_to ns;

  in
    val n__eqs = mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs;
    val is_emptys = map warn n__eqs;
    val is_finite = forall (not o lazy_rec_to [] false) n__eqs;
  end;
in (* local *)
  val _ = trace " Proving finite_ind...";
  val finite_ind =
    let
      fun concf n dn = %:(P_name n) $ (dc_take dn $ %:"n" `%(x_name n));
      val goal = ind_term concf;

      fun tacf {prems, context} =
        let
          val tacs1 = [
            quant_tac context 1,
            simp_tac HOL_ss 1,
            InductTacs.induct_tac context [[SOME "n"]] 1,
            simp_tac (take_ss addsimps prems) 1,
            TRY (safe_tac HOL_cs)];
          fun arg_tac arg =
            case_UU_tac context (prems @ con_rews) 1
              (List.nth (dnames, rec_of arg) ^ "_take n$" ^ vname arg);
          fun con_tacs (con, args) = 
            asm_simp_tac take_ss 1 ::
            map arg_tac (filter is_nonlazy_rec args) @
            [resolve_tac prems 1] @
            map (K (atac 1)) (nonlazy args) @
            map (K (etac spec 1)) (filter is_rec args);
          fun cases_tacs (cons, cases) =
            res_inst_tac context [(("x", 0), "x")] cases 1 ::
            asm_simp_tac (take_ss addsimps prems) 1 ::
            maps con_tacs cons;
        in
          tacs1 @ maps cases_tacs (conss ~~ cases)
        end;
    in pg'' thy [] goal tacf
       handle ERROR _ => (warning "Proof of finite_ind failed."; TrueI)
    end;

  val _ = trace " Proving take_lemmas...";
  val take_lemmas =
    let
      fun take_lemma n (dn, ax_reach) =
        let
          val lhs = dc_take dn $ Bound 0 `%(x_name n);
          val rhs = dc_take dn $ Bound 0 `%(x_name n^"'");
          val concl = mk_trp (%:(x_name n) === %:(x_name n^"'"));
          val goal = mk_All ("n", mk_trp (lhs === rhs)) ===> concl;
          val rules = [contlub_fst RS contlubE RS ssubst,
                       contlub_snd RS contlubE RS ssubst];
          fun tacf {prems, context} = [
            res_inst_tac context [(("t", 0), x_name n    )] (ax_reach RS subst) 1,
            res_inst_tac context [(("t", 0), x_name n^"'")] (ax_reach RS subst) 1,
            stac fix_def2 1,
            REPEAT (CHANGED
              (resolve_tac rules 1 THEN chain_tac 1)),
            stac contlub_cfun_fun 1,
            stac contlub_cfun_fun 2,
            rtac lub_equal 3,
            chain_tac 1,
            rtac allI 1,
            resolve_tac prems 1];
        in pg'' thy axs_take_def goal tacf end;
    in mapn take_lemma 1 (dnames ~~ axs_reach) end;

(* ----- theorems concerning finiteness and induction ----------------------- *)

  val _ = trace " Proving finites, ind...";
  val (finites, ind) =
  (
    if is_finite
    then (* finite case *)
      let 
        fun take_enough dn = mk_ex ("n",dc_take dn $ Bound 0 ` %:"x" === %:"x");
        fun dname_lemma dn =
          let
            val prem1 = mk_trp (defined (%:"x"));
            val disj1 = mk_all ("n", dc_take dn $ Bound 0 ` %:"x" === UU);
            val prem2 = mk_trp (mk_disj (disj1, take_enough dn));
            val concl = mk_trp (take_enough dn);
            val goal = prem1 ===> prem2 ===> concl;
            val tacs = [
              etac disjE 1,
              etac notE 1,
              resolve_tac take_lemmas 1,
              asm_simp_tac take_ss 1,
              atac 1];
          in pg [] goal (K tacs) end;
        val _ = trace " Proving finite_lemmas1a";
        val finite_lemmas1a = map dname_lemma dnames;
 
        val _ = trace " Proving finite_lemma1b";
        val finite_lemma1b =
          let
            fun mk_eqn n ((dn, args), _) =
              let
                val disj1 = dc_take dn $ Bound 1 ` Bound 0 === UU;
                val disj2 = dc_take dn $ Bound 1 ` Bound 0 === Bound 0;
              in
                mk_constrainall
                  (x_name n, Type (dn,args), mk_disj (disj1, disj2))
              end;
            val goal =
              mk_trp (mk_all ("n", foldr1 mk_conj (mapn mk_eqn 1 eqs)));
            fun arg_tacs ctxt vn = [
              eres_inst_tac ctxt [(("x", 0), vn)] all_dupE 1,
              etac disjE 1,
              asm_simp_tac (HOL_ss addsimps con_rews) 1,
              asm_simp_tac take_ss 1];
            fun con_tacs ctxt (con, args) =
              asm_simp_tac take_ss 1 ::
              maps (arg_tacs ctxt) (nonlazy_rec args);
            fun foo_tacs ctxt n (cons, cases) =
              simp_tac take_ss 1 ::
              rtac allI 1 ::
              res_inst_tac ctxt [(("x", 0), x_name n)] cases 1 ::
              asm_simp_tac take_ss 1 ::
              maps (con_tacs ctxt) cons;
            fun tacs ctxt =
              rtac allI 1 ::
              InductTacs.induct_tac ctxt [[SOME "n"]] 1 ::
              simp_tac take_ss 1 ::
              TRY (safe_tac (empty_cs addSEs [conjE] addSIs [conjI])) ::
              flat (mapn (foo_tacs ctxt) 1 (conss ~~ cases));
          in pg [] goal tacs end;

        fun one_finite (dn, l1b) =
          let
            val goal = mk_trp (%%:(dn^"_finite") $ %:"x");
            fun tacs ctxt = [
              case_UU_tac ctxt take_rews 1 "x",
              eresolve_tac finite_lemmas1a 1,
              step_tac HOL_cs 1,
              step_tac HOL_cs 1,
              cut_facts_tac [l1b] 1,
              fast_tac HOL_cs 1];
          in pg axs_finite_def goal tacs end;

        val _ = trace " Proving finites";
        val finites = map one_finite (dnames ~~ atomize global_ctxt finite_lemma1b);
        val _ = trace " Proving ind";
        val ind =
          let
            fun concf n dn = %:(P_name n) $ %:(x_name n);
            fun tacf {prems, context} =
              let
                fun finite_tacs (finite, fin_ind) = [
                  rtac(rewrite_rule axs_finite_def finite RS exE)1,
                  etac subst 1,
                  rtac fin_ind 1,
                  ind_prems_tac prems];
              in
                TRY (safe_tac HOL_cs) ::
                maps finite_tacs (finites ~~ atomize global_ctxt finite_ind)
              end;
          in pg'' thy [] (ind_term concf) tacf end;
      in (finites, ind) end (* let *)

    else (* infinite case *)
      let
        fun one_finite n dn =
          read_instantiate global_ctxt [(("P", 0), dn ^ "_finite " ^ x_name n)] excluded_middle;
        val finites = mapn one_finite 1 dnames;

        val goal =
          let
            fun one_adm n _ = mk_trp (mk_adm (%:(P_name n)));
            fun concf n dn = %:(P_name n) $ %:(x_name n);
          in Logic.list_implies (mapn one_adm 1 dnames, ind_term concf) end;
        val cont_rules =
            [cont_id, cont_const, cont2cont_Rep_CFun,
             cont2cont_fst, cont2cont_snd];
        fun tacf {prems, context} =
          map (fn ax_reach => rtac (ax_reach RS subst) 1) axs_reach @ [
          quant_tac context 1,
          rtac (adm_impl_admw RS wfix_ind) 1,
          REPEAT_DETERM (rtac adm_all 1),
          REPEAT_DETERM (
            TRY (rtac adm_conj 1) THEN 
            rtac adm_subst 1 THEN 
            REPEAT (resolve_tac cont_rules 1) THEN
            resolve_tac prems 1),
          strip_tac 1,
          rtac (rewrite_rule axs_take_def finite_ind) 1,
          ind_prems_tac prems];
        val ind = (pg'' thy [] goal tacf
          handle ERROR _ =>
            (warning "Cannot prove infinite induction rule"; TrueI));
      in (finites, ind) end
  )
      handle THM _ =>
             (warning "Induction proofs failed (THM raised)."; ([], TrueI))
           | ERROR _ =>
             (warning "Induction proofs failed (ERROR raised)."; ([], TrueI));


end; (* local *)

(* ----- theorem concerning coinduction ------------------------------------- *)

local
  val xs = mapn (fn n => K (x_name n)) 1 dnames;
  fun bnd_arg n i = Bound(2*(n_eqs - n)-i-1);
  val take_ss = HOL_ss addsimps take_rews;
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

val inducts = Project_Rule.projections (ProofContext.init thy) ind;
fun ind_rule (dname, rule) = ((Binding.empty, [rule]), [Induct.induct_type dname]);
val induct_failed = (Thm.prop_of ind = Thm.prop_of TrueI);

in thy |> Sign.add_path comp_dnam
       |> snd o PureThy.add_thmss [
           ((Binding.name "take_rews"  , take_rews   ), [Simplifier.simp_add]),
           ((Binding.name "take_lemmas", take_lemmas ), []),
           ((Binding.name "finites"    , finites     ), []),
           ((Binding.name "finite_ind" , [finite_ind]), []),
           ((Binding.name "ind"        , [ind]       ), []),
           ((Binding.name "coind"      , [coind]     ), [])]
       |> (if induct_failed then I
           else snd o PureThy.add_thmss (map ind_rule (dnames ~~ inducts)))
       |> Sign.parent_path |> pair take_rews
end; (* let *)
end; (* local *)
end; (* struct *)
