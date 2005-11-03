(*  Title:      HOLCF/domain/theorems.ML
    ID:         $Id$
    Author:     David von Oheimb
                New proofs/tactics by Brian Huffman

Proof generator for domain section.
*)

val HOLCF_ss = simpset();

structure Domain_Theorems = struct

local

open Domain_Library;
infixr 0 ===>;infixr 0 ==>;infix 0 == ; 
infix 1 ===; infix 1 ~= ; infix 1 <<; infix 1 ~<<;
infix 9 `   ; infix 9 `% ; infix 9 `%%; infixr 9 oo;

(* ----- general proof facilities ------------------------------------------- *)

fun inferT sg pre_tm =
  #1 (Sign.infer_types (Sign.pp sg) sg (K NONE) (K NONE) [] true ([pre_tm],propT));

fun pg'' thy defs t tacs =
  let val t' = inferT thy t in
    standard (Goal.prove thy [] (Logic.strip_imp_prems t') (Logic.strip_imp_concl t')
      (fn prems => rewrite_goals_tac defs THEN EVERY (tacs (map (rewrite_rule defs) prems))))
  end;

fun pg'  thy defs t tacsf=pg'' thy defs t (fn []   => tacsf 
                                | prems=> (cut_facts_tac prems 1)::tacsf);

fun case_UU_tac rews i v =      case_tac (v^"=UU") i THEN
                                asm_simp_tac (HOLCF_ss addsimps rews) i;

val chain_tac = REPEAT_DETERM o resolve_tac 
                [chain_iterate, ch2ch_Rep_CFunR, ch2ch_Rep_CFunL];

(* ----- general proofs ----------------------------------------------------- *)

val all2E = prove_goal HOL.thy "[| !x y . P x y; P x y ==> R |] ==> R"
 (fn prems =>[
                                resolve_tac prems 1,
                                cut_facts_tac prems 1,
                                fast_tac HOL_cs 1]);

val dist_eqI = prove_goal (the_context ()) "!!x::'a::po. ~ x << y ==> x ~= y" 
             (fn prems => [
               (blast_tac (claset() addDs [antisym_less_inverse]) 1)]);
(*
infixr 0 y;
val b = 0;
fun _ y t = by t;
fun g defs t = let val sg = sign_of thy;
                     val ct = Thm.cterm_of sg (inferT sg t);
                 in goalw_cterm defs ct end;
*)

in

fun theorems (((dname,_),cons) : eq, eqs : eq list) thy =
let

val dummy = writeln ("Proving isomorphism properties of domain "^dname^" ...");
val pg = pg' thy;

(* ----- getting the axioms and definitions --------------------------------- *)

local fun ga s dn = get_thm thy (Name (dn ^ "." ^ s)) in
val ax_abs_iso    = ga "abs_iso"  dname;
val ax_rep_iso    = ga "rep_iso"  dname;
val ax_when_def   = ga "when_def" dname;
val axs_con_def   = map (fn (con,_) => ga (extern_name con^"_def") dname) cons;
val axs_dis_def   = map (fn (con,_) => ga (   dis_name con^"_def") dname) cons;
val axs_mat_def   = map (fn (con,_) => ga (   mat_name con^"_def") dname) cons;
val axs_sel_def   = List.concat(map (fn (_,args) => List.mapPartial (fn arg =>
                 Option.map (fn sel => ga (sel^"_def") dname) (sel_of arg)) args)
									  cons);
val ax_copy_def   = ga "copy_def" dname;
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
val iso_rews = map standard [ax_abs_iso,ax_rep_iso,abs_strict,rep_strict];

(* ----- generating beta reduction rules from definitions-------------------- *)

local
  fun arglist (Const _ $ Abs (s,_,t)) = let
        val (vars,body) = arglist t
        in  (s :: vars, body) end
  |   arglist t = ([],t);
  fun bind_fun vars t = Library.foldr mk_All (vars,t);
  fun bound_vars 0 = [] | bound_vars i = (Bound (i-1) :: bound_vars (i-1));
in
  fun appl_of_def def = let
        val (_ $ con $ lam) = concl_of def;
        val (vars, rhs) = arglist lam;
        val lhs = list_ccomb (con, bound_vars (length vars));
        val appl = bind_fun vars (lhs == rhs);
        val cs = ContProc.cont_thms lam;
        val betas = map (fn c => mk_meta_eq (c RS beta_cfun)) cs;
        in pg (def::betas) appl [rtac reflexive_thm 1] end;
end;

val when_appl = appl_of_def ax_when_def;
val con_appls = map appl_of_def axs_con_def;

local
  fun arg2typ n arg = let val t = TVar (("'a",n),pcpoS)
                      in (n+1, if is_lazy arg then mk_uT t else t) end;
  fun args2typ n [] = (n,oneT)
  |   args2typ n [arg] = arg2typ n arg
  |   args2typ n (arg::args) = let val (n1,t1) = arg2typ n arg;
                                   val (n2,t2) = args2typ n1 args
			       in  (n2, mk_sprodT (t1, t2)) end;
  fun cons2typ n [] = (n,oneT)
  |   cons2typ n [con] = args2typ n (snd con)
  |   cons2typ n (con::cons) = let val (n1,t1) = args2typ n (snd con);
                                   val (n2,t2) = cons2typ n1 cons
			       in  (n2, mk_ssumT (t1, t2)) end;
in
  fun cons2ctyp cons = ctyp_of (sign_of thy) (snd (cons2typ 1 cons));
end;

local 
  val iso_swap = iso_locale RS iso_iso_swap;
  fun one_con (con,args) = let val vns = map vname args in
    Library.foldr mk_ex (vns, foldr1 mk_conj ((%:x_name === con_app2 con %: vns)::
                              map (defined o %:) (nonlazy args))) end;
  val exh = foldr1 mk_disj ((%:x_name===UU)::map one_con cons);
  val my_ctyp = cons2ctyp cons;
  val thm1 = instantiate' [SOME my_ctyp] [] exh_start;
  val thm2 = rewrite_rule (map mk_meta_eq ex_defined_iffs) thm1;
  val thm3 = rewrite_rule [mk_meta_eq conj_assoc] thm2;
in
val exhaust = pg con_appls (mk_trp exh)[
(* first 3 rules replace "x = UU \/ P" with "rep$x = UU \/ P" *)
			rtac disjE 1,
			etac (rep_defin' RS disjI1) 2,
			etac disjI2 2,
			rewrite_goals_tac [mk_meta_eq iso_swap],
			rtac thm3 1];
val casedist = standard (rewrite_rule exh_casedists (exhaust RS exh_casedist0));
end;

local 
  fun bind_fun t = Library.foldr mk_All (when_funs cons,t);
  fun bound_fun i _ = Bound (length cons - i);
  val when_app  = list_ccomb (%%:(dname^"_when"), mapn bound_fun 1 cons);
in
val when_strict = pg [when_appl, mk_meta_eq rep_strict]
			(bind_fun(mk_trp(strict when_app)))
			[resolve_tac [sscase1,ssplit1,strictify1] 1];
val when_apps = let fun one_when n (con,args) = pg (when_appl :: con_appls)
                (bind_fun (lift_defined %: (nonlazy args, 
                mk_trp(when_app`(con_app con args) ===
                       list_ccomb(bound_fun n 0,map %# args)))))[
                asm_simp_tac (HOLCF_ss addsimps [ax_abs_iso]) 1];
        in mapn one_when 1 cons end;
end;
val when_rews = when_strict::when_apps;

(* ----- theorems concerning the constructors, discriminators and selectors - *)

val dis_rews = let
  val dis_stricts = map (fn (con,_) => pg axs_dis_def (mk_trp(
                             strict(%%:(dis_name con)))) [
                                rtac when_strict 1]) cons;
  val dis_apps = let fun one_dis c (con,args)= pg axs_dis_def
                   (lift_defined %: (nonlazy args,
                        (mk_trp((%%:(dis_name c))`(con_app con args) ===
                              %%:(if con=c then TT_N else FF_N))))) [
                                asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
        in List.concat(map (fn (c,_) => map (one_dis c) cons) cons) end;
  val dis_defins = map (fn (con,args) => pg [] (defined(%:x_name) ==> 
                      defined(%%:(dis_name con)`%x_name)) [
                                rtac casedist 1,
                                contr_tac 1,
                                DETERM_UNTIL_SOLVED (CHANGED(asm_simp_tac 
                                        (HOLCF_ss addsimps dis_apps) 1))]) cons;
in dis_stricts @ dis_defins @ dis_apps end;

val mat_rews = let
  val mat_stricts = map (fn (con,_) => pg axs_mat_def (mk_trp(
                             strict(%%:(mat_name con)))) [
                                rtac when_strict 1]) cons;
  val mat_apps = let fun one_mat c (con,args)= pg axs_mat_def
                   (lift_defined %: (nonlazy args,
                        (mk_trp((%%:(mat_name c))`(con_app con args) ===
                              (if con=c
                                  then %%:returnN`(mk_ctuple (map %# args))
                                  else %%:failN)))))
                   [asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
        in List.concat(map (fn (c,_) => map (one_mat c) cons) cons) end;
in mat_stricts @ mat_apps end;

val con_stricts = List.concat(map (fn (con,args) => map (fn vn =>
                        pg con_appls
                           (mk_trp(con_app2 con (fn arg => if vname arg = vn 
                                        then UU else %# arg) args === UU))[
                                asm_simp_tac (HOLCF_ss addsimps [abs_strict]) 1]
                        ) (nonlazy args)) cons);
val con_defins = map (fn (con,args) => pg []
                        (lift_defined %: (nonlazy args,
                                mk_trp(defined(con_app con args)))) ([
                          rtac rev_contrapos 1, 
                          eres_inst_tac [("f",dis_name con)] cfun_arg_cong 1,
                          asm_simp_tac (HOLCF_ss addsimps dis_rews) 1] )) cons;
val con_rews = con_stricts @ con_defins;

val con_compacts =
  let
    val rules = [compact_sinl, compact_sinr, compact_spair, compact_up, compact_ONE];
    fun one_compact (con,args) = pg con_appls
      (lift (fn x => %%:compactN $ %#x) (args, mk_trp(%%:compactN $ (con_app con args))))
      [rtac (iso_locale RS iso_compact_abs) 1, REPEAT (resolve_tac rules 1 ORELSE atac 1)];
  in map one_compact cons end;

val sel_stricts = let fun one_sel sel = pg axs_sel_def (mk_trp(strict(%%:sel))) [
                                simp_tac (HOLCF_ss addsimps when_rews) 1];
in List.concat(map (fn (_,args) => List.mapPartial (fn arg => Option.map one_sel (sel_of arg)) args) cons) end;
val sel_apps = let fun one_sel c n sel = map (fn (con,args) => 
                let val nlas = nonlazy args;
                    val vns  = map vname args;
                in pg axs_sel_def (lift_defined %:
                   (List.filter (fn v => con=c andalso (v<>List.nth(vns,n))) nlas,
                                mk_trp((%%:sel)`(con_app con args) === 
                                (if con=c then %:(List.nth(vns,n)) else UU))))
                            ( (if con=c then [] 
                       else map(case_UU_tac(when_rews@con_stricts)1) nlas)
                     @(if con=c andalso ((List.nth(vns,n)) mem nlas)
                                 then[case_UU_tac (when_rews @ con_stricts) 1 
                                                  (List.nth(vns,n))] else [])
                     @ [asm_simp_tac(HOLCF_ss addsimps when_rews)1])end) cons;
in List.concat(map  (fn (c,args) => 
     List.concat(List.mapPartial I (mapn (fn n => fn arg => Option.map (one_sel c n) (sel_of arg)) 0 args))) cons) end;
val sel_defins = if length cons=1 then List.mapPartial (fn arg => Option.map (fn sel => pg [](defined(%:x_name)==> 
                        defined(%%:sel`%x_name)) [
                                rtac casedist 1,
                                contr_tac 1,
                                DETERM_UNTIL_SOLVED (CHANGED(asm_simp_tac 
                                             (HOLCF_ss addsimps sel_apps) 1))])(sel_of arg)) 
                 (filter_out is_lazy (snd(hd cons))) else [];
val sel_rews = sel_stricts @ sel_defins @ sel_apps;

val distincts_le = let
    fun dist (con1, args1) (con2, args2) = pg []
              (lift_defined %: ((nonlazy args1),
                        (mk_trp (con_app con1 args1 ~<< con_app con2 args2))))([
                        rtac rev_contrapos 1,
                        eres_inst_tac[("f",dis_name con1)] monofun_cfun_arg 1]
                      @map(case_UU_tac (con_stricts @ dis_rews)1)(nonlazy args2)
                      @[asm_simp_tac (HOLCF_ss addsimps dis_rews) 1]);
    fun distinct (con1,args1) (con2,args2) =
        let val arg1 = (con1, args1)
            val arg2 = (con2,
			ListPair.map (fn (arg,vn) => upd_vname (K vn) arg)
                        (args2, variantlist(map vname args2,map vname args1)))
        in [dist arg1 arg2, dist arg2 arg1] end;
    fun distincts []      = []
    |   distincts (c::cs) = (map (distinct c) cs) :: distincts cs;
in distincts cons end;
val dist_les = List.concat (List.concat distincts_le);
val dist_eqs = let
    fun distinct (_,args1) ((_,args2),leqs) = let
        val (le1,le2) = (hd leqs, hd(tl leqs));
        val (eq1,eq2) = (le1 RS dist_eqI, le2 RS dist_eqI) in
        if nonlazy args1 = [] then [eq1, eq1 RS not_sym] else
        if nonlazy args2 = [] then [eq2, eq2 RS not_sym] else
                                        [eq1, eq2] end;
    fun distincts []      = []
    |   distincts ((c,leqs)::cs) = List.concat
	            (ListPair.map (distinct c) ((map #1 cs),leqs)) @
		    distincts cs;
    in map standard (distincts (cons~~distincts_le)) end;

local 
  fun pgterm rel con args =
    let
      fun append s = upd_vname(fn v => v^s);
      val (largs,rargs) = (args, map (append "'") args);
      val concl = mk_trp (foldr1 mk_conj (ListPair.map rel (map %# largs, map %# rargs)));
      val prem = mk_trp (rel(con_app con largs,con_app con rargs));
      val prop = prem ===> lift_defined %: (nonlazy largs, concl);
    in pg con_appls prop end;
  val cons' = List.filter (fn (_,args) => args<>[]) cons;
in
val inverts =
  let
    val abs_less = ax_abs_iso RS (allI RS injection_less) RS iffD1;
    val tacs = [
      dtac abs_less 1,
      REPEAT (dresolve_tac [sinl_less RS iffD1, sinr_less RS iffD1] 1),
      asm_full_simp_tac (HOLCF_ss addsimps [spair_less]) 1];
  in map (fn (con,args) => pgterm (op <<) con args tacs) cons' end;
val injects =
  let
    val abs_eq = ax_abs_iso RS (allI RS injection_eq) RS iffD1;
    val tacs = [
      dtac abs_eq 1,
      REPEAT (dresolve_tac [sinl_inject, sinr_inject] 1),
      asm_full_simp_tac (HOLCF_ss addsimps [spair_eq]) 1];
  in map (fn (con,args) => pgterm (op ===) con args tacs) cons' end;
end;

(* ----- theorems concerning one induction step ----------------------------- *)

val copy_strict = pg[ax_copy_def](mk_trp(strict(dc_copy`%"f"))) [
                   asm_simp_tac(HOLCF_ss addsimps [abs_strict, when_strict]) 1];
val copy_apps = map (fn (con,args) => pg [ax_copy_def]
                    (lift_defined %: (nonlazy_rec args,
                        mk_trp(dc_copy`%"f"`(con_app con args) ===
                (con_app2 con (app_rec_arg (cproj (%:"f") eqs)) args))))
                        (map (case_UU_tac (abs_strict::when_strict::con_stricts)
                                 1 o vname)
                         (List.filter (fn a => not (is_rec a orelse is_lazy a)) args)
                        @[asm_simp_tac (HOLCF_ss addsimps when_apps) 1,
                          simp_tac (HOLCF_ss addsimps con_appls) 1]))cons;
val copy_stricts = map (fn (con,args) => pg [] (mk_trp(dc_copy`UU`
                                        (con_app con args) ===UU))
     (let val rews = copy_strict::copy_apps@con_rews
                         in map (case_UU_tac rews 1) (nonlazy args) @ [
                             asm_simp_tac (HOLCF_ss addsimps rews) 1] end))
                        (List.filter (fn (_,args)=>exists is_nonlazy_rec args) cons);
val copy_rews = copy_strict::copy_apps @ copy_stricts;
in thy |> Theory.add_path (Sign.base_name dname)
       |> (#1 o (PureThy.add_thmss (map Thm.no_attributes [
		("iso_rews" , iso_rews  ),
		("exhaust"  , [exhaust] ),
		("casedist" , [casedist]),
		("when_rews", when_rews ),
		("compacts", con_compacts),
		("con_rews", con_rews),
		("sel_rews", sel_rews),
		("dis_rews", dis_rews),
		("dist_les", dist_les),
		("dist_eqs", dist_eqs),
		("inverts" , inverts ),
		("injects" , injects ),
		("copy_rews", copy_rews)])))
       |> (#1 o PureThy.add_thmss [(("match_rews", mat_rews), [Simplifier.simp_add_global])])
       |> Theory.parent_path |> rpair (iso_rews @ when_rews @ con_rews @ sel_rews @ dis_rews @
                 dist_les @ dist_eqs @ copy_rews)
end; (* let *)

fun comp_theorems (comp_dnam, eqs: eq list) thy =
let
val dnames = map (fst o fst) eqs;
val conss  = map  snd        eqs;
val comp_dname = Sign.full_name (sign_of thy) comp_dnam;

val d = writeln("Proving induction properties of domain "^comp_dname^" ...");
val pg = pg' thy;

(* ----- getting the composite axiom and definitions ------------------------ *)

local fun ga s dn = get_thm thy (Name (dn ^ "." ^ s)) in
val axs_reach      = map (ga "reach"     ) dnames;
val axs_take_def   = map (ga "take_def"  ) dnames;
val axs_finite_def = map (ga "finite_def") dnames;
val ax_copy2_def   =      ga "copy_def"  comp_dnam;
val ax_bisim_def   =      ga "bisim_def" comp_dnam;
end; (* local *)

local fun gt  s dn = get_thm  thy (Name (dn ^ "." ^ s));
      fun gts s dn = get_thms thy (Name (dn ^ "." ^ s)) in
val cases     =       map (gt  "casedist" ) dnames;
val con_rews  = List.concat (map (gts "con_rews" ) dnames);
val copy_rews = List.concat (map (gts "copy_rews") dnames);
end; (* local *)

fun dc_take dn = %%:(dn^"_take");
val x_name = idx_name dnames "x"; 
val P_name = idx_name dnames "P";
val n_eqs = length eqs;

(* ----- theorems concerning finite approximation and finite induction ------ *)

local
  val iterate_Cprod_ss = simpset_of Fix.thy;
  val copy_con_rews  = copy_rews @ con_rews;
  val copy_take_defs = (if n_eqs = 1 then [] else [ax_copy2_def]) @ axs_take_def;
  val take_stricts=pg copy_take_defs(mk_trp(foldr1 mk_conj(map(fn((dn,args),_)=>
            strict(dc_take dn $ %:"n")) eqs))) ([
                        induct_tac "n" 1,
                        simp_tac iterate_Cprod_ss 1,
                        asm_simp_tac (iterate_Cprod_ss addsimps copy_rews)1]);
  val take_stricts' = rewrite_rule copy_take_defs take_stricts;
  val take_0s = mapn(fn n=> fn dn => pg axs_take_def(mk_trp((dc_take dn $ %%:"0")
                                                        `%x_name n === UU))[
                                simp_tac iterate_Cprod_ss 1]) 1 dnames;
  val c_UU_tac = case_UU_tac (take_stricts'::copy_con_rews) 1;
  val take_apps = pg copy_take_defs (mk_trp(foldr1 mk_conj 
            (List.concat(map (fn ((dn,_),cons) => map (fn (con,args) => Library.foldr mk_all 
        (map vname args,(dc_take dn $ (%%:"Suc" $ %:"n"))`(con_app con args) ===
         con_app2 con (app_rec_arg (fn n=>dc_take (List.nth(dnames,n))$ %:"n"))
                              args)) cons) eqs)))) ([
                                simp_tac iterate_Cprod_ss 1,
                                induct_tac "n" 1,
                            simp_tac(iterate_Cprod_ss addsimps copy_con_rews) 1,
                                asm_full_simp_tac (HOLCF_ss addsimps 
                                      (List.filter (has_fewer_prems 1) copy_rews)) 1,
                                TRY(safe_tac HOL_cs)] @
                        (List.concat(map (fn ((dn,_),cons) => map (fn (con,args) => 
                                if nonlazy_rec args = [] then all_tac else
                                EVERY(map c_UU_tac (nonlazy_rec args)) THEN
                                asm_full_simp_tac (HOLCF_ss addsimps copy_rews)1
                                                           ) cons) eqs)));
in
val take_rews = map standard (atomize take_stricts @ take_0s @ atomize take_apps);
end; (* local *)

local
  fun one_con p (con,args) = Library.foldr mk_All (map vname args,
        lift_defined (bound_arg (map vname args)) (nonlazy args,
        lift (fn arg => %:(P_name (1+rec_of arg)) $ bound_arg args arg)
         (List.filter is_rec args,mk_trp(%:p $ con_app2 con (bound_arg args) args))));
  fun one_eq ((p,cons),concl) = (mk_trp(%:p $ UU) ===> 
                           Library.foldr (op ===>) (map (one_con p) cons,concl));
  fun ind_term concf = Library.foldr one_eq (mapn (fn n => fn x => (P_name n, x))1conss,
                        mk_trp(foldr1 mk_conj (mapn concf 1 dnames)));
  val take_ss = HOL_ss addsimps take_rews;
  fun quant_tac i = EVERY(mapn(fn n=> fn _=> res_inst_tac[("x",x_name n)]spec i)
                               1 dnames);
  fun ind_prems_tac prems = EVERY(List.concat (map (fn cons => (
                                     resolve_tac prems 1 ::
                                     List.concat (map (fn (_,args) => 
                                       resolve_tac prems 1 ::
                                       map (K(atac 1)) (nonlazy args) @
                                       map (K(atac 1)) (List.filter is_rec args))
                                     cons))) conss));
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
    fun warn (n,cons)  = if all_rec_to [] false (n,cons) then (warning
        ("domain "^List.nth(dnames,n)^" is empty!"); true) else false;
    fun lazy_rec_to ns = rec_to exists I  lazy_rec_to ns;

  in val n__eqs     = mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs;
     val is_emptys = map warn n__eqs;
     val is_finite = forall (not o lazy_rec_to [] false) n__eqs;
  end;
in (* local *)
val finite_ind = pg'' thy [] (ind_term (fn n => fn dn => %:(P_name n)$
                             (dc_take dn $ %:"n" `%(x_name n)))) (fn prems => [
                                quant_tac 1,
                                simp_tac HOL_ss 1,
                                induct_tac "n" 1,
                                simp_tac (take_ss addsimps prems) 1,
                                TRY(safe_tac HOL_cs)]
                                @ List.concat(map (fn (cons,cases) => [
                                 res_inst_tac [("x","x")] cases 1,
                                 asm_simp_tac (take_ss addsimps prems) 1]
                                 @ List.concat(map (fn (con,args) => 
                                  asm_simp_tac take_ss 1 ::
                                  map (fn arg =>
                                   case_UU_tac (prems@con_rews) 1 (
                           List.nth(dnames,rec_of arg)^"_take n$"^vname arg))
                                  (List.filter is_nonlazy_rec args) @ [
                                  resolve_tac prems 1] @
                                  map (K (atac 1))      (nonlazy args) @
                                  map (K (etac spec 1)) (List.filter is_rec args)) 
                                 cons))
                                (conss~~cases)));

val take_lemmas =mapn(fn n=> fn(dn,ax_reach)=> pg'' thy axs_take_def(mk_All("n",
                mk_trp(dc_take dn $ Bound 0 `%(x_name n) === 
                       dc_take dn $ Bound 0 `%(x_name n^"'")))
           ===> mk_trp(%:(x_name n) === %:(x_name n^"'"))) (fn prems => [
                        res_inst_tac[("t",x_name n    )](ax_reach RS subst) 1,
                        res_inst_tac[("t",x_name n^"'")](ax_reach RS subst) 1,
                                stac fix_def2 1,
                                REPEAT(CHANGED(rtac(contlub_cfun_arg RS ssubst)1
                                               THEN chain_tac 1)),
                                stac contlub_cfun_fun 1,
                                stac contlub_cfun_fun 2,
                                rtac lub_equal 3,
                                chain_tac 1,
                                rtac allI 1,
                                resolve_tac prems 1])) 1 (dnames~~axs_reach);

(* ----- theorems concerning finiteness and induction ----------------------- *)

val (finites,ind) = if is_finite then
  let 
    fun take_enough dn = mk_ex ("n",dc_take dn $ Bound 0 ` %:"x" === %:"x");
    val finite_lemmas1a = map (fn dn => pg [] (mk_trp(defined (%:"x")) ===> 
        mk_trp(mk_disj(mk_all("n",dc_take dn $ Bound 0 ` %:"x" === UU),
        take_enough dn)) ===> mk_trp(take_enough dn)) [
                                etac disjE 1,
                                etac notE 1,
                                resolve_tac take_lemmas 1,
                                asm_simp_tac take_ss 1,
                                atac 1]) dnames;
    val finite_lemma1b = pg [] (mk_trp (mk_all("n",foldr1 mk_conj (mapn 
        (fn n => fn ((dn,args),_) => mk_constrainall(x_name n,Type(dn,args),
         mk_disj(dc_take dn $ Bound 1 ` Bound 0 === UU,
                 dc_take dn $ Bound 1 ` Bound 0 === Bound 0))) 1 eqs)))) ([
                                rtac allI 1,
                                induct_tac "n" 1,
                                simp_tac take_ss 1,
                        TRY(safe_tac(empty_cs addSEs[conjE] addSIs[conjI]))] @
                                List.concat(mapn (fn n => fn (cons,cases) => [
                                  simp_tac take_ss 1,
                                  rtac allI 1,
                                  res_inst_tac [("x",x_name n)] cases 1,
                                  asm_simp_tac take_ss 1] @ 
                                  List.concat(map (fn (con,args) => 
                                    asm_simp_tac take_ss 1 ::
                                    List.concat(map (fn vn => [
                                      eres_inst_tac [("x",vn)] all_dupE 1,
                                      etac disjE 1,
                                      asm_simp_tac (HOL_ss addsimps con_rews) 1,
                                      asm_simp_tac take_ss 1])
                                    (nonlazy_rec args)))
                                  cons))
                                1 (conss~~cases)));
    val finites = map (fn (dn,l1b) => pg axs_finite_def (mk_trp(
                                                %%:(dn^"_finite") $ %:"x"))[
                                case_UU_tac take_rews 1 "x",
                                eresolve_tac finite_lemmas1a 1,
                                step_tac HOL_cs 1,
                                step_tac HOL_cs 1,
                                cut_facts_tac [l1b] 1,
                        fast_tac HOL_cs 1]) (dnames~~atomize finite_lemma1b);
  in
  (finites,
   pg'' thy[](ind_term (fn n => fn dn => %:(P_name n) $ %:(x_name n)))(fn prems =>
                                TRY(safe_tac HOL_cs) ::
                         List.concat (map (fn (finite,fin_ind) => [
                               rtac(rewrite_rule axs_finite_def finite RS exE)1,
                                etac subst 1,
                                rtac fin_ind 1,
                                ind_prems_tac prems]) 
                                   (finites~~(atomize finite_ind)) ))
) end (* let *) else
  (mapn (fn n => fn dn => read_instantiate_sg (sign_of thy) 
                    [("P",dn^"_finite "^x_name n)] excluded_middle) 1 dnames,
   pg'' thy [] (Library.foldr (op ===>) (mapn (fn n => K(mk_trp(%%:admN $ %:(P_name n))))
               1 dnames, ind_term (fn n => fn dn => %:(P_name n) $ %:(x_name n))))
                   (fn prems => map (fn ax_reach => rtac (ax_reach RS subst) 1) 
                                    axs_reach @ [
                                quant_tac 1,
                                rtac (adm_impl_admw RS wfix_ind) 1,
                                 REPEAT_DETERM(rtac adm_all2 1),
                                 REPEAT_DETERM(TRY(rtac adm_conj 1) THEN 
                                                   rtac adm_subst 1 THEN 
                                        cont_tacR 1 THEN resolve_tac prems 1),
                                strip_tac 1,
                                rtac (rewrite_rule axs_take_def finite_ind) 1,
                                ind_prems_tac prems])
  handle ERROR => (warning "Cannot prove infinite induction rule"; refl))
end; (* local *)

(* ----- theorem concerning coinduction ------------------------------------- *)

local
  val xs = mapn (fn n => K (x_name n)) 1 dnames;
  fun bnd_arg n i = Bound(2*(n_eqs - n)-i-1);
  val take_ss = HOL_ss addsimps take_rews;
  val sproj   = prj (fn s => K("fst("^s^")")) (fn s => K("snd("^s^")"));
  val coind_lemma=pg[ax_bisim_def](mk_trp(mk_imp(%%:(comp_dname^"_bisim") $ %:"R",
                Library.foldr (fn (x,t)=> mk_all(x,mk_all(x^"'",t))) (xs,
                  Library.foldr mk_imp (mapn (fn n => K(proj (%:"R") eqs n $ 
                                      bnd_arg n 0 $ bnd_arg n 1)) 0 dnames,
                    foldr1 mk_conj (mapn (fn n => fn dn => 
                                (dc_take dn $ %:"n" `bnd_arg n 0 === 
                                (dc_take dn $ %:"n" `bnd_arg n 1)))0 dnames))))))
                             ([ rtac impI 1,
                                induct_tac "n" 1,
                                simp_tac take_ss 1,
                                safe_tac HOL_cs] @
                                List.concat(mapn (fn n => fn x => [
                                  rotate_tac (n+1) 1,
                                  etac all2E 1,
                                  eres_inst_tac [("P1", sproj "R" eqs n^
                                        " "^x^" "^x^"'")](mp RS disjE) 1,
                                  TRY(safe_tac HOL_cs),
                                  REPEAT(CHANGED(asm_simp_tac take_ss 1))]) 
                                0 xs));
in
val coind = pg [] (mk_trp(%%:(comp_dname^"_bisim") $ %:"R") ===>
                Library.foldr (op ===>) (mapn (fn n => fn x => 
                  mk_trp(proj (%:"R") eqs n $ %:x $ %:(x^"'"))) 0 xs,
                  mk_trp(foldr1 mk_conj (map (fn x => %:x === %:(x^"'")) xs)))) ([
                                TRY(safe_tac HOL_cs)] @
                                List.concat(map (fn take_lemma => [
                                  rtac take_lemma 1,
                                  cut_facts_tac [coind_lemma] 1,
                                  fast_tac HOL_cs 1])
                                take_lemmas));
end; (* local *)

in thy |> Theory.add_path comp_dnam
       |> (#1 o (PureThy.add_thmss (map Thm.no_attributes [
		("take_rews"  , take_rews  ),
		("take_lemmas", take_lemmas),
		("finites"    , finites    ),
		("finite_ind", [finite_ind]),
		("ind"       , [ind       ]),
		("coind"     , [coind     ])])))
       |> Theory.parent_path |> rpair take_rews
end; (* let *)
end; (* local *)
end; (* struct *)
