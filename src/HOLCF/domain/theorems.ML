(* theorems.ML
   ID:         $Id$
   Author : David von Oheimb
   Created: 06-Jun-95
   Updated: 08-Jun-95 first proof from cterms
   Updated: 26-Jun-95 proofs for exhaustion thms
   Updated: 27-Jun-95 proofs for discriminators, constructors and selectors
   Updated: 06-Jul-95 proofs for distinctness, invertibility and injectivity
   Updated: 17-Jul-95 proofs for induction rules
   Updated: 19-Jul-95 proof for co-induction rule
   Updated: 28-Aug-95 definedness theorems for selectors (completion)
   Updated: 05-Sep-95 simultaneous domain equations (main part)
   Updated: 11-Sep-95 simultaneous domain equations (coding finished)
   Updated: 13-Sep-95 simultaneous domain equations (debugging)
   Copyright 1995 TU Muenchen
*)


structure Domain_Theorems = struct

local

open Domain_Library;
infixr 0 ===>;infixr 0 ==>;infix 0 == ; 
infix 1 ===; infix 1 ~= ; infix 1 <<; infix 1 ~<<;
infix 9 `   ; infix 9 `% ; infix 9 `%%; infixr 9 oo;

(* ----- general proof facilities ------------------------------------------------- *)

fun inferT sg pre_tm = #2(Sign.infer_types sg (K None)(K None)[]true([pre_tm],propT));

(*
infix 0 y;
val b=0;
fun _ y t = by t;
fun  g  defs t = let val sg = sign_of thy;
                     val ct = Thm.cterm_of sg (inferT sg t);
                 in goalw_cterm defs ct end;
*)

fun pg'' thy defs t = let val sg = sign_of thy;
                          val ct = Thm.cterm_of sg (inferT sg t);
                      in prove_goalw_cterm defs ct end;
fun pg'  thy defs t tacsf=pg'' thy defs t (fn []   => tacsf 
                                            | prems=> (cut_facts_tac prems 1)::tacsf);

fun REPEAT_DETERM_UNTIL p tac = 
let fun drep st = if p st then Sequence.single st
                          else (case Sequence.pull(tapply(tac,st)) of
                                  None        => Sequence.null
                                | Some(st',_) => drep st')
in Tactic drep end;
val UNTIL_SOLVED = REPEAT_DETERM_UNTIL (has_fewer_prems 1);

local val trueI2 = prove_goal HOL.thy "f~=x ==> True" (fn prems => [rtac TrueI 1]) in
val kill_neq_tac = dtac trueI2 end;
fun case_UU_tac rews i v =      res_inst_tac [("Q",v^"=UU")] classical2 i THEN
                                asm_simp_tac (HOLCF_ss addsimps rews) i;

val chain_tac = REPEAT_DETERM o resolve_tac 
                [is_chain_iterate, ch2ch_fappR, ch2ch_fappL];

(* ----- general proofs ----------------------------------------------------------- *)

val swap3 = prove_goal HOL.thy "[| Q ==> P; ~P |] ==> ~Q" (fn prems => [
                                cut_facts_tac prems 1,
                                etac swap 1,
                                dtac notnotD 1,
                                etac (hd prems) 1]);

val dist_eqI = prove_goal Porder0.thy "~ x << y ==> x ~= y" (fn prems => [
                                cut_facts_tac prems 1,
                                etac swap 1,
                                dtac notnotD 1,
                                asm_simp_tac HOLCF_ss 1]);
val cfst_strict  = prove_goal Cprod3.thy "cfst`UU = UU" (fn _ => [
                                (simp_tac (HOLCF_ss addsimps [inst_cprod_pcpo2]) 1)]);
val csnd_strict  = prove_goal Cprod3.thy "csnd`UU = UU" (fn _ => [
                        (simp_tac (HOLCF_ss addsimps [inst_cprod_pcpo2]) 1)]);

in


fun theorems thy (((dname,_),cons) : eq, eqs :eq list) =
let

val dummy = writeln ("Proving isomorphism properties of domain "^dname^"...");
val pg = pg' thy;

(* ----- getting the axioms and definitions --------------------------------------- *)

local val ga = get_axiom thy in
val ax_abs_iso    = ga (dname^"_abs_iso"   );
val ax_rep_iso    = ga (dname^"_rep_iso"   );
val ax_when_def   = ga (dname^"_when_def"  );
val axs_con_def   = map (fn (con,_) => ga (extern_name con ^"_def")) cons;
val axs_dis_def   = map (fn (con,_) => ga (   dis_name con ^"_def")) cons;
val axs_sel_def   = flat(map (fn (_,args) => 
                    map (fn     arg => ga (sel_of arg      ^"_def")) args) cons);
val ax_copy_def   = ga (dname^"_copy_def"  );
end; (* local *)

(* ----- theorems concerning the isomorphism -------------------------------------- *)

val dc_abs  = %%(dname^"_abs");
val dc_rep  = %%(dname^"_rep");
val dc_copy = %%(dname^"_copy");
val x_name = "x";

val (rep_strict, abs_strict) = let 
               val r = ax_rep_iso RS (ax_abs_iso RS (allI  RSN(2,allI RS iso_strict)))
               in (r RS conjunct1, r RS conjunct2) end;
val abs_defin' = pg [] ((dc_abs`%x_name === UU) ==> (%x_name === UU)) [
                                res_inst_tac [("t",x_name)] (ax_abs_iso RS subst) 1,
                                etac ssubst 1,
                                rtac rep_strict 1];
val rep_defin' = pg [] ((dc_rep`%x_name === UU) ==> (%x_name === UU)) [
                                res_inst_tac [("t",x_name)] (ax_rep_iso RS subst) 1,
                                etac ssubst 1,
                                rtac abs_strict 1];
val iso_rews = [ax_abs_iso,ax_rep_iso,abs_strict,rep_strict];

local 
val iso_swap = pg [] (dc_rep`%"x" === %"y" ==> %"x" === dc_abs`%"y") [
                                dres_inst_tac [("f",dname^"_abs")] cfun_arg_cong 1,
                                etac (ax_rep_iso RS subst) 1];
fun exh foldr1 cn quant foldr2 var = let
  fun one_con (con,args) = let val vns = map vname args in
    foldr quant (vns, foldr2 ((%x_name === con_app2 con (var vns) vns)::
                              map (defined o (var vns)) (nonlazy args))) end
  in foldr1 ((cn(%x_name===UU))::map one_con cons) end;
in
val cases = let 
            fun common_tac thm = rtac thm 1 THEN contr_tac 1;
            fun unit_tac true = common_tac liftE1
            |   unit_tac _    = all_tac;
            fun prod_tac []          = common_tac oneE
            |   prod_tac [arg]       = unit_tac (is_lazy arg)
            |   prod_tac (arg::args) = 
                                common_tac sprodE THEN
                                kill_neq_tac 1 THEN
                                unit_tac (is_lazy arg) THEN
                                prod_tac args;
            fun sum_one_tac p = SELECT_GOAL(EVERY[
                                rtac p 1,
                                rewrite_goals_tac axs_con_def,
                                dtac iso_swap 1,
                                simp_tac HOLCF_ss 1,
                                UNTIL_SOLVED(fast_tac HOL_cs 1)]) 1;
            fun sum_tac [(_,args)]       [p]        = 
                                prod_tac args THEN sum_one_tac p
            |   sum_tac ((_,args)::cons') (p::prems) = DETERM(
                                common_tac ssumE THEN
                                kill_neq_tac 1 THEN kill_neq_tac 2 THEN
                                prod_tac args THEN sum_one_tac p) THEN
                                sum_tac cons' prems
            |   sum_tac _ _ = Imposs "theorems:sum_tac";
          in pg'' thy [] (exh (fn l => foldr (op ===>) (l,mk_trp(%"P")))
                              (fn T => T ==> %"P") mk_All
                              (fn l => foldr (op ===>) (map mk_trp l,mk_trp(%"P")))
                              bound_arg)
                             (fn prems => [
                                cut_facts_tac [excluded_middle] 1,
                                etac disjE 1,
                                rtac (hd prems) 2,
                                etac rep_defin' 2,
                                if is_one_con_one_arg (not o is_lazy) cons
                                then rtac (hd (tl prems)) 1 THEN atac 2 THEN
                                     rewrite_goals_tac axs_con_def THEN
                                     simp_tac (HOLCF_ss addsimps [ax_rep_iso]) 1
                                else sum_tac cons (tl prems)])end;
val exhaust = pg [] (mk_trp(exh (foldr' mk_disj) Id mk_ex (foldr' mk_conj) (K %))) [
                                rtac cases 1,
                                UNTIL_SOLVED(fast_tac HOL_cs 1)];
end;

local 
val when_app = foldl (op `) (%%(dname^"_when"), map % (when_funs cons));
val when_appl = pg [ax_when_def] (mk_trp(when_app`%x_name===when_body cons 
                (fn (_,n) => %(nth_elem(n-1,when_funs cons)))`(dc_rep`%x_name))) [
                                simp_tac HOLCF_ss 1];
in
val when_strict = pg [] ((if is_one_con_one_arg (K true) cons 
        then fn t => mk_trp(strict(%"f")) ===> t else Id)(mk_trp(strict when_app))) [
                                simp_tac(HOLCF_ss addsimps [when_appl,rep_strict]) 1];
val when_apps = let fun one_when n (con,args) = pg axs_con_def
                (lift_defined % (nonlazy args, mk_trp(when_app`(con_app con args) ===
                 mk_cfapp(%(nth_elem(n,when_funs cons)),map %# args))))[
                        asm_simp_tac (HOLCF_ss addsimps [when_appl,ax_abs_iso]) 1];
                in mapn one_when 0 cons end;
end;
val when_rews = when_strict::when_apps;

(* ----- theorems concerning the constructors, discriminators and selectors ------- *)

val dis_stricts = map (fn (con,_) => pg axs_dis_def (mk_trp(
                        (if is_one_con_one_arg (K true) cons then mk_not else Id)
                         (strict(%%(dis_name con))))) [
                simp_tac (HOLCF_ss addsimps (if is_one_con_one_arg (K true) cons 
                                        then [ax_when_def] else when_rews)) 1]) cons;
val dis_apps = let fun one_dis c (con,args)= pg (axs_dis_def)
                   (lift_defined % (nonlazy args, (*(if is_one_con_one_arg is_lazy cons
                        then curry (lift_defined %#) args else Id)
#################*)
                        (mk_trp((%%(dis_name c))`(con_app con args) ===
                              %%(if con=c then "TT" else "FF"))))) [
                                asm_simp_tac (HOLCF_ss addsimps when_rews) 1];
        in flat(map (fn (c,_) => map (one_dis c) cons) cons) end;
val dis_defins = map (fn (con,args) => pg [] (defined(%x_name)==> 
                      defined(%%(dis_name con)`%x_name)) [
                                rtac cases 1,
                                contr_tac 1,
                                UNTIL_SOLVED (CHANGED(asm_simp_tac 
                                              (HOLCF_ss addsimps dis_apps) 1))]) cons;
val dis_rews = dis_stricts @ dis_defins @ dis_apps;

val con_stricts = flat(map (fn (con,args) => map (fn vn =>
                        pg (axs_con_def) 
                           (mk_trp(con_app2 con (fn arg => if vname arg = vn 
                                        then UU else %# arg) args === UU))[
                                asm_simp_tac (HOLCF_ss addsimps [abs_strict]) 1]
                        ) (nonlazy args)) cons);
val con_defins = map (fn (con,args) => pg []
                        (lift_defined % (nonlazy args,
                                mk_trp(defined(con_app con args)))) ([
                                rtac swap3 1] @ (if is_one_con_one_arg (K true) cons 
                                then [
                                  if is_lazy (hd args) then rtac defined_up 2
                                                       else atac 2,
                                  rtac abs_defin' 1,    
                                  asm_full_simp_tac (HOLCF_ss addsimps axs_con_def) 1]
                                else [
                                  eres_inst_tac [("f",dis_name con)] cfun_arg_cong 1,
                                  asm_simp_tac (HOLCF_ss addsimps dis_rews) 1])))cons;
val con_rews = con_stricts @ con_defins;

val sel_stricts = let fun one_sel sel = pg axs_sel_def (mk_trp(strict(%%sel))) [
                                simp_tac (HOLCF_ss addsimps when_rews) 1];
in flat(map (fn (_,args) => map (fn arg => one_sel (sel_of arg)) args) cons) end;
val sel_apps = let fun one_sel c n sel = map (fn (con,args) => 
                let val nlas = nonlazy args;
                    val vns  = map vname args;
                in pg axs_sel_def (lift_defined %
                   (filter (fn v => con=c andalso (v<>nth_elem(n,vns))) nlas,
   mk_trp((%%sel)`(con_app con args) === (if con=c then %(nth_elem(n,vns)) else UU))))
                            ( (if con=c then [] 
                               else map(case_UU_tac(when_rews@con_stricts)1) nlas)
                             @(if con=c andalso ((nth_elem(n,vns)) mem nlas)
                                         then[case_UU_tac (when_rews @ con_stricts) 1 
                                                          (nth_elem(n,vns))] else [])
                             @ [asm_simp_tac(HOLCF_ss addsimps when_rews)1])end) cons;
in flat(map  (fn (c,args) => 
        flat(mapn (fn n => fn arg => one_sel c n (sel_of arg)) 0 args)) cons) end;
val sel_defins = if length cons = 1 then map (fn arg => pg [] (defined(%x_name) ==> 
                        defined(%%(sel_of arg)`%x_name)) [
                                rtac cases 1,
                                contr_tac 1,
                                UNTIL_SOLVED (CHANGED(asm_simp_tac 
                                              (HOLCF_ss addsimps sel_apps) 1))]) 
                 (filter_out is_lazy (snd(hd cons))) else [];
val sel_rews = sel_stricts @ sel_defins @ sel_apps;

val distincts_le = let
    fun dist (con1, args1) (con2, args2) = pg []
              (lift_defined % ((nonlazy args1),
                             (mk_trp (con_app con1 args1 ~<< con_app con2 args2))))([
                        rtac swap3 1,
                        eres_inst_tac [("fo5",dis_name con1)] monofun_cfun_arg 1]
                      @ map (case_UU_tac (con_stricts @ dis_rews) 1) (nonlazy args2)
                      @[asm_simp_tac (HOLCF_ss addsimps dis_rews) 1]);
    fun distinct (con1,args1) (con2,args2) =
        let val arg1 = (con1, args1);
            val arg2 = (con2, (map (fn (arg,vn) => upd_vname (K vn) arg)
                              (args2~~variantlist(map vname args2,map vname args1))));
        in [dist arg1 arg2, dist arg2 arg1] end;
    fun distincts []      = []
    |   distincts (c::cs) = (map (distinct c) cs) :: distincts cs;
in distincts cons end;
val dists_le = flat (flat distincts_le);
val dists_eq = let
    fun distinct (_,args1) ((_,args2),leqs) = let
        val (le1,le2) = (hd leqs, hd(tl leqs));
        val (eq1,eq2) = (le1 RS dist_eqI, le2 RS dist_eqI) in
        if nonlazy args1 = [] then [eq1, eq1 RS not_sym] else
        if nonlazy args2 = [] then [eq2, eq2 RS not_sym] else
                                        [eq1, eq2] end;
    fun distincts []      = []
    |   distincts ((c,leqs)::cs) = flat(map (distinct c) ((map fst cs)~~leqs)) @
                                   distincts cs;
    in distincts (cons~~distincts_le) end;

local 
  fun pgterm rel con args = let
                fun append s = upd_vname(fn v => v^s);
                val (largs,rargs) = (args, map (append "'") args);
                in pg [] (mk_trp (rel(con_app con largs,con_app con rargs)) ===>
                      lift_defined % ((nonlazy largs),lift_defined % ((nonlazy rargs),
                            mk_trp (foldr' mk_conj 
                                (map rel (map %# largs ~~ map %# rargs)))))) end;
  val cons' = filter (fn (_,args) => args<>[]) cons;
in
val inverts = map (fn (con,args) => 
                pgterm (op <<) con args (flat(map (fn arg => [
                                TRY(rtac conjI 1),
                                dres_inst_tac [("fo5",sel_of arg)] monofun_cfun_arg 1,
                                asm_full_simp_tac (HOLCF_ss addsimps sel_apps) 1]
                                                      ) args))) cons';
val injects = map (fn ((con,args),inv_thm) => 
                           pgterm (op ===) con args [
                                etac (antisym_less_inverse RS conjE) 1,
                                dtac inv_thm 1, REPEAT(atac 1),
                                dtac inv_thm 1, REPEAT(atac 1),
                                TRY(safe_tac HOL_cs),
                                REPEAT(rtac antisym_less 1 ORELSE atac 1)] )
                  (cons'~~inverts);
end;

(* ----- theorems concerning one induction step ----------------------------------- *)

val copy_strict = pg [ax_copy_def] ((if is_one_con_one_arg (K true) cons then fn t =>
         mk_trp(strict(cproj (%"f") eqs (rec_of (hd(snd(hd cons)))))) ===> t
        else Id) (mk_trp(strict(dc_copy`%"f")))) [
                                asm_simp_tac(HOLCF_ss addsimps [abs_strict,rep_strict,
                                                        cfst_strict,csnd_strict]) 1];
val copy_apps = map (fn (con,args) => pg (ax_copy_def::axs_con_def)
                    (lift_defined %# (filter is_nonlazy_rec args,
                        mk_trp(dc_copy`%"f"`(con_app con args) ===
                           (con_app2 con (app_rec_arg (cproj (%"f") eqs)) args))))
                                 (map (case_UU_tac [ax_abs_iso] 1 o vname)
                                   (filter(fn a=>not(is_rec a orelse is_lazy a))args)@
                                 [asm_simp_tac (HOLCF_ss addsimps [ax_abs_iso]) 1])
                )cons;
val copy_stricts = map(fn(con,args)=>pg[](mk_trp(dc_copy`UU`(con_app con args) ===UU))
             (let val rews = cfst_strict::csnd_strict::copy_strict::copy_apps@con_rews
                         in map (case_UU_tac rews 1) (nonlazy args) @ [
                             asm_simp_tac (HOLCF_ss addsimps rews) 1] end))
                   (filter (fn (_,args)=>exists is_nonlazy_rec args) cons);
val copy_rews = copy_strict::copy_apps @ copy_stricts;

in     (iso_rews, exhaust, cases, when_rews,
        con_rews, sel_rews, dis_rews, dists_eq, dists_le, inverts, injects,
        copy_rews)
end; (* let *)


fun comp_theorems thy (comp_dname, eqs: eq list, casess, con_rews, copy_rews) =
let

val dummy = writeln ("Proving induction properties of domain "^comp_dname^"...");
val pg = pg' thy;

val dnames = map (fst o fst) eqs;
val conss  = map  snd        eqs;

(* ----- getting the composite axiom and definitions ------------------------------ *)

local val ga = get_axiom thy in
val axs_reach      = map (fn dn => ga (dn ^  "_reach"   )) dnames;
val axs_take_def   = map (fn dn => ga (dn ^  "_take_def")) dnames;
val axs_finite_def = map (fn dn => ga (dn ^"_finite_def")) dnames;
val ax_copy2_def   = ga (comp_dname^ "_copy_def");
val ax_bisim_def   = ga (comp_dname^"_bisim_def");
end; (* local *)

(* ----- theorems concerning finiteness and induction ----------------------------- *)

fun dc_take dn = %%(dn^"_take");
val x_name = idx_name dnames "x"; 
val P_name = idx_name dnames "P";

local
  val iterate_ss = simpset_of "Fix";    
  val iterate_Cprod_strict_ss = iterate_ss addsimps [cfst_strict, csnd_strict];
  val iterate_Cprod_ss = iterate_ss addsimps [cfst2,csnd2,csplit2];
  val copy_con_rews  = copy_rews @ con_rews;
  val copy_take_defs = (if length dnames=1 then [] else [ax_copy2_def]) @axs_take_def;
  val take_stricts = pg copy_take_defs (mk_trp(foldr' mk_conj (map (fn ((dn,args),_)=>
                  (dc_take dn $ %"n")`UU === mk_constrain(Type(dn,args),UU)) eqs)))([
                                nat_ind_tac "n" 1,
                                simp_tac iterate_ss 1,
                                simp_tac iterate_Cprod_strict_ss 1,
                                asm_simp_tac iterate_Cprod_ss 1,
                                TRY(safe_tac HOL_cs)] @
                        map(K(asm_simp_tac (HOL_ss addsimps copy_rews)1))dnames);
  val take_stricts' = rewrite_rule copy_take_defs take_stricts;
  val take_0s = mapn (fn n => fn dn => pg axs_take_def(mk_trp((dc_take dn $ %%"0")
                                                                `%x_name n === UU))[
                                simp_tac iterate_Cprod_strict_ss 1]) 1 dnames;
  val take_apps = pg copy_take_defs (mk_trp(foldr' mk_conj 
            (flat(map (fn ((dn,_),cons) => map (fn (con,args) => foldr mk_all 
                (map vname args,(dc_take dn $ (%%"Suc" $ %"n"))`(con_app con args) ===
                 con_app2 con (app_rec_arg (fn n=>dc_take (nth_elem(n,dnames))$ %"n"))
                              args)) cons) eqs)))) ([
                                nat_ind_tac "n" 1,
                                simp_tac iterate_Cprod_strict_ss 1,
                                simp_tac (HOLCF_ss addsimps copy_con_rews) 1,
                                TRY(safe_tac HOL_cs)] @
                        (flat(map (fn ((dn,_),cons) => map (fn (con,args) => EVERY (
                                asm_full_simp_tac iterate_Cprod_ss 1::
                                map (case_UU_tac (take_stricts'::copy_con_rews) 1)
                                    (nonlazy args) @[
                                asm_full_simp_tac (HOLCF_ss addsimps copy_rews) 1])
                        ) cons) eqs)));
in
val take_rews = atomize take_stricts @ take_0s @ atomize take_apps;
end; (* local *)

val take_lemmas = mapn (fn n => fn(dn,ax_reach) => pg'' thy axs_take_def (mk_All("n",
                mk_trp(dc_take dn $ Bound 0 `%(x_name n) === 
                       dc_take dn $ Bound 0 `%(x_name n^"'")))
           ===> mk_trp(%(x_name n) === %(x_name n^"'"))) (fn prems => [
                                res_inst_tac[("t",x_name n    )](ax_reach RS subst) 1,
                                res_inst_tac[("t",x_name n^"'")](ax_reach RS subst) 1,
                                rtac (fix_def2 RS ssubst) 1,
                                REPEAT(CHANGED(rtac (contlub_cfun_arg RS ssubst) 1
                                               THEN chain_tac 1)),
                                rtac (contlub_cfun_fun RS ssubst) 1,
                                rtac (contlub_cfun_fun RS ssubst) 2,
                                rtac lub_equal 3,
                                chain_tac 1,
                                rtac allI 1,
                                resolve_tac prems 1])) 1 (dnames~~axs_reach);

local
  fun one_con p (con,args) = foldr mk_All (map vname args,
        lift_defined (bound_arg (map vname args)) (nonlazy args,
        lift (fn arg => %(P_name (1+rec_of arg)) $ bound_arg args arg)
             (filter is_rec args,mk_trp(%p $ con_app2 con (bound_arg args) args))));
  fun one_eq ((p,cons),concl) = (mk_trp(%p $ UU) ===> 
                           foldr (op ===>) (map (one_con p) cons,concl));
  fun ind_term concf = foldr one_eq (mapn (fn n => fn x => (P_name n, x)) 1 conss,
        mk_trp(foldr' mk_conj (mapn (fn n => concf (P_name n,x_name n)) 1 dnames)));
  val take_ss = HOL_ss addsimps take_rews;
  fun ind_tacs tacsf thms1 thms2 prems = TRY(safe_tac HOL_cs)::
                                flat (mapn (fn n => fn (thm1,thm2) => 
                                  tacsf (n,prems) (thm1,thm2) @ 
                                  flat (map (fn cons =>
                                    (resolve_tac prems 1 ::
                                     flat (map (fn (_,args) => 
                                       resolve_tac prems 1::
                                       map (K(atac 1)) (nonlazy args) @
                                       map (K(atac 1)) (filter is_rec args))
                                     cons)))
                                   conss))
                                0 (thms1~~thms2));
  local 
    fun all_rec_to ns lazy_rec (n,cons) = forall (exists (fn arg => 
                  is_rec arg andalso not(rec_of arg mem ns) andalso
                  ((rec_of arg =  n andalso not(lazy_rec orelse is_lazy arg)) orelse 
                    rec_of arg <> n andalso all_rec_to (rec_of arg::ns) 
                      (lazy_rec orelse is_lazy arg) (n, (nth_elem(rec_of arg,conss))))
                  ) o snd) cons;
    fun warn (n,cons) = if all_rec_to [] false (n,cons) then (writeln 
                           ("WARNING: domain "^nth_elem(n,dnames)^" is empty!"); true)
                        else false;
    fun lazy_rec_to ns lazy_rec (n,cons) = exists (exists (fn arg => 
                  is_rec arg andalso not(rec_of arg mem ns) andalso
                  ((rec_of arg =  n andalso (lazy_rec orelse is_lazy arg)) orelse 
                    rec_of arg <> n andalso lazy_rec_to (rec_of arg::ns)
                     (lazy_rec orelse is_lazy arg) (n, (nth_elem(rec_of arg,conss))))
                 ) o snd) cons;
  in val is_emptys = map warn (mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs);
     val is_finite = forall (not o lazy_rec_to [] false) 
                            (mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs)
  end;
in
val finite_ind = pg'' thy [] (ind_term (fn (P,x) => fn dn => 
                          mk_all(x,%P $ (dc_take dn $ %"n" `Bound 0)))) (fn prems=> [
                                nat_ind_tac "n" 1,
                                simp_tac (take_ss addsimps prems) 1,
                                TRY(safe_tac HOL_cs)]
                                @ flat(mapn (fn n => fn (cons,cases) => [
                                 res_inst_tac [("x",x_name n)] cases 1,
                                 asm_simp_tac (take_ss addsimps prems) 1]
                                 @ flat(map (fn (con,args) => 
                                  asm_simp_tac take_ss 1 ::
                                  map (fn arg =>
                                   case_UU_tac (prems@con_rews) 1 (
                                   nth_elem(rec_of arg,dnames)^"_take n1`"^vname arg))
                                  (filter is_nonlazy_rec args) @ [
                                  resolve_tac prems 1] @
                                  map (K (atac 1))      (nonlazy args) @
                                  map (K (etac spec 1)) (filter is_rec args)) 
                                 cons))
                                1 (conss~~casess)));

val (finites,ind) = if is_finite then
let 
  fun take_enough dn = mk_ex ("n",dc_take dn $ Bound 0 ` %"x" === %"x");
  val finite_lemmas1a = map (fn dn => pg [] (mk_trp(defined (%"x")) ===> 
        mk_trp(mk_disj(mk_all("n",dc_take dn $ Bound 0 ` %"x" === UU),
        take_enough dn)) ===> mk_trp(take_enough dn)) [
                                etac disjE 1,
                                etac notE 1,
                                resolve_tac take_lemmas 1,
                                asm_simp_tac take_ss 1,
                                atac 1]) dnames;
  val finite_lemma1b = pg [] (mk_trp (mk_all("n",foldr' mk_conj (mapn 
        (fn n => fn ((dn,args),_) => mk_constrainall(x_name n,Type(dn,args),
         mk_disj(dc_take dn $ Bound 1 ` Bound 0 === UU,
                 dc_take dn $ Bound 1 ` Bound 0 === Bound 0))) 1 eqs)))) ([
                                rtac allI 1,
                                nat_ind_tac "n" 1,
                                simp_tac take_ss 1,
                                TRY(safe_tac(empty_cs addSEs[conjE] addSIs[conjI]))] @
                                flat(mapn (fn n => fn (cons,cases) => [
                                  simp_tac take_ss 1,
                                  rtac allI 1,
                                  res_inst_tac [("x",x_name n)] cases 1,
                                  asm_simp_tac take_ss 1] @ 
                                  flat(map (fn (con,args) => 
                                    asm_simp_tac take_ss 1 ::
                                    flat(map (fn arg => [
                                      eres_inst_tac [("x",vname arg)] all_dupE 1,
                                      etac disjE 1,
                                      asm_simp_tac (HOL_ss addsimps con_rews) 1,
                                      asm_simp_tac take_ss 1])
                                    (filter is_nonlazy_rec args)))
                                  cons))
                                1 (conss~~casess))) handle ERROR => raise ERROR;
  val all_finite=map (fn(dn,l1b)=>pg axs_finite_def (mk_trp(%%(dn^"_finite") $ %"x"))[
                                case_UU_tac take_rews 1 "x",
                                eresolve_tac finite_lemmas1a 1,
                                step_tac HOL_cs 1,
                                step_tac HOL_cs 1,
                                cut_facts_tac [l1b] 1,
                                fast_tac HOL_cs 1]) (dnames~~atomize finite_lemma1b);
in
(all_finite,
 pg'' thy [] (ind_term (fn (P,x) => fn dn => %P $ %x))
                               (ind_tacs (fn _ => fn (all_fin,finite_ind) => [
                                rtac (rewrite_rule axs_finite_def all_fin RS exE) 1,
                                etac subst 1,
                                rtac finite_ind 1]) all_finite (atomize finite_ind))
) end (* let *) else
(mapn (fn n => fn dn => read_instantiate_sg (sign_of thy) 
                    [("P",dn^"_finite "^x_name n)] excluded_middle) 1 dnames,
 pg'' thy [] (foldr (op ===>) (mapn (fn n =>K(mk_trp(%%"adm" $ %(P_name n))))1
                                       dnames,ind_term (fn(P,x)=>fn dn=> %P $ %x)))
                               (ind_tacs (fn (n,prems) => fn (ax_reach,finite_ind) =>[
                                rtac (ax_reach RS subst) 1,
                                res_inst_tac [("x",x_name n)] spec 1,
                                rtac wfix_ind 1,
                                rtac adm_impl_admw 1,
                                resolve_tac adm_thms 1,
                                rtac adm_subst 1,
                                cont_tacR 1,
                                resolve_tac prems 1,
                                strip_tac 1,
                                rtac(rewrite_rule axs_take_def finite_ind) 1])
                                 axs_reach (atomize finite_ind))
)
end; (* local *)

local
  val xs = mapn (fn n => K (x_name n)) 1 dnames;
  fun bnd_arg n i = Bound(2*(length dnames - n)-i-1);
  val take_ss = HOL_ss addsimps take_rews;
  val sproj   = bin_branchr (fn s => "fst("^s^")") (fn s => "snd("^s^")");
  val coind_lemma = pg [ax_bisim_def] (mk_trp(mk_imp(%%(comp_dname^"_bisim") $ %"R",
                foldr (fn (x,t)=> mk_all(x,mk_all(x^"'",t))) (xs,
                  foldr mk_imp (mapn (fn n => K(proj (%"R") dnames n $ 
                                      bnd_arg n 0 $ bnd_arg n 1)) 0 dnames,
                    foldr' mk_conj (mapn (fn n => fn dn => 
                                (dc_take dn $ %"n" `bnd_arg n 0 === 
                                (dc_take dn $ %"n" `bnd_arg n 1))) 0 dnames)))))) ([
                                rtac impI 1,
                                nat_ind_tac "n" 1,
                                simp_tac take_ss 1,
                                safe_tac HOL_cs] @
                                flat(mapn (fn n => fn x => [
                                  etac allE 1, etac allE 1, 
                                  eres_inst_tac [("P1",sproj "R" dnames n^
                                                  " "^x^" "^x^"'")](mp RS disjE) 1,
                                  TRY(safe_tac HOL_cs),
                                  REPEAT(CHANGED(asm_simp_tac take_ss 1))]) 
                                0 xs));
in
val coind = pg [] (mk_trp(%%(comp_dname^"_bisim") $ %"R") ===>
                foldr (op ===>) (mapn (fn n => fn x => 
                        mk_trp(proj (%"R") dnames n $ %x $ %(x^"'"))) 0 xs,
                        mk_trp(foldr' mk_conj (map (fn x => %x === %(x^"'")) xs)))) ([
                                TRY(safe_tac HOL_cs)] @
                                flat(map (fn take_lemma => [
                                  rtac take_lemma 1,
                                  cut_facts_tac [coind_lemma] 1,
                                  fast_tac HOL_cs 1])
                                take_lemmas));
end; (* local *)


in (take_rews, take_lemmas, finites, finite_ind, ind, coind)

end; (* let *)
end; (* local *)
end; (* struct *)
