(*  Title:      LCF/lcf.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

For lcf.thy.  Basic lemmas about LCF
*)

open LCF;

signature LCF_LEMMAS =
sig
  val ap_term: thm
  val ap_thm: thm
  val COND_cases: thm
  val COND_cases_iff: thm
  val Contrapos: thm
  val cong: thm
  val ext: thm
  val eq_imp_less1: thm
  val eq_imp_less2: thm
  val less_anti_sym: thm
  val less_ap_term: thm
  val less_ap_thm: thm
  val less_refl: thm
  val less_UU: thm
  val not_UU_eq_TT: thm
  val not_UU_eq_FF: thm
  val not_TT_eq_UU: thm
  val not_TT_eq_FF: thm
  val not_FF_eq_UU: thm
  val not_FF_eq_TT: thm
  val rstac: thm list -> int -> tactic
  val stac: thm -> int -> tactic
  val sstac: thm list -> int -> tactic
  val strip_tac: int -> tactic
  val tr_induct: thm
  val UU_abs: thm
  val UU_app: thm
end;


structure LCF_Lemmas : LCF_LEMMAS =

struct

(* Standard abbreviations *)

val rstac = resolve_tac;
fun stac th = rtac(th RS sym RS subst);
fun sstac ths = EVERY' (map stac ths);

fun strip_tac i = REPEAT(rstac [impI,allI] i); 

val eq_imp_less1 = prove_goal thy "x=y ==> x << y"
        (fn prems => [rtac (rewrite_rule[eq_def](hd prems) RS conjunct1) 1]);

val eq_imp_less2 = prove_goal thy "x=y ==> y << x"
        (fn prems => [rtac (rewrite_rule[eq_def](hd prems) RS conjunct2) 1]);

val less_refl = refl RS eq_imp_less1;

val less_anti_sym = prove_goal thy "[| x << y; y << x |] ==> x=y"
        (fn prems => [rewtac eq_def,
                      REPEAT(rstac(conjI::prems)1)]);

val ext = prove_goal thy
        "(!!x::'a::cpo. f(x)=(g(x)::'b::cpo)) ==> (%x.f(x))=(%x.g(x))"
        (fn [prem] => [REPEAT(rstac[less_anti_sym, less_ext, allI,
                                    prem RS eq_imp_less1,
                                    prem RS eq_imp_less2]1)]);

val cong = prove_goal thy "[| f=g; x=y |] ==> f(x)=g(y)"
        (fn prems => [cut_facts_tac prems 1, etac subst 1, etac subst 1,
                      rtac refl 1]);

val less_ap_term = less_refl RS mono;
val less_ap_thm = less_refl RSN (2,mono);
val ap_term = refl RS cong;
val ap_thm = refl RSN (2,cong);

val UU_abs = prove_goal thy "(%x::'a::cpo.UU) = UU"
        (fn _ => [rtac less_anti_sym 1, rtac minimal 2,
                  rtac less_ext 1, rtac allI 1, rtac minimal 1]);

val UU_app = UU_abs RS sym RS ap_thm;

val less_UU = prove_goal thy "x << UU ==> x=UU"
        (fn prems=> [rtac less_anti_sym 1,rstac prems 1,rtac minimal 1]);


val tr_induct = prove_goal thy "[| P(UU); P(TT); P(FF) |] ==> ALL b.P(b)"
        (fn prems => [rtac allI 1, rtac mp 1,
                      res_inst_tac[("p","b")]tr_cases 2,
                      fast_tac (FOL_cs addIs prems) 1]);


val Contrapos = prove_goal thy "(A ==> B) ==> (~B ==> ~A)"
        (fn prems => [rtac notI 1, rtac notE 1, rstac prems 1,
                      rstac prems 1, atac 1]);

val not_less_imp_not_eq1 = eq_imp_less1 COMP Contrapos;
val not_less_imp_not_eq2 = eq_imp_less2 COMP Contrapos;

val not_UU_eq_TT = not_TT_less_UU RS not_less_imp_not_eq2;
val not_UU_eq_FF = not_FF_less_UU RS not_less_imp_not_eq2;
val not_TT_eq_UU = not_TT_less_UU RS not_less_imp_not_eq1;
val not_TT_eq_FF = not_TT_less_FF RS not_less_imp_not_eq1;
val not_FF_eq_UU = not_FF_less_UU RS not_less_imp_not_eq1;
val not_FF_eq_TT = not_FF_less_TT RS not_less_imp_not_eq1;


val COND_cases_iff = (prove_goal thy
  "ALL b. P(b=>x|y) <-> (b=UU-->P(UU)) & (b=TT-->P(x)) & (b=FF-->P(y))"
        (fn _ => [cut_facts_tac [not_UU_eq_TT,not_UU_eq_FF,not_TT_eq_UU,
                                 not_TT_eq_FF,not_FF_eq_UU,not_FF_eq_TT]1,
                  rtac tr_induct 1, stac COND_UU 1, stac COND_TT 2,
                  stac COND_FF 3, REPEAT(fast_tac FOL_cs 1)]))  RS spec;

val lemma = prove_goal thy "A<->B ==> B ==> A"
        (fn prems => [cut_facts_tac prems 1, rewtac iff_def,
                      fast_tac FOL_cs 1]);

val COND_cases = conjI RSN (2,conjI RS (COND_cases_iff RS lemma));

end;

open LCF_Lemmas;

