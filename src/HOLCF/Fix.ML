
(* legacy ML bindings *)

val iterate_0 = thm "iterate_0";
val iterate_Suc = thm "iterate_Suc";
val Ifix_def = thm "Ifix_def";
val fix_def = thm "fix_def";
val adm_def = thm "adm_def";
val admw_def = thm "admw_def";
val iterate_Suc2 = thm "iterate_Suc2";
val chain_iterate2 = thm "chain_iterate2";
val chain_iterate = thm "chain_iterate";
val Ifix_eq = thm "Ifix_eq";
val Ifix_least = thm "Ifix_least";
val monofun_iterate = thm "monofun_iterate";
val contlub_iterate = thm "contlub_iterate";
val cont_iterate = thm "cont_iterate";
val monofun_iterate2 = thm "monofun_iterate2";
val contlub_iterate2 = thm "contlub_iterate2";
val cont_iterate2 = thm "cont_iterate2";
val monofun_Ifix = thm "monofun_Ifix";
(*val chain_iterate_lub = thm "chain_iterate_lub";*)
(*val contlub_Ifix_lemma1 = thm "contlub_Ifix_lemma1";*)
(*val ex_lub_iterate = thm "ex_lub_iterate";*)
val contlub_Ifix = thm "contlub_Ifix";
val cont_Ifix = thm "cont_Ifix";
val fix_eq = thm "fix_eq";
val fix_least = thm "fix_least";
val fix_eqI = thm "fix_eqI";
val fix_eq2 = thm "fix_eq2";
val fix_eq3 = thm "fix_eq3";
val fix_eq4 = thm "fix_eq4";
val fix_eq5 = thm "fix_eq5";
val Ifix_def2 = thm "Ifix_def2";
val fix_def2 = thm "fix_def2";
val admI = thm "admI";
val triv_admI = thm "triv_admI";
val admD = thm "admD";
val admw_def2 = thm "admw_def2";
val def_fix_ind = thm "def_fix_ind";
val adm_impl_admw = thm "adm_impl_admw";
val fix_ind = thm "fix_ind";
val def_fix_ind = thm "def_fix_ind";
val wfix_ind = thm "wfix_ind";
val def_wfix_ind = thm "def_wfix_ind";
val adm_max_in_chain = thm "adm_max_in_chain";
val adm_chfin = thm "adm_chfin";
val adm_chfindom = thm "adm_chfindom";
val admI2 = thm "admI2";
val adm_less = thm "adm_less";
val adm_conj = thm "adm_conj";
val adm_not_free = thm "adm_not_free";
val adm_not_less = thm "adm_not_less";
val adm_all = thm "adm_all";
val adm_all2 = thm "adm_all2";
val adm_subst = thm "adm_subst";
val adm_UU_not_less = thm "adm_UU_not_less";
val adm_not_UU = thm "adm_not_UU";
val adm_eq = thm "adm_eq";
val adm_disj_lemma1 = thm "adm_disj_lemma1";
val adm_disj_lemma2 = thm "adm_disj_lemma2";
val adm_disj_lemma3 = thm "adm_disj_lemma3";
val adm_disj_lemma4 = thm "adm_disj_lemma4";
val adm_disj_lemma5 = thm "adm_disj_lemma5";
val adm_disj_lemma6 = thm "adm_disj_lemma6";
val adm_disj_lemma7 = thm "adm_disj_lemma7";
val adm_disj_lemma8 = thm "adm_disj_lemma8";
val adm_disj_lemma9 = thm "adm_disj_lemma9";
val adm_disj_lemma10 = thm "adm_disj_lemma10";
val adm_disj_lemma12 = thm "adm_disj_lemma12";
val adm_lemma11 = thm "adm_lemma11";
val adm_disj = thm "adm_disj";
val adm_imp = thm "adm_imp";
val adm_iff = thm "adm_iff";
val adm_not_conj = thm "adm_not_conj";
val adm_lemmas = [adm_not_free, adm_imp, adm_disj, adm_eq, adm_not_UU,
        adm_UU_not_less, adm_all2, adm_not_less, adm_not_conj, adm_iff]

structure Fix =
struct
  val thy = the_context ();
  val Ifix_def = Ifix_def;
  val fix_def = fix_def;
  val adm_def = adm_def;
  val admw_def = admw_def;
end;

fun fix_tac3 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq3) i));

fun fix_tac5 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq5) i));

(* proves the unfolding theorem for function equations f = fix$... *)
fun fix_prover thy fixeq s = prove_goal thy s (fn prems => [
        (rtac trans 1),
        (rtac (fixeq RS fix_eq4) 1),
        (rtac trans 1),
        (rtac beta_cfun 1),
        (Simp_tac 1)
        ]);

(* proves the unfolding theorem for function definitions f == fix$... *)
fun fix_prover2 thy fixdef s = prove_goal thy s (fn prems => [
        (rtac trans 1),
        (rtac (fix_eq2) 1),
        (rtac fixdef 1),
        (rtac beta_cfun 1),
        (Simp_tac 1)
        ]);

(* proves an application case for a function from its unfolding thm *)
fun case_prover thy unfold s = prove_goal thy s (fn prems => [
        (cut_facts_tac prems 1),
        (rtac trans 1),
        (stac unfold 1),
        Auto_tac
        ]);
