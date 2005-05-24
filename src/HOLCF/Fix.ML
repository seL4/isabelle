
(* legacy ML bindings *)

val iterate_0 = thm "iterate_0";
val iterate_Suc = thm "iterate_Suc";
val Ifix_def = thm "Ifix_def";
val fix_def = thm "fix_def";
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
val admw_def2 = thm "admw_def2";
val def_fix_ind = thm "def_fix_ind";
val adm_impl_admw = thm "adm_impl_admw";
val fix_ind = thm "fix_ind";
val def_fix_ind = thm "def_fix_ind";
val wfix_ind = thm "wfix_ind";
val def_wfix_ind = thm "def_wfix_ind";

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
