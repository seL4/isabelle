
(* legacy ML bindings *)

val adm_chfindom = thm "adm_chfindom";
val adm_impl_admw = thm "adm_impl_admw";
val admw_def = thm "admw_def";
val chain_iterate2 = thm "chain_iterate2";
val chain_iterate = thm "chain_iterate";
val def_fix_ind = thm "def_fix_ind";
val def_wfix_ind = thm "def_wfix_ind";
val fix_const = thm "fix_const";
val fix_def2 = thm "fix_def2";
val fix_defined = thm "fix_defined";
val fix_defined_iff = thm "fix_defined_iff";
val fix_def = thm "fix_def";
val fix_eq2 = thm "fix_eq2";
val fix_eq3 = thm "fix_eq3";
val fix_eq4 = thm "fix_eq4";
val fix_eq5 = thm "fix_eq5";
val fix_eqI = thm "fix_eqI";
val fix_eq = thm "fix_eq";
val fix_id = thm "fix_id";
val fix_ind = thm "fix_ind";
val fix_least = thm "fix_least";
val fix_strict = thm "fix_strict";
val iterate_0 = thm "iterate_0";
val iterate_Suc2 = thm "iterate_Suc2";
val iterate_Suc = thm "iterate_Suc";
val wfix_ind = thm "wfix_ind";

structure Fix =
struct
  val thy = the_context ();
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
