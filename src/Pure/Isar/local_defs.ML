(*  Title:      Pure/Isar/local_defs.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Local definitions.
*)

signature LOCAL_DEFS =
sig
  val def: string -> Proof.context attribute list -> string *  (string * string list)
    -> Proof.state -> Proof.state
  val def_i: string -> Proof.context attribute list -> string * (term * term list)
    -> Proof.state -> Proof.state
end;

structure LocalDefs: LOCAL_DEFS =
struct


(* export_def *)

fun dest_lhs cprop =
  let val x = #1 (Logic.dest_equals (Thm.term_of cprop))
  in Term.dest_Free x; Thm.cterm_of (Thm.sign_of_cterm cprop) x end
  handle TERM _ => raise TERM ("Malformed definitional assumption encountered:\n" ^
      quote (Display.string_of_cterm cprop), []);

fun export_def _ cprops thm =
  thm
  |> Drule.implies_intr_list cprops
  |> Drule.forall_intr_list (map dest_lhs cprops)
  |> Drule.forall_elim_vars 0
  |> RANGE (replicate (length cprops) (Tactic.rtac Drule.reflexive_thm)) 1;


(* def(_i) *)

fun gen_def fix prep_term prep_pats raw_name atts (x, (raw_rhs, raw_pats)) state =
  let
    val _ = Proof.assert_forward state;
    val ctxt = Proof.context_of state;

    (*rhs*)
    val name = if raw_name = "" then Thm.def_name x else raw_name;
    val rhs = prep_term ctxt raw_rhs;
    val T = Term.fastype_of rhs;
    val pats = prep_pats T (ProofContext.declare_term rhs ctxt) raw_pats;

    (*lhs*)
    val lhs = ProofContext.bind_skolem ctxt [x] (Free (x, T));
  in
    state
    |> fix [([x], None)]
    |> Proof.match_bind_i [(pats, rhs)]
    |> Proof.assm_i export_def [((name, atts), [(Logic.mk_equals (lhs, rhs), ([], []))])]
  end;

val def = gen_def Proof.fix ProofContext.read_term ProofContext.read_term_pats;
val def_i = gen_def Proof.fix_i ProofContext.cert_term ProofContext.cert_term_pats;


end;
