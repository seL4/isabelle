(*  Title:      Pure/Isar/local_defs.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Local definitions.
*)

signature LOCAL_DEFS =
sig
  val def: string -> Proof.context attribute list
    -> (string * string option) *  (string * string list) -> Proof.state -> Proof.state
  val def_i: string -> Proof.context attribute list
    -> (string * typ option) * (term * term list) -> Proof.state -> Proof.state
end;

structure LocalDefs: LOCAL_DEFS =
struct

val refl_tac = Tactic.rtac (Drule.standard (Drule.reflexive_thm RS Drule.triv_goal));

fun gen_def fix prep_term prep_pats raw_name atts ((x, raw_T), (raw_rhs, raw_pats)) state =
  let
    val _ = Proof.assert_forward state;

    (*rhs*)
    val ctxt = Proof.context_of state;
    val name = if raw_name = "" then Thm.def_name x else raw_name;
    val rhs = prep_term ctxt raw_rhs;
    val T = Term.fastype_of rhs;
    val pats = prep_pats T (ProofContext.declare_term rhs ctxt) raw_pats;

    (*lhs*)
    val state' = fix [([x], raw_T)] state;
    val lhs = ProofContext.intern_skolem (Proof.context_of state') (Free (x, T));
  in
    state'
    |> Proof.match_bind_i [(pats, rhs)]
    |> Proof.assm_i (refl_tac, refl_tac) [(name, atts, [(Logic.mk_equals (lhs, rhs), ([], []))])]
  end;

val def = gen_def Proof.fix ProofContext.read_term ProofContext.read_term_pats;
val def_i = gen_def Proof.fix_i ProofContext.cert_term ProofContext.cert_term_pats;


end;
