(*  Title:      Pure/Isar/local_defs.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Local definitions.
*)

signature LOCAL_DEFS =
sig
  val def: string -> Proof.context attribute list
    -> (string * string option) *  (string * string list) -> Proof.state -> Proof.state
  val def_i: string -> Proof.context attribute list
    -> (string * typ) * (term * term list) -> Proof.state -> Proof.state
end;

structure LocalDefs: LOCAL_DEFS =
struct


val refl_tac = Tactic.rtac (Drule.standard (Drule.reflexive_thm RS Drule.triv_goal));


fun gen_def fix prep_term match_binds raw_name atts ((x, raw_T), (raw_rhs, raw_pats)) state =
  let
    fun err msg = raise Proof.STATE ("Bad local def: " ^ msg, state);

    val state' = fix [([x], raw_T)] state;
    val ctxt' = Proof.context_of state';

    val name = if raw_name = "" then Thm.def_name x else raw_name;
    val rhs = prep_term ctxt' raw_rhs;
    val T = Term.fastype_of rhs;
    val lhs = ProofContext.cert_term ctxt' (Free (x, T));
    val eq = Logic.mk_equals (lhs, rhs);
  in
    if lhs mem Term.add_term_frees (rhs, []) then
      err "lhs occurs on rhs"
    else if not (Term.term_tfrees rhs subset Term.typ_tfrees T) then
      err "extra type variables on rhs"
    else ();
    state'
    |> match_binds [(raw_pats, raw_rhs)]   (*note: raw_rhs prepared twice!*)
    |> Proof.assm_i (refl_tac, refl_tac) [(name, atts, [(eq, ([], []))])]
  end;

val def = gen_def Proof.fix ProofContext.read_term Proof.match_bind;
val def_i = gen_def Proof.fix_i ProofContext.cert_term Proof.match_bind_i;


end;
