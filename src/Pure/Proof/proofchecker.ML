(*  Title:      Pure/Proof/proofchecker.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Simple proof checker based only on the core inference rules
of Isabelle/Pure.
*)

signature PROOF_CHECKER =
sig
  val thm_of_proof : theory -> Proofterm.proof -> thm
end;

structure ProofChecker : PROOF_CHECKER =
struct

open Proofterm;

(***** construct a theorem out of a proof term *****)

fun lookup_thm thy =
  let val tab = foldr Symtab.update
    (flat (map thms_of (thy :: Theory.ancestors_of thy)), Symtab.empty)
  in
    (fn s => case Symtab.lookup (tab, s) of
       None => error ("Unknown theorem " ^ quote s)
     | Some thm => thm)
  end;

fun beta_eta_convert thm =
  let
    val beta_thm = beta_conversion true (cprop_of thm);
    val (_, rhs) = Drule.dest_equals (cprop_of beta_thm);
  in Thm.equal_elim (Thm.transitive beta_thm (eta_conversion rhs)) thm end;

fun thm_of_proof thy prf =
  let
    val names = add_prf_names ([], prf);
    val sg = sign_of thy;
    val lookup = lookup_thm thy;

    fun thm_of _ _ (PThm ((name, _), _, prop', Some Ts)) =
          let
            val thm = lookup name;
            val {prop, ...} = rep_thm thm;
            val _ = if prop=prop' then () else
              error ("Duplicate use of theorem name " ^ quote name ^ "\n" ^
                Sign.string_of_term sg prop ^ "\n\n" ^
                Sign.string_of_term sg prop');
            val tvars = term_tvars prop;
            val ctye = map fst tvars ~~ map (Thm.ctyp_of sg) Ts
          in
            Thm.instantiate (ctye, []) (forall_intr_vars thm)
          end

      | thm_of _ _ (PAxm (name, _, Some Ts)) =
          let
            val thm = get_axiom thy name;
            val {prop, ...} = rep_thm thm;
            val tvars = term_tvars prop;
            val ctye = map fst tvars ~~ map (Thm.ctyp_of sg) Ts
          in
            Thm.instantiate (ctye, []) (forall_intr_vars thm)
          end

      | thm_of _ Hs (PBound i) = nth_elem (i, Hs)

      | thm_of vs Hs (Abst (s, Some T, prf)) =
          let
            val x = variant (names @ map fst vs) s;
            val thm = thm_of ((x, T) :: vs) Hs prf
          in
            Thm.forall_intr (Thm.cterm_of sg (Free (x, T))) thm
          end

      | thm_of vs Hs (prf % Some t) =
          let
            val thm = thm_of vs Hs prf
            val ct = Thm.cterm_of sg (Term.subst_bounds (map Free vs, t))
          in Thm.forall_elim ct thm end

      | thm_of vs Hs (AbsP (s, Some t, prf)) =
          let
            val ct = Thm.cterm_of sg (Term.subst_bounds (map Free vs, t));
            val thm = thm_of vs (Thm.assume ct :: Hs) prf
          in
            Thm.implies_intr ct thm
          end

      | thm_of vs Hs (prf %% prf') =
          let 
            val thm = beta_eta_convert (thm_of vs Hs prf);
            val thm' = beta_eta_convert (thm_of vs Hs prf')
          in
            Thm.implies_elim thm thm'
          end

      | thm_of _ _ (Hyp t) = Thm.assume (Thm.cterm_of sg t)

      | thm_of _ _ _ = error "thm_of_proof: partial proof term";

  in thm_of [] [] prf end;

end;

