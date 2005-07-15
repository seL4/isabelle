(*  Title:      Pure/Proof/proofchecker.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

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
  let val tab = fold_rev (curry Symtab.update) (PureThy.all_thms_of thy) Symtab.empty
  in
    (fn s => case Symtab.lookup (tab, s) of
       NONE => error ("Unknown theorem " ^ quote s)
     | SOME thm => thm)
  end;

val beta_eta_convert =
  Drule.fconv_rule Drule.beta_eta_conversion;

fun thm_of_proof thy prf =
  let
    val names = add_prf_names ([], prf);
    val sg = sign_of thy;
    val lookup = lookup_thm thy;

    fun thm_of_atom thm Ts =
      let
        val tvars = term_tvars (Thm.full_prop_of thm);
        val (thm', fmap) = Thm.varifyT' [] thm;
        val ctye = map (pairself (Thm.ctyp_of sg))
          (map TVar tvars @ map (fn ((_, S), ixn) => TVar (ixn, S)) fmap ~~ Ts)
      in
        Thm.instantiate (ctye, []) (forall_intr_vars (forall_intr_frees thm'))
      end;

    fun thm_of _ _ (PThm ((name, _), _, prop', SOME Ts)) =
          let
            val thm = Drule.implies_intr_hyps (lookup name);
            val {prop, ...} = rep_thm thm;
            val _ = if prop aconv prop' then () else
              error ("Duplicate use of theorem name " ^ quote name ^ "\n" ^
                Sign.string_of_term sg prop ^ "\n\n" ^
                Sign.string_of_term sg prop');
          in thm_of_atom thm Ts end

      | thm_of _ _ (PAxm (name, _, SOME Ts)) =
          thm_of_atom (get_axiom thy name) Ts

      | thm_of _ Hs (PBound i) = List.nth (Hs, i)

      | thm_of vs Hs (Abst (s, SOME T, prf)) =
          let
            val x = variant (names @ map fst vs) s;
            val thm = thm_of ((x, T) :: vs) Hs prf
          in
            Thm.forall_intr (Thm.cterm_of sg (Free (x, T))) thm
          end

      | thm_of vs Hs (prf % SOME t) =
          let
            val thm = thm_of vs Hs prf
            val ct = Thm.cterm_of sg (Term.subst_bounds (map Free vs, t))
          in Thm.forall_elim ct thm end

      | thm_of vs Hs (AbsP (s, SOME t, prf)) =
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

  in beta_eta_convert (thm_of [] [] prf) end;

end;
