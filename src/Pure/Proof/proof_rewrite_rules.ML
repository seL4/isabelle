(*  Title:      Pure/Proof/proof_rewrite_rules.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Simplification function for partial proof terms involving
meta level rules.
*)

signature PROOF_REWRITE_RULES =
sig
  val rprocs : (string * (typ list -> Proofterm.proof -> Proofterm.proof option)) list
end;

structure ProofRewriteRules : PROOF_REWRITE_RULES =
struct

open Proofterm;

fun rew _ (PThm (("ProtoPure.rev_triv_goal", _), _, _, _) %% _ %
      (PThm (("ProtoPure.triv_goal", _), _, _, _) %% _ % prf)) = Some prf
  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% _ %% _ %
      (PAxm ("ProtoPure.equal_intr", _, _) %% _ %% _ % prf % _)) = Some prf
  | rew _ (PAxm ("ProtoPure.symmetric", _, _) %% _ %% _ %
      (PAxm ("ProtoPure.equal_intr", _, _) %% A %% B % prf1 % prf2)) =
          Some (equal_intr_axm %% B %% A % prf2 % prf1)

  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% Some X %% Some Y %
      (PAxm ("ProtoPure.combination", _, _) %% _ %% _ %% _ %% _ %
        (PAxm ("ProtoPure.combination", _, _) %% Some (Const ("==>", _)) %% _ %% _ %% _ %
           (PAxm ("ProtoPure.reflexive", _, _) %% _) % prf1) % prf2)) =
      let
        val _ $ A $ C = Envir.beta_norm X;
        val _ $ B $ D = Envir.beta_norm Y
      in Some (AbsP ("H1", None, AbsP ("H2", None,
        equal_elim_axm %%% C %%% D % incr_pboundvars 2 0 prf2 %
          (PBound 1 % (equal_elim_axm %%% B %%% A %
            (symmetric_axm %% None %% None % incr_pboundvars 2 0 prf1) % PBound 0)))))
      end

  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% Some X %% Some Y %
      (PAxm ("ProtoPure.symmetric", _, _) %% _ %% _ %
        (PAxm ("ProtoPure.combination", _, _) %% _ %% _ %% _ %% _ %
          (PAxm ("ProtoPure.combination", _, _) %% Some (Const ("==>", _)) %% _ %% _ %% _ %
             (PAxm ("ProtoPure.reflexive", _, _) %% _) % prf1) % prf2))) =
      let
        val _ $ A $ C = Envir.beta_norm Y;
        val _ $ B $ D = Envir.beta_norm X
      in Some (AbsP ("H1", None, AbsP ("H2", None,
        equal_elim_axm %%% D %%% C %
          (symmetric_axm %% None %% None % incr_pboundvars 2 0 prf2)
            % (PBound 1 % (equal_elim_axm %%% A %%% B % incr_pboundvars 2 0 prf1 % PBound 0)))))
      end

  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% Some X %% Some Y %
      (PAxm ("ProtoPure.combination", _, _) %% Some (Const ("all", _)) %% _ %% _ %% _ %
        (PAxm ("ProtoPure.reflexive", _, _) %% _) %
          (PAxm ("ProtoPure.abstract_rule", _, _) %% _ %% _ % prf))) =
      let
        val _ $ P = Envir.beta_norm X;
        val _ $ Q = Envir.beta_norm Y;
      in Some (AbsP ("H", None, Abst ("x", None,
          equal_elim_axm %%% incr_boundvars 1 P $ Bound 0 %%% incr_boundvars 1 Q $ Bound 0 %
            (incr_pboundvars 1 1 prf %%% Bound 0) % (PBound 0 %%% Bound 0))))
      end

  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% Some X %% Some Y %
      (PAxm ("ProtoPure.symmetric", _, _) %% _ %% _ %        
        (PAxm ("ProtoPure.combination", _, _) %% Some (Const ("all", _)) %% _ %% _ %% _ %
          (PAxm ("ProtoPure.reflexive", _, _) %% _) %
            (PAxm ("ProtoPure.abstract_rule", _, _) %% _ %% _ % prf)))) =
      let
        val _ $ P = Envir.beta_norm X;
        val _ $ Q = Envir.beta_norm Y;
      in Some (AbsP ("H", None, Abst ("x", None,
        equal_elim_axm %%% incr_boundvars 1 P $ Bound 0 %%% incr_boundvars 1 Q $ Bound 0 %
          (symmetric_axm %% None %% None % (incr_pboundvars 1 1 prf %%% Bound 0))
            % (PBound 0 %%% Bound 0))))
      end

  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% Some A %% Some C %
      (PAxm ("ProtoPure.transitive", _, _) %% _ %% Some B %% _ % prf1 % prf2) % prf3) =
         Some (equal_elim_axm %%% B %%% C % prf2 %
           (equal_elim_axm %%% A %%% B % prf1 % prf3))
  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% Some A %% Some C %
      (PAxm ("ProtoPure.symmetric", _, _) %% _ %% _ %
        (PAxm ("ProtoPure.transitive", _, _) %% _ %% Some B %% _ % prf1 % prf2)) % prf3) =
         Some (equal_elim_axm %%% B %%% C % (symmetric_axm %% None %% None % prf1) %
           (equal_elim_axm %%% A %%% B % (symmetric_axm %% None %% None % prf2) % prf3))

  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% _ %% _ %
      (PAxm ("ProtoPure.reflexive", _, _) %% _) % prf) = Some prf
  | rew _ (PAxm ("ProtoPure.equal_elim", _, _) %% _ %% _ %
      (PAxm ("ProtoPure.symmetric", _, _) %% _ %% _ %
        (PAxm ("ProtoPure.reflexive", _, _) %% _)) % prf) = Some prf

  | rew _ _ = None;

val rprocs = [("Pure/meta_equality", rew)];

end;

Proofterm.add_prf_rprocs ProtoPure.thy ProofRewriteRules.rprocs;
