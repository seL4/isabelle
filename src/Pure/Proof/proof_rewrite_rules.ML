(*  Title:      Pure/Proof/proof_rewrite_rules.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Simplification functions for proof terms involving meta level rules.
*)

signature PROOF_REWRITE_RULES =
sig
  val rew : bool -> typ list -> Proofterm.proof -> Proofterm.proof option
  val rprocs : bool -> (string * (typ list -> Proofterm.proof -> Proofterm.proof option)) list
  val rewrite_terms : (term -> term) -> Proofterm.proof -> Proofterm.proof
  val elim_defs : Sign.sg -> bool -> thm list -> Proofterm.proof -> Proofterm.proof
  val setup : (theory -> theory) list
end;

structure ProofRewriteRules : PROOF_REWRITE_RULES =
struct

open Proofterm;

fun rew b =
  let
    fun ? x = if b then Some x else None;
    fun ax (prf as PAxm (s, prop, _)) Ts =
      if b then PAxm (s, prop, Some Ts) else prf;
    fun ty T = if b then
        let val Type (_, [Type (_, [U, _]), _]) = T
        in Some U end
      else None;
    val equal_intr_axm = ax equal_intr_axm [];
    val equal_elim_axm = ax equal_elim_axm [];
    val symmetric_axm = ax symmetric_axm [propT];

    fun rew' _ (PThm (("ProtoPure.rev_triv_goal", _), _, _, _) % _ %%
        (PThm (("ProtoPure.triv_goal", _), _, _, _) % _ %% prf)) = Some prf
      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.equal_intr", _, _) % _ % _ %% prf %% _)) = Some prf
      | rew' _ (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
        (PAxm ("ProtoPure.equal_intr", _, _) % A % B %% prf1 %% prf2)) =
            Some (equal_intr_axm % B % A %% prf2 %% prf1)

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some (_ $ A) % Some (_ $ B) %%
        (PAxm ("ProtoPure.combination", _, _) % Some (Const ("Goal", _)) %
          _ % _ % _ %% (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %%
        ((tg as PThm (("ProtoPure.triv_goal", _), _, _, _)) % _ %% prf2)) =
        Some (tg %> B %% (equal_elim_axm %> A %> B %% prf1 %% prf2))

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some (_ $ A) % Some (_ $ B) %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
          (PAxm ("ProtoPure.combination", _, _) % Some (Const ("Goal", _)) %
             _ % _ % _ %% (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1)) %%
        ((tg as PThm (("ProtoPure.triv_goal", _), _, _, _)) % _ %% prf2)) =
        Some (tg %> B %% (equal_elim_axm %> A %> B %%
          (symmetric_axm % ? B % ? A %% prf1) %% prf2))

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some X % Some Y %%
        (PAxm ("ProtoPure.combination", _, _) % _ % _ % _ % _ %%
          (PAxm ("ProtoPure.combination", _, _) % Some (Const ("==>", _)) % _ % _ % _ %%
             (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %% prf2)) =
        let
          val _ $ A $ C = Envir.beta_norm X;
          val _ $ B $ D = Envir.beta_norm Y
        in Some (AbsP ("H1", ? X, AbsP ("H2", ? B,
          equal_elim_axm %> C %> D %% incr_pboundvars 2 0 prf2 %%
            (PBound 1 %% (equal_elim_axm %> B %> A %%
              (symmetric_axm % ? A % ? B %% incr_pboundvars 2 0 prf1) %% PBound 0)))))
        end

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some X % Some Y %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
          (PAxm ("ProtoPure.combination", _, _) % _ % _ % _ % _ %%
            (PAxm ("ProtoPure.combination", _, _) % Some (Const ("==>", _)) % _ % _ % _ %%
               (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %% prf2))) =
        let
          val _ $ A $ C = Envir.beta_norm Y;
          val _ $ B $ D = Envir.beta_norm X
        in Some (AbsP ("H1", ? X, AbsP ("H2", ? A,
          equal_elim_axm %> D %> C %%
            (symmetric_axm % ? C % ? D %% incr_pboundvars 2 0 prf2)
              %% (PBound 1 %% (equal_elim_axm %> A %> B %% incr_pboundvars 2 0 prf1 %% PBound 0)))))
        end

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some X % Some Y %%
        (PAxm ("ProtoPure.combination", _, _) % Some (Const ("all", _)) % _ % _ % _ %%
          (PAxm ("ProtoPure.reflexive", _, _) % _) %%
            (PAxm ("ProtoPure.abstract_rule", _, _) % _ % _ %% prf))) =
        let
          val Const (_, T) $ P = Envir.beta_norm X;
          val _ $ Q = Envir.beta_norm Y;
        in Some (AbsP ("H", ? X, Abst ("x", ty T,
            equal_elim_axm %> incr_boundvars 1 P $ Bound 0 %> incr_boundvars 1 Q $ Bound 0 %%
              (incr_pboundvars 1 1 prf %> Bound 0) %% (PBound 0 %> Bound 0))))
        end

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some X % Some Y %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%        
          (PAxm ("ProtoPure.combination", _, _) % Some (Const ("all", _)) % _ % _ % _ %%
            (PAxm ("ProtoPure.reflexive", _, _) % _) %%
              (PAxm ("ProtoPure.abstract_rule", _, _) % _ % _ %% prf)))) =
        let
          val Const (_, T) $ P = Envir.beta_norm X;
          val _ $ Q = Envir.beta_norm Y;
          val t = incr_boundvars 1 P $ Bound 0;
          val u = incr_boundvars 1 Q $ Bound 0
        in Some (AbsP ("H", ? X, Abst ("x", ty T,
          equal_elim_axm %> t %> u %%
            (symmetric_axm % ? u % ? t %% (incr_pboundvars 1 1 prf %> Bound 0))
              %% (PBound 0 %> Bound 0))))
        end

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some A % Some C %%
        (PAxm ("ProtoPure.transitive", _, _) % _ % Some B % _ %% prf1 %% prf2) %% prf3) =
           Some (equal_elim_axm %> B %> C %% prf2 %%
             (equal_elim_axm %> A %> B %% prf1 %% prf3))
      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % Some A % Some C %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
          (PAxm ("ProtoPure.transitive", _, _) % _ % Some B % _ %% prf1 %% prf2)) %% prf3) =
           Some (equal_elim_axm %> B %> C %% (symmetric_axm % ? C % ? B %% prf1) %%
             (equal_elim_axm %> A %> B %% (symmetric_axm % ? B % ? A %% prf2) %% prf3))

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf) = Some prf
      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
          (PAxm ("ProtoPure.reflexive", _, _) % _)) %% prf) = Some prf

      | rew' _ (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %% prf)) = Some prf

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.equal_elim", _, _) % Some (_ $ A $ C) % Some (_ $ B $ D) %%
          (PAxm ("ProtoPure.combination", _, _) % _ % _ % _ % _ %%
            (PAxm ("ProtoPure.combination", _, _) % Some (Const ("==", _)) % _ % _ % _ %%
              (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %% prf2) %% prf3) %% prf4) =
          Some (equal_elim_axm %> C %> D %% prf2 %%
            (equal_elim_axm %> A %> C %% prf3 %%
              (equal_elim_axm %> B %> A %% (symmetric_axm % ? A % ? B %% prf1) %% prf4)))

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
          (PAxm ("ProtoPure.equal_elim", _, _) % Some (_ $ A $ C) % Some (_ $ B $ D) %%
            (PAxm ("ProtoPure.combination", _, _) % _ % _ % _ % _ %%
              (PAxm ("ProtoPure.combination", _, _) % Some (Const ("==", _)) % _ % _ % _ %%
                (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %% prf2) %% prf3)) %% prf4) =
          Some (equal_elim_axm %> A %> B %% prf1 %%
            (equal_elim_axm %> C %> A %% (symmetric_axm % ? A % ? C %% prf3) %%
              (equal_elim_axm %> D %> C %% (symmetric_axm % ? C % ? D %% prf2) %% prf4)))

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.equal_elim", _, _) % Some (_ $ B $ D) % Some (_ $ A $ C) %%
          (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
            (PAxm ("ProtoPure.combination", _, _) % _ % _ % _ % _ %%
              (PAxm ("ProtoPure.combination", _, _) % Some (Const ("==", _)) % _ % _ % _ %%
                (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %% prf2)) %% prf3) %% prf4) =
          Some (equal_elim_axm %> D %> C %% (symmetric_axm % ? C % ? D %% prf2) %%
            (equal_elim_axm %> B %> D %% prf3 %%
              (equal_elim_axm %> A %> B %% prf1 %% prf4)))

      | rew' _ (PAxm ("ProtoPure.equal_elim", _, _) % _ % _ %%
        (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
          (PAxm ("ProtoPure.equal_elim", _, _) % Some (_ $ B $ D) % Some (_ $ A $ C) %%
            (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %%
              (PAxm ("ProtoPure.combination", _, _) % _ % _ % _ % _ %%
                (PAxm ("ProtoPure.combination", _, _) % Some (Const ("==", _)) % _ % _ % _ %%
                  (PAxm ("ProtoPure.reflexive", _, _) % _) %% prf1) %% prf2)) %% prf3)) %% prf4) =
          Some (equal_elim_axm %> B %> A %% (symmetric_axm % ? A % ? B %% prf1) %%
            (equal_elim_axm %> D %> B %% (symmetric_axm % ? B % ? D %% prf3) %%
              (equal_elim_axm %> C %> D %% prf2 %% prf4)))

      | rew' _ ((prf as PAxm ("ProtoPure.combination", _, _) %
        Some ((eq as Const ("==", T)) $ t) % _ % _ % _) %%
          (PAxm ("ProtoPure.reflexive", _, _) % _)) =
        let val (U, V) = (case T of
          Type (_, [U, V]) => (U, V) | _ => (dummyT, dummyT))
        in Some (prf %% (ax combination_axm [V, U] %> eq % ? eq % ? t % ? t %%
          (ax reflexive_axm [T] % ? eq) %% (ax reflexive_axm [U] % ? t)))
        end

      | rew' _ _ = None;
  in rew' end;

fun rprocs b = [("Pure/meta_equality", rew b)];
val setup = [Proofterm.add_prf_rprocs (rprocs false)];


(**** apply rewriting function to all terms in proof ****)

fun rewrite_terms r =
  let
    fun rew_term Ts t =
      let
        val frees = map Free (variantlist
          (replicate (length Ts) "x", add_term_names (t, [])) ~~ Ts);
        val t' = r (subst_bounds (frees, t));
        fun strip [] t = t
          | strip (_ :: xs) (Abs (_, _, t)) = strip xs t;
      in
        strip Ts (foldl (uncurry lambda o Library.swap) (t', frees))
      end;

    fun rew Ts (prf1 %% prf2) = rew Ts prf1 %% rew Ts prf2
      | rew Ts (prf % Some t) = rew Ts prf % Some (rew_term Ts t)
      | rew Ts (Abst (s, Some T, prf)) = Abst (s, Some T, rew (T :: Ts) prf)
      | rew Ts (AbsP (s, Some t, prf)) = AbsP (s, Some (rew_term Ts t), rew Ts prf)
      | rew _ prf = prf

  in rew [] end;


(**** eliminate definitions in proof ****)

fun vars_of t = rev (foldl_aterms
  (fn (vs, v as Var _) => v ins vs | (vs, _) => vs) ([], t));

fun insert_refl defs Ts (prf1 %% prf2) =
      insert_refl defs Ts prf1 %% insert_refl defs Ts prf2
  | insert_refl defs Ts (Abst (s, Some T, prf)) =
      Abst (s, Some T, insert_refl defs (T :: Ts) prf)
  | insert_refl defs Ts (AbsP (s, t, prf)) =
      AbsP (s, t, insert_refl defs Ts prf)
  | insert_refl defs Ts prf = (case strip_combt prf of
        (PThm ((s, _), _, prop, Some Ts), ts) =>
          if s mem defs then
            let
              val vs = vars_of prop;
              val tvars = term_tvars prop;
              val (_, rhs) = Logic.dest_equals prop;
              val rhs' = foldl betapply (subst_TVars (map fst tvars ~~ Ts)
                (foldr (fn p => Abs ("", dummyT, abstract_over p)) (vs, rhs)),
                map the ts);
            in
              change_type (Some [fastype_of1 (Ts, rhs')]) reflexive_axm %> rhs'
            end
          else prf
      | (_, []) => prf
      | (prf', ts) => proof_combt' (insert_refl defs Ts prf', ts));

fun elim_defs sign r defs prf =
  let
    val tsig = Sign.tsig_of sign;
    val defs' = map (Logic.dest_equals o prop_of o Drule.abs_def) defs
    val defnames = map Thm.name_of_thm defs;
    val f = if not r then I else
      let
        val cnames = map (fst o dest_Const o fst) defs';
        val thms = flat (map (fn (s, ps) =>
            if s mem defnames then []
            else map (pair s o Some o fst) (filter_out (fn (p, _) =>
              null (add_term_consts (p, []) inter cnames)) ps))
          (Symtab.dest (thms_of_proof Symtab.empty prf)))
      in Reconstruct.expand_proof sign thms end
  in
    rewrite_terms (Pattern.rewrite_term tsig defs' [])
      (insert_refl defnames [] (f prf))
  end;

end;
