(*  Title:      HOL/TPTP/TPTP_Proof_Reconstruction.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Unit tests for proof reconstruction module.

NOTE
  - Makes use of the PolyML structure.
*)

theory TPTP_Proof_Reconstruction_Test
imports TPTP_Test TPTP_Proof_Reconstruction
begin

declare [[exception_trace]]
ML {*
print_depth 200;
PolyML.Compiler.maxInlineSize := 0;
(* FIXME doesn't work with Isabelle?
   PolyML.Compiler.debug := true *)
*}

declare [[
  tptp_trace_reconstruction = true
]]

lemma "! (X1 :: bool) (X2 :: bool) (X3 :: bool) (X4 :: bool) (X5 :: bool). P \<Longrightarrow> ! (X1 :: bool) (X3 :: bool) (X5 :: bool). P"
apply (tactic {*canonicalise_qtfr_order @{context} 1*})
oops

lemma "! (X1 :: bool) (X2 :: bool) (X3 :: bool) (X4 :: bool) (X5 :: bool). P \<Longrightarrow> ! (X1 :: bool) (X3 :: bool) (X5 :: bool). P"
apply (tactic {*canonicalise_qtfr_order @{context} 1*})
apply (rule allI)+
apply (tactic {*nominal_inst_parametermatch_tac @{context} @{thm allE} 1*})+
oops

(*Could test bind_tac further with NUM667^1 inode43*)

(*
  (* SEU581^2.p_nux *)
     (* (Annotated_step ("inode1", "bind"), *)
lemma "\<forall>(SV5\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
            SV6\<Colon>TPTP_Interpret.ind.
            (bnd_in (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
              (bnd_powerset bnd_sK1_A) =
             bnd_in (bnd_dsetconstr SV6 SV5)
              (bnd_powerset SV6)) =
            False \<Longrightarrow>
         (bnd_in (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
           (bnd_powerset bnd_sK1_A) =
          bnd_in (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
           (bnd_powerset bnd_sK1_A)) =
         False"
ML_prf {*
open TPTP_Syntax;
open TPTP_Proof;


val binds =
[Bind ("SV6", Atom (THF_Atom_term (Term_Func (Uninterpreted "sK1_A", [])))), Bind ("SV5", Quant (Lambda, [("SX0", SOME (Fmla_type (Atom (THF_Atom_term (Term_Func (TypeSymbol Type_Ind, []))))))], Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_Func (Uninterpreted "sK2_SY15", []))), Atom (THF_Atom_term (Term_Var "SX0"))])))]
(* |> TPTP_Reconstruct.permute *)

(*
val binds =
[Bind ("SV5", Quant (Lambda, [("SX0", SOME (Fmla_type (Atom (THF_Atom_term (Term_Func (TypeSymbol Type_Ind, []))))))], Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_Func (Uninterpreted "sK2_SY15", []))), Atom (THF_Atom_term (Term_Var "SX0"))]))),
Bind ("SV6", Atom (THF_Atom_term (Term_Func (Uninterpreted "sK1_A", []))))
]
*)

val tec =
(*
  map (bind_tac @{context} (hd prob_names)) binds
  |> FIRST
*)
  bind_tac @{context} (hd prob_names) binds
*}
apply (tactic {*tec*})
done

     (* (Annotated_step ("inode2", "bind"), *)
lemma "\<forall>(SV7\<Colon>TPTP_Interpret.ind) SV8\<Colon>TPTP_Interpret.ind.
            (bnd_subset SV8 SV7 =
             bnd_subset (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
              bnd_sK1_A) =
            False \<or>
            bnd_in SV8 (bnd_powerset SV7) = False \<Longrightarrow>
         (bnd_subset (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
           bnd_sK1_A =
          bnd_subset (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
           bnd_sK1_A) =
         False \<or>
         bnd_in (bnd_dsetconstr bnd_sK1_A bnd_sK2_SY15)
          (bnd_powerset bnd_sK1_A) =
         False"
ML_prf {*
open TPTP_Syntax;
open TPTP_Proof;


val binds =
[Bind ("SV8", Fmla (Interpreted_ExtraLogic Apply, [Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_Func (Uninterpreted "dsetconstr", []))), Atom (THF_Atom_term (Term_Func (Uninterpreted "sK1_A", [])))]), Quant (Lambda, [("SX0", SOME (Fmla_type (Atom (THF_Atom_term (Term_Func (TypeSymbol Type_Ind, []))))))], Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_Func (Uninterpreted "sK2_SY15", []))), Atom (THF_Atom_term (Term_Var "SX0"))]))])), Bind ("SV7", Atom (THF_Atom_term (Term_Func (Uninterpreted "sK1_A", []))))]
(* |> TPTP_Reconstruct.permute *)

val tec =
(*
  map (bind_tac @{context} (hd prob_names)) binds
  |> FIRST
*)
  bind_tac @{context} (hd prob_names) binds
*}
apply (tactic {*tec*})
done
*)

(*
from SEU897^5
lemma "
\<forall>SV9 SV10 SV11 SV12 SV13 SV14.
   (((((bnd_sK5_SY14 SV14 SV13 SV12 = SV11) = False \<or>
       (bnd_sK4_SX0 = SV10 (bnd_sK5_SY14 SV9 SV10 SV11)) =
       False) \<or>
      bnd_cR SV14 = False) \<or>
     (SV12 = SV13 SV14) = False) \<or>
    bnd_cR SV9 = False) \<or>
   (SV11 = SV10 SV9) = False \<Longrightarrow>
\<forall>SV14 SV13 SV12 SV10 SV9.
   (((((bnd_sK5_SY14 SV14 SV13 SV12 =
        bnd_sK5_SY14 SV14 SV13 SV12) =
       False \<or>
       (bnd_sK4_SX0 =
        SV10
         (bnd_sK5_SY14 SV9 SV10
           (bnd_sK5_SY14 SV14 SV13 SV12))) =
       False) \<or>
      bnd_cR SV14 = False) \<or>
     (SV12 = SV13 SV14) = False) \<or>
    bnd_cR SV9 = False) \<or>
   (bnd_sK5_SY14 SV14 SV13 SV12 = SV10 SV9) = False"
ML_prf {*
open TPTP_Syntax;
open TPTP_Proof;

val binds =
[Bind ("SV11", Fmla (Interpreted_ExtraLogic Apply, [Fmla (Interpreted_ExtraLogic Apply, [Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_Func (Uninterpreted "sK5_SY14", []))), Atom (THF_Atom_term (Term_Var "SV14"))]), Atom (THF_Atom_term (Term_Var "SV13"))]), Atom (THF_Atom_term (Term_Var "SV12"))]))]

val tec = bind_tac @{context} (hd prob_names) binds
*}
apply (tactic {*tec*})
done
*)


subsection "Interpreting the inferences"

(*from SET598^5
lemma "(bnd_sK1_X = (\<lambda>SY17. bnd_sK2_Y SY17 \<and> bnd_sK3_Z SY17) \<longrightarrow>
   ((\<forall>SY25. bnd_sK1_X SY25 \<longrightarrow> bnd_sK2_Y SY25) \<and>
    (\<forall>SY26. bnd_sK1_X SY26 \<longrightarrow> bnd_sK3_Z SY26)) \<and>
   (\<forall>SY27.
       (\<forall>SY21. SY27 SY21 \<longrightarrow> bnd_sK2_Y SY21) \<and>
       (\<forall>SY15. SY27 SY15 \<longrightarrow> bnd_sK3_Z SY15) \<longrightarrow>
       (\<forall>SY30. SY27 SY30 \<longrightarrow> bnd_sK1_X SY30))) =
  False \<Longrightarrow>
  (\<not> (bnd_sK1_X = (\<lambda>SY17. bnd_sK2_Y SY17 \<and> bnd_sK3_Z SY17) \<longrightarrow>
      ((\<forall>SY25. bnd_sK1_X SY25 \<longrightarrow> bnd_sK2_Y SY25) \<and>
       (\<forall>SY26. bnd_sK1_X SY26 \<longrightarrow> bnd_sK3_Z SY26)) \<and>
      (\<forall>SY27.
          (\<forall>SY21. SY27 SY21 \<longrightarrow> bnd_sK2_Y SY21) \<and>
          (\<forall>SY15. SY27 SY15 \<longrightarrow> bnd_sK3_Z SY15) \<longrightarrow>
          (\<forall>SY30. SY27 SY30 \<longrightarrow> bnd_sK1_X SY30)))) =
  True"
apply (tactic {*polarity_switch_tac @{context}*})
done
lemma "
  (((\<forall>SY25. bnd_sK1_X SY25 \<longrightarrow> bnd_sK2_Y SY25) \<and>
    (\<forall>SY26. bnd_sK1_X SY26 \<longrightarrow> bnd_sK3_Z SY26)) \<and>
   (\<forall>SY27.
       (\<forall>SY21. SY27 SY21 \<longrightarrow> bnd_sK2_Y SY21) \<and>
       (\<forall>SY15. SY27 SY15 \<longrightarrow> bnd_sK3_Z SY15) \<longrightarrow>
       (\<forall>SY30. SY27 SY30 \<longrightarrow> bnd_sK1_X SY30)) \<longrightarrow>
   bnd_sK1_X = (\<lambda>SY17. bnd_sK2_Y SY17 \<and> bnd_sK3_Z SY17)) =
  False \<Longrightarrow>
  (\<not> (((\<forall>SY25. bnd_sK1_X SY25 \<longrightarrow> bnd_sK2_Y SY25) \<and>
       (\<forall>SY26. bnd_sK1_X SY26 \<longrightarrow> bnd_sK3_Z SY26)) \<and>
      (\<forall>SY27.
          (\<forall>SY21. SY27 SY21 \<longrightarrow> bnd_sK2_Y SY21) \<and>
          (\<forall>SY15. SY27 SY15 \<longrightarrow> bnd_sK3_Z SY15) \<longrightarrow>
          (\<forall>SY30. SY27 SY30 \<longrightarrow> bnd_sK1_X SY30)) \<longrightarrow>
      bnd_sK1_X = (\<lambda>SY17. bnd_sK2_Y SY17 \<and> bnd_sK3_Z SY17))) =
  True"
apply (tactic {*polarity_switch_tac @{context}*})
done
*)

(* beware lack of type annotations
(* lemma "!!x. (A x = B x) = False ==> (B x = A x) = False" *)
(* lemma "!!x. (A x = B x) = True ==> (B x = A x) = True" *)
(* lemma "((A x) = (B x)) = True ==> ((B x) = (A x)) = True" *)
lemma "(A = B) = True ==> (B = A) = True"
*)
lemma "!!x. ((A x :: bool) = B x) = False ==> (B x = A x) = False"
apply (tactic {*expander_animal @{context} 1*})
oops

lemma "(A & B) ==> ~(~A | ~B)"
by (tactic {*expander_animal @{context} 1*})

lemma "(A | B) ==> ~(~A & ~B)"
by (tactic {*expander_animal @{context} 1*})

lemma "(A | B) | C ==> A | (B | C)"
by (tactic {*expander_animal @{context} 1*})

lemma "(~~A) = B ==> A = B"
by (tactic {*expander_animal @{context} 1*})

lemma "~ ~ (A = True) ==> A = True"
by (tactic {*expander_animal @{context} 1*})

(*This might not be a goal which might realistically arise:
lemma "((~~A) = B) & (B = (~~A)) ==> ~(~(A = B) | ~(B = A))" *)
lemma "((~~A) = True) ==> ~(~(A = True) | ~(True = A))"
apply (tactic {*expander_animal @{context} 1*})+
apply (rule conjI)
apply assumption
apply (rule sym, assumption)
done

lemma "A = B ==> ((~~A) = B) & (B = (~~A)) ==> ~(~(A = B) | ~(B = A))"
by (tactic {*expander_animal @{context} 1*})+

(*some lemmas assume constants in the signature of PUZ114^5*)
consts
  PUZ114_5_bnd_sK1 :: "TPTP_Interpret.ind"
  PUZ114_5_bnd_sK2 :: "TPTP_Interpret.ind"
  PUZ114_5_bnd_sK3 :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  PUZ114_5_bnd_sK4 :: "(TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool) \<Rightarrow> TPTP_Interpret.ind"
  PUZ114_5_bnd_sK5 :: "(TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool) \<Rightarrow> TPTP_Interpret.ind"
  PUZ114_5_bnd_s :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"
  PUZ114_5_bnd_c1 :: TPTP_Interpret.ind

(*testing logical expansion*)
lemma "!! SY30. (SY30 PUZ114_5_bnd_c1 PUZ114_5_bnd_c1 \<and>
       (\<forall>Xj Xk.
           SY30 Xj Xk \<longrightarrow>
           SY30 (PUZ114_5_bnd_s (PUZ114_5_bnd_s Xj)) Xk \<and>
           SY30 (PUZ114_5_bnd_s Xj) (PUZ114_5_bnd_s Xk)) \<longrightarrow>
       SY30 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2)
==> (
       (~ SY30 PUZ114_5_bnd_c1 PUZ114_5_bnd_c1)
     | (~ (\<forall>Xj Xk.
           SY30 Xj Xk \<longrightarrow>
           SY30 (PUZ114_5_bnd_s (PUZ114_5_bnd_s Xj)) Xk \<and>
           SY30 (PUZ114_5_bnd_s Xj) (PUZ114_5_bnd_s Xk)))
     | SY30 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2
)"
by (tactic {*expander_animal @{context} 1*})+

(*
extcnf_forall_pos:

     (! X. L1) | ... | Ln
 ----------------------------   X' fresh
  ! X'. (L1[X'/X] | ... | Ln)

After elimination rule has been applied we'll have a subgoal which looks like this:
            (! X. L1)
 ----------------------------   X' fresh
  ! X'. (L1[X'/X] | ... | Ln)
and we need to transform it so that, in Isabelle, we go from
 (! X. L1) ==> ! X'. (L1[X'/X] | ... | Ln)
to
 \<And> X'. L1[X'/X] ==> (L1[X'/X] | ... | Ln)
(where X' is fresh, or renamings are done suitably).*)

lemma "A | B \<Longrightarrow> A | B | C"
apply (tactic {*flip_conclusion_tac @{context} 1*})+
apply (tactic {*break_hypotheses 1*})+
oops

consts
  CSR122_1_bnd_lBill_THFTYPE_i :: TPTP_Interpret.ind
  CSR122_1_bnd_lMary_THFTYPE_i :: TPTP_Interpret.ind
  CSR122_1_bnd_lSue_THFTYPE_i :: TPTP_Interpret.ind
  CSR122_1_bnd_n2009_THFTYPE_i :: TPTP_Interpret.ind
  CSR122_1_bnd_lYearFn_THFTYPE_IiiI :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"
  CSR122_1_bnd_holdsDuring_THFTYPE_IiooI ::
    "TPTP_Interpret.ind \<Rightarrow> bool \<Rightarrow> bool"
  CSR122_1_bnd_likes_THFTYPE_IiioI ::
    "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"

lemma "\<forall>SV2. (CSR122_1_bnd_holdsDuring_THFTYPE_IiooI
                 (CSR122_1_bnd_lYearFn_THFTYPE_IiiI CSR122_1_bnd_n2009_THFTYPE_i)
                 (\<not> (\<not> CSR122_1_bnd_likes_THFTYPE_IiioI
                        CSR122_1_bnd_lMary_THFTYPE_i
                        CSR122_1_bnd_lBill_THFTYPE_i \<or>
                     \<not> CSR122_1_bnd_likes_THFTYPE_IiioI
                        CSR122_1_bnd_lSue_THFTYPE_i
                        CSR122_1_bnd_lBill_THFTYPE_i)) =
                CSR122_1_bnd_holdsDuring_THFTYPE_IiooI SV2 True) =
               False \<Longrightarrow>
         \<forall>SV2. (CSR122_1_bnd_lYearFn_THFTYPE_IiiI CSR122_1_bnd_n2009_THFTYPE_i =
                SV2) =
               False \<or>
               ((\<not> (\<not> CSR122_1_bnd_likes_THFTYPE_IiioI
                       CSR122_1_bnd_lMary_THFTYPE_i CSR122_1_bnd_lBill_THFTYPE_i \<or>
                    \<not> CSR122_1_bnd_likes_THFTYPE_IiioI CSR122_1_bnd_lSue_THFTYPE_i
                       CSR122_1_bnd_lBill_THFTYPE_i)) =
                True) =
               False"
apply (rule allI, erule_tac x = "SV2" in allE)
apply (tactic {*extuni_dec_tac @{context} 1*})
done

(*SEU882^5*)
(*
lemma
 "\<forall>(SV2\<Colon>TPTP_Interpret.ind)
        SV1\<Colon>TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind.
        (SV1 SV2 = bnd_sK1_Xy) =
        False
   \<Longrightarrow>
   \<forall>SV2\<Colon>TPTP_Interpret.ind.
            (bnd_sK1_Xy = bnd_sK1_Xy) =
            False"
ML_prf {*
open TPTP_Syntax;
open TPTP_Proof;

val binds =
[Bind ("SV1", Quant (Lambda, [("SX0", SOME (Fmla_type (Atom (THF_Atom_term (Term_Func (TypeSymbol Type_Ind, []))))))], Atom (THF_Atom_term (Term_Func (Uninterpreted "sK1_Xy", [])))))]

val tec = bind_tac @{context} (hd prob_names) binds
*}
(*
apply (tactic {*strip_qtfrs
                (* THEN tec *)*})
*)
apply (tactic {*tec*})
done
*)

lemma "A | B \<Longrightarrow> C1 | A | C2 | B | C3"
apply (erule disjE)
apply (tactic {*clause_breaker 1*})
apply (tactic {*clause_breaker 1*})
done

lemma "A \<Longrightarrow> A"
apply (tactic {*clause_breaker 1*})
done

typedecl NUM667_1_bnd_nat
consts
  NUM667_1_bnd_less :: "NUM667_1_bnd_nat \<Rightarrow> NUM667_1_bnd_nat \<Rightarrow> bool"
  NUM667_1_bnd_x :: NUM667_1_bnd_nat
  NUM667_1_bnd_y :: NUM667_1_bnd_nat

(*NUM667^1 node 302 -- dec*)
lemma "\<forall>SV12 SV13 SV14 SV9 SV10 SV11.
       ((((NUM667_1_bnd_less SV12 SV13 = NUM667_1_bnd_less SV11 SV10) = False \<or>
          (SV14 = SV13) = False) \<or>
         NUM667_1_bnd_less SV12 SV14 = False) \<or>
        NUM667_1_bnd_less SV9 SV10 = True) \<or>
       (SV9 = SV11) =
       False \<Longrightarrow>
       \<forall>SV9 SV14 SV10 SV13 SV11 SV12.
       (((((SV12 = SV11) = False \<or> (SV13 = SV10) = False) \<or>
          (SV14 = SV13) = False) \<or>
         NUM667_1_bnd_less SV12 SV14 = False) \<or>
        NUM667_1_bnd_less SV9 SV10 = True) \<or>
       (SV9 = SV11) =
       False"
apply (tactic {*strip_qtfrs_tac @{context}*})
apply (tactic {*break_hypotheses 1*})
apply (tactic {*ALLGOALS (TRY o clause_breaker)*})
apply (tactic {*extuni_dec_tac @{context} 1*})
done

ML {*
extuni_dec_n @{context} 2;
*}

(*NUM667^1, node 202*)
lemma "\<forall>SV9 SV10 SV11.
       ((((SV9 = SV11) = (NUM667_1_bnd_x = NUM667_1_bnd_y)) = False \<or>
         NUM667_1_bnd_less SV11 SV10 = False) \<or>
        NUM667_1_bnd_less SV9 SV10 = True) \<or>
       NUM667_1_bnd_less NUM667_1_bnd_x NUM667_1_bnd_y =
       True \<Longrightarrow>
       \<forall>SV10 SV9 SV11.
       ((((SV11 = NUM667_1_bnd_x) = False \<or> (SV9 = NUM667_1_bnd_y) = False) \<or>
         NUM667_1_bnd_less SV11 SV10 = False) \<or>
        NUM667_1_bnd_less SV9 SV10 = True) \<or>
       NUM667_1_bnd_less NUM667_1_bnd_x NUM667_1_bnd_y =
       True"
apply (tactic {*strip_qtfrs_tac @{context}*})
apply (tactic {*break_hypotheses 1*})
apply (tactic {*ALLGOALS (TRY o clause_breaker)*})
apply (tactic {*extuni_dec_tac @{context} 1*})
done

(*NUM667^1 node 141*)
(*
lemma "((bnd_x = bnd_x) = False \<or> (bnd_y = bnd_z) = False) \<or>
         bnd_less bnd_x bnd_y = True \<Longrightarrow>
         (bnd_y = bnd_z) = False \<or> bnd_less bnd_x bnd_y = True"
apply (tactic {*strip_qtfrs*})
apply (tactic {*break_hypotheses 1*})
apply (tactic {*ALLGOALS (TRY o clause_breaker)*})
apply (erule extuni_triv)
done
*)

ML {*
fun full_extcnf_combined_tac ctxt =
  extcnf_combined_tac ctxt NONE
   [ConstsDiff,
    StripQuantifiers,
    Flip_Conclusion,
    Loop [
     Close_Branch,
     ConjI,
     King_Cong,
     Break_Hypotheses,
     Existential_Free,
     Existential_Var,
     Universal,
     RemoveRedundantQuantifications],
    CleanUp [RemoveHypothesesFromSkolemDefs, RemoveDuplicates],
    AbsorbSkolemDefs]
   []
*}

ML {*
fun nonfull_extcnf_combined_tac ctxt feats =
  extcnf_combined_tac ctxt NONE
   [ConstsDiff,
    StripQuantifiers,
    InnerLoopOnce (Break_Hypotheses :: feats),
    AbsorbSkolemDefs]
   []
*}

consts SEU882_5_bnd_sK1_Xy :: TPTP_Interpret.ind
lemma
  "\<forall>SV2. (SEU882_5_bnd_sK1_Xy = SEU882_5_bnd_sK1_Xy) = False \<Longrightarrow>
   (SEU882_5_bnd_sK1_Xy = SEU882_5_bnd_sK1_Xy) = False"
(* apply (erule_tac x = "(@X. False)" in allE) *)
(* apply (tactic {*remove_redundant_quantification 1*}) *)
(* apply assumption *)
by (tactic {*nonfull_extcnf_combined_tac @{context} [RemoveRedundantQuantifications, Extuni_FlexRigid]*})

(*NUM667^1*)
(*
     (* (Annotated_step ("153", "extuni_triv"), *)
lemma "((bnd_y = bnd_x) = False \<or> (bnd_z = bnd_z) = False) \<or>
         (bnd_y = bnd_z) = True \<Longrightarrow>
         (bnd_y = bnd_x) = False \<or> (bnd_y = bnd_z) = True"
apply (tactic {*nonfull_extcnf_combined_tac [Extuni_Triv]*})
done
     (* (Annotated_step ("162", "extuni_triv"), *)
lemma "((bnd_y = bnd_x) = False \<or> (bnd_z = bnd_z) = False) \<or>
         bnd_less bnd_y bnd_z = True \<Longrightarrow>
         (bnd_y = bnd_x) = False \<or> bnd_less bnd_y bnd_z = True"
apply (tactic {*nonfull_extcnf_combined_tac [Extuni_Triv]*})
done
*)

(* SEU602^2 *)
consts
  SEU602_2_bnd_sK7_E :: "(TPTP_Interpret.ind \<Rightarrow> bool) \<Rightarrow> TPTP_Interpret.ind"
  SEU602_2_bnd_sK2_SY17 :: TPTP_Interpret.ind
  SEU602_2_bnd_in :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"

     (* (Annotated_step ("113", "extuni_func"), *)
lemma "\<forall>SV49\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
            (SV49 =
             (\<lambda>SY23\<Colon>TPTP_Interpret.ind.
                 \<not> SEU602_2_bnd_in SY23 SEU602_2_bnd_sK2_SY17)) =
            False \<Longrightarrow>
         \<forall>SV49\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
            (SV49 (SEU602_2_bnd_sK7_E SV49) =
             (\<not> SEU602_2_bnd_in (SEU602_2_bnd_sK7_E SV49) SEU602_2_bnd_sK2_SY17)) =
            False"
(*FIXME this (and similar) tests are getting the "Bad background theory of goal state" error since upgrading to Isabelle2013-2.*)
by (tactic {*fn thm =>
  let
    val ctxt =
      theory_of_thm thm
      |> Context.Theory
      |> Context.proof_of
  in nonfull_extcnf_combined_tac ctxt [Extuni_Func, Existential_Var] thm
  end*})
(*by (tactic {*nonfull_extcnf_combined_tac @{context} [Extuni_Func, Existential_Var]*})*)
oops

consts
  SEV405_5_bnd_sK1_SY2 :: "(TPTP_Interpret.ind \<Rightarrow> bool) \<Rightarrow> TPTP_Interpret.ind"
  SEV405_5_bnd_cA :: bool

lemma "\<forall>SV1\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
            (\<forall>SY2\<Colon>TPTP_Interpret.ind.
                \<not> (\<not> (\<not> SV1 SY2 \<or> SEV405_5_bnd_cA) \<or>
                   \<not> (\<not> SEV405_5_bnd_cA \<or> SV1 SY2))) =
            False \<Longrightarrow>
         \<forall>SV1\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
            (\<not> (\<not> (\<not> SV1 (SEV405_5_bnd_sK1_SY2 SV1) \<or> SEV405_5_bnd_cA) \<or>
                \<not> (\<not> SEV405_5_bnd_cA \<or> SV1 (SEV405_5_bnd_sK1_SY2 SV1)))) =
            False"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Existential_Var]*})
(*
strip quantifiers -- creating a space of permutations; from shallowest to deepest (iterative deepening)
flip the conclusion -- giving us branch
apply some collection of rules, in some order, until the space has been explored completely. advantage of not having extcnf_combined: search space is shallow -- particularly if the collection of rules is small.
*)

consts
  SEU581_2_bnd_sK1 :: "TPTP_Interpret.ind"
  SEU581_2_bnd_sK2 :: "TPTP_Interpret.ind \<Rightarrow> bool"
  SEU581_2_bnd_subset :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> HOL.bool"
  SEU581_2_bnd_dsetconstr ::  "TPTP_Interpret.ind \<Rightarrow> (TPTP_Interpret.ind \<Rightarrow> HOL.bool) \<Rightarrow> TPTP_Interpret.ind"

(*testing parameters*)
lemma "! X :: TPTP_Interpret.ind . (\<forall>A B. SEU581_2_bnd_in B (SEU581_2_bnd_powerset A) \<longrightarrow> SEU581_2_bnd_subset B A) = True
\<Longrightarrow> ! X :: TPTP_Interpret.ind . (\<forall>A B. \<not> SEU581_2_bnd_in B (SEU581_2_bnd_powerset A) \<or> SEU581_2_bnd_subset B A) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "(A & B) = True ==> (A | B) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "(\<not> bnd_subset (bnd_dsetconstr bnd_sK1 bnd_sK2) bnd_sK1) = True \<Longrightarrow> (bnd_subset (bnd_dsetconstr bnd_sK1 bnd_sK2) bnd_sK1) = False"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing goals with parameters*)
lemma "(\<not> bnd_subset (bnd_dsetconstr bnd_sK1 bnd_sK2) bnd_sK1) = True \<Longrightarrow> ! X. (bnd_subset (bnd_dsetconstr bnd_sK1 bnd_sK2) bnd_sK1) = False"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "(A & B) = True ==> (B & A) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*appreciating differences between THEN, REPEAT, and APPEND*)
lemma "A & B ==> B & A"
apply (tactic {*
  TRY (etac @{thm conjE} 1)
  THEN TRY (rtac @{thm conjI} 1)*})
by assumption+

lemma "A & B ==> B & A"
by (tactic {*
  etac @{thm conjE} 1
  THEN rtac @{thm conjI} 1
  THEN REPEAT (atac 1)*})

lemma "A & B ==> B & A"
apply (tactic {*
  rtac @{thm conjI} 1
  APPEND etac @{thm conjE} 1*})+
back
by assumption+

consts
  SEU581_2_bnd_sK3 :: "TPTP_Interpret.ind"
  SEU581_2_bnd_sK4 :: "TPTP_Interpret.ind"
  SEU581_2_bnd_sK5 :: "(TPTP_Interpret.ind \<Rightarrow> bool) \<Rightarrow> TPTP_Interpret.ind"
  SEU581_2_bnd_powerset :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"
  SEU581_2_bnd_in :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"

consts
  bnd_c1 :: TPTP_Interpret.ind
  bnd_s :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"

lemma "(\<forall>SX0. (\<not> (\<not> SX0 (PUZ114_5_bnd_sK4 SX0) (PUZ114_5_bnd_sK5 SX0) \<or>
              \<not> (\<not> SX0 (bnd_s (bnd_s (PUZ114_5_bnd_sK4 SX0)))
                    (PUZ114_5_bnd_sK5 SX0) \<or>
                 \<not> SX0 (bnd_s (PUZ114_5_bnd_sK4 SX0))
                    (bnd_s (PUZ114_5_bnd_sK5 SX0)))) \<or>
           \<not> SX0 bnd_c1 bnd_c1) \<or>
          SX0 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2) =
   True ==> \<forall>SV1. ((\<not> (\<not> SV1 (PUZ114_5_bnd_sK4 SV1) (PUZ114_5_bnd_sK5 SV1) \<or>
              \<not> (\<not> SV1 (bnd_s (bnd_s (PUZ114_5_bnd_sK4 SV1)))
                    (PUZ114_5_bnd_sK5 SV1) \<or>
                 \<not> SV1 (bnd_s (PUZ114_5_bnd_sK4 SV1))
                    (bnd_s (PUZ114_5_bnd_sK5 SV1)))) \<or>
           \<not> SV1 bnd_c1 bnd_c1) \<or>
          SV1 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2) =
         True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "(\<not> SEU581_2_bnd_subset (SEU581_2_bnd_dsetconstr SEU581_2_bnd_sK1 SEU581_2_bnd_sK2) SEU581_2_bnd_sK1) = True \<Longrightarrow> (SEU581_2_bnd_subset (SEU581_2_bnd_dsetconstr SEU581_2_bnd_sK1 SEU581_2_bnd_sK2) SEU581_2_bnd_sK1) = False"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing repeated application of simulator*)
lemma "(\<not> \<not> False) = True \<Longrightarrow>
    SEU581_2_bnd_subset (SEU581_2_bnd_dsetconstr SEU581_2_bnd_sK1 SEU581_2_bnd_sK2) SEU581_2_bnd_sK1 = True \<or>
    False = True \<or> False = True \<or> False = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*Testing non-normal conclusion. Ideally we should be able to apply
  the tactic to arbitrary chains of extcnf steps -- where it's not
  generally the case that the conclusions are normal.*)
lemma "(\<not> \<not> False) = True \<Longrightarrow>
    SEU581_2_bnd_subset (SEU581_2_bnd_dsetconstr SEU581_2_bnd_sK1 SEU581_2_bnd_sK2) SEU581_2_bnd_sK1 = True \<or>
    (\<not> False) = False"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing repeated application of simulator, involving different extcnf rules*)
lemma "(\<not> \<not> (False | False)) = True \<Longrightarrow>
    SEU581_2_bnd_subset (SEU581_2_bnd_dsetconstr SEU581_2_bnd_sK1 SEU581_2_bnd_sK2) SEU581_2_bnd_sK1 = True \<or>
    False = True \<or> False = True \<or> False = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing logical expansion*)
lemma "(\<forall>A B. SEU581_2_bnd_in B (SEU581_2_bnd_powerset A) \<longrightarrow> SEU581_2_bnd_subset B A) = True
\<Longrightarrow> (\<forall>A B. \<not> SEU581_2_bnd_in B (SEU581_2_bnd_powerset A) \<or> SEU581_2_bnd_subset B A) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing extcnf_forall_pos*)
lemma "(\<forall>A Xphi. SEU581_2_bnd_in (SEU581_2_bnd_dsetconstr A Xphi) (SEU581_2_bnd_powerset A)) = True \<Longrightarrow> \<forall>SV1. (\<forall>SY14.
             SEU581_2_bnd_in (SEU581_2_bnd_dsetconstr SV1 SY14)
              (SEU581_2_bnd_powerset SV1)) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "((\<forall>A Xphi. SEU581_2_bnd_in (SEU581_2_bnd_dsetconstr A Xphi) (SEU581_2_bnd_powerset A)) = True) | ((~ False) = False) \<Longrightarrow>
\<forall>SV1. ((\<forall>SY14. SEU581_2_bnd_in (SEU581_2_bnd_dsetconstr SV1 SY14) (SEU581_2_bnd_powerset SV1)) = True) | ((~ False) = False)"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing parameters*)
lemma "(\<forall>A B. SEU581_2_bnd_in B (SEU581_2_bnd_powerset A) \<longrightarrow> SEU581_2_bnd_subset B A) = True
\<Longrightarrow> ! X. (\<forall>A B. \<not> SEU581_2_bnd_in B (SEU581_2_bnd_powerset A) \<or> SEU581_2_bnd_subset B A) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "((? A .P1 A) = False) | P2 = True \<Longrightarrow> !X. ((P1 X) = False | P2 = True)"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "((!A . (P1a A | P1b A)) = True) | (P2 = True) \<Longrightarrow> !X. (P1a X = True | P1b X = True | P2 = True)"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "! Y. (((!A .(P1a A | P1b A)) = True) | P2 = True) \<Longrightarrow> ! Y. (!X. (P1a X = True | P1b X = True | P2 = True))"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "! Y. (((!A .(P1a A | P1b A)) = True) | P2 = True) \<Longrightarrow> ! Y. (!X. (P1a X = True | P1b X = True | P2 = True))"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "! Y. (((!A .(P1a A | P1b A)) = True) | P2 = True) \<Longrightarrow> ! Y. (!X. (P1a X = True | P1b X = True | P2 = True))"
by (tactic {*full_extcnf_combined_tac @{context}*})

consts dud_bnd_s :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"

(*this lemma kills blast*)
lemma "(\<not> (\<forall>SX0 SX1.
          \<not> PUZ114_5_bnd_sK3 SX0 SX1 \<or> PUZ114_5_bnd_sK3 (dud_bnd_s (dud_bnd_s SX0)) SX1) \<or>
    \<not> (\<forall>SX0 SX1.
          \<not> PUZ114_5_bnd_sK3 SX0 SX1 \<or>
          PUZ114_5_bnd_sK3 (dud_bnd_s SX0) (dud_bnd_s SX1))) =
   False \<Longrightarrow> (\<not> (\<forall>SX0 SX1.
          \<not> PUZ114_5_bnd_sK3 SX0 SX1 \<or>
          PUZ114_5_bnd_sK3 (dud_bnd_s SX0) (dud_bnd_s SX1))) =
   False"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing logical expansion -- this should be done by blast*)
lemma "(\<forall>A B. bnd_in B (bnd_powerset A) \<longrightarrow> SEU581_2_bnd_subset B A) = True
\<Longrightarrow> (\<forall>A B. \<not> bnd_in B (bnd_powerset A) \<or> SEU581_2_bnd_subset B A) = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

(*testing related to PUZ114^5.p.out*)
lemma "\<forall>SV1. ((\<not> (\<not> SV1 (PUZ114_5_bnd_sK4 SV1) (PUZ114_5_bnd_sK5 SV1) \<or>
                    \<not> (\<not> SV1 (bnd_s (bnd_s (PUZ114_5_bnd_sK4 SV1)))
                          (PUZ114_5_bnd_sK5 SV1) \<or>
                       \<not> SV1 (bnd_s (PUZ114_5_bnd_sK4 SV1))
                          (bnd_s (PUZ114_5_bnd_sK5 SV1))))) =
                True \<or>
                (\<not> SV1 bnd_c1 bnd_c1) = True) \<or>
               SV1 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2 = True \<Longrightarrow>
         \<forall>SV1. (SV1 bnd_c1 bnd_c1 = False \<or>
                (\<not> (\<not> SV1 (PUZ114_5_bnd_sK4 SV1) (PUZ114_5_bnd_sK5 SV1) \<or>
                    \<not> (\<not> SV1 (bnd_s (bnd_s (PUZ114_5_bnd_sK4 SV1)))
                          (PUZ114_5_bnd_sK5 SV1) \<or>
                       \<not> SV1 (bnd_s (PUZ114_5_bnd_sK4 SV1))
                          (bnd_s (PUZ114_5_bnd_sK5 SV1))))) =
                True) \<or>
               SV1 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2 = True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "\<forall>SV2. (\<forall>SY41.
                   \<not> PUZ114_5_bnd_sK3 SV2 SY41 \<or>
                   PUZ114_5_bnd_sK3 (dud_bnd_s (dud_bnd_s SV2)) SY41) =
               True \<Longrightarrow>
         \<forall>SV4 SV2.
            (\<not> PUZ114_5_bnd_sK3 SV2 SV4 \<or>
             PUZ114_5_bnd_sK3 (dud_bnd_s (dud_bnd_s SV2)) SV4) =
            True"
by (tactic {*full_extcnf_combined_tac @{context}*})

lemma "\<forall>SV3. (\<forall>SY42.
                   \<not> PUZ114_5_bnd_sK3 SV3 SY42 \<or>
                   PUZ114_5_bnd_sK3 (dud_bnd_s SV3) (dud_bnd_s SY42)) =
               True \<Longrightarrow>
         \<forall>SV5 SV3.
            (\<not> PUZ114_5_bnd_sK3 SV3 SV5 \<or>
             PUZ114_5_bnd_sK3 (dud_bnd_s SV3) (dud_bnd_s SV5)) =
            True"
by (tactic {*full_extcnf_combined_tac @{context}*})


subsection "unfold_def"
     (* (Annotated_step ("9", "unfold_def"), *)
lemma "bnd_kpairiskpair =
             (ALL Xx Xy.
                 bnd_iskpair
                  (bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                    (bnd_setadjoin (bnd_setadjoin Xx (bnd_setadjoin Xy bnd_emptyset))
                      bnd_emptyset))) &
             bnd_kpair =
             (%Xx Xy.
                 bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                  (bnd_setadjoin (bnd_setadjoin Xx (bnd_setadjoin Xy bnd_emptyset))
                    bnd_emptyset)) &
             bnd_iskpair =
             (%A. EX Xx. bnd_in Xx (bnd_setunion A) &
                         (EX Xy. bnd_in Xy (bnd_setunion A) &
                                 A = bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                                      (bnd_setadjoin
                                        (bnd_setadjoin Xx
(bnd_setadjoin Xy bnd_emptyset))
                                        bnd_emptyset))) &
             (~ (ALL SY0 SY1.
                    EX SY3.
                       bnd_in SY3
                        (bnd_setunion
                          (bnd_setadjoin (bnd_setadjoin SY0 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY0 (bnd_setadjoin SY1 bnd_emptyset))
                              bnd_emptyset))) &
                       (EX SY4.
                           bnd_in SY4
                            (bnd_setunion
                              (bnd_setadjoin (bnd_setadjoin SY0 bnd_emptyset)
                                (bnd_setadjoin
                                  (bnd_setadjoin SY0
                                    (bnd_setadjoin SY1 bnd_emptyset))
                                  bnd_emptyset))) &
                           bnd_setadjoin (bnd_setadjoin SY0 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY0 (bnd_setadjoin SY1 bnd_emptyset))
                              bnd_emptyset) =
                           bnd_setadjoin (bnd_setadjoin SY3 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY3 (bnd_setadjoin SY4 bnd_emptyset))
                              bnd_emptyset)))) =
             True
             ==> (~ (ALL SX0 SX1.
                        ~ (ALL SX2.
                              ~ ~ (~ bnd_in SX2
                                      (bnd_setunion
                                        (bnd_setadjoin
(bnd_setadjoin SX0 bnd_emptyset)
(bnd_setadjoin (bnd_setadjoin SX0 (bnd_setadjoin SX1 bnd_emptyset)) bnd_emptyset))) |
                                   ~ ~ (ALL SX3.
 ~ ~ (~ bnd_in SX3
         (bnd_setunion
           (bnd_setadjoin (bnd_setadjoin SX0 bnd_emptyset)
             (bnd_setadjoin (bnd_setadjoin SX0 (bnd_setadjoin SX1 bnd_emptyset))
               bnd_emptyset))) |
      bnd_setadjoin (bnd_setadjoin SX0 bnd_emptyset)
       (bnd_setadjoin (bnd_setadjoin SX0 (bnd_setadjoin SX1 bnd_emptyset))
         bnd_emptyset) ~=
      bnd_setadjoin (bnd_setadjoin SX2 bnd_emptyset)
       (bnd_setadjoin (bnd_setadjoin SX2 (bnd_setadjoin SX3 bnd_emptyset))
         bnd_emptyset))))))) =
                 True"
by (tactic {*unfold_def_tac @{context} []*})

     (* (Annotated_step ("10", "unfold_def"), *)
lemma "bnd_kpairiskpair =
             (ALL Xx Xy.
                 bnd_iskpair
                  (bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                    (bnd_setadjoin (bnd_setadjoin Xx (bnd_setadjoin Xy bnd_emptyset))
                      bnd_emptyset))) &
             bnd_kpair =
             (%Xx Xy.
                 bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                  (bnd_setadjoin (bnd_setadjoin Xx (bnd_setadjoin Xy bnd_emptyset))
                    bnd_emptyset)) &
             bnd_iskpair =
             (%A. EX Xx. bnd_in Xx (bnd_setunion A) &
                         (EX Xy. bnd_in Xy (bnd_setunion A) &
                                 A = bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                                      (bnd_setadjoin
                                        (bnd_setadjoin Xx
(bnd_setadjoin Xy bnd_emptyset))
                                        bnd_emptyset))) &
             (ALL SY5 SY6.
                 EX SY7.
                    bnd_in SY7
                     (bnd_setunion
                       (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                         (bnd_setadjoin
                           (bnd_setadjoin SY5 (bnd_setadjoin SY6 bnd_emptyset))
                           bnd_emptyset))) &
                    (EX SY8.
                        bnd_in SY8
                         (bnd_setunion
                           (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                             (bnd_setadjoin
                               (bnd_setadjoin SY5 (bnd_setadjoin SY6 bnd_emptyset))
                               bnd_emptyset))) &
                        bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                         (bnd_setadjoin
                           (bnd_setadjoin SY5 (bnd_setadjoin SY6 bnd_emptyset))
                           bnd_emptyset) =
                        bnd_setadjoin (bnd_setadjoin SY7 bnd_emptyset)
                         (bnd_setadjoin
                           (bnd_setadjoin SY7 (bnd_setadjoin SY8 bnd_emptyset))
                           bnd_emptyset))) =
             True
             ==> (ALL SX0 SX1.
                     ~ (ALL SX2.
                           ~ ~ (~ bnd_in SX2
                                   (bnd_setunion
                                     (bnd_setadjoin (bnd_setadjoin SX0 bnd_emptyset)
                                       (bnd_setadjoin
                                         (bnd_setadjoin SX0
 (bnd_setadjoin SX1 bnd_emptyset))
                                         bnd_emptyset))) |
                                ~ ~ (ALL SX3.
                                        ~ ~ (~ bnd_in SX3
      (bnd_setunion
        (bnd_setadjoin (bnd_setadjoin SX0 bnd_emptyset)
          (bnd_setadjoin (bnd_setadjoin SX0 (bnd_setadjoin SX1 bnd_emptyset))
            bnd_emptyset))) |
   bnd_setadjoin (bnd_setadjoin SX0 bnd_emptyset)
    (bnd_setadjoin (bnd_setadjoin SX0 (bnd_setadjoin SX1 bnd_emptyset))
      bnd_emptyset) ~=
   bnd_setadjoin (bnd_setadjoin SX2 bnd_emptyset)
    (bnd_setadjoin (bnd_setadjoin SX2 (bnd_setadjoin SX3 bnd_emptyset))
      bnd_emptyset)))))) =
                 True"
by (tactic {*unfold_def_tac @{context} []*})

     (* (Annotated_step ("12", "unfold_def"), *)
lemma "bnd_cCKB6_BLACK =
         (\<lambda>Xu Xv.
             \<forall>Xw. Xw bnd_c1 bnd_c1 \<and>
                  (\<forall>Xj Xk.
                      Xw Xj Xk \<longrightarrow>
                      Xw (bnd_s (bnd_s Xj)) Xk \<and>
                      Xw (bnd_s Xj) (bnd_s Xk)) \<longrightarrow>
                  Xw Xu Xv) \<and>
         ((((\<forall>SY36 SY37.
                \<not> PUZ114_5_bnd_sK3 SY36 SY37 \<or>
                PUZ114_5_bnd_sK3 (bnd_s (bnd_s SY36)) SY37) \<and>
            (\<forall>SY38 SY39.
                \<not> PUZ114_5_bnd_sK3 SY38 SY39 \<or>
                PUZ114_5_bnd_sK3 (bnd_s SY38) (bnd_s SY39))) \<and>
           PUZ114_5_bnd_sK3 bnd_c1 bnd_c1) \<and>
          \<not> PUZ114_5_bnd_sK3 (bnd_s (bnd_s (bnd_s PUZ114_5_bnd_sK1)))
             (bnd_s PUZ114_5_bnd_sK2)) =
         True \<Longrightarrow>
         (\<not> (\<not> \<not> (\<not> \<not> (\<not> (\<forall>SX0 SX1.
                             \<not> PUZ114_5_bnd_sK3 SX0 SX1 \<or>
                             PUZ114_5_bnd_sK3 (bnd_s (bnd_s SX0)) SX1) \<or>
                       \<not> (\<forall>SX0 SX1.
                             \<not> PUZ114_5_bnd_sK3 SX0 SX1 \<or>
                             PUZ114_5_bnd_sK3 (bnd_s SX0) (bnd_s SX1))) \<or>
                  \<not> PUZ114_5_bnd_sK3 bnd_c1 bnd_c1) \<or>
             \<not> \<not> PUZ114_5_bnd_sK3 (bnd_s (bnd_s (bnd_s PUZ114_5_bnd_sK1)))
                  (bnd_s PUZ114_5_bnd_sK2))) =
         True"
(*
apply (erule conjE)+
apply (erule subst)+
apply (tactic {*log_expander 1*})+
apply (rule refl)
*)
by (tactic {*unfold_def_tac @{context} []*})

     (* (Annotated_step ("13", "unfold_def"), *)
lemma "bnd_cCKB6_BLACK =
         (\<lambda>Xu Xv.
             \<forall>Xw. Xw bnd_c1 bnd_c1 \<and>
                  (\<forall>Xj Xk.
                      Xw Xj Xk \<longrightarrow>
                      Xw (bnd_s (bnd_s Xj)) Xk \<and>
                      Xw (bnd_s Xj) (bnd_s Xk)) \<longrightarrow>
                  Xw Xu Xv) \<and>
         (\<forall>SY30.
             (SY30 (PUZ114_5_bnd_sK4 SY30) (PUZ114_5_bnd_sK5 SY30) \<and>
              (\<not> SY30 (bnd_s (bnd_s (PUZ114_5_bnd_sK4 SY30)))
                  (PUZ114_5_bnd_sK5 SY30) \<or>
               \<not> SY30 (bnd_s (PUZ114_5_bnd_sK4 SY30))
                  (bnd_s (PUZ114_5_bnd_sK5 SY30))) \<or>
              \<not> SY30 bnd_c1 bnd_c1) \<or>
             SY30 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2) =
         True \<Longrightarrow>
         (\<forall>SX0. (\<not> (\<not> SX0 (PUZ114_5_bnd_sK4 SX0) (PUZ114_5_bnd_sK5 SX0) \<or>
                    \<not> (\<not> SX0 (bnd_s (bnd_s (PUZ114_5_bnd_sK4 SX0)))
                          (PUZ114_5_bnd_sK5 SX0) \<or>
                       \<not> SX0 (bnd_s (PUZ114_5_bnd_sK4 SX0))
                          (bnd_s (PUZ114_5_bnd_sK5 SX0)))) \<or>
                 \<not> SX0 bnd_c1 bnd_c1) \<or>
                SX0 PUZ114_5_bnd_sK1 PUZ114_5_bnd_sK2) =
         True"
(*
apply (erule conjE)+
apply (tactic {*expander_animal 1*})+
apply assumption
*)
by (tactic {*unfold_def_tac @{context} []*})

(*FIXME move this heuristic elsewhere*)
ML {*
(*Other than the list (which must not be empty) this function
  expects a parameter indicating the smallest integer.
  (Using Int.minInt isn't always viable).*)
fun max_int_floored min l =
  if null l then raise List.Empty
  else fold (curry Int.max) l min;

val _ = @{assert} (max_int_floored ~101002 [1]  = 1)
val _ = @{assert} (max_int_floored 0 [1, 3, 5] = 5)

fun max_index_floored min l =
  let
    val max = max_int_floored min l
  in find_index (pair max #> op =) l end
*}

ML {*
max_index_floored 0 [1, 3, 5]
*}

ML {*
(*
Given argument ([h_1, ..., h_n], conc),
obtained from term of form
  h_1 ==> ... ==> h_n ==> conclusion,
this function indicates which h_i is biggest,
or NONE if h_n = 0.
*)
fun biggest_hypothesis (hypos, _) =
  if null hypos then NONE
  else
    map size_of_term hypos
    |> max_index_floored 0
    |> SOME
*}

ML {*
fun biggest_hyp_first_tac i = fn st =>
  let
    val results = TERMFUN biggest_hypothesis (SOME i) st
val _ = tracing ("result=" ^ PolyML.makestring results)
  in
    if null results then no_tac st
    else
      let
        val result = the_single results
      in
        case result of
            NONE => no_tac st
          | SOME n =>
              if n > 0 then rotate_tac n i st else no_tac st
      end
  end
*}

     (* (Annotated_step ("6", "unfold_def"), *)
lemma  "(\<not> (\<exists>U :: TPTP_Interpret.ind \<Rightarrow> bool. \<forall>V. U V = SEV405_5_bnd_cA)) = True \<Longrightarrow>
         (\<not> \<not> (\<forall>SX0 :: TPTP_Interpret.ind \<Rightarrow> bool. \<not> (\<forall>SX1. \<not> (\<not> (\<not> SX0 SX1 \<or> SEV405_5_bnd_cA) \<or>
 \<not> (\<not> SEV405_5_bnd_cA \<or> SX0 SX1))))) =
         True"
(* by (tactic {*unfold_def_tac []*}) *)
oops

subsection "Using leo2_tac"
(*these require PUZ114^5's proof to be loaded

ML {*leo2_tac @{context} (hd prob_names) "50"*}

ML {*leo2_tac @{context} (hd prob_names) "4"*}

ML {*leo2_tac @{context} (hd prob_names) "9"*}

     (* (Annotated_step ("9", "extcnf_combined"), *)
lemma "(\<forall>SY30.
             SY30 bnd_c1 bnd_c1 \<and>
             (\<forall>Xj Xk.
                 SY30 Xj Xk \<longrightarrow>
                 SY30 (bnd_s (bnd_s Xj)) Xk \<and>
                 SY30 (bnd_s Xj) (bnd_s Xk)) \<longrightarrow>
             SY30 bnd_sK1 bnd_sK2) =
         True \<Longrightarrow>
         (\<forall>SY30.
             (SY30 (bnd_sK4 SY30) (bnd_sK5 SY30) \<and>
              (\<not> SY30 (bnd_s (bnd_s (bnd_sK4 SY30)))
                  (bnd_sK5 SY30) \<or>
               \<not> SY30 (bnd_s (bnd_sK4 SY30))
                  (bnd_s (bnd_sK5 SY30))) \<or>
              \<not> SY30 bnd_c1 bnd_c1) \<or>
             SY30 bnd_sK1 bnd_sK2) =
         True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "9") 1*})
*)



typedecl GEG007_1_bnd_reg
consts
  GEG007_1_bnd_sK7_SX2 :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> GEG007_1_bnd_reg"
  GEG007_1_bnd_sK6_SX2 :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> GEG007_1_bnd_reg"
  GEG007_1_bnd_a :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  GEG007_1_bnd_catalunya  :: "GEG007_1_bnd_reg"
  GEG007_1_bnd_spain :: "GEG007_1_bnd_reg"
  GEG007_1_bnd_c :: "GEG007_1_bnd_reg \<Rightarrow> GEG007_1_bnd_reg \<Rightarrow> bool"

     (* (Annotated_step ("147", "extcnf_forall_neg"), *)
lemma "\<forall>SV13 SV6.
            (\<forall>SX2. \<not> GEG007_1_bnd_c SX2 GEG007_1_bnd_spain \<or>
                   GEG007_1_bnd_c SX2 GEG007_1_bnd_catalunya) =
            False \<or>
            GEG007_1_bnd_a SV6 SV13 = False \<Longrightarrow>
         \<forall>SV6 SV13.
            (\<not> GEG007_1_bnd_c (GEG007_1_bnd_sK7_SX2 SV13 SV6) GEG007_1_bnd_spain \<or>
             GEG007_1_bnd_c (GEG007_1_bnd_sK7_SX2 SV13 SV6) GEG007_1_bnd_catalunya) =
            False \<or>
            GEG007_1_bnd_a SV6 SV13 = False"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Existential_Var]*})

     (* (Annotated_step ("116", "extcnf_forall_neg"), *)
lemma "\<forall>SV13 SV6.
            (\<forall>SX2. \<not> \<not> (\<not> \<not> (\<not> GEG007_1_bnd_c SX2 GEG007_1_bnd_catalunya \<or>
                             \<not> \<not> \<not> (\<forall>SX3.
       \<not> \<not> (\<not> (\<forall>SX4. \<not> GEG007_1_bnd_c SX4 SX3 \<or> GEG007_1_bnd_c SX4 SX2) \<or>
            \<not> (\<forall>SX4. \<not> GEG007_1_bnd_c SX4 SX3 \<or>
                     GEG007_1_bnd_c SX4 GEG007_1_bnd_catalunya)))) \<or>
                        \<not> \<not> (\<not> GEG007_1_bnd_c SX2 GEG007_1_bnd_spain \<or>
                             \<not> \<not> \<not> (\<forall>SX3.
       \<not> \<not> (\<not> (\<forall>SX4. \<not> GEG007_1_bnd_c SX4 SX3 \<or> GEG007_1_bnd_c SX4 SX2) \<or>
            \<not> (\<forall>SX4. \<not> GEG007_1_bnd_c SX4 SX3 \<or>
                     GEG007_1_bnd_c SX4 GEG007_1_bnd_spain)))))) =
            False \<or>
            GEG007_1_bnd_a SV6 SV13 = False \<Longrightarrow>
         \<forall>SV6 SV13.
            (\<not> \<not> (\<not> \<not> (\<not> GEG007_1_bnd_c (GEG007_1_bnd_sK6_SX2 SV13 SV6)
                          GEG007_1_bnd_catalunya \<or>
                       \<not> \<not> \<not> (\<forall>SY68.
 \<not> \<not> (\<not> (\<forall>SY69.
            \<not> GEG007_1_bnd_c SY69 SY68 \<or>
            GEG007_1_bnd_c SY69 (GEG007_1_bnd_sK6_SX2 SV13 SV6)) \<or>
      \<not> (\<forall>SX4. \<not> GEG007_1_bnd_c SX4 SY68 \<or> GEG007_1_bnd_c SX4 GEG007_1_bnd_catalunya)))) \<or>
                  \<not> \<not> (\<not> GEG007_1_bnd_c (GEG007_1_bnd_sK6_SX2 SV13 SV6)
                          GEG007_1_bnd_spain \<or>
                       \<not> \<not> \<not> (\<forall>SY71.
 \<not> \<not> (\<not> (\<forall>SY72.
            \<not> GEG007_1_bnd_c SY72 SY71 \<or>
            GEG007_1_bnd_c SY72 (GEG007_1_bnd_sK6_SX2 SV13 SV6)) \<or>
      \<not> (\<forall>SX4. \<not> GEG007_1_bnd_c SX4 SY71 \<or> GEG007_1_bnd_c SX4 GEG007_1_bnd_spain)))))) =
            False \<or>
            GEG007_1_bnd_a SV6 SV13 = False"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Existential_Var]*})

consts PUZ107_5_bnd_sK1_SX0 ::
  "TPTP_Interpret.ind
      \<Rightarrow> TPTP_Interpret.ind
        \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"

lemma "\<forall>(SV4\<Colon>TPTP_Interpret.ind) (SV8\<Colon>TPTP_Interpret.ind)
   (SV6\<Colon>TPTP_Interpret.ind) (SV2\<Colon>TPTP_Interpret.ind)
   (SV3\<Colon>TPTP_Interpret.ind) SV1\<Colon>TPTP_Interpret.ind.
   ((SV1 \<noteq> SV3) = False \<or> PUZ107_5_bnd_sK1_SX0 SV1 SV2 SV6 SV8 = False) \<or>
   PUZ107_5_bnd_sK1_SX0 SV3 SV4 SV6 SV8 = False \<Longrightarrow>
\<forall>(SV4\<Colon>TPTP_Interpret.ind) (SV8\<Colon>TPTP_Interpret.ind)
   (SV6\<Colon>TPTP_Interpret.ind) (SV2\<Colon>TPTP_Interpret.ind)
   (SV3\<Colon>TPTP_Interpret.ind) SV1\<Colon>TPTP_Interpret.ind.
   ((SV1 = SV3) = True \<or> PUZ107_5_bnd_sK1_SX0 SV1 SV2 SV6 SV8 = False) \<or>
   PUZ107_5_bnd_sK1_SX0 SV3 SV4 SV6 SV8 = False"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Not_neg]*})

lemma "
\<forall>(SV8\<Colon>TPTP_Interpret.ind) (SV6\<Colon>TPTP_Interpret.ind)
   (SV4\<Colon>TPTP_Interpret.ind) (SV2\<Colon>TPTP_Interpret.ind)
   (SV3\<Colon>TPTP_Interpret.ind) SV1\<Colon>TPTP_Interpret.ind.
   ((SV1 \<noteq> SV3 \<or> SV2 \<noteq> SV4) = False \<or>
    PUZ107_5_bnd_sK1_SX0 SV1 SV2 SV6 SV8 = False) \<or>
   PUZ107_5_bnd_sK1_SX0 SV3 SV4 SV6 SV8 = False \<Longrightarrow>
\<forall>(SV4\<Colon>TPTP_Interpret.ind) (SV8\<Colon>TPTP_Interpret.ind)
   (SV6\<Colon>TPTP_Interpret.ind) (SV2\<Colon>TPTP_Interpret.ind)
   (SV3\<Colon>TPTP_Interpret.ind) SV1\<Colon>TPTP_Interpret.ind.
   ((SV1 \<noteq> SV3) = False \<or> PUZ107_5_bnd_sK1_SX0 SV1 SV2 SV6 SV8 = False) \<or>
   PUZ107_5_bnd_sK1_SX0 SV3 SV4 SV6 SV8 = False"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Or_neg]*})

consts
  NUM016_5_bnd_a :: TPTP_Interpret.ind
  NUM016_5_bnd_prime :: "TPTP_Interpret.ind \<Rightarrow> bool"
  NUM016_5_bnd_factorial_plus_one :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"
  NUM016_5_bnd_prime_divisor :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"
  NUM016_5_bnd_divides :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  NUM016_5_bnd_less :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"

     (* (Annotated_step ("6", "unfold_def"), *)
lemma "((((((((((((\<forall>X\<Colon>TPTP_Interpret.ind. \<not> NUM016_5_bnd_less X X) \<and>
                    (\<forall>(X\<Colon>TPTP_Interpret.ind)
                        Y\<Colon>TPTP_Interpret.ind.
                        \<not> NUM016_5_bnd_less X Y \<or> \<not> NUM016_5_bnd_less Y X)) \<and>
                   (\<forall>X\<Colon>TPTP_Interpret.ind. NUM016_5_bnd_divides X X)) \<and>
                  (\<forall>(X\<Colon>TPTP_Interpret.ind)
                      (Y\<Colon>TPTP_Interpret.ind)
                      Z\<Colon>TPTP_Interpret.ind.
                      (\<not> NUM016_5_bnd_divides X Y \<or> \<not> NUM016_5_bnd_divides Y Z) \<or>
                      NUM016_5_bnd_divides X Z)) \<and>
                 (\<forall>(X\<Colon>TPTP_Interpret.ind) Y\<Colon>TPTP_Interpret.ind.
                     \<not> NUM016_5_bnd_divides X Y \<or> \<not> NUM016_5_bnd_less Y X)) \<and>
                (\<forall>X\<Colon>TPTP_Interpret.ind.
                    NUM016_5_bnd_less X (NUM016_5_bnd_factorial_plus_one X))) \<and>
               (\<forall>(X\<Colon>TPTP_Interpret.ind) Y\<Colon>TPTP_Interpret.ind.
                   \<not> NUM016_5_bnd_divides X (NUM016_5_bnd_factorial_plus_one Y) \<or>
                   NUM016_5_bnd_less Y X)) \<and>
              (\<forall>X\<Colon>TPTP_Interpret.ind.
                  NUM016_5_bnd_prime X \<or>
                  NUM016_5_bnd_divides (NUM016_5_bnd_prime_divisor X) X)) \<and>
             (\<forall>X\<Colon>TPTP_Interpret.ind.
                 NUM016_5_bnd_prime X \<or>
                 NUM016_5_bnd_prime (NUM016_5_bnd_prime_divisor X))) \<and>
            (\<forall>X\<Colon>TPTP_Interpret.ind.
                NUM016_5_bnd_prime X \<or>
                NUM016_5_bnd_less (NUM016_5_bnd_prime_divisor X) X)) \<and>
           NUM016_5_bnd_prime NUM016_5_bnd_a) \<and>
          (\<forall>X\<Colon>TPTP_Interpret.ind.
              (\<not> NUM016_5_bnd_prime X \<or> \<not> NUM016_5_bnd_less NUM016_5_bnd_a X) \<or>
              NUM016_5_bnd_less (NUM016_5_bnd_factorial_plus_one NUM016_5_bnd_a) X)) =
         True \<Longrightarrow>
         (\<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> \<not> (\<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
     \<not> NUM016_5_bnd_less SX0 SX0) \<or>
                               \<not> (\<forall>(SX0\<Colon>TPTP_Interpret.ind)
     SX1\<Colon>TPTP_Interpret.ind.
     \<not> NUM016_5_bnd_less SX0 SX1 \<or> \<not> NUM016_5_bnd_less SX1 SX0)) \<or>
                          \<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
NUM016_5_bnd_divides SX0 SX0)) \<or>
                     \<not> (\<forall>(SX0\<Colon>TPTP_Interpret.ind)
                           (SX1\<Colon>TPTP_Interpret.ind)
                           SX2\<Colon>TPTP_Interpret.ind.
                           (\<not> NUM016_5_bnd_divides SX0 SX1 \<or>
                            \<not> NUM016_5_bnd_divides SX1 SX2) \<or>
                           NUM016_5_bnd_divides SX0 SX2)) \<or>
                \<not> (\<forall>(SX0\<Colon>TPTP_Interpret.ind)
                      SX1\<Colon>TPTP_Interpret.ind.
                      \<not> NUM016_5_bnd_divides SX0 SX1 \<or>
                      \<not> NUM016_5_bnd_less SX1 SX0)) \<or>
           \<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
                 NUM016_5_bnd_less SX0 (NUM016_5_bnd_factorial_plus_one SX0))) \<or>
      \<not> (\<forall>(SX0\<Colon>TPTP_Interpret.ind) SX1\<Colon>TPTP_Interpret.ind.
            \<not> NUM016_5_bnd_divides SX0 (NUM016_5_bnd_factorial_plus_one SX1) \<or>
            NUM016_5_bnd_less SX1 SX0)) \<or>
 \<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
       NUM016_5_bnd_prime SX0 \<or>
       NUM016_5_bnd_divides (NUM016_5_bnd_prime_divisor SX0) SX0)) \<or>
                            \<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
  NUM016_5_bnd_prime SX0 \<or> NUM016_5_bnd_prime (NUM016_5_bnd_prime_divisor SX0))) \<or>
                       \<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
                             NUM016_5_bnd_prime SX0 \<or>
                             NUM016_5_bnd_less (NUM016_5_bnd_prime_divisor SX0)
                              SX0)) \<or>
                  \<not> NUM016_5_bnd_prime NUM016_5_bnd_a) \<or>
             \<not> (\<forall>SX0\<Colon>TPTP_Interpret.ind.
                   (\<not> NUM016_5_bnd_prime SX0 \<or> \<not> NUM016_5_bnd_less NUM016_5_bnd_a SX0) \<or>
                   NUM016_5_bnd_less (NUM016_5_bnd_factorial_plus_one NUM016_5_bnd_a)
                    SX0))) =
         True"
by (tactic {*unfold_def_tac @{context} []*})

     (* (Annotated_step ("3", "unfold_def"), *)
lemma "(~ ((((((((((((ALL X. ~ bnd_less X X) &
                           (ALL X Y. ~ bnd_less X Y | ~ bnd_less Y X)) &
                          (ALL X. bnd_divides X X)) &
                         (ALL X Y Z.
                             (~ bnd_divides X Y | ~ bnd_divides Y Z) |
                             bnd_divides X Z)) &
                        (ALL X Y. ~ bnd_divides X Y | ~ bnd_less Y X)) &
                       (ALL X. bnd_less X (bnd_factorial_plus_one X))) &
                      (ALL X Y.
                          ~ bnd_divides X (bnd_factorial_plus_one Y) |
                          bnd_less Y X)) &
                     (ALL X. bnd_prime X | bnd_divides (bnd_prime_divisor X) X)) &
                    (ALL X. bnd_prime X | bnd_prime (bnd_prime_divisor X))) &
                   (ALL X. bnd_prime X | bnd_less (bnd_prime_divisor X) X)) &
                  bnd_prime bnd_a) &
                 (ALL X. (~ bnd_prime X | ~ bnd_less bnd_a X) |
                         bnd_less (bnd_factorial_plus_one bnd_a) X))) =
             False
             ==> (~ ((((((((((((ALL X. ~ bnd_less X X) &
                               (ALL X Y. ~ bnd_less X Y | ~ bnd_less Y X)) &
                              (ALL X. bnd_divides X X)) &
                             (ALL X Y Z.
                                 (~ bnd_divides X Y | ~ bnd_divides Y Z) |
                                 bnd_divides X Z)) &
                            (ALL X Y. ~ bnd_divides X Y | ~ bnd_less Y X)) &
                           (ALL X. bnd_less X (bnd_factorial_plus_one X))) &
                          (ALL X Y.
                              ~ bnd_divides X (bnd_factorial_plus_one Y) |
                              bnd_less Y X)) &
                         (ALL X. bnd_prime X |
                                 bnd_divides (bnd_prime_divisor X) X)) &
                        (ALL X. bnd_prime X | bnd_prime (bnd_prime_divisor X))) &
                       (ALL X. bnd_prime X | bnd_less (bnd_prime_divisor X) X)) &
                      bnd_prime bnd_a) &
                     (ALL X. (~ bnd_prime X | ~ bnd_less bnd_a X) |
                             bnd_less (bnd_factorial_plus_one bnd_a) X))) =
                 False"
by (tactic {*unfold_def_tac @{context} []*})

(* SET062^6.p.out
      [[(Annotated_step ("3", "unfold_def"), *)
lemma "(\<forall>Z3. False \<longrightarrow> bnd_cA Z3) = False \<Longrightarrow>
         (\<forall>Z3. False \<longrightarrow> bnd_cA Z3) = False"
by (tactic {*unfold_def_tac @{context} []*})

(*
(* SEU559^2.p.out *)
   (* [[(Annotated_step ("3", "unfold_def"), *)
lemma "bnd_subset = (\<lambda>A B. \<forall>Xx. bnd_in Xx A \<longrightarrow> bnd_in Xx B) \<and>
         (\<forall>A B. (\<forall>Xx. bnd_in Xx A \<longrightarrow> bnd_in Xx B) \<longrightarrow>
                bnd_subset A B) =
         False \<Longrightarrow>
         (\<forall>SY0 SY1.
             (\<forall>Xx. bnd_in Xx SY0 \<longrightarrow> bnd_in Xx SY1) \<longrightarrow>
             (\<forall>SY5. bnd_in SY5 SY0 \<longrightarrow> bnd_in SY5 SY1)) =
         False"
by (tactic {*unfold_def_tac [@{thm bnd_subset_def}]*})

(* SEU559^2.p.out
    [[(Annotated_step ("6", "unfold_def"), *)
lemma "(\<not> (\<exists>Xx. \<forall>Xy. Xx \<longrightarrow> Xy)) = True \<Longrightarrow>
         (\<not> \<not> (\<forall>SX0. \<not> (\<forall>SX1. \<not> SX0 \<or> SX1))) = True"
by (tactic {*unfold_def_tac []*})

(* SEU502^2.p.out
    [[(Annotated_step ("3", "unfold_def"), *)
lemma "bnd_emptysetE =
         (\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) \<and>
         (bnd_emptysetE \<longrightarrow>
          (\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> False)) =
         False \<Longrightarrow>
         ((\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) \<longrightarrow>
          (\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> False)) =
         False"
by (tactic {*unfold_def_tac [@{thm bnd_emptysetE_def}]*})
*)

typedecl AGT037_2_bnd_mu
consts
  AGT037_2_bnd_sK1_SX0 :: TPTP_Interpret.ind
  AGT037_2_bnd_cola :: AGT037_2_bnd_mu
  AGT037_2_bnd_jan :: AGT037_2_bnd_mu
  AGT037_2_bnd_possibly_likes :: "AGT037_2_bnd_mu \<Rightarrow> AGT037_2_bnd_mu \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  AGT037_2_bnd_sK5_SY68 ::
    "TPTP_Interpret.ind
     \<Rightarrow> AGT037_2_bnd_mu
       \<Rightarrow> AGT037_2_bnd_mu
         \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind"
  AGT037_2_bnd_likes :: "AGT037_2_bnd_mu \<Rightarrow> AGT037_2_bnd_mu \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  AGT037_2_bnd_very_much_likes :: "AGT037_2_bnd_mu \<Rightarrow> AGT037_2_bnd_mu \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  AGT037_2_bnd_a1 :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  AGT037_2_bnd_a2 :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"
  AGT037_2_bnd_a3 :: "TPTP_Interpret.ind \<Rightarrow> TPTP_Interpret.ind \<Rightarrow> bool"

(*test that nullary skolem terms are OK*)
     (* (Annotated_step ("79", "extcnf_forall_neg"), *)
lemma "(\<forall>SX0\<Colon>TPTP_Interpret.ind.
             AGT037_2_bnd_possibly_likes AGT037_2_bnd_jan AGT037_2_bnd_cola SX0) =
         False \<Longrightarrow>
         AGT037_2_bnd_possibly_likes AGT037_2_bnd_jan AGT037_2_bnd_cola AGT037_2_bnd_sK1_SX0 =
         False"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Existential_Var]*})

     (* (Annotated_step ("202", "extcnf_forall_neg"), *)
lemma "\<forall>(SV13\<Colon>TPTP_Interpret.ind) (SV39\<Colon>AGT037_2_bnd_mu) (SV29\<Colon>AGT037_2_bnd_mu)
            SV45\<Colon>TPTP_Interpret.ind.
            ((((\<forall>SY68\<Colon>TPTP_Interpret.ind.
                   \<not> AGT037_2_bnd_a1 SV45 SY68 \<or>
                   AGT037_2_bnd_likes SV29 SV39 SY68) =
               False \<or>
               (\<not> (\<forall>SY69\<Colon>TPTP_Interpret.ind.
                      \<not> AGT037_2_bnd_a2 SV45 SY69 \<or>
                      AGT037_2_bnd_likes SV29 SV39 SY69)) =
               True) \<or>
              AGT037_2_bnd_likes SV29 SV39 SV45 = False) \<or>
             AGT037_2_bnd_very_much_likes SV29 SV39 SV45 = True) \<or>
            AGT037_2_bnd_a3 SV13 SV45 = False \<Longrightarrow>
         \<forall>(SV29\<Colon>AGT037_2_bnd_mu) (SV39\<Colon>AGT037_2_bnd_mu) (SV13\<Colon>TPTP_Interpret.ind)
            SV45\<Colon>TPTP_Interpret.ind.
            ((((\<not> AGT037_2_bnd_a1 SV45
                   (AGT037_2_bnd_sK5_SY68 SV13 SV39 SV29 SV45) \<or>
                AGT037_2_bnd_likes SV29 SV39
                 (AGT037_2_bnd_sK5_SY68 SV13 SV39 SV29 SV45)) =
               False \<or>
               (\<not> (\<forall>SY69\<Colon>TPTP_Interpret.ind.
                      \<not> AGT037_2_bnd_a2 SV45 SY69 \<or>
                      AGT037_2_bnd_likes SV29 SV39 SY69)) =
               True) \<or>
              AGT037_2_bnd_likes SV29 SV39 SV45 = False) \<or>
             AGT037_2_bnd_very_much_likes SV29 SV39 SV45 = True) \<or>
            AGT037_2_bnd_a3 SV13 SV45 = False"
(*
apply (rule allI)+
apply (erule_tac x = "SV13" in allE)
apply (erule_tac x = "SV39" in allE)
apply (erule_tac x = "SV29" in allE)
apply (erule_tac x = "SV45" in allE)
apply (erule disjE)+
defer
apply (tactic {*clause_breaker 1*})+
apply (drule_tac sk = "bnd_sK5_SY68 SV13 SV39 SV29 SV45" in leo2_skolemise)
defer
apply (tactic {*clause_breaker 1*})
apply (tactic {*nonfull_extcnf_combined_tac []*})
*)
by (tactic {*nonfull_extcnf_combined_tac @{context} [Existential_Var]*})

(*(*NUM667^1*)
lemma "\<forall>SV12 SV13 SV14 SV9 SV10 SV11.
   ((((bnd_less SV12 SV13 = bnd_less SV11 SV10) = False \<or>
      (SV14 = SV13) = False) \<or>
     bnd_less SV12 SV14 = False) \<or>
    bnd_less SV9 SV10 = True) \<or>
   (SV9 = SV11) = False \<Longrightarrow>
\<forall>SV9 SV14 SV10 SV11 SV13 SV12.
   ((((bnd_less SV12 SV13 = False \<or>
       bnd_less SV11 SV10 = False) \<or>
      (SV14 = SV13) = False) \<or>
     bnd_less SV12 SV14 = False) \<or>
    bnd_less SV9 SV10 = True) \<or>
   (SV9 = SV11) = False"
(*
apply (tactic {*
  extcnf_combined_tac NONE
   [ConstsDiff,
    StripQuantifiers]
   []*})
*)
(*
apply (rule allI)+
apply (erule_tac x = "SV12" in allE)
apply (erule_tac x = "SV13" in allE)
apply (erule_tac x = "SV14" in allE)
apply (erule_tac x = "SV9" in allE)
apply (erule_tac x = "SV10" in allE)
apply (erule_tac x = "SV11" in allE)
*)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "300") 1*})


(*NUM667^1 node 302 -- dec*)
lemma "\<forall>SV12 SV13 SV14 SV9 SV10 SV11.
       ((((bnd_less SV12 SV13 = bnd_less SV11 SV10) = False \<or>
          (SV14 = SV13) = False) \<or>
         bnd_less SV12 SV14 = False) \<or>
        bnd_less SV9 SV10 = True) \<or>
       (SV9 = SV11) =
       False \<Longrightarrow>
       \<forall>SV9 SV14 SV10 SV13 SV11 SV12.
       (((((SV12 = SV11) = False \<or> (SV13 = SV10) = False) \<or>
          (SV14 = SV13) = False) \<or>
         bnd_less SV12 SV14 = False) \<or>
        bnd_less SV9 SV10 = True) \<or>
       (SV9 = SV11) =
       False"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "302") 1*})
*)


(*
(*CSR122^2*)
     (* (Annotated_step ("23", "extuni_bool2"), *)
lemma "(bnd_holdsDuring_THFTYPE_IiooI
           (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
           (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                  bnd_lBill_THFTYPE_i \<or>
               \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                  bnd_lBill_THFTYPE_i)) =
          bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
           bnd_lBill_THFTYPE_i) =
         False \<Longrightarrow>
         bnd_holdsDuring_THFTYPE_IiooI
          (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
          (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                 bnd_lBill_THFTYPE_i \<or>
              \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                 bnd_lBill_THFTYPE_i)) =
         True \<or>
         bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
          bnd_lBill_THFTYPE_i =
         True"
(* apply (erule extuni_bool2) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "23") 1*})

     (* (Annotated_step ("24", "extuni_bool1"), *)
lemma "(bnd_holdsDuring_THFTYPE_IiooI
           (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
           (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                  bnd_lBill_THFTYPE_i \<or>
               \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                  bnd_lBill_THFTYPE_i)) =
          bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
           bnd_lBill_THFTYPE_i) =
         False \<Longrightarrow>
         bnd_holdsDuring_THFTYPE_IiooI
          (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
          (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                 bnd_lBill_THFTYPE_i \<or>
              \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                 bnd_lBill_THFTYPE_i)) =
         False \<or>
         bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
          bnd_lBill_THFTYPE_i =
         False"
(* apply (erule extuni_bool1) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "24") 1*})

     (* (Annotated_step ("25", "extuni_bool2"), *)
lemma "(bnd_holdsDuring_THFTYPE_IiooI
           (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
           (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                  bnd_lBill_THFTYPE_i \<or>
               \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                  bnd_lBill_THFTYPE_i)) =
          bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
           bnd_lBill_THFTYPE_i) =
         False \<Longrightarrow>
         bnd_holdsDuring_THFTYPE_IiooI
          (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
          (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                 bnd_lBill_THFTYPE_i \<or>
              \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                 bnd_lBill_THFTYPE_i)) =
         True \<or>
         bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
          bnd_lBill_THFTYPE_i =
         True"
(* apply (erule extuni_bool2) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "25") 1*})

     (* (Annotated_step ("26", "extuni_bool1"), *)
lemma "\<forall>SV2. (bnd_holdsDuring_THFTYPE_IiooI
                 (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
                 (\<not> (\<not> bnd_likes_THFTYPE_IiioI
                        bnd_lMary_THFTYPE_i
                        bnd_lBill_THFTYPE_i \<or>
                     \<not> bnd_likes_THFTYPE_IiioI
                        bnd_lSue_THFTYPE_i
                        bnd_lBill_THFTYPE_i)) =
                bnd_holdsDuring_THFTYPE_IiooI SV2 True) =
               False \<Longrightarrow>
         \<forall>SV2. bnd_holdsDuring_THFTYPE_IiooI
                (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
                (\<not> (\<not> bnd_likes_THFTYPE_IiioI
                       bnd_lMary_THFTYPE_i bnd_lBill_THFTYPE_i \<or>
                    \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                       bnd_lBill_THFTYPE_i)) =
               False \<or>
               bnd_holdsDuring_THFTYPE_IiooI SV2 True = False"
(* apply (rule allI, erule allE) *)
(* apply (erule extuni_bool1) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "26") 1*})

     (* (Annotated_step ("27", "extuni_bool2"), *)
lemma "\<forall>SV2. (bnd_holdsDuring_THFTYPE_IiooI
                 (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
                 (\<not> (\<not> bnd_likes_THFTYPE_IiioI
                        bnd_lMary_THFTYPE_i
                        bnd_lBill_THFTYPE_i \<or>
                     \<not> bnd_likes_THFTYPE_IiioI
                        bnd_lSue_THFTYPE_i
                        bnd_lBill_THFTYPE_i)) =
                bnd_holdsDuring_THFTYPE_IiooI SV2 True) =
               False \<Longrightarrow>
         \<forall>SV2. bnd_holdsDuring_THFTYPE_IiooI
                (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
                (\<not> (\<not> bnd_likes_THFTYPE_IiioI
                       bnd_lMary_THFTYPE_i bnd_lBill_THFTYPE_i \<or>
                    \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                       bnd_lBill_THFTYPE_i)) =
               True \<or>
               bnd_holdsDuring_THFTYPE_IiooI SV2 True = True"
(* apply (rule allI, erule allE) *)
(* apply (erule extuni_bool2) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "27") 1*})

     (* (Annotated_step ("30", "extuni_bool1"), *)
lemma "((\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                 bnd_lBill_THFTYPE_i \<or>
              \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                 bnd_lBill_THFTYPE_i)) =
          True) =
         False \<Longrightarrow>
         (\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                bnd_lBill_THFTYPE_i \<or>
             \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                bnd_lBill_THFTYPE_i)) =
         False \<or>
         True = False"
(* apply (erule extuni_bool1) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "30") 1*})

     (* (Annotated_step ("29", "extuni_bind"), *)
lemma "(bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i =
          bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i) =
         False \<or>
         ((\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                 bnd_lBill_THFTYPE_i \<or>
              \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                 bnd_lBill_THFTYPE_i)) =
          True) =
         False \<Longrightarrow>
         ((\<not> (\<not> bnd_likes_THFTYPE_IiioI bnd_lMary_THFTYPE_i
                 bnd_lBill_THFTYPE_i \<or>
              \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                 bnd_lBill_THFTYPE_i)) =
          True) =
         False"
(* apply (tactic {*break_hypotheses 1*}) *)
(* apply (erule extuni_bind) *)
(* apply (tactic {*clause_breaker 1*}) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "29") 1*})

     (* (Annotated_step ("28", "extuni_dec"), *)
lemma "\<forall>SV2. (bnd_holdsDuring_THFTYPE_IiooI
                 (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i)
                 (\<not> (\<not> bnd_likes_THFTYPE_IiioI
                        bnd_lMary_THFTYPE_i
                        bnd_lBill_THFTYPE_i \<or>
                     \<not> bnd_likes_THFTYPE_IiioI
                        bnd_lSue_THFTYPE_i
                        bnd_lBill_THFTYPE_i)) =
                bnd_holdsDuring_THFTYPE_IiooI SV2 True) =
               False \<Longrightarrow>
         \<forall>SV2. (bnd_lYearFn_THFTYPE_IiiI bnd_n2009_THFTYPE_i =
                SV2) =
               False \<or>
               ((\<not> (\<not> bnd_likes_THFTYPE_IiioI
                       bnd_lMary_THFTYPE_i bnd_lBill_THFTYPE_i \<or>
                    \<not> bnd_likes_THFTYPE_IiioI bnd_lSue_THFTYPE_i
                       bnd_lBill_THFTYPE_i)) =
                True) =
               False"
(* apply (rule allI) *)
(* apply (erule_tac x = "SV2" in allE) *)
(* apply (erule extuni_dec_2) *)
(* done *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "28") 1*})
*)

(* QUA002^1
   (* [[(Annotated_step ("49", "extuni_dec"), *)
lemma "((bnd_sK3_E = bnd_sK1_X1 \<or> bnd_sK3_E = bnd_sK2_X2) =
          (bnd_sK3_E = bnd_sK2_X2 \<or> bnd_sK3_E = bnd_sK1_X1)) =
         False \<Longrightarrow>
         ((bnd_sK3_E = bnd_sK2_X2) = (bnd_sK3_E = bnd_sK2_X2)) =
         False \<or>
         ((bnd_sK3_E = bnd_sK1_X1) = (bnd_sK3_E = bnd_sK1_X1)) =
         False"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "49") 1*})

     (* (Annotated_step ("20", "unfold_def"), *)
lemma "(bnd_addition bnd_sK1_X1 bnd_sK2_X2 \<noteq>
          bnd_addition bnd_sK2_X2 bnd_sK1_X1) =
         True \<Longrightarrow>
         (bnd_sup
           (\<lambda>SX0\<Colon>TPTP_Interpret.ind.
               SX0 = bnd_sK1_X1 \<or> SX0 = bnd_sK2_X2) \<noteq>
          bnd_sup
           (\<lambda>SX0\<Colon>TPTP_Interpret.ind.
               SX0 = bnd_sK2_X2 \<or> SX0 = bnd_sK1_X1)) =
         True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "20") 1*})
*)

(*
(*SEU620^2*)
     (* (Annotated_step ("11", "unfold_def"), *)
lemma "bnd_kpairiskpair =
         (\<forall>Xx Xy.
             bnd_iskpair
              (bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                (bnd_setadjoin
                  (bnd_setadjoin Xx
                    (bnd_setadjoin Xy bnd_emptyset))
                  bnd_emptyset))) \<and>
         bnd_kpair =
         (\<lambda>Xx Xy.
             bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
              (bnd_setadjoin
                (bnd_setadjoin Xx
                  (bnd_setadjoin Xy bnd_emptyset))
                bnd_emptyset)) \<and>
         bnd_iskpair =
         (\<lambda>A. \<exists>Xx. bnd_in Xx (bnd_setunion A) \<and>
                   (\<exists>Xy. bnd_in Xy (bnd_setunion A) \<and>
                         A =
                         bnd_setadjoin
                          (bnd_setadjoin Xx bnd_emptyset)
                          (bnd_setadjoin
                            (bnd_setadjoin Xx
                              (bnd_setadjoin Xy bnd_emptyset))
                            bnd_emptyset))) \<and>
         (\<forall>SY5 SY6.
             (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
               (bnd_setadjoin
                 (bnd_setadjoin SY5
                   (bnd_setadjoin SY6 bnd_emptyset))
                 bnd_emptyset) =
              bnd_setadjoin
               (bnd_setadjoin (bnd_sK3 SY6 SY5) bnd_emptyset)
               (bnd_setadjoin
                 (bnd_setadjoin (bnd_sK3 SY6 SY5)
                   (bnd_setadjoin (bnd_sK4 SY6 SY5)
                     bnd_emptyset))
                 bnd_emptyset) \<and>
              bnd_in (bnd_sK4 SY6 SY5)
               (bnd_setunion
                 (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                   (bnd_setadjoin
                     (bnd_setadjoin SY5
                       (bnd_setadjoin SY6 bnd_emptyset))
                     bnd_emptyset)))) \<and>
             bnd_in (bnd_sK3 SY6 SY5)
              (bnd_setunion
                (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                  (bnd_setadjoin
                    (bnd_setadjoin SY5
                      (bnd_setadjoin SY6 bnd_emptyset))
                    bnd_emptyset)))) =
         True \<Longrightarrow>
         (\<forall>SX0 SX1.
             \<not> (\<not> \<not> (bnd_setadjoin
                      (bnd_setadjoin SX0 bnd_emptyset)
                      (bnd_setadjoin
                        (bnd_setadjoin SX0
                          (bnd_setadjoin SX1 bnd_emptyset))
                        bnd_emptyset) \<noteq>
                     bnd_setadjoin
                      (bnd_setadjoin (bnd_sK3 SX1 SX0)
                        bnd_emptyset)
                      (bnd_setadjoin
                        (bnd_setadjoin (bnd_sK3 SX1 SX0)
                          (bnd_setadjoin (bnd_sK4 SX1 SX0)
                            bnd_emptyset))
                        bnd_emptyset) \<or>
                     \<not> bnd_in (bnd_sK4 SX1 SX0)
                        (bnd_setunion
                          (bnd_setadjoin
                            (bnd_setadjoin SX0 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SX0
(bnd_setadjoin SX1 bnd_emptyset))
                              bnd_emptyset)))) \<or>
                \<not> bnd_in (bnd_sK3 SX1 SX0)
                   (bnd_setunion
                     (bnd_setadjoin
                       (bnd_setadjoin SX0 bnd_emptyset)
                       (bnd_setadjoin
                         (bnd_setadjoin SX0
                           (bnd_setadjoin SX1 bnd_emptyset))
                         bnd_emptyset))))) =
         True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "11") 1*})

     (* (Annotated_step ("3", "unfold_def"), *)
lemma "bnd_kpairiskpair =
         (\<forall>Xx Xy.
             bnd_iskpair
              (bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
                (bnd_setadjoin
                  (bnd_setadjoin Xx
                    (bnd_setadjoin Xy bnd_emptyset))
                  bnd_emptyset))) \<and>
         bnd_kpair =
         (\<lambda>Xx Xy.
             bnd_setadjoin (bnd_setadjoin Xx bnd_emptyset)
              (bnd_setadjoin
                (bnd_setadjoin Xx
                  (bnd_setadjoin Xy bnd_emptyset))
                bnd_emptyset)) \<and>
         bnd_iskpair =
         (\<lambda>A. \<exists>Xx. bnd_in Xx (bnd_setunion A) \<and>
                   (\<exists>Xy. bnd_in Xy (bnd_setunion A) \<and>
                         A =
                         bnd_setadjoin
                          (bnd_setadjoin Xx bnd_emptyset)
                          (bnd_setadjoin
                            (bnd_setadjoin Xx
                              (bnd_setadjoin Xy bnd_emptyset))
                            bnd_emptyset))) \<and>
         (bnd_kpairiskpair \<longrightarrow>
          (\<forall>Xx Xy. bnd_iskpair (bnd_kpair Xx Xy))) =
         False \<Longrightarrow>
         ((\<forall>SY5 SY6.
              \<exists>SY7. bnd_in SY7
                     (bnd_setunion
                       (bnd_setadjoin
                         (bnd_setadjoin SY5 bnd_emptyset)
                         (bnd_setadjoin
                           (bnd_setadjoin SY5
                             (bnd_setadjoin SY6 bnd_emptyset))
                           bnd_emptyset))) \<and>
                    (\<exists>SY8. bnd_in SY8
                            (bnd_setunion
                              (bnd_setadjoin
(bnd_setadjoin SY5 bnd_emptyset)
(bnd_setadjoin
  (bnd_setadjoin SY5 (bnd_setadjoin SY6 bnd_emptyset))
  bnd_emptyset))) \<and>
                           bnd_setadjoin
                            (bnd_setadjoin SY5 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY5
(bnd_setadjoin SY6 bnd_emptyset))
                              bnd_emptyset) =
                           bnd_setadjoin
                            (bnd_setadjoin SY7 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY7
(bnd_setadjoin SY8 bnd_emptyset))
                              bnd_emptyset))) \<longrightarrow>
          (\<forall>SY0 SY1.
              \<exists>SY3. bnd_in SY3
                     (bnd_setunion
                       (bnd_setadjoin
                         (bnd_setadjoin SY0 bnd_emptyset)
                         (bnd_setadjoin
                           (bnd_setadjoin SY0
                             (bnd_setadjoin SY1 bnd_emptyset))
                           bnd_emptyset))) \<and>
                    (\<exists>SY4. bnd_in SY4
                            (bnd_setunion
                              (bnd_setadjoin
(bnd_setadjoin SY0 bnd_emptyset)
(bnd_setadjoin
  (bnd_setadjoin SY0 (bnd_setadjoin SY1 bnd_emptyset))
  bnd_emptyset))) \<and>
                           bnd_setadjoin
                            (bnd_setadjoin SY0 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY0
(bnd_setadjoin SY1 bnd_emptyset))
                              bnd_emptyset) =
                           bnd_setadjoin
                            (bnd_setadjoin SY3 bnd_emptyset)
                            (bnd_setadjoin
                              (bnd_setadjoin SY3
(bnd_setadjoin SY4 bnd_emptyset))
                              bnd_emptyset)))) =
         False"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "3") 1*})

     (* (Annotated_step ("8", "extcnf_combined"), *)
lemma "(\<forall>SY5 SY6.
             \<exists>SY7. bnd_in SY7
                    (bnd_setunion
                      (bnd_setadjoin
                        (bnd_setadjoin SY5 bnd_emptyset)
                        (bnd_setadjoin
                          (bnd_setadjoin SY5
                            (bnd_setadjoin SY6 bnd_emptyset))
                          bnd_emptyset))) \<and>
                   (\<exists>SY8. bnd_in SY8
                           (bnd_setunion
                             (bnd_setadjoin
                               (bnd_setadjoin SY5 bnd_emptyset)
                               (bnd_setadjoin
 (bnd_setadjoin SY5 (bnd_setadjoin SY6 bnd_emptyset))
 bnd_emptyset))) \<and>
                          bnd_setadjoin
                           (bnd_setadjoin SY5 bnd_emptyset)
                           (bnd_setadjoin
                             (bnd_setadjoin SY5
                               (bnd_setadjoin SY6 bnd_emptyset))
                             bnd_emptyset) =
                          bnd_setadjoin
                           (bnd_setadjoin SY7 bnd_emptyset)
                           (bnd_setadjoin
                             (bnd_setadjoin SY7
                               (bnd_setadjoin SY8 bnd_emptyset))
                             bnd_emptyset))) =
         True \<Longrightarrow>
         (\<forall>SY5 SY6.
             (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
               (bnd_setadjoin
                 (bnd_setadjoin SY5
                   (bnd_setadjoin SY6 bnd_emptyset))
                 bnd_emptyset) =
              bnd_setadjoin
               (bnd_setadjoin (bnd_sK3 SY6 SY5) bnd_emptyset)
               (bnd_setadjoin
                 (bnd_setadjoin (bnd_sK3 SY6 SY5)
                   (bnd_setadjoin (bnd_sK4 SY6 SY5)
                     bnd_emptyset))
                 bnd_emptyset) \<and>
              bnd_in (bnd_sK4 SY6 SY5)
               (bnd_setunion
                 (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                   (bnd_setadjoin
                     (bnd_setadjoin SY5
                       (bnd_setadjoin SY6 bnd_emptyset))
                     bnd_emptyset)))) \<and>
             bnd_in (bnd_sK3 SY6 SY5)
              (bnd_setunion
                (bnd_setadjoin (bnd_setadjoin SY5 bnd_emptyset)
                  (bnd_setadjoin
                    (bnd_setadjoin SY5
                      (bnd_setadjoin SY6 bnd_emptyset))
                    bnd_emptyset)))) =
         True"
by (tactic {*
HEADGOAL (extcnf_combined_tac Full false (hd prob_names))
*})

     (* (Annotated_step ("7", "extcnf_combined"), *)
lemma "(\<not> (\<forall>SY0 SY1.
                \<exists>SY3. bnd_in SY3
                       (bnd_setunion
                         (bnd_setadjoin
                           (bnd_setadjoin SY0 bnd_emptyset)
                           (bnd_setadjoin
                             (bnd_setadjoin SY0
                               (bnd_setadjoin SY1 bnd_emptyset))
                             bnd_emptyset))) \<and>
                      (\<exists>SY4. bnd_in SY4
                              (bnd_setunion
(bnd_setadjoin (bnd_setadjoin SY0 bnd_emptyset)
  (bnd_setadjoin
    (bnd_setadjoin SY0 (bnd_setadjoin SY1 bnd_emptyset))
    bnd_emptyset))) \<and>
                             bnd_setadjoin
                              (bnd_setadjoin SY0 bnd_emptyset)
                              (bnd_setadjoin
(bnd_setadjoin SY0 (bnd_setadjoin SY1 bnd_emptyset))
bnd_emptyset) =
                             bnd_setadjoin
                              (bnd_setadjoin SY3 bnd_emptyset)
                              (bnd_setadjoin
(bnd_setadjoin SY3 (bnd_setadjoin SY4 bnd_emptyset))
bnd_emptyset)))) =
         True \<Longrightarrow>
         (\<forall>SY24.
             (\<forall>SY25.
                 bnd_setadjoin
                  (bnd_setadjoin bnd_sK1 bnd_emptyset)
                  (bnd_setadjoin
                    (bnd_setadjoin bnd_sK1
                      (bnd_setadjoin bnd_sK2 bnd_emptyset))
                    bnd_emptyset) \<noteq>
                 bnd_setadjoin (bnd_setadjoin SY24 bnd_emptyset)
                  (bnd_setadjoin
                    (bnd_setadjoin SY24
                      (bnd_setadjoin SY25 bnd_emptyset))
                    bnd_emptyset) \<or>
                 \<not> bnd_in SY25
                    (bnd_setunion
                      (bnd_setadjoin
                        (bnd_setadjoin bnd_sK1 bnd_emptyset)
                        (bnd_setadjoin
                          (bnd_setadjoin bnd_sK1
                            (bnd_setadjoin bnd_sK2
                              bnd_emptyset))
                          bnd_emptyset)))) \<or>
             \<not> bnd_in SY24
                (bnd_setunion
                  (bnd_setadjoin
                    (bnd_setadjoin bnd_sK1 bnd_emptyset)
                    (bnd_setadjoin
                      (bnd_setadjoin bnd_sK1
                        (bnd_setadjoin bnd_sK2 bnd_emptyset))
                      bnd_emptyset)))) =
         True"
by (tactic {*HEADGOAL (extcnf_combined_tac Full false (hd prob_names))*})
*)

(*PUZ081^2*)
(*
     (* (Annotated_step ("9", "unfold_def"), *)
lemma "bnd_says bnd_mel
          (\<not> bnd_knave bnd_zoey \<and> \<not> bnd_knave bnd_mel) \<Longrightarrow>
         bnd_says bnd_mel
          (\<not> bnd_knave bnd_zoey \<and> \<not> bnd_knave bnd_mel) =
         True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "9") 1*})

     (* (Annotated_step ("10", "unfold_def"), *)
lemma "bnd_says bnd_zoey (bnd_knave bnd_mel) \<Longrightarrow>
         bnd_says bnd_zoey (bnd_knave bnd_mel) = True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "10") 1*})

     (* (Annotated_step ("11", "unfold_def"), *)
lemma "\<forall>P S. bnd_knave P \<and> bnd_says P S \<longrightarrow> \<not> S \<Longrightarrow>
         (\<forall>P S. bnd_knave P \<and> bnd_says P S \<longrightarrow> \<not> S) = True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "11") 1*})

     (* (Annotated_step ("12", "unfold_def"), *)
lemma "\<forall>P S. bnd_knight P \<and> bnd_says P S \<longrightarrow> S \<Longrightarrow>
         (\<forall>P S. bnd_knight P \<and> bnd_says P S \<longrightarrow> S) = True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "12") 1*})

     (* (Annotated_step ("13", "unfold_def"), *)
lemma "\<forall>P. bnd_knight P \<noteq> bnd_knave P \<Longrightarrow>
         (\<forall>P. bnd_knight P \<noteq> bnd_knave P) = True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "13") 1*})

     (* (Annotated_step ("15", "extcnf_combined"), *)
lemma "(\<not> (\<exists>TZ TM. TZ bnd_zoey \<and> TM bnd_mel)) = True \<Longrightarrow>
         ((\<forall>TM. \<not> TM bnd_mel) \<or> (\<forall>TZ. \<not> TZ bnd_zoey)) = True"
by (tactic {*extcnf_combined_tac Full false (hd prob_names) 1*})

     (* (Annotated_step ("18", "extcnf_combined"), *)
lemma "(\<forall>P. bnd_knight P \<noteq> bnd_knave P) = True \<Longrightarrow>
         ((\<forall>P. \<not> bnd_knave P \<or> \<not> bnd_knight P) \<and>
          (\<forall>P. bnd_knave P \<or> bnd_knight P)) =
         True"
by (tactic {*extcnf_combined_tac Full false (hd prob_names) 1*})
*)

(*
(*from SEU667^2.p.out*)
     (* (Annotated_step ("10", "unfold_def"), *)
lemma "bnd_dpsetconstrSub =
         (\<forall>A B Xphi.
             bnd_subset (bnd_dpsetconstr A B Xphi)
              (bnd_cartprod A B)) \<and>
         bnd_dpsetconstr =
         (\<lambda>A B Xphi.
             bnd_dsetconstr (bnd_cartprod A B)
              (\<lambda>Xu. \<exists>Xx. bnd_in Xx A \<and>
                         (\<exists>Xy. (bnd_in Xy B \<and> Xphi Xx Xy) \<and>
                               Xu = bnd_kpair Xx Xy))) \<and>
         bnd_breln = (\<lambda>A B C. bnd_subset C (bnd_cartprod A B)) \<and>
         (\<not> bnd_subset
             (bnd_dsetconstr (bnd_cartprod bnd_sK1 bnd_sK2)
               (\<lambda>SY66.
                   \<exists>SY67.
                      bnd_in SY67 bnd_sK1 \<and>
                      (\<exists>SY68.
                          (bnd_in SY68 bnd_sK2 \<and>
                           bnd_sK3 SY67 SY68) \<and>
                          SY66 = bnd_kpair SY67 SY68)))
             (bnd_cartprod bnd_sK1 bnd_sK2)) =
         True \<Longrightarrow>
         (\<not> bnd_subset
             (bnd_dsetconstr (bnd_cartprod bnd_sK1 bnd_sK2)
               (\<lambda>SX0. \<not> (\<forall>SX1. \<not> \<not> (\<not> bnd_in SX1 bnd_sK1 \<or>
    \<not> \<not> (\<forall>SX2. \<not> \<not> (\<not> \<not> (\<not> bnd_in SX2 bnd_sK2 \<or>
                         \<not> bnd_sK3 SX1 SX2) \<or>
                    SX0 \<noteq> bnd_kpair SX1 SX2))))))
             (bnd_cartprod bnd_sK1 bnd_sK2)) =
         True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "10") 1*})


     (* (Annotated_step ("11", "unfold_def"), *)
lemma "bnd_dpsetconstrSub =
         (\<forall>A B Xphi.
             bnd_subset (bnd_dpsetconstr A B Xphi)
              (bnd_cartprod A B)) \<and>
         bnd_dpsetconstr =
         (\<lambda>A B Xphi.
             bnd_dsetconstr (bnd_cartprod A B)
              (\<lambda>Xu. \<exists>Xx. bnd_in Xx A \<and>
                         (\<exists>Xy. (bnd_in Xy B \<and> Xphi Xx Xy) \<and>
                               Xu = bnd_kpair Xx Xy))) \<and>
         bnd_breln = (\<lambda>A B C. bnd_subset C (bnd_cartprod A B)) \<and>
         (\<forall>SY21 SY22 SY23.
             bnd_subset
              (bnd_dsetconstr (bnd_cartprod SY21 SY22)
                (\<lambda>SY35.
                    \<exists>SY36.
                       bnd_in SY36 SY21 \<and>
                       (\<exists>SY37.
                           (bnd_in SY37 SY22 \<and> SY23 SY36 SY37) \<and>
                           SY35 = bnd_kpair SY36 SY37)))
              (bnd_cartprod SY21 SY22)) =
         True \<Longrightarrow>
         (\<forall>SX0 SX1 SX2.
             bnd_subset
              (bnd_dsetconstr (bnd_cartprod SX0 SX1)
                (\<lambda>SX3. \<not> (\<forall>SX4. \<not> \<not> (\<not> bnd_in SX4 SX0 \<or>
     \<not> \<not> (\<forall>SX5. \<not> \<not> (\<not> \<not> (\<not> bnd_in SX5 SX1 \<or> \<not> SX2 SX4 SX5) \<or>
                     SX3 \<noteq> bnd_kpair SX4 SX5))))))
              (bnd_cartprod SX0 SX1)) =
         True"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "11") 1*})
*)

(*
(*from ALG001^5*)
      (* (Annotated_step ("4", "extcnf_forall_neg"), *)
lemma "(\<forall>(Xh1 :: bnd_g \<Rightarrow> bnd_b) (Xh2 :: bnd_b \<Rightarrow> bnd_a) (Xf1 :: bnd_g \<Rightarrow> bnd_g \<Rightarrow> bnd_g) (Xf2 :: bnd_b \<Rightarrow> bnd_b \<Rightarrow> bnd_b) (Xf3 :: bnd_a \<Rightarrow> bnd_a \<Rightarrow> bnd_a).
             (\<forall>Xx Xy. Xh1 (Xf1 Xx Xy) = Xf2 (Xh1 Xx) (Xh1 Xy)) \<and>
             (\<forall>Xx Xy.
                 Xh2 (Xf2 Xx Xy) = Xf3 (Xh2 Xx) (Xh2 Xy)) \<longrightarrow>
             (\<forall>Xx Xy.
                 Xh2 (Xh1 (Xf1 Xx Xy)) =
                 Xf3 (Xh2 (Xh1 Xx)) (Xh2 (Xh1 Xy)))) =
         False \<Longrightarrow>
         ((\<forall>SY35 SY36.
              bnd_sK1 (bnd_sK3 SY35 SY36) =
              bnd_sK4 (bnd_sK1 SY35) (bnd_sK1 SY36)) \<and>
          (\<forall>SY31 SY32.
              bnd_sK2 (bnd_sK4 SY31 SY32) =
              bnd_sK5 (bnd_sK2 SY31) (bnd_sK2 SY32)) \<longrightarrow>
          (\<forall>SY39 SY40.
              bnd_sK2 (bnd_sK1 (bnd_sK3 SY39 SY40)) =
              bnd_sK5 (bnd_sK2 (bnd_sK1 SY39))
               (bnd_sK2 (bnd_sK1 SY40)))) =
         False"
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "4") 1*})
*)

(*SYN044^4*)
(*
ML {*
print_depth 1400;
(* the_tactics *)
*}

     (* (Annotated_step ("12", "unfold_def"), *)
lemma "bnd_mor =
         (\<lambda>(X\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             (Y\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) U\<Colon>TPTP_Interpret.ind.
             X U \<or> Y U) \<and>
         bnd_mnot =
         (\<lambda>(X\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) U\<Colon>TPTP_Interpret.ind.
             \<not> X U) \<and>
         bnd_mimplies =
         (\<lambda>U\<Colon>TPTP_Interpret.ind \<Rightarrow> bool. bnd_mor (bnd_mnot U)) \<and>
         bnd_mbox_s4 =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) X\<Colon>TPTP_Interpret.ind.
             \<forall>Y\<Colon>TPTP_Interpret.ind. bnd_irel X Y \<longrightarrow> P Y) \<and>
         bnd_mand =
         (\<lambda>(X\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             (Y\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) U\<Colon>TPTP_Interpret.ind.
             X U \<and> Y U) \<and>
         bnd_ixor =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_inot (bnd_iequiv P Q)) \<and>
         bnd_ivalid = All \<and>
         bnd_itrue = (\<lambda>W\<Colon>TPTP_Interpret.ind. True) \<and>
         bnd_isatisfiable = Ex \<and>
         bnd_ior =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_mor (bnd_mbox_s4 P) (bnd_mbox_s4 Q)) \<and>
         bnd_inot =
         (\<lambda>P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_mnot (bnd_mbox_s4 P)) \<and>
         bnd_iinvalid =
         (\<lambda>Phi\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             \<forall>W\<Colon>TPTP_Interpret.ind. \<not> Phi W) \<and>
         bnd_iimplies =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_mimplies (bnd_mbox_s4 P) (bnd_mbox_s4 Q)) \<and>
         bnd_iimplied =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool. bnd_iimplies Q P) \<and>
         bnd_ifalse = bnd_inot bnd_itrue \<and>
         bnd_iequiv =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_iand (bnd_iimplies P Q) (bnd_iimplies Q P)) \<and>
         bnd_icountersatisfiable =
         (\<lambda>Phi\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             \<exists>W\<Colon>TPTP_Interpret.ind. \<not> Phi W) \<and>
         bnd_iatom = (\<lambda>P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool. P) \<and>
         bnd_iand = bnd_mand \<and>
         (\<forall>(X\<Colon>TPTP_Interpret.ind) (Y\<Colon>TPTP_Interpret.ind)
             Z\<Colon>TPTP_Interpret.ind.
             bnd_irel X Y \<and> bnd_irel Y Z \<longrightarrow> bnd_irel X Z) \<Longrightarrow>
         (\<forall>(X\<Colon>TPTP_Interpret.ind) (Y\<Colon>TPTP_Interpret.ind)
             Z\<Colon>TPTP_Interpret.ind.
             bnd_irel X Y \<and> bnd_irel Y Z \<longrightarrow> bnd_irel X Z) =
         True"
(* by (tactic {*tectoc @{context}*}) *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "12") 1*})

     (* (Annotated_step ("11", "unfold_def"), *)
lemma "bnd_mor =
         (\<lambda>(X\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             (Y\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) U\<Colon>TPTP_Interpret.ind.
             X U \<or> Y U) \<and>
         bnd_mnot =
         (\<lambda>(X\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) U\<Colon>TPTP_Interpret.ind.
             \<not> X U) \<and>
         bnd_mimplies =
         (\<lambda>U\<Colon>TPTP_Interpret.ind \<Rightarrow> bool. bnd_mor (bnd_mnot U)) \<and>
         bnd_mbox_s4 =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) X\<Colon>TPTP_Interpret.ind.
             \<forall>Y\<Colon>TPTP_Interpret.ind. bnd_irel X Y \<longrightarrow> P Y) \<and>
         bnd_mand =
         (\<lambda>(X\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             (Y\<Colon>TPTP_Interpret.ind \<Rightarrow> bool) U\<Colon>TPTP_Interpret.ind.
             X U \<and> Y U) \<and>
         bnd_ixor =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_inot (bnd_iequiv P Q)) \<and>
         bnd_ivalid = All \<and>
         bnd_itrue = (\<lambda>W\<Colon>TPTP_Interpret.ind. True) \<and>
         bnd_isatisfiable = Ex \<and>
         bnd_ior =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_mor (bnd_mbox_s4 P) (bnd_mbox_s4 Q)) \<and>
         bnd_inot =
         (\<lambda>P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_mnot (bnd_mbox_s4 P)) \<and>
         bnd_iinvalid =
         (\<lambda>Phi\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             \<forall>W\<Colon>TPTP_Interpret.ind. \<not> Phi W) \<and>
         bnd_iimplies =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_mimplies (bnd_mbox_s4 P) (bnd_mbox_s4 Q)) \<and>
         bnd_iimplied =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool. bnd_iimplies Q P) \<and>
         bnd_ifalse = bnd_inot bnd_itrue \<and>
         bnd_iequiv =
         (\<lambda>(P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool)
             Q\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             bnd_iand (bnd_iimplies P Q) (bnd_iimplies Q P)) \<and>
         bnd_icountersatisfiable =
         (\<lambda>Phi\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
             \<exists>W\<Colon>TPTP_Interpret.ind. \<not> Phi W) \<and>
         bnd_iatom = (\<lambda>P\<Colon>TPTP_Interpret.ind \<Rightarrow> bool. P) \<and>
         bnd_iand = bnd_mand \<and>
         bnd_ivalid
          (bnd_iimplies (bnd_iatom bnd_q) (bnd_iatom bnd_r)) \<Longrightarrow>
         (\<forall>SY161\<Colon>TPTP_Interpret.ind.
             \<not> (\<forall>SY162\<Colon>TPTP_Interpret.ind.
                   bnd_irel SY161 SY162 \<longrightarrow> bnd_q SY162) \<or>
             (\<forall>SY163\<Colon>TPTP_Interpret.ind.
                 bnd_irel SY161 SY163 \<longrightarrow> bnd_r SY163)) =
         True"
(* by (tactic {*tectoc @{context}*}) *)
by (tactic {*rtac (leo2_tac @{context} (hd prob_names) "11") 1*})

lemma "
(\<forall>SY136.
    \<not> (\<forall>SY137. bnd_irel SY136 SY137 \<longrightarrow> bnd_r SY137) \<or>
    (\<forall>SY138.
        bnd_irel SY136 SY138 \<longrightarrow> bnd_p SY138 \<and> bnd_q SY138)) =
True \<Longrightarrow>
(\<forall>SY136.
    bnd_irel SY136 (bnd_sK5 SY136) \<and> \<not> bnd_r (bnd_sK5 SY136) \<or>
    (\<forall>SY138. \<not> bnd_irel SY136 SY138 \<or> bnd_p SY138) \<and>
    (\<forall>SY138. \<not> bnd_irel SY136 SY138 \<or> bnd_q SY138)) =
True"
by (tactic {*HEADGOAL (extcnf_combined_tac Full false (hd prob_names))*})
*)

     (* (Annotated_step ("11", "extcnf_forall_neg"), *)
lemma "\<forall>SV1\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
            (\<forall>SY2\<Colon>TPTP_Interpret.ind.
                \<not> (\<not> (\<not> SV1 SY2 \<or> SEV405_5_bnd_cA) \<or>
                   \<not> (\<not> SEV405_5_bnd_cA \<or> SV1 SY2))) =
            False \<Longrightarrow>
         \<forall>SV1\<Colon>TPTP_Interpret.ind \<Rightarrow> bool.
            (\<not> (\<not> (\<not> SV1 (SEV405_5_bnd_sK1_SY2 SV1) \<or> SEV405_5_bnd_cA) \<or>
                \<not> (\<not> SEV405_5_bnd_cA \<or> SV1 (SEV405_5_bnd_sK1_SY2 SV1)))) =
            False"
(* apply (tactic {*full_extcnf_combined_tac*}) *)
by (tactic {*nonfull_extcnf_combined_tac @{context} [Existential_Var]*})

     (* (Annotated_step ("13", "extcnf_forall_pos"), *)
lemma "(\<forall>SY31 SY32.
             bnd_sK2 (bnd_sK4 SY31 SY32) =
             bnd_sK5 (bnd_sK2 SY31) (bnd_sK2 SY32)) =
         True \<Longrightarrow>
         \<forall>SV1. (\<forall>SY42.
                   bnd_sK2 (bnd_sK4 SV1 SY42) =
                   bnd_sK5 (bnd_sK2 SV1) (bnd_sK2 SY42)) =
               True"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Universal]*})

     (* (Annotated_step ("14", "extcnf_forall_pos"), *)
lemma "(\<forall>SY35 SY36.
             bnd_sK1 (bnd_sK3 SY35 SY36) =
             bnd_sK4 (bnd_sK1 SY35) (bnd_sK1 SY36)) =
         True \<Longrightarrow>
         \<forall>SV2. (\<forall>SY43.
                   bnd_sK1 (bnd_sK3 SV2 SY43) =
                   bnd_sK4 (bnd_sK1 SV2) (bnd_sK1 SY43)) =
               True"
by (tactic {*nonfull_extcnf_combined_tac @{context} [Universal]*})


(*from SYO198^5.p.out*)
   (* [[(Annotated_step ("11", "extcnf_forall_special_pos"), *)
lemma "(\<forall>SX0\<Colon>bool \<Rightarrow> bool.
             \<not> \<not> (\<not> SX0 bnd_sK1_Xx \<or> \<not> SX0 bnd_sK2_Xy)) =
         True \<Longrightarrow>
         (\<not> \<not> (\<not> True \<or> \<not> True)) = True"
apply (tactic {*extcnf_forall_special_pos_tac 1*})
done

     (* (Annotated_step ("13", "extcnf_forall_special_pos"), *)
lemma "(\<forall>SX0\<Colon>bool \<Rightarrow> bool.
             \<not> \<not> (\<not> SX0 bnd_sK1_Xx \<or> \<not> SX0 bnd_sK2_Xy)) =
         True \<Longrightarrow>
         (\<not> \<not> (\<not> bnd_sK1_Xx \<or> \<not> bnd_sK2_Xy)) = True"
apply (tactic {*extcnf_forall_special_pos_tac 1*})
done

   (* [[(Annotated_step ("8", "polarity_switch"), *)
lemma "(\<forall>(Xx\<Colon>bool) (Xy\<Colon>bool) Xz\<Colon>bool. True \<and> True \<longrightarrow> True) =
         False \<Longrightarrow>
         (\<not> (\<forall>(Xx\<Colon>bool) (Xy\<Colon>bool) Xz\<Colon>bool.
                True \<and> True \<longrightarrow> True)) =
         True"
apply (tactic {*nonfull_extcnf_combined_tac @{context} [Polarity_switch]*})
done

lemma "((\<forall>SY22 SY23 SY24.
       bnd_sK1_RRR SY22 SY23 \<and> bnd_sK1_RRR SY23 SY24 \<longrightarrow>
       bnd_sK1_RRR SY22 SY24) \<and>
   (\<forall>SY25.
       (\<forall>SY26. SY25 SY26 \<longrightarrow> bnd_sK1_RRR SY26 (bnd_sK2_U SY25)) \<and>
       (\<forall>SY27.
           (\<forall>SY28. SY25 SY28 \<longrightarrow> bnd_sK1_RRR SY28 SY27) \<longrightarrow>
           bnd_sK1_RRR (bnd_sK2_U SY25) SY27)) \<longrightarrow>
   (\<forall>SY29. \<exists>SY30. \<forall>SY31. SY29 SY31 \<longrightarrow> bnd_sK1_RRR SY31 SY30)) =
  False \<Longrightarrow>
  (\<forall>SY25.
      (\<forall>SY26. SY25 SY26 \<longrightarrow> bnd_sK1_RRR SY26 (bnd_sK2_U SY25)) \<and>
      (\<forall>SY27.
          (\<forall>SY28. SY25 SY28 \<longrightarrow> bnd_sK1_RRR SY28 SY27) \<longrightarrow>
          bnd_sK1_RRR (bnd_sK2_U SY25) SY27)) =
  True"
apply (tactic {*standard_cnf_tac @{context} 1*})
done

lemma "((\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) \<longrightarrow>
   (\<forall>Xx Xy. bnd_in Xx (bnd_setadjoin Xx Xy)) \<longrightarrow>
   (\<forall>A B. A = B \<longrightarrow>
          (\<forall>Xx Xy. Xx = Xy \<longrightarrow> bnd_in Xx A = bnd_in Xy B)) \<longrightarrow>
   (\<forall>SY0. bnd_in SY0 bnd_omega \<longrightarrow>
          bnd_setadjoin SY0 SY0 \<noteq> bnd_emptyset)) =
  False \<Longrightarrow>
 (\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) =
  True"
apply (tactic {*standard_cnf_tac @{context} 1*})
done

lemma "((\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) \<longrightarrow>
   (\<forall>Xx Xy. bnd_in Xx (bnd_setadjoin Xx Xy)) \<longrightarrow>
   (\<forall>A B. A = B \<longrightarrow>
          (\<forall>Xx Xy. Xx = Xy \<longrightarrow> bnd_in Xx A = bnd_in Xy B)) \<longrightarrow>
   (\<forall>SY0. bnd_in SY0 bnd_omega \<longrightarrow>
          bnd_setadjoin SY0 SY0 \<noteq> bnd_emptyset)) =
  False \<Longrightarrow>
  (\<forall>Xx Xy. bnd_in Xx (bnd_setadjoin Xx Xy)) =
  True"
apply (tactic {*standard_cnf_tac @{context} 1*})
done

lemma "((\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) \<longrightarrow>
   (\<forall>Xx Xy. bnd_in Xx (bnd_setadjoin Xx Xy)) \<longrightarrow>
   (\<forall>A B. A = B \<longrightarrow>
          (\<forall>Xx Xy. Xx = Xy \<longrightarrow> bnd_in Xx A = bnd_in Xy B)) \<longrightarrow>
   (\<forall>SY0. bnd_in SY0 bnd_omega \<longrightarrow>
          bnd_setadjoin SY0 SY0 \<noteq> bnd_emptyset)) =
  False \<Longrightarrow>
  (\<forall>A B. A = B \<longrightarrow>
         (\<forall>Xx Xy. Xx = Xy \<longrightarrow> bnd_in Xx A = bnd_in Xy B)) =
  True"
apply (tactic {*standard_cnf_tac @{context} 1*})
done

lemma "((\<forall>Xx. bnd_in Xx bnd_emptyset \<longrightarrow> (\<forall>Xphi. Xphi)) \<longrightarrow>
   (\<forall>Xx Xy. bnd_in Xx (bnd_setadjoin Xx Xy)) \<longrightarrow>
   (\<forall>A B. A = B \<longrightarrow>
          (\<forall>Xx Xy. Xx = Xy \<longrightarrow> bnd_in Xx A = bnd_in Xy B)) \<longrightarrow>
   (\<forall>SY0. bnd_in SY0 bnd_omega \<longrightarrow>
          bnd_setadjoin SY0 SY0 \<noteq> bnd_emptyset)) =
  False \<Longrightarrow>
  (\<forall>SY0. bnd_in SY0 bnd_omega \<longrightarrow>
         bnd_setadjoin SY0 SY0 \<noteq> bnd_emptyset) =
  False"
apply (tactic {*standard_cnf_tac @{context} 1*})
done

(*nested conjunctions*)
lemma "((((\<forall>Xx. bnd_cP bnd_e Xx = Xx) \<and>
     (\<forall>Xy. bnd_cP Xy bnd_e = Xy)) \<and>
    (\<forall>Xz. bnd_cP Xz Xz = bnd_e)) \<and>
   (\<forall>Xx Xy Xz.
       bnd_cP (bnd_cP Xx Xy) Xz = bnd_cP Xx (bnd_cP Xy Xz)) \<longrightarrow>
   (\<forall>Xa Xb. bnd_cP Xa Xb = bnd_cP Xb Xa)) =
  False \<Longrightarrow>
  (\<forall>Xx. bnd_cP bnd_e Xx = Xx) =
  True"
apply (tactic {*standard_cnf_tac @{context} 1*})
done

end