(*  Title:      HOL/Tools/rewrite_hol_proof.ML
    Author:     Stefan Berghofer, TU Muenchen

Rewrite rules for HOL proofs.
*)

signature REWRITE_HOL_PROOF =
sig
  val rews: (Proofterm.proof * Proofterm.proof) list
  val elim_cong: typ list -> term option list -> Proofterm.proof -> (Proofterm.proof * Proofterm.proof) option
end;

structure Rewrite_HOL_Proof : REWRITE_HOL_PROOF =
struct

val rews =
  map (apply2 (Proof_Syntax.proof_of_term \<^theory> true) o Logic.dest_equals o
    Logic.varify_global o Proof_Syntax.read_term \<^theory> true propT o Syntax.implode_input)

  (** eliminate meta-equality rules **)

  [\<open>(equal_elim \<cdot> x1 \<cdot> x2 \<bullet>
      (combination \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> Trueprop \<cdot> x3 \<cdot> A \<cdot> B \<bullet>
        (axm.reflexive \<cdot> TYPE('T3) \<cdot> x4) \<bullet> prf1)) \<equiv>
    (iffD1 \<cdot> A \<cdot> B \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE(bool) \<cdot> A \<cdot> B \<bullet> arity_type_bool \<bullet> prf1))\<close>,

   \<open>(equal_elim \<cdot> x1 \<cdot> x2 \<bullet> (axm.symmetric \<cdot> TYPE('T1) \<cdot> x3 \<cdot> x4 \<bullet>
      (combination \<cdot> TYPE('T2) \<cdot> TYPE('T3) \<cdot> Trueprop \<cdot> x5 \<cdot> A \<cdot> B \<bullet>
        (axm.reflexive \<cdot> TYPE('T4) \<cdot> x6) \<bullet> prf1))) \<equiv>
    (iffD2 \<cdot> A \<cdot> B \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE(bool) \<cdot> A \<cdot> B \<bullet> arity_type_bool \<bullet> prf1))\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('U) \<cdot> x1 \<cdot> x2 \<bullet> prfU \<bullet>
      (combination \<cdot> TYPE('T) \<cdot> TYPE('U) \<cdot> f \<cdot> g \<cdot> x \<cdot> y \<bullet> prf1 \<bullet> prf2)) \<equiv>
    (cong \<cdot> TYPE('T) \<cdot> TYPE('U) \<cdot> f \<cdot> g \<cdot> x \<cdot> y \<bullet>
      (Pure.PClass type_class \<cdot> TYPE('T)) \<bullet> prfU \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE('T \<Rightarrow> 'U) \<cdot> f \<cdot> g \<bullet> (Pure.PClass type_class \<cdot> TYPE('T \<Rightarrow> 'U)) \<bullet> prf1) \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> (Pure.PClass type_class \<cdot> TYPE('T)) \<bullet> prf2))\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x1 \<cdot> x2 \<bullet> prfT \<bullet>
      (axm.transitive \<cdot> TYPE('T) \<cdot> x \<cdot> y \<cdot> z \<bullet> prf1 \<bullet> prf2)) \<equiv>
    (HOL.trans \<cdot> TYPE('T) \<cdot> x \<cdot> y \<cdot> z \<bullet> prfT \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prfT \<bullet> prf1) \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> y \<cdot> z \<bullet> prfT \<bullet> prf2))\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x \<cdot> x \<bullet> prfT \<bullet> (axm.reflexive \<cdot> TYPE('T) \<cdot> x)) \<equiv>
    (HOL.refl \<cdot> TYPE('T) \<cdot> x \<bullet> prfT)\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prfT \<bullet>
      (axm.symmetric \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prf)) \<equiv>
    (sym \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prfT \<bullet> (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prfT \<bullet> prf))\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T \<Rightarrow> 'U) \<cdot> x1 \<cdot> x2 \<bullet> prfTU \<bullet>
      (abstract_rule \<cdot> TYPE('T) \<cdot> TYPE('U) \<cdot> f \<cdot> g \<bullet> prf)) \<equiv>
    (ext \<cdot> TYPE('T) \<cdot> TYPE('U) \<cdot> f \<cdot> g \<bullet>
      (Pure.PClass type_class \<cdot> TYPE('T)) \<bullet> (Pure.PClass type_class \<cdot> TYPE('U)) \<bullet>
      (\<^bold>\<lambda>(x::'T). meta_eq_to_obj_eq \<cdot> TYPE('U) \<cdot> f x \<cdot> g x \<bullet>
         (Pure.PClass type_class \<cdot> TYPE('U)) \<bullet> (prf \<cdot> x)))\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prfT \<bullet>
      (eq_reflection \<cdot> TYPE('T) \<cdot> x \<cdot> y \<bullet> prfT \<bullet> prf)) \<equiv> prf\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x1 \<cdot> x2 \<bullet> prfT \<bullet> (equal_elim \<cdot> x3 \<cdot> x4 \<bullet>
      (combination \<cdot> TYPE('T) \<cdot> TYPE(prop) \<cdot> x7 \<cdot> x8 \<cdot> C \<cdot> D \<bullet>
        (combination \<cdot> TYPE('T) \<cdot> TYPE('T3) \<cdot> (\<equiv>) \<cdot> (\<equiv>) \<cdot> A \<cdot> B \<bullet>
          (axm.reflexive \<cdot> TYPE('T4) \<cdot> (\<equiv>)) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3)) \<equiv>
    (iffD1 \<cdot> A = C \<cdot> B = D \<bullet>
      (cong \<cdot> TYPE('T) \<cdot> TYPE(bool) \<cdot> (=) A \<cdot> (=) B \<cdot> C \<cdot> D \<bullet>
        prfT \<bullet> arity_type_bool \<bullet>
        (cong \<cdot> TYPE('T) \<cdot> TYPE('T\<Rightarrow>bool) \<cdot>
          ((=) :: 'T\<Rightarrow>'T\<Rightarrow>bool) \<cdot> ((=) :: 'T\<Rightarrow>'T\<Rightarrow>bool) \<cdot> A \<cdot> B \<bullet>
          prfT \<bullet> (Pure.PClass type_class \<cdot> TYPE('T\<Rightarrow>bool)) \<bullet>
          (HOL.refl \<cdot> TYPE('T\<Rightarrow>'T\<Rightarrow>bool) \<cdot> ((=) :: 'T\<Rightarrow>'T\<Rightarrow>bool) \<bullet>
             (Pure.PClass type_class \<cdot> TYPE('T\<Rightarrow>'T\<Rightarrow>bool))) \<bullet>
          (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> A \<cdot> B \<bullet> prfT \<bullet> prf1)) \<bullet>
        (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> C \<cdot> D \<bullet> prfT \<bullet> prf2)) \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> A \<cdot> C \<bullet> prfT \<bullet> prf3))\<close>,

   \<open>(meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> x1 \<cdot> x2 \<bullet> prfT \<bullet> (equal_elim \<cdot> x3 \<cdot> x4 \<bullet>
      (axm.symmetric \<cdot> TYPE('T2) \<cdot> x5 \<cdot> x6 \<bullet>
        (combination \<cdot> TYPE('T) \<cdot> TYPE(prop) \<cdot> x7 \<cdot> x8 \<cdot> C \<cdot> D \<bullet>
          (combination \<cdot> TYPE('T) \<cdot> TYPE('T3) \<cdot> (\<equiv>) \<cdot> (\<equiv>) \<cdot> A \<cdot> B \<bullet>
            (axm.reflexive \<cdot> TYPE('T4) \<cdot> (\<equiv>)) \<bullet> prf1) \<bullet> prf2)) \<bullet> prf3)) \<equiv>
    (iffD2 \<cdot> A = C \<cdot> B = D \<bullet>
      (cong \<cdot> TYPE('T) \<cdot> TYPE(bool) \<cdot> (=) A \<cdot> (=) B \<cdot> C \<cdot> D \<bullet>
        prfT \<bullet> arity_type_bool \<bullet>
        (cong \<cdot> TYPE('T) \<cdot> TYPE('T\<Rightarrow>bool) \<cdot>
          ((=) :: 'T\<Rightarrow>'T\<Rightarrow>bool) \<cdot> ((=) :: 'T\<Rightarrow>'T\<Rightarrow>bool) \<cdot> A \<cdot> B \<bullet>
          prfT \<bullet> (Pure.PClass type_class \<cdot> TYPE('T\<Rightarrow>bool)) \<bullet>
          (HOL.refl \<cdot> TYPE('T\<Rightarrow>'T\<Rightarrow>bool) \<cdot> ((=) :: 'T\<Rightarrow>'T\<Rightarrow>bool) \<bullet>
             (Pure.PClass type_class \<cdot> TYPE('T\<Rightarrow>'T\<Rightarrow>bool))) \<bullet>
          (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> A \<cdot> B \<bullet> prfT \<bullet> prf1)) \<bullet>
        (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> C \<cdot> D \<bullet> prfT \<bullet> prf2)) \<bullet>
      (meta_eq_to_obj_eq \<cdot> TYPE('T) \<cdot> B \<cdot> D \<bullet> prfT \<bullet> prf3))\<close>,

   (** rewriting on bool: insert proper congruence rules for logical connectives **)

   (* All *)

   \<open>(iffD1 \<cdot> All P \<cdot> All Q \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> All \<cdot> All \<cdot> P \<cdot> Q \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (HOL.refl \<cdot> TYPE('T3) \<cdot> x1 \<bullet> prfT3) \<bullet>
      (ext \<cdot> TYPE('a) \<cdot> TYPE(bool) \<cdot> x2 \<cdot> x3 \<bullet> prfa \<bullet> prfb \<bullet> prf)) \<bullet> prf') \<equiv>
    (allI \<cdot> TYPE('a) \<cdot> Q \<bullet> prfa \<bullet>
      (\<^bold>\<lambda>x.
          iffD1 \<cdot> P x \<cdot> Q x \<bullet> (prf \<cdot> x) \<bullet>
           (spec \<cdot> TYPE('a) \<cdot> P \<cdot> x \<bullet> prfa \<bullet> prf')))\<close>,

   \<open>(iffD2 \<cdot> All P \<cdot> All Q \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> All \<cdot> All \<cdot> P \<cdot> Q \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (HOL.refl \<cdot> TYPE('T3) \<cdot> x1 \<bullet> prfT3) \<bullet>
      (ext \<cdot> TYPE('a) \<cdot> TYPE(bool) \<cdot> x2 \<cdot> x3 \<bullet> prfa \<bullet> prfb \<bullet> prf)) \<bullet> prf') \<equiv>
    (allI \<cdot> TYPE('a) \<cdot> P \<bullet> prfa \<bullet>
      (\<^bold>\<lambda>x.
          iffD2 \<cdot> P x \<cdot> Q x \<bullet> (prf \<cdot> x) \<bullet>
           (spec \<cdot> TYPE('a) \<cdot> Q \<cdot> x \<bullet> prfa \<bullet> prf')))\<close>,

   (* Ex *)

   \<open>(iffD1 \<cdot> Ex P \<cdot> Ex Q \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> Ex \<cdot> Ex \<cdot> P \<cdot> Q \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (HOL.refl \<cdot> TYPE('T3) \<cdot> x1 \<bullet> prfT3) \<bullet>
      (ext \<cdot> TYPE('a) \<cdot> TYPE(bool) \<cdot> x2 \<cdot> x3 \<bullet> prfa \<bullet> prfb \<bullet> prf)) \<bullet> prf') \<equiv>
    (exE \<cdot> TYPE('a) \<cdot> P \<cdot> \<exists>x. Q x \<bullet> prfa \<bullet> prf' \<bullet>
      (\<^bold>\<lambda>x H : P x.
          exI \<cdot> TYPE('a) \<cdot> Q \<cdot> x \<bullet> prfa \<bullet>
           (iffD1 \<cdot> P x \<cdot> Q x \<bullet> (prf \<cdot> x) \<bullet> H)))\<close>,

   \<open>(iffD2 \<cdot> Ex P \<cdot> Ex Q \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> Ex \<cdot> Ex \<cdot> P \<cdot> Q \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (HOL.refl \<cdot> TYPE('T3) \<cdot> x1 \<bullet> prfT3) \<bullet>
      (ext \<cdot> TYPE('a) \<cdot> TYPE(bool) \<cdot> x2 \<cdot> x3 \<bullet> prfa \<bullet> prfb \<bullet> prf)) \<bullet> prf') \<equiv>
    (exE \<cdot> TYPE('a) \<cdot> Q \<cdot> \<exists>x. P x \<bullet> prfa \<bullet> prf' \<bullet>
      (\<^bold>\<lambda>x H : Q x.
          exI \<cdot> TYPE('a) \<cdot> P \<cdot> x \<bullet> prfa \<bullet>
           (iffD2 \<cdot> P x \<cdot> Q x \<bullet> (prf \<cdot> x) \<bullet> H)))\<close>,

   (* \<and> *)

   \<open>(iffD1 \<cdot> A \<and> C \<cdot> B \<and> D \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (cong \<cdot> TYPE('T3) \<cdot> TYPE('T4) \<cdot> (\<and>) \<cdot> (\<and>) \<cdot> A \<cdot> B \<bullet> prfT3 \<bullet> prfT4 \<bullet>
        (HOL.refl \<cdot> TYPE('T5) \<cdot> (\<and>) \<bullet> prfT5) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<equiv>
    (conjI \<cdot> B \<cdot> D \<bullet>
      (iffD1 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> (conjunct1 \<cdot> A \<cdot> C \<bullet> prf3)) \<bullet>
      (iffD1 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet> (conjunct2 \<cdot> A \<cdot> C \<bullet> prf3)))\<close>,

   \<open>(iffD2 \<cdot> A \<and> C \<cdot> B \<and> D \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (cong \<cdot> TYPE('T3) \<cdot> TYPE('T4) \<cdot> (\<and>) \<cdot> (\<and>) \<cdot> A \<cdot> B \<bullet> prfT3 \<bullet> prfT4 \<bullet>
        (HOL.refl \<cdot> TYPE('T5) \<cdot> (\<and>) \<bullet> prfT5) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<equiv>
    (conjI \<cdot> A \<cdot> C \<bullet>
      (iffD2 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> (conjunct1 \<cdot> B \<cdot> D \<bullet> prf3)) \<bullet>
      (iffD2 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet> (conjunct2 \<cdot> B \<cdot> D \<bullet> prf3)))\<close>,

   \<open>(cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (\<and>) A \<cdot> (\<and>) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot> (\<and>) A \<bullet> prfbb)) \<equiv>
    (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (\<and>) A \<cdot> (\<and>) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot>
        ((\<and>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((\<and>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> A \<cdot> A \<bullet>
          prfb \<bullet> prfbb \<bullet>
          (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((\<and>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<bullet>
             (Pure.PClass type_class \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool))) \<bullet>
          (HOL.refl \<cdot> TYPE(bool) \<cdot> A \<bullet> prfb)))\<close>,

   (* \<or> *)

   \<open>(iffD1 \<cdot> A \<or> C \<cdot> B \<or> D \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (cong \<cdot> TYPE('T3) \<cdot> TYPE('T4) \<cdot> (\<or>) \<cdot> (\<or>) \<cdot> A \<cdot> B \<bullet> prfT3 \<bullet> prfT4 \<bullet>
        (HOL.refl \<cdot> TYPE('T5) \<cdot> (\<or>) \<bullet> prfT5) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<equiv>
    (disjE \<cdot> A \<cdot> C \<cdot> B \<or> D \<bullet> prf3 \<bullet>
      (\<^bold>\<lambda>H : A. disjI1 \<cdot> B \<cdot> D \<bullet> (iffD1 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> H)) \<bullet>
      (\<^bold>\<lambda>H : C. disjI2 \<cdot> D \<cdot> B \<bullet> (iffD1 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet> H)))\<close>,

   \<open>(iffD2 \<cdot> A \<or> C \<cdot> B \<or> D \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (cong \<cdot> TYPE('T3) \<cdot> TYPE('T4) \<cdot> (\<or>) \<cdot> (\<or>) \<cdot> A \<cdot> B \<bullet> prfT3 \<bullet> prfT4 \<bullet>
        (HOL.refl \<cdot> TYPE('T5) \<cdot> (\<or>) \<bullet> prfT5) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<equiv>
    (disjE \<cdot> B \<cdot> D \<cdot> A \<or> C \<bullet> prf3 \<bullet>
      (\<^bold>\<lambda>H : B. disjI1 \<cdot> A \<cdot> C \<bullet> (iffD2 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> H)) \<bullet>
      (\<^bold>\<lambda>H : D. disjI2 \<cdot> C \<cdot> A \<bullet> (iffD2 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet> H)))\<close>,

   \<open>(cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (\<or>) A \<cdot> (\<or>) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot> (\<or>) A \<bullet> prfbb)) \<equiv>
    (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (\<or>) A \<cdot> (\<or>) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot>
        ((\<or>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((\<or>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> A \<cdot> A \<bullet>
          prfb \<bullet> prfbb \<bullet>
          (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((\<or>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<bullet>
             (Pure.PClass type_class \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool))) \<bullet>
          (HOL.refl \<cdot> TYPE(bool) \<cdot> A \<bullet> prfb)))\<close>,

   (* \<longrightarrow> *)

   \<open>(iffD1 \<cdot> A \<longrightarrow> C \<cdot> B \<longrightarrow> D \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (cong \<cdot> TYPE('T3) \<cdot> TYPE('T4) \<cdot> (\<longrightarrow>) \<cdot> (\<longrightarrow>) \<cdot> A \<cdot> B \<bullet> prfT3 \<bullet> prfT4 \<bullet>
        (HOL.refl \<cdot> TYPE('T5) \<cdot> (\<longrightarrow>) \<bullet> prfT5) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<equiv>
    (impI \<cdot> B \<cdot> D \<bullet> (\<^bold>\<lambda>H: B. iffD1 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet>
      (mp \<cdot> A \<cdot> C \<bullet> prf3 \<bullet> (iffD2 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> H))))\<close>,

   \<open>(iffD2 \<cdot> A \<longrightarrow> C \<cdot> B \<longrightarrow> D \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (cong \<cdot> TYPE('T3) \<cdot> TYPE('T4) \<cdot> (\<longrightarrow>) \<cdot> (\<longrightarrow>) \<cdot> A \<cdot> B \<bullet> prfT3 \<bullet> prfT4 \<bullet>
        (HOL.refl \<cdot> TYPE('T5) \<cdot> (\<longrightarrow>) \<bullet> prfT5) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<equiv>
    (impI \<cdot> A \<cdot> C \<bullet> (\<^bold>\<lambda>H: A. iffD2 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet>
      (mp \<cdot> B \<cdot> D \<bullet> prf3 \<bullet> (iffD1 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> H))))\<close>,

   \<open>(cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (\<longrightarrow>) A \<cdot> (\<longrightarrow>) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot> (\<longrightarrow>) A \<bullet> prfbb)) \<equiv>
    (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (\<longrightarrow>) A \<cdot> (\<longrightarrow>) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot>
        ((\<longrightarrow>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((\<longrightarrow>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> A \<cdot> A \<bullet>
          prfb \<bullet> prfbb \<bullet>
          (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((\<longrightarrow>) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<bullet>
             (Pure.PClass type_class \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool))) \<bullet>
          (HOL.refl \<cdot> TYPE(bool) \<cdot> A \<bullet> prfb)))\<close>,

   (* \<not> *)

   \<open>(iffD1 \<cdot> \<not> P \<cdot> \<not> Q \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> Not \<cdot> Not \<cdot> P \<cdot> Q \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (HOL.refl \<cdot> TYPE('T3) \<cdot> Not \<bullet> prfT3) \<bullet> prf1) \<bullet> prf2) \<equiv>
    (notI \<cdot> Q \<bullet> (\<^bold>\<lambda>H: Q.
      notE \<cdot> P \<cdot> False \<bullet> prf2 \<bullet> (iffD2 \<cdot> P \<cdot> Q \<bullet> prf1 \<bullet> H)))\<close>,

   \<open>(iffD2 \<cdot> \<not> P \<cdot> \<not> Q \<bullet> (cong \<cdot> TYPE('T1) \<cdot> TYPE('T2) \<cdot> Not \<cdot> Not \<cdot> P \<cdot> Q \<bullet> prfT1 \<bullet> prfT2 \<bullet>
      (HOL.refl \<cdot> TYPE('T3) \<cdot> Not \<bullet> prfT3) \<bullet> prf1) \<bullet> prf2) \<equiv>
    (notI \<cdot> P \<bullet> (\<^bold>\<lambda>H: P.
      notE \<cdot> Q \<cdot> False \<bullet> prf2 \<bullet> (iffD1 \<cdot> P \<cdot> Q \<bullet> prf1 \<bullet> H)))\<close>,

   (* = *)

   \<open>(iffD1 \<cdot> B \<cdot> D \<bullet>
      (iffD1 \<cdot> A = C \<cdot> B = D \<bullet> (cong \<cdot> TYPE(bool) \<cdot> TYPE('T1) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfb \<bullet> prfT1 \<bullet>
        (cong \<cdot> TYPE(bool) \<cdot> TYPE('T2) \<cdot> (=) \<cdot> (=) \<cdot> A \<cdot> B \<bullet> prfb \<bullet> prfT2 \<bullet>
          (HOL.refl \<cdot> TYPE('T3) \<cdot> (=) \<bullet> prfT3) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<bullet> prf4) \<equiv>
    (iffD1 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet>
      (iffD1 \<cdot> A \<cdot> C \<bullet> prf3 \<bullet> (iffD2 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> prf4)))\<close>,

   \<open>(iffD2 \<cdot> B \<cdot> D \<bullet>
      (iffD1 \<cdot> A = C \<cdot> B = D \<bullet> (cong \<cdot> TYPE(bool) \<cdot> TYPE('T1) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfb \<bullet> prfT1 \<bullet>
        (cong \<cdot> TYPE(bool) \<cdot> TYPE('T2) \<cdot> (=) \<cdot> (=) \<cdot> A \<cdot> B \<bullet> prfb \<bullet> prfT2 \<bullet>
          (HOL.refl \<cdot> TYPE('T3) \<cdot> (=) \<bullet> prfT3) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<bullet> prf4) \<equiv>
    (iffD1 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet>
      (iffD2 \<cdot> A \<cdot> C \<bullet> prf3 \<bullet> (iffD2 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet> prf4)))\<close>,

   \<open>(iffD1 \<cdot> A \<cdot> C \<bullet>
      (iffD2 \<cdot> A = C \<cdot> B = D \<bullet> (cong \<cdot> TYPE(bool) \<cdot> TYPE('T1) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfb \<bullet> prfT1 \<bullet>
        (cong \<cdot> TYPE(bool) \<cdot> TYPE('T2) \<cdot> (=) \<cdot> (=) \<cdot> A \<cdot> B \<bullet> prfb \<bullet> prfT2 \<bullet>
          (HOL.refl \<cdot> TYPE('T3) \<cdot> (=) \<bullet> prfT3) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<bullet> prf4)\<equiv>
    (iffD2 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet>
      (iffD1 \<cdot> B \<cdot> D \<bullet> prf3 \<bullet> (iffD1 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> prf4)))\<close>,

   \<open>(iffD2 \<cdot> A \<cdot> C \<bullet>
      (iffD2 \<cdot> A = C \<cdot> B = D \<bullet> (cong \<cdot> TYPE(bool) \<cdot> TYPE('T1) \<cdot> x1 \<cdot> x2 \<cdot> C \<cdot> D \<bullet> prfb \<bullet> prfT1 \<bullet>
        (cong \<cdot> TYPE(bool) \<cdot> TYPE('T2) \<cdot> (=) \<cdot> (=) \<cdot> A \<cdot> B \<bullet> prfb \<bullet> prfT2 \<bullet>
          (HOL.refl \<cdot> TYPE('T3) \<cdot> (=) \<bullet> prfT3) \<bullet> prf1) \<bullet> prf2) \<bullet> prf3) \<bullet> prf4) \<equiv>
    (iffD2 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet>
      (iffD2 \<cdot> B \<cdot> D \<bullet> prf3 \<bullet> (iffD1 \<cdot> C \<cdot> D \<bullet> prf2 \<bullet> prf4)))\<close>,

   \<open>(cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (=) A \<cdot> (=) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot> (=) A \<bullet> prfbb)) \<equiv>
    (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool) \<cdot> (=) A \<cdot> (=) A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prfb \<bullet>
      (cong \<cdot> TYPE(bool) \<cdot> TYPE(bool\<Rightarrow>bool) \<cdot>
        ((=) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((=) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> A \<cdot> A \<bullet>
          prfb \<bullet> prfbb \<bullet>
          (HOL.refl \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool) \<cdot> ((=) :: bool\<Rightarrow>bool\<Rightarrow>bool) \<bullet>
             (Pure.PClass type_class \<cdot> TYPE(bool\<Rightarrow>bool\<Rightarrow>bool))) \<bullet>
          (HOL.refl \<cdot> TYPE(bool) \<cdot> A \<bullet> prfb)))\<close>,

   (** transitivity, reflexivity, and symmetry **)

   \<open>(iffD1 \<cdot> A \<cdot> C \<bullet> (HOL.trans \<cdot> TYPE(bool) \<cdot> A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prf1 \<bullet> prf2) \<bullet> prf3) \<equiv>
    (iffD1 \<cdot> B \<cdot> C \<bullet> prf2 \<bullet> (iffD1 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> prf3))\<close>,

   \<open>(iffD2 \<cdot> A \<cdot> C \<bullet> (HOL.trans \<cdot> TYPE(bool) \<cdot> A \<cdot> B \<cdot> C \<bullet> prfb \<bullet> prf1 \<bullet> prf2) \<bullet> prf3) \<equiv>
    (iffD2 \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> (iffD2 \<cdot> B \<cdot> C \<bullet> prf2 \<bullet> prf3))\<close>,

   \<open>(iffD1 \<cdot> A \<cdot> A \<bullet> (HOL.refl \<cdot> TYPE(bool) \<cdot> A \<bullet> prfb) \<bullet> prf) \<equiv> prf\<close>,

   \<open>(iffD2 \<cdot> A \<cdot> A \<bullet> (HOL.refl \<cdot> TYPE(bool) \<cdot> A \<bullet> prfb) \<bullet> prf) \<equiv> prf\<close>,

   \<open>(iffD1 \<cdot> A \<cdot> B \<bullet> (sym \<cdot> TYPE(bool) \<cdot> B \<cdot> A \<bullet> prfb \<bullet> prf)) \<equiv> (iffD2 \<cdot> B \<cdot> A \<bullet> prf)\<close>,

   \<open>(iffD2 \<cdot> A \<cdot> B \<bullet> (sym \<cdot> TYPE(bool) \<cdot> B \<cdot> A \<bullet> prfb \<bullet> prf)) \<equiv> (iffD1 \<cdot> B \<cdot> A \<bullet> prf)\<close>,

   (** normalization of HOL proofs **)

   \<open>(mp \<cdot> A \<cdot> B \<bullet> (impI \<cdot> A \<cdot> B \<bullet> prf)) \<equiv> prf\<close>,

   \<open>(impI \<cdot> A \<cdot> B \<bullet> (mp \<cdot> A \<cdot> B \<bullet> prf)) \<equiv> prf\<close>,

   \<open>(spec \<cdot> TYPE('a) \<cdot> P \<cdot> x \<bullet> prfa \<bullet> (allI \<cdot> TYPE('a) \<cdot> P \<bullet> prfa \<bullet> prf)) \<equiv> prf \<cdot> x\<close>,

   \<open>(allI \<cdot> TYPE('a) \<cdot> P \<bullet> prfa \<bullet> (\<^bold>\<lambda>x::'a. spec \<cdot> TYPE('a) \<cdot> P \<cdot> x \<bullet> prfa \<bullet> prf)) \<equiv> prf\<close>,

   \<open>(exE \<cdot> TYPE('a) \<cdot> P \<cdot> Q \<bullet> prfa \<bullet> (exI \<cdot> TYPE('a) \<cdot> P \<cdot> x \<bullet> prfa \<bullet> prf1) \<bullet> prf2) \<equiv> (prf2 \<cdot> x \<bullet> prf1)\<close>,

   \<open>(exE \<cdot> TYPE('a) \<cdot> P \<cdot> Q \<bullet> prfa \<bullet> prf \<bullet> (exI \<cdot> TYPE('a) \<cdot> P \<bullet> prfa)) \<equiv> prf\<close>,

   \<open>(disjE \<cdot> P \<cdot> Q \<cdot> R \<bullet> (disjI1 \<cdot> P \<cdot> Q \<bullet> prf1) \<bullet> prf2 \<bullet> prf3) \<equiv> (prf2 \<bullet> prf1)\<close>,

   \<open>(disjE \<cdot> P \<cdot> Q \<cdot> R \<bullet> (disjI2 \<cdot> Q \<cdot> P \<bullet> prf1) \<bullet> prf2 \<bullet> prf3) \<equiv> (prf3 \<bullet> prf1)\<close>,

   \<open>(conjunct1 \<cdot> P \<cdot> Q \<bullet> (conjI \<cdot> P \<cdot> Q \<bullet> prf1 \<bullet> prf2)) \<equiv> prf1\<close>,

   \<open>(conjunct2 \<cdot> P \<cdot> Q \<bullet> (conjI \<cdot> P \<cdot> Q \<bullet> prf1 \<bullet> prf2)) \<equiv> prf2\<close>,

   \<open>(iffD1 \<cdot> A \<cdot> B \<bullet> (iffI \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> prf2)) \<equiv> prf1\<close>,

   \<open>(iffD2 \<cdot> A \<cdot> B \<bullet> (iffI \<cdot> A \<cdot> B \<bullet> prf1 \<bullet> prf2)) \<equiv> prf2\<close>];


(** Replace congruence rules by substitution rules **)

fun strip_cong ps (PThm ({thm_name = (("HOL.cong", 0), _), ...}, _) % _ % _ % SOME x % SOME y %%
      prfa %% prfT %% prf1 %% prf2) = strip_cong (((x, y), (prf2, prfa)) :: ps) prf1
  | strip_cong ps (PThm ({thm_name = (("HOL.refl", 0), _), ...}, _) % SOME f %% _) = SOME (f, ps)
  | strip_cong _ _ = NONE;

val subst_prf = Proofterm.any_head_of (Thm.proof_of @{thm subst});
val sym_prf = Proofterm.any_head_of (Thm.proof_of @{thm sym});

fun make_subst Ts prf xs (_, []) = prf
  | make_subst Ts prf xs (f, ((x, y), (prf', clprf)) :: ps) =
      let val T = fastype_of1 (Ts, x)
      in if x aconv y then make_subst Ts prf (xs @ [x]) (f, ps)
        else Proofterm.change_types (SOME [T]) subst_prf %> x %> y %>
          Abs ("z", T, list_comb (incr_boundvars 1 f,
            map (incr_boundvars 1) xs @ Bound 0 ::
            map (incr_boundvars 1 o snd o fst) ps)) %% clprf %% prf' %%
          make_subst Ts prf (xs @ [x]) (f, ps)
      end;

fun make_sym Ts ((x, y), (prf, clprf)) =
  ((y, x),
    (Proofterm.change_types (SOME [fastype_of1 (Ts, x)]) sym_prf %> x %> y %% clprf %% prf, clprf));

fun mk_AbsP P t = AbsP ("H", Option.map HOLogic.mk_Trueprop P, t);

fun elim_cong_aux Ts (PThm ({thm_name = (("HOL.iffD1", 0), _), ...}, _) % _ % _ %% prf1 %% prf2) =
      Option.map (make_subst Ts prf2 []) (strip_cong [] prf1)
  | elim_cong_aux Ts (PThm ({thm_name = (("HOL.iffD1", 0), _), ...}, _) % P % _ %% prf) =
      Option.map (mk_AbsP P o make_subst Ts (PBound 0) [])
        (strip_cong [] (Proofterm.incr_boundvars 1 0 prf))
  | elim_cong_aux Ts (PThm ({thm_name = (("HOL.iffD2", 0), _), ...}, _) % _ % _ %% prf1 %% prf2) =
      Option.map (make_subst Ts prf2 [] o
        apsnd (map (make_sym Ts))) (strip_cong [] prf1)
  | elim_cong_aux Ts (PThm ({thm_name = (("HOL.iffD2", 0), _), ...}, _) % _ % P %% prf) =
      Option.map (mk_AbsP P o make_subst Ts (PBound 0) [] o
        apsnd (map (make_sym Ts))) (strip_cong [] (Proofterm.incr_boundvars 1 0 prf))
  | elim_cong_aux _ _ = NONE;

fun elim_cong Ts hs prf = Option.map (rpair Proofterm.no_skel) (elim_cong_aux Ts prf);

end;
