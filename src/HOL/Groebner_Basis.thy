(*  Title:      HOL/Groebner_Basis.thy
    Author:     Amine Chaieb, TU Muenchen
*)

section \<open>Groebner bases\<close>

theory Groebner_Basis
imports Semiring_Normalization Parity
begin

subsection \<open>Groebner Bases\<close>

lemmas bool_simps = simp_thms(1-34) \<comment> \<open>FIXME move to @{theory HOL}\<close>

lemma nnf_simps: \<comment> \<open>FIXME shadows fact binding in @{theory HOL}\<close>
  "(\<not>(P \<and> Q)) = (\<not>P \<or> \<not>Q)" "(\<not>(P \<or> Q)) = (\<not>P \<and> \<not>Q)"
  "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
  "(P = Q) = ((P \<and> Q) \<or> (\<not>P \<and> \<not> Q))" "(\<not> \<not>(P)) = P"
  by blast+

lemma dnf:
  "(P \<and> (Q \<or> R)) = ((P\<and>Q) \<or> (P\<and>R))"
  "((Q \<or> R) \<and> P) = ((Q\<and>P) \<or> (R\<and>P))"
  "(P \<and> Q) = (Q \<and> P)"
  "(P \<or> Q) = (Q \<or> P)"
  by blast+

lemmas weak_dnf_simps = dnf bool_simps

lemma PFalse:
    "P \<equiv> False \<Longrightarrow> \<not> P"
    "\<not> P \<Longrightarrow> (P \<equiv> False)"
  by auto

named_theorems algebra "pre-simplification rules for algebraic methods"
ML_file "Tools/groebner.ML"

method_setup algebra = \<open>
  let
    fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()
    val addN = "add"
    val delN = "del"
    val any_keyword = keyword addN || keyword delN
    val thms = Scan.repeats (Scan.unless any_keyword Attrib.multi_thm);
  in
    Scan.optional (keyword addN |-- thms) [] --
     Scan.optional (keyword delN |-- thms) [] >>
    (fn (add_ths, del_ths) => fn ctxt =>
      SIMPLE_METHOD' (Groebner.algebra_tac add_ths del_ths ctxt))
  end
\<close> "solve polynomial equations over (semi)rings and ideal membership problems using Groebner bases"

declare dvd_def[algebra]
declare mod_eq_0_iff_dvd[algebra]
declare mod_div_trivial[algebra]
declare mod_mod_trivial[algebra]
declare div_by_0[algebra]
declare mod_by_0[algebra]
declare mult_div_mod_eq[algebra]
declare div_minus_minus[algebra]
declare mod_minus_minus[algebra]
declare div_minus_right[algebra]
declare mod_minus_right[algebra]
declare div_0[algebra]
declare mod_0[algebra]
declare mod_by_1[algebra]
declare div_by_1[algebra]
declare mod_minus1_right[algebra]
declare div_minus1_right[algebra]
declare mod_mult_self2_is_0[algebra]
declare mod_mult_self1_is_0[algebra]
declare zmod_eq_0_iff[algebra]
declare dvd_0_left_iff[algebra]
declare zdvd1_eq[algebra]
declare mod_eq_dvd_iff[algebra]
declare nat_mod_eq_iff[algebra]

context semiring_parity
begin

declare even_mult_iff [algebra]
declare even_power [algebra]

end

context ring_parity
begin

declare even_minus [algebra]

end

declare even_Suc [algebra]
declare even_diff_nat [algebra]

end
