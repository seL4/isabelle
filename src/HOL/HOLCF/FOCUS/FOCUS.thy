(*  Title:      HOL/HOLCF/FOCUS/FOCUS.thy
    Author:     David von Oheimb, TU Muenchen
*)

section \<open>Top level of FOCUS\<close>

theory FOCUS
imports Fstream
begin

lemma ex_eqI [intro!]: "\<exists>xx. x = xx"
by auto

lemma ex2_eqI [intro!]: "\<exists>xx yy. x = xx & y = yy"
by auto

lemma eq_UU_symf: "(UU = f x) = (f x = UU)"
by auto

lemma fstream_exhaust_slen_eq: "(#x \<noteq> 0) = (\<exists>a y. x = a~> y)"
by (simp add: slen_empty_eq fstream_exhaust_eq)

lemmas [simp] =
  slen_less_1_eq fstream_exhaust_slen_eq
  slen_fscons_eq slen_fscons_less_eq Suc_ile_eq

declare strictI [elim]

end
