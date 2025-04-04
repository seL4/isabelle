(*  Title:      HOL/Library/Infinite_Typeclass.thy
*)

section \<open>Infinite Type Class\<close>
text \<open>The type class of infinite sets (orginally from the Incredible Proof Machine)\<close>

theory Infinite_Typeclass
  imports Complex_Main
begin

class infinite =
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

begin

lemma arb_element: "finite Y \<Longrightarrow> \<exists>x :: 'a. x \<notin> Y"
  using ex_new_if_finite infinite_UNIV
  by blast

lemma arb_finite_subset: "finite Y \<Longrightarrow> \<exists>X :: 'a set. Y \<inter> X = {} \<and> finite X \<and> n \<le> card X"
proof -
  assume fin: "finite Y"
  then obtain X where "X \<subseteq> UNIV - Y" "finite X" "n \<le> card X"
    using infinite_UNIV
    by (metis Compl_eq_Diff_UNIV finite_compl infinite_arbitrarily_large order_refl)
  then show ?thesis
    by auto
qed

lemma arb_inj_on_finite_infinite: "finite(A :: 'b set) \<Longrightarrow> \<exists>f :: 'b \<Rightarrow> 'a. inj_on f A"
by (meson arb_finite_subset card_le_inj infinite_imp_nonempty)

lemma arb_countable_map: "finite Y \<Longrightarrow> \<exists>f :: (nat \<Rightarrow> 'a). inj f \<and> range f \<subseteq> UNIV - Y"
  using infinite_UNIV
  by (auto simp: infinite_countable_subset)

end

instance nat :: infinite
  by (intro_classes) simp

instance int :: infinite
  by (intro_classes) simp

instance rat :: infinite
proof
  show "infinite (UNIV::rat set)"
  by (simp add: infinite_UNIV_char_0)
qed

instance real :: infinite
proof
  show "infinite (UNIV::real set)"
  by (simp add: infinite_UNIV_char_0)
qed

instance complex :: infinite
proof
  show "infinite (UNIV::complex set)"
  by (simp add: infinite_UNIV_char_0)
qed

instance option :: (infinite) infinite
  by intro_classes (simp add: infinite_UNIV)

instance prod :: (infinite, type) infinite
  by intro_classes (simp add: finite_prod infinite_UNIV)

instance list :: (type) infinite
  by intro_classes (simp add: infinite_UNIV_listI)

end
