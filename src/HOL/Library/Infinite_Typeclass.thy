(*  Title:      HOL/Library/Infinite_Typeclass.thy
*)

section \<open>Infinite Type Class\<close>
text \<open>The type class of infinite sets (orginally from the Incredible Proof Machine)\<close>

theory Infinite_Typeclass
  imports Complex_Main
begin

class infinite =
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

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
