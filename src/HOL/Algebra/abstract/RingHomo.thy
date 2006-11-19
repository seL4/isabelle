(*
    Ring homomorphism
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

header {* Ring homomorphism *}

theory RingHomo imports Ring2 begin

definition
  homo :: "('a::ring => 'b::ring) => bool" where
  "homo f \<longleftrightarrow> (ALL a b. f (a + b) = f a + f b &
                                   f (a * b) = f a * f b) &
                                   f 1 = 1"


lemma homoI:
  "!! f. [| !! a b. f (a + b) = f a + f b; !! a b. f (a * b) = f a * f b;  
            f 1 = 1 |] ==> homo f"
  unfolding homo_def by blast

lemma homo_add [simp]: "!! f. homo f ==> f (a + b) = f a + f b"
  unfolding homo_def by blast

lemma homo_mult [simp]: "!! f. homo f ==> f (a * b) = f a * f b"
  unfolding homo_def by blast

lemma homo_one [simp]: "!! f. homo f ==> f 1 = 1"
  unfolding homo_def by blast

lemma homo_zero [simp]: "!! f::('a::ring=>'b::ring). homo f ==> f 0 = 0"
  apply (rule_tac a = "f 0" in a_lcancel)
  apply (simp (no_asm_simp) add: homo_add [symmetric])
  done

lemma homo_uminus [simp]:
  "!! f::('a::ring=>'b::ring). homo f ==> f (-a) = - f a"
  apply (rule_tac a = "f a" in a_lcancel)
  apply (frule homo_zero)
  apply (simp (no_asm_simp) add: homo_add [symmetric])
  done

lemma homo_power [simp]: "!! f::('a::ring=>'b::ring). homo f ==> f (a ^ n) = f a ^ n"
  apply (induct_tac n)
   apply (drule homo_one)
   apply simp
  apply (drule_tac a = "a^n" and b = "a" in homo_mult)
  apply simp
  done

lemma homo_SUM [simp]:
  "!! f::('a::ring=>'b::ring).  
    homo f ==> f (setsum g {..n::nat}) = setsum (f o g) {..n}"
  apply (induct_tac n)
   apply simp
  apply simp
  done

lemma id_homo [simp]: "homo (%x. x)"
  by (blast intro!: homoI)

end
