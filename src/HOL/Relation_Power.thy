(*  Title:      HOL/Relation_Power.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen
*)

header{*Powers of Relations and Functions*}

theory Relation_Power
imports Nat
begin

instance
  set :: (type) power ..  
      --{* only type @{typ "('a * 'a) set"} should be in class @{text power}!*}

(*R^n = R O ... O R, the n-fold composition of R*)
primrec (relpow)
  "R^0 = Id"
  "R^(Suc n) = R O (R^n)"


instance
  fun :: (type, type) power ..
      --{* only type @{typ "'a => 'a"} should be in class @{text power}!*}

(*f^n = f o ... o f, the n-fold composition of f*)
primrec (funpow)
  "f^0 = id"
  "f^(Suc n) = f o (f^n)"

text{*WARNING: due to the limits of Isabelle's type classes, exponentiation on
functions and relations has too general a domain, namely @{typ "('a * 'b)set"}
and @{typ "'a => 'b"}.  Explicit type constraints may therefore be necessary.
For example, @{term "range(f^n) = A"} and @{term "Range(R^n) = B"} need
constraints.*}

lemma funpow_add: "f ^ (m+n) = f^m o f^n"
by(induct m) simp_all

lemma funpow_swap1: "f((f^n) x) = (f^n)(f x)"
proof -
  have "f((f^n) x) = (f^(n+1)) x" by simp
  also have "\<dots>  = (f^n o f^1) x" by (simp only:funpow_add)
  also have "\<dots> = (f^n)(f x)" by simp
  finally show ?thesis .
qed

lemma rel_pow_1: "!!R:: ('a*'a)set. R^1 = R"
by simp
declare rel_pow_1 [simp]

lemma rel_pow_0_I: "(x,x) : R^0"
by simp

lemma rel_pow_Suc_I: "[| (x,y) : R^n; (y,z):R |] ==> (x,z):R^(Suc n)"
apply (auto ); 
done

lemma rel_pow_Suc_I2 [rule_format]:
     "\<forall>z. (x,y) : R --> (y,z):R^n -->  (x,z):R^(Suc n)"
apply (induct_tac "n", simp_all)
apply blast
done

lemma rel_pow_0_E: "[| (x,y) : R^0; x=y ==> P |] ==> P"
by simp

lemma rel_pow_Suc_E: 
     "[| (x,z) : R^(Suc n);  !!y. [| (x,y) : R^n; (y,z) : R |] ==> P |] ==> P"
by auto

lemma rel_pow_E: 
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;         
        !!y m. [| n = Suc m; (x,y) : R^m; (y,z) : R |] ==> P   
     |] ==> P"
by (case_tac "n", auto)

lemma rel_pow_Suc_D2 [rule_format]:
     "\<forall>x z. (x,z):R^(Suc n) --> (\<exists>y. (x,y):R & (y,z):R^n)"
apply (induct_tac "n")
apply (blast intro: rel_pow_0_I elim: rel_pow_0_E rel_pow_Suc_E)
apply (blast intro: rel_pow_Suc_I elim: rel_pow_0_E rel_pow_Suc_E)
done


lemma rel_pow_Suc_D2':
     "\<forall>x y z. (x,y) : R^n & (y,z) : R --> (\<exists>w. (x,w) : R & (w,z) : R^n)"
by (induct_tac "n", simp_all, blast)

lemma rel_pow_E2: 
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;         
        !!y m. [| n = Suc m; (x,y) : R; (y,z) : R^m |] ==> P   
     |] ==> P"
apply (case_tac "n", simp) 
apply (cut_tac n=nat and R=R in rel_pow_Suc_D2', simp, blast) 
done

lemma rtrancl_imp_UN_rel_pow: "!!p. p:R^* ==> p : (UN n. R^n)"
apply (simp only: split_tupled_all)
apply (erule rtrancl_induct)
apply (blast intro: rel_pow_0_I rel_pow_Suc_I)+
done

lemma rel_pow_imp_rtrancl: "!!p. p:R^n ==> p:R^*"
apply (simp only: split_tupled_all)
apply (induct "n")
apply (blast intro: rtrancl_refl elim: rel_pow_0_E)
apply (blast elim: rel_pow_Suc_E intro: rtrancl_into_rtrancl)
done

lemma rtrancl_is_UN_rel_pow: "R^* = (UN n. R^n)"
by (blast intro: rtrancl_imp_UN_rel_pow rel_pow_imp_rtrancl)


lemma single_valued_rel_pow [rule_format]:
     "!!r::('a * 'a)set. single_valued r ==> single_valued (r^n)"
apply (rule single_valuedI)
apply (induct_tac "n", simp)
apply (fast dest: single_valuedD elim: rel_pow_Suc_E)
done

ML
{*
val funpow_add = thm "funpow_add";
val rel_pow_1 = thm "rel_pow_1";
val rel_pow_0_I = thm "rel_pow_0_I";
val rel_pow_Suc_I = thm "rel_pow_Suc_I";
val rel_pow_Suc_I2 = thm "rel_pow_Suc_I2";
val rel_pow_0_E = thm "rel_pow_0_E";
val rel_pow_Suc_E = thm "rel_pow_Suc_E";
val rel_pow_E = thm "rel_pow_E";
val rel_pow_Suc_D2 = thm "rel_pow_Suc_D2";
val rel_pow_Suc_D2 = thm "rel_pow_Suc_D2";
val rel_pow_E2 = thm "rel_pow_E2";
val rtrancl_imp_UN_rel_pow = thm "rtrancl_imp_UN_rel_pow";
val rel_pow_imp_rtrancl = thm "rel_pow_imp_rtrancl";
val rtrancl_is_UN_rel_pow = thm "rtrancl_is_UN_rel_pow";
val single_valued_rel_pow = thm "single_valued_rel_pow";
*}

end
