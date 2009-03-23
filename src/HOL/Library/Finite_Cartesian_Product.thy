(* Title:      HOL/Library/Finite_Cartesian_Product
   Author:     Amine Chaieb, University of Cambridge
*)

header {* Definition of finite Cartesian product types. *}

theory Finite_Cartesian_Product
imports Main (*FIXME: ATP_Linkup is only needed for metis at a few places. We could dispense of that by changing the proofs.*)
begin

definition hassize (infixr "hassize" 12) where
  "(S hassize n) = (finite S \<and> card S = n)"

lemma hassize_image_inj: assumes f: "inj_on f S" and S: "S hassize n"
  shows "f ` S hassize n"
  using f S card_image[OF f]
    by (simp add: hassize_def inj_on_def)


subsection {* Finite Cartesian products, with indexing and lambdas. *}

typedef (open Cart)
  ('a, 'b) "^" (infixl "^" 15)
    = "UNIV :: ('b \<Rightarrow> 'a) set"
  morphisms Cart_nth Cart_lambda ..

notation Cart_nth (infixl "$" 90)

notation (xsymbols) Cart_lambda (binder "\<chi>" 10)

lemma stupid_ext: "(\<forall>x. f x = g x) \<longleftrightarrow> (f = g)"
  apply auto
  apply (rule ext)
  apply auto
  done

lemma Cart_eq: "((x:: 'a ^ 'b) = y) \<longleftrightarrow> (\<forall>i. x$i = y$i)"
  by (simp add: Cart_nth_inject [symmetric] expand_fun_eq)

lemma Cart_lambda_beta [simp]: "Cart_lambda g $ i = g i"
  by (simp add: Cart_lambda_inverse)

lemma Cart_lambda_unique:
  fixes f :: "'a ^ 'b"
  shows "(\<forall>i. f$i = g i) \<longleftrightarrow> Cart_lambda g = f"
  by (auto simp add: Cart_eq)

lemma Cart_lambda_eta: "(\<chi> i. (g$i)) = g"
  by (simp add: Cart_eq)

text{* A non-standard sum to "paste" Cartesian products. *}

definition pastecart :: "'a ^ 'm \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ ('m + 'n)" where
  "pastecart f g = (\<chi> i. case i of Inl a \<Rightarrow> f$a | Inr b \<Rightarrow> g$b)"

definition fstcart:: "'a ^('m + 'n) \<Rightarrow> 'a ^ 'm" where
  "fstcart f = (\<chi> i. (f$(Inl i)))"

definition sndcart:: "'a ^('m + 'n) \<Rightarrow> 'a ^ 'n" where
  "sndcart f = (\<chi> i. (f$(Inr i)))"

lemma nth_pastecart_Inl [simp]: "pastecart f g $ Inl a = f$a"
  unfolding pastecart_def by simp

lemma nth_pastecart_Inr [simp]: "pastecart f g $ Inr b = g$b"
  unfolding pastecart_def by simp

lemma nth_fstcart [simp]: "fstcart f $ i = f $ Inl i"
  unfolding fstcart_def by simp

lemma nth_sndtcart [simp]: "sndcart f $ i = f $ Inr i"
  unfolding sndcart_def by simp

lemma finite_sum_image: "(UNIV::('a + 'b) set) = range Inl \<union> range Inr"
by (auto, case_tac x, auto)

lemma fstcart_pastecart: "fstcart (pastecart (x::'a ^'m ) (y:: 'a ^ 'n)) = x"
  by (simp add: Cart_eq)

lemma sndcart_pastecart: "sndcart (pastecart (x::'a ^'m ) (y:: 'a ^ 'n)) = y"
  by (simp add: Cart_eq)

lemma pastecart_fst_snd: "pastecart (fstcart z) (sndcart z) = z"
  by (simp add: Cart_eq pastecart_def fstcart_def sndcart_def split: sum.split)

lemma pastecart_eq: "(x = y) \<longleftrightarrow> (fstcart x = fstcart y) \<and> (sndcart x = sndcart y)"
  using pastecart_fst_snd[of x] pastecart_fst_snd[of y] by metis

lemma forall_pastecart: "(\<forall>p. P p) \<longleftrightarrow> (\<forall>x y. P (pastecart x y))"
  by (metis pastecart_fst_snd fstcart_pastecart sndcart_pastecart)

lemma exists_pastecart: "(\<exists>p. P p)  \<longleftrightarrow> (\<exists>x y. P (pastecart x y))"
  by (metis pastecart_fst_snd fstcart_pastecart sndcart_pastecart)

end
