(*  Title:      HOL/Multivariate_Analysis/Finite_Cartesian_Product.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* Definition of finite Cartesian product types. *}

theory Finite_Cartesian_Product
imports Main
begin

subsection {* Finite Cartesian products, with indexing and lambdas. *}

typedef (open Cart)
  ('a, 'b) cart = "UNIV :: (('b::finite) \<Rightarrow> 'a) set"
  morphisms Cart_nth Cart_lambda ..

notation Cart_nth (infixl "$" 90)

notation (xsymbols) Cart_lambda (binder "\<chi>" 10)

(*
  Translate "'b ^ 'n" into "'b ^ ('n :: finite)". When 'n has already more than
  the finite type class write "cart 'b 'n"
*)

syntax "_finite_cart" :: "type \<Rightarrow> type \<Rightarrow> type" ("(_ ^/ _)" [15, 16] 15)

parse_translation {*
let
  fun cart t u = Syntax.const @{type_name cart} $ t $ u;   (* FIXME @{type_syntax} *)
  fun finite_cart_tr [t, u as Free (x, _)] =
        if Syntax.is_tid x then
          cart t (Syntax.const @{syntax_const "_ofsort"} $ u $ Syntax.const (hd @{sort finite}))
        else cart t u
    | finite_cart_tr [t, u] = cart t u
in
  [(@{syntax_const "_finite_cart"}, finite_cart_tr)]
end
*}

lemma stupid_ext: "(\<forall>x. f x = g x) \<longleftrightarrow> (f = g)"
  by (auto intro: ext)

lemma Cart_eq: "(x = y) \<longleftrightarrow> (\<forall>i. x$i = y$i)"
  by (simp add: Cart_nth_inject [symmetric] expand_fun_eq)

lemma Cart_lambda_beta [simp]: "Cart_lambda g $ i = g i"
  by (simp add: Cart_lambda_inverse)

lemma Cart_lambda_unique: "(\<forall>i. f$i = g i) \<longleftrightarrow> Cart_lambda g = f"
  by (auto simp add: Cart_eq)

lemma Cart_lambda_eta: "(\<chi> i. (g$i)) = g"
  by (simp add: Cart_eq)

text{* A non-standard sum to "paste" Cartesian products. *}

definition "pastecart f g = (\<chi> i. case i of Inl a \<Rightarrow> f$a | Inr b \<Rightarrow> g$b)"
definition "fstcart f = (\<chi> i. (f$(Inl i)))"
definition "sndcart f = (\<chi> i. (f$(Inr i)))"

lemma nth_pastecart_Inl [simp]: "pastecart f g $ Inl a = f$a"
  unfolding pastecart_def by simp

lemma nth_pastecart_Inr [simp]: "pastecart f g $ Inr b = g$b"
  unfolding pastecart_def by simp

lemma nth_fstcart [simp]: "fstcart f $ i = f $ Inl i"
  unfolding fstcart_def by simp

lemma nth_sndtcart [simp]: "sndcart f $ i = f $ Inr i"
  unfolding sndcart_def by simp

lemma finite_sum_image: "(UNIV::('a + 'b) set) = range Inl \<union> range Inr"
  apply auto
  apply (case_tac x)
   apply auto
  done

lemma fstcart_pastecart[simp]: "fstcart (pastecart x y) = x"
  by (simp add: Cart_eq)

lemma sndcart_pastecart[simp]: "sndcart (pastecart x y) = y"
  by (simp add: Cart_eq)

lemma pastecart_fst_snd[simp]: "pastecart (fstcart z) (sndcart z) = z"
  by (simp add: Cart_eq pastecart_def fstcart_def sndcart_def split: sum.split)

lemma pastecart_eq: "(x = y) \<longleftrightarrow> (fstcart x = fstcart y) \<and> (sndcart x = sndcart y)"
  using pastecart_fst_snd[of x] pastecart_fst_snd[of y] by metis

lemma forall_pastecart: "(\<forall>p. P p) \<longleftrightarrow> (\<forall>x y. P (pastecart x y))"
  by (metis pastecart_fst_snd)

lemma exists_pastecart: "(\<exists>p. P p) \<longleftrightarrow> (\<exists>x y. P (pastecart x y))"
  by (metis pastecart_fst_snd)

end
