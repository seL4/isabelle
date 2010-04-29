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

notation
  Cart_nth (infixl "$" 90) and
  Cart_lambda (binder "\<chi>" 10)

(*
  Translate "'b ^ 'n" into "'b ^ ('n :: finite)". When 'n has already more than
  the finite type class write "cart 'b 'n"
*)

syntax "_finite_cart" :: "type \<Rightarrow> type \<Rightarrow> type" ("(_ ^/ _)" [15, 16] 15)

parse_translation {*
let
  fun cart t u = Syntax.const @{type_syntax cart} $ t $ u;
  fun finite_cart_tr [t, u as Free (x, _)] =
        if Syntax.is_tid x then
          cart t (Syntax.const @{syntax_const "_ofsort"} $ u $ Syntax.const @{class_syntax finite})
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

end
