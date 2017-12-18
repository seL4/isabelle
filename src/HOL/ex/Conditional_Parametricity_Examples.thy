(*  Title:    HOL/ex/Conditional_Parametricity_Examples.thy
    Author:   Jan Gilcher, Andreas Lochbihler, Dmitriy Traytel, ETH Zürich

Examples for the parametric_constant command
*)

theory Conditional_Parametricity_Examples
  imports "HOL-Library.Conditional_Parametricity"
begin

definition "bar x xs = rev (x # xs)"
parametric_constant bar_def

definition bar2 where "bar2 = bar"
parametric_constant bar2_def

parametric_constant bar_thm[transfer_rule]: bar_def
parametric_constant bar2_thm1: bar2_def

definition "t1 y x = zip x y"
parametric_constant t1_thm: t1_def

definition "t2 f x = f (rev x)"
parametric_constant t2_thm: t2_def

definition "t3 xs = rev (rev (xs :: 'b list))"
parametric_constant t3_thm: t3_def

definition "t4 f x = rev (f x (f x (rev x)))"
parametric_constant t4_thm: t4_def

definition "t5 x y = zip x (rev y)"
parametric_constant t5_thm: t5_def

(* Conditional Parametricity*)

definition "t6_1 x y = inf y x"
parametric_constant t6_1_thm: t6_1_def

definition "t6_2 x y = sup y x"
parametric_constant t6_2_thm: t6_2_def

definition "t6_3 x z y = sup (inf x y) z"
parametric_constant t6_3_thm: t6_3_def

definition "t6_4 x xs y = map (sup (inf y x)) xs"
parametric_constant t6_4_thm: t6_4_def

definition "t7 x y = (y = x)"
parametric_constant t7_thm: t7_def

definition "t8 x y = ((x=y) \<and> (y=x))"
parametric_constant t8_thm: t8_def

(* Definition via primrec*)
primrec delete where
  "delete _ [] = []"
| "delete x (y # ys) = (if x = y then ys else y # (delete x ys))"
parametric_constant delete_thm: delete_def

definition "foo f x y = (if f x = f y then x else sup y x)"
parametric_constant foo_parametricity: foo_def

end