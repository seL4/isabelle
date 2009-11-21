(*  Title:      FOL/ex/LocaleTest.thy
    Author:     Clemens Ballarin, TU Muenchen

Test environment for the locale implementation.
*)

theory LocaleTest
imports FOL
begin

typedecl int arities int :: "term"
consts plus :: "int => int => int" (infixl "+" 60)
  zero :: int ("0")
  minus :: "int => int" ("- _")

axioms
  int_assoc: "(x + y::int) + z = x + (y + z)"
  int_zero: "0 + x = x"
  int_minus: "(-x) + x = 0"
  int_minus2: "-(-x) = x"

section {* Inference of parameter types *}

locale param1 = fixes p
print_locale! param1

locale param2 = fixes p :: 'b
print_locale! param2

(*
locale param_top = param2 r for r :: "'b :: {}"
  Fails, cannot generalise parameter.
*)

locale param3 = fixes p (infix ".." 50)
print_locale! param3

locale param4 = fixes p :: "'a => 'a => 'a" (infix ".." 50)
print_locale! param4


subsection {* Incremental type constraints *}

locale constraint1 =
  fixes  prod (infixl "**" 65)
  assumes l_id: "x ** y = x"
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"
print_locale! constraint1

locale constraint2 =
  fixes p and q
  assumes "p = q"
print_locale! constraint2


section {* Inheritance *}

locale semi =
  fixes prod (infixl "**" 65)
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"
print_locale! semi thm semi_def

locale lgrp = semi +
  fixes one and inv
  assumes lone: "one ** x = x"
    and linv: "inv(x) ** x = one"
print_locale! lgrp thm lgrp_def lgrp_axioms_def

locale add_lgrp = semi "op ++" for sum (infixl "++" 60) +
  fixes zero and neg
  assumes lzero: "zero ++ x = x"
    and lneg: "neg(x) ++ x = zero"
print_locale! add_lgrp thm add_lgrp_def add_lgrp_axioms_def

locale rev_lgrp = semi "%x y. y ++ x" for sum (infixl "++" 60)
print_locale! rev_lgrp thm rev_lgrp_def

locale hom = f: semi f + g: semi g for f and g
print_locale! hom thm hom_def

locale perturbation = semi + d: semi "%x y. delta(x) ** delta(y)" for delta
print_locale! perturbation thm perturbation_def

locale pert_hom = d1: perturbation f d1 + d2: perturbation f d2 for f d1 d2
print_locale! pert_hom thm pert_hom_def

text {* Alternative expression, obtaining nicer names in @{text "semi f"}. *}
locale pert_hom' = semi f + d1: perturbation f d1 + d2: perturbation f d2 for f d1 d2
print_locale! pert_hom' thm pert_hom'_def


section {* Syntax declarations *}

locale logic =
  fixes land (infixl "&&" 55)
    and lnot ("-- _" [60] 60)
  assumes assoc: "(x && y) && z = x && (y && z)"
    and notnot: "-- (-- x) = x"
begin

definition lor (infixl "||" 50) where
  "x || y = --(-- x && -- y)"

end
print_locale! logic

locale use_decl = logic + semi "op ||"
print_locale! use_decl thm use_decl_def

locale extra_type =
  fixes a :: 'a
    and P :: "'a => 'b => o"
begin

definition test :: "'a => o" where
  "test(x) <-> (ALL b. P(x, b))"

end

term extra_type.test thm extra_type.test_def

interpretation var?: extra_type "0" "%x y. x = 0" .

thm var.test_def


text {* Under which circumstances term syntax remains active. *}

locale "syntax" =
  fixes p1 :: "'a => 'b"
    and p2 :: "'b => o"
begin

definition d1 :: "'a => o" where "d1(x) <-> ~ p2(p1(x))"
definition d2 :: "'b => o" where "d2(x) <-> ~ p2(x)"

thm d1_def d2_def

end

thm syntax.d1_def syntax.d2_def

locale syntax' = "syntax" p1 p2 for p1 :: "'a => 'a" and p2 :: "'a => o"
begin

thm d1_def d2_def  (* should print as "d1(?x) <-> ..." and "d2(?x) <-> ..." *)

ML {*
  fun check_syntax ctxt thm expected =
    let
      val obtained = PrintMode.setmp [] (Display.string_of_thm ctxt) thm;
    in
      if obtained <> expected
      then error ("Theorem syntax '" ^ obtained ^ "' obtained, but '" ^ expected ^ "' expected.")
      else ()
    end;
*}

ML {*
  check_syntax @{context} @{thm d1_def} "d1(?x) <-> ~ p2(p1(?x))";
  check_syntax @{context} @{thm d2_def} "d2(?x) <-> ~ p2(?x)";
*}

end

locale syntax'' = "syntax" p3 p2 for p3 :: "'a => 'b" and p2 :: "'b => o"
begin

thm d1_def d2_def
  (* should print as "syntax.d1(p3, p2, ?x) <-> ..." and "d2(?x) <-> ..." *)

ML {*
  check_syntax @{context} @{thm d1_def} "syntax.d1(p3, p2, ?x) <-> ~ p2(p3(?x))";
  check_syntax @{context} @{thm d2_def} "d2(?x) <-> ~ p2(?x)";
*}

end


section {* Foundational versions of theorems *}

thm logic.assoc
thm logic.lor_def


section {* Defines *}

locale logic_def =
  fixes land (infixl "&&" 55)
    and lor (infixl "||" 50)
    and lnot ("-- _" [60] 60)
  assumes assoc: "(x && y) && z = x && (y && z)"
    and notnot: "-- (-- x) = x"
  defines "x || y == --(-- x && -- y)"
begin

thm lor_def
(* Can we get rid the the additional hypothesis, caused by LocalTheory.notes? *)

lemma "x || y = --(-- x && --y)"
  by (unfold lor_def) (rule refl)

end

(* Inheritance of defines *)

locale logic_def2 = logic_def
begin

lemma "x || y = --(-- x && --y)"
  by (unfold lor_def) (rule refl)

end


section {* Notes *}

(* A somewhat arcane homomorphism example *)

definition semi_hom where
  "semi_hom(prod, sum, h) <-> (ALL x y. h(prod(x, y)) = sum(h(x), h(y)))"

lemma semi_hom_mult:
  "semi_hom(prod, sum, h) ==> h(prod(x, y)) = sum(h(x), h(y))"
  by (simp add: semi_hom_def)

locale semi_hom_loc = prod: semi prod + sum: semi sum
  for prod and sum and h +
  assumes semi_homh: "semi_hom(prod, sum, h)"
  notes semi_hom_mult = semi_hom_mult [OF semi_homh]

thm semi_hom_loc.semi_hom_mult
(* unspecified, attribute not applied in backgroud theory !!! *)

lemma (in semi_hom_loc) "h(prod(x, y)) = sum(h(x), h(y))"
  by (rule semi_hom_mult)

(* Referring to facts from within a context specification *)

lemma
  assumes x: "P <-> P"
  notes y = x
  shows True ..


section {* Theorem statements *}

lemma (in lgrp) lcancel:
  "x ** y = x ** z <-> y = z"
proof
  assume "x ** y = x ** z"
  then have "inv(x) ** x ** y = inv(x) ** x ** z" by (simp add: assoc)
  then show "y = z" by (simp add: lone linv)
qed simp
print_locale! lgrp


locale rgrp = semi +
  fixes one and inv
  assumes rone: "x ** one = x"
    and rinv: "x ** inv(x) = one"
begin

lemma rcancel:
  "y ** x = z ** x <-> y = z"
proof
  assume "y ** x = z ** x"
  then have "y ** (x ** inv(x)) = z ** (x ** inv(x))"
    by (simp add: assoc [symmetric])
  then show "y = z" by (simp add: rone rinv)
qed simp

end
print_locale! rgrp


subsection {* Patterns *}

lemma (in rgrp)
  assumes "y ** x = z ** x" (is ?a)
  shows "y = z" (is ?t)
proof -
  txt {* Weird proof involving patterns from context element and conclusion. *}
  {
    assume ?a
    then have "y ** (x ** inv(x)) = z ** (x ** inv(x))"
      by (simp add: assoc [symmetric])
    then have ?t by (simp add: rone rinv)
  }
  note x = this
  show ?t by (rule x [OF `?a`])
qed


section {* Interpretation between locales: sublocales *}

sublocale lgrp < right: rgrp
print_facts
proof unfold_locales
  {
    fix x
    have "inv(x) ** x ** one = inv(x) ** x" by (simp add: linv lone)
    then show "x ** one = x" by (simp add: assoc lcancel)
  }
  note rone = this
  {
    fix x
    have "inv(x) ** x ** inv(x) = inv(x) ** one"
      by (simp add: linv lone rone)
    then show "x ** inv(x) = one" by (simp add: assoc lcancel)
  }
qed

(* effect on printed locale *)

print_locale! lgrp

(* use of derived theorem *)

lemma (in lgrp)
  "y ** x = z ** x <-> y = z"
  apply (rule rcancel)
  done

(* circular interpretation *)

sublocale rgrp < left: lgrp
proof unfold_locales
  {
    fix x
    have "one ** (x ** inv(x)) = x ** inv(x)" by (simp add: rinv rone)
    then show "one ** x = x" by (simp add: assoc [symmetric] rcancel)
  }
  note lone = this
  {
    fix x
    have "inv(x) ** (x ** inv(x)) = one ** inv(x)"
      by (simp add: rinv lone rone)
    then show "inv(x) ** x = one" by (simp add: assoc [symmetric] rcancel)
  }
qed

(* effect on printed locale *)

print_locale! rgrp
print_locale! lgrp


(* Duality *)

locale order =
  fixes less :: "'a => 'a => o" (infix "<<" 50)
  assumes refl: "x << x"
    and trans: "[| x << y; y << z |] ==> x << z"

sublocale order < dual: order "%x y. y << x"
  apply unfold_locales apply (rule refl) apply (blast intro: trans)
  done

print_locale! order  (* Only two instances of order. *)

locale order' =
  fixes less :: "'a => 'a => o" (infix "<<" 50)
  assumes refl: "x << x"
    and trans: "[| x << y; y << z |] ==> x << z"

locale order_with_def = order'
begin

definition greater :: "'a => 'a => o" (infix ">>" 50) where
  "x >> y <-> y << x"

end

sublocale order_with_def < dual: order' "op >>"
  apply unfold_locales
  unfolding greater_def
  apply (rule refl) apply (blast intro: trans)
  done

print_locale! order_with_def
(* Note that decls come after theorems that make use of them. *)


(* locale with many parameters ---
   interpretations generate alternating group A5 *)


locale A5 =
  fixes A and B and C and D and E
  assumes eq: "A <-> B <-> C <-> D <-> E"

sublocale A5 < 1: A5 _ _ D E C
print_facts
  using eq apply (blast intro: A5.intro) done

sublocale A5 < 2: A5 C _ E _ A
print_facts
  using eq apply (blast intro: A5.intro) done

sublocale A5 < 3: A5 B C A _ _
print_facts
  using eq apply (blast intro: A5.intro) done

(* Any even permutation of parameters is subsumed by the above. *)

print_locale! A5


(* Free arguments of instance *)

locale trivial =
  fixes P and Q :: o
  assumes Q: "P <-> P <-> Q"
begin

lemma Q_triv: "Q" using Q by fast

end

sublocale trivial < x: trivial x _
  apply unfold_locales using Q by fast

print_locale! trivial

context trivial begin thm x.Q [where ?x = True] end

sublocale trivial < y: trivial Q Q
  by unfold_locales
  (* Succeeds since previous interpretation is more general. *)

print_locale! trivial  (* No instance for y created (subsumed). *)


subsection {* Sublocale, then interpretation in theory *}

interpretation int?: lgrp "op +" "0" "minus"
proof unfold_locales
qed (rule int_assoc int_zero int_minus)+

thm int.assoc int.semi_axioms

interpretation int2?: semi "op +"
  by unfold_locales  (* subsumed, thm int2.assoc not generated *)

ML {* (PureThy.get_thms @{theory} "int2.assoc";
    error "thm int2.assoc was generated")
  handle ERROR "Unknown fact \"int2.assoc\"" => ([]:thm list); *}

thm int.lone int.right.rone
  (* the latter comes through the sublocale relation *)


subsection {* Interpretation in theory, then sublocale *}

interpretation fol: logic "op +" "minus"
  by unfold_locales (rule int_assoc int_minus2)+

locale logic2 =
  fixes land (infixl "&&" 55)
    and lnot ("-- _" [60] 60)
  assumes assoc: "(x && y) && z = x && (y && z)"
    and notnot: "-- (-- x) = x"
begin

definition lor (infixl "||" 50) where
  "x || y = --(-- x && -- y)"

end

sublocale logic < two: logic2
  by unfold_locales (rule assoc notnot)+

thm fol.two.assoc


subsection {* Declarations and sublocale *}

locale logic_a = logic
locale logic_b = logic

sublocale logic_a < logic_b
  by unfold_locales


subsection {* Equations *}

locale logic_o =
  fixes land (infixl "&&" 55)
    and lnot ("-- _" [60] 60)
  assumes assoc_o: "(x && y) && z <-> x && (y && z)"
    and notnot_o: "-- (-- x) <-> x"
begin

definition lor_o (infixl "||" 50) where
  "x || y <-> --(-- x && -- y)"

end

interpretation x: logic_o "op &" "Not"
  where bool_logic_o: "logic_o.lor_o(op &, Not, x, y) <-> x | y"
proof -
  show bool_logic_o: "PROP logic_o(op &, Not)" by unfold_locales fast+
  show "logic_o.lor_o(op &, Not, x, y) <-> x | y"
    by (unfold logic_o.lor_o_def [OF bool_logic_o]) fast
qed

thm x.lor_o_def bool_logic_o

lemma lor_triv: "z <-> z" ..

lemma (in logic_o) lor_triv: "x || y <-> x || y" by fast

thm lor_triv [where z = True] (* Check strict prefix. *)
  x.lor_triv


subsection {* Inheritance of mixins *}

locale reflexive =
  fixes le :: "'a => 'a => o" (infix "\<sqsubseteq>" 50)
  assumes refl: "x \<sqsubseteq> x"
begin

definition less (infix "\<sqsubset>" 50) where "x \<sqsubset> y <-> x \<sqsubseteq> y & x ~= y"

end

consts
  gle :: "'a => 'a => o" gless :: "'a => 'a => o"
  gle' :: "'a => 'a => o" gless' :: "'a => 'a => o"

axioms
  grefl: "gle(x, x)" gless_def: "gless(x, y) <-> gle(x, y) & x ~= y"
  grefl': "gle'(x, x)" gless'_def: "gless'(x, y) <-> gle'(x, y) & x ~= y"

text {* Mixin not applied to locales further up the hierachy. *}

locale mixin = reflexive
begin
lemmas less_thm = less_def
end

interpretation le: mixin gle where "reflexive.less(gle, x, y) <-> gless(x, y)"
proof -
  show "mixin(gle)" by unfold_locales (rule grefl)
  note reflexive = this[unfolded mixin_def]
  show "reflexive.less(gle, x, y) <-> gless(x, y)"
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

thm le.less_def  (* mixin not applied *)
lemma "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y" by (rule le.less_def)
thm le.less_thm  (* mixin applied *)
lemma "gless(x, y) <-> gle(x, y) & x ~= y" by (rule le.less_thm)

lemma "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y"
  by (rule le.less_def)
lemma "gless(x, y) <-> gle(x, y) & x ~= y"
  by (rule le.less_thm)

text {* Mixin propagated along the locale hierarchy *}

locale mixin2 = mixin
begin
lemmas less_thm2 = less_def
end

interpretation le: mixin2 gle
  by unfold_locales

thm le.less_thm2  (* mixin applied *)
lemma "gless(x, y) <-> gle(x, y) & x ~= y"
  by (rule le.less_thm2)

text {* Mixin only available in original context *}

(* This section is not finished. *)

locale mixin3 = mixin le' for le' :: "'a => 'a => o" (infix "\<sqsubseteq>''" 50)

lemma (in mixin2) before:
  "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y"
proof -
  have "reflexive(gle)" by unfold_locales (rule grefl)
  note th = reflexive.less_def[OF this]
  then show ?thesis by (simp add: th)
qed

interpretation le': mixin2 gle'
  apply unfold_locales apply (rule grefl') done

lemma (in mixin2) after:
  "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y"
proof -
  have "reflexive(gle)" by unfold_locales (rule grefl)
  note th = reflexive.less_def[OF this]
  then show ?thesis by (simp add: th)
qed

thm le'.less_def le'.less_thm le'.less_thm2 le'.before le'.after

locale combined = le: reflexive le + le': mixin le'
  for le :: "'a => 'a => o" (infixl "\<sqsubseteq>" 50) and le' :: "'a => 'a => o" (infixl "\<sqsubseteq>''" 50)

interpretation combined gle gle'
  apply unfold_locales done

thm le.less_def le.less_thm le'.less_def le'.less_thm


subsection {* Interpretation in proofs *}

lemma True
proof
  interpret "local": lgrp "op +" "0" "minus"
    by unfold_locales  (* subsumed *)
  {
    fix zero :: int
    assume "!!x. zero + x = x" "!!x. (-x) + x = zero"
    then interpret local_fixed: lgrp "op +" zero "minus"
      by unfold_locales
    thm local_fixed.lone
  }
  assume "!!x zero. zero + x = x" "!!x zero. (-x) + x = zero"
  then interpret local_free: lgrp "op +" zero "minus" for zero
    by unfold_locales
  thm local_free.lone [where ?zero = 0]
qed

end
