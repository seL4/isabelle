(*  Title:      FOL/ex/Locale_Test/Locale_Test1.thy
    Author:     Clemens Ballarin, TU Muenchen

Test environment for the locale implementation.
*)

theory Locale_Test1
imports FOL
begin

typedecl int arities int :: "term"
consts plus :: "int => int => int" (infixl "+" 60)
  zero :: int ("0")
  minus :: "int => int" ("- _")

axiomatization where
  int_assoc: "(x + y::int) + z = x + (y + z)" and
  int_zero: "0 + x = x" and
  int_minus: "(-x) + x = 0" and
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

locale use_decl = l: logic + semi "op ||"
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
      val obtained = Print_Mode.setmp [] (Display.string_of_thm ctxt) thm;
    in
      if obtained <> expected
      then error ("Theorem syntax '" ^ obtained ^ "' obtained, but '" ^ expected ^ "' expected.")
      else ()
    end;
*}

declare [[show_hyps]]

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

ML {* (Global_Theory.get_thms @{theory} "int2.assoc";
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
  where bool_logic_o: "x.lor_o(x, y) <-> x | y"
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

axiomatization
  gle :: "'a => 'a => o" and gless :: "'a => 'a => o" and
  gle' :: "'a => 'a => o" and gless' :: "'a => 'a => o"
where
  grefl: "gle(x, x)" and gless_def: "gless(x, y) <-> gle(x, y) & x ~= y" and
  grefl': "gle'(x, x)" and gless'_def: "gless'(x, y) <-> gle'(x, y) & x ~= y"

text {* Setup *}

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

text {* Mixin does not leak to a side branch. *}

locale mixin3 = reflexive
begin
lemmas less_thm3 = less_def
end

interpretation le: mixin3 gle
  by unfold_locales

thm le.less_thm3  (* mixin not applied *)
lemma "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y" by (rule le.less_thm3)

text {* Mixin only available in original context *}

locale mixin4_base = reflexive

locale mixin4_mixin = mixin4_base

interpretation le: mixin4_mixin gle
  where "reflexive.less(gle, x, y) <-> gless(x, y)"
proof -
  show "mixin4_mixin(gle)" by unfold_locales (rule grefl)
  note reflexive = this[unfolded mixin4_mixin_def mixin4_base_def mixin_def]
  show "reflexive.less(gle, x, y) <-> gless(x, y)"
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

locale mixin4_copy = mixin4_base
begin
lemmas less_thm4 = less_def
end

locale mixin4_combined = le1: mixin4_mixin le' + le2: mixin4_copy le for le' le
begin
lemmas less_thm4' = less_def
end

interpretation le4: mixin4_combined gle' gle
  by unfold_locales (rule grefl')

thm le4.less_thm4' (* mixin not applied *)
lemma "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y"
  by (rule le4.less_thm4')

text {* Inherited mixin applied to new theorem *}

locale mixin5_base = reflexive

locale mixin5_inherited = mixin5_base

interpretation le5: mixin5_base gle
  where "reflexive.less(gle, x, y) <-> gless(x, y)"
proof -
  show "mixin5_base(gle)" by unfold_locales
  note reflexive = this[unfolded mixin5_base_def mixin_def]
  show "reflexive.less(gle, x, y) <-> gless(x, y)"
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

interpretation le5: mixin5_inherited gle
  by unfold_locales

lemmas (in mixin5_inherited) less_thm5 = less_def

thm le5.less_thm5  (* mixin applied *)
lemma "gless(x, y) <-> gle(x, y) & x ~= y"
  by (rule le5.less_thm5)

text {* Mixin pushed down to existing inherited locale *}

locale mixin6_base = reflexive

locale mixin6_inherited = mixin5_base

interpretation le6: mixin6_base gle
  by unfold_locales
interpretation le6: mixin6_inherited gle
  by unfold_locales
interpretation le6: mixin6_base gle
  where "reflexive.less(gle, x, y) <-> gless(x, y)"
proof -
  show "mixin6_base(gle)" by unfold_locales
  note reflexive = this[unfolded mixin6_base_def mixin_def]
  show "reflexive.less(gle, x, y) <-> gless(x, y)"
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

lemmas (in mixin6_inherited) less_thm6 = less_def

thm le6.less_thm6  (* mixin applied *)
lemma "gless(x, y) <-> gle(x, y) & x ~= y"
  by (rule le6.less_thm6)

text {* Existing mixin inherited through sublocale relation *}

locale mixin7_base = reflexive

locale mixin7_inherited = reflexive

interpretation le7: mixin7_base gle
  where "reflexive.less(gle, x, y) <-> gless(x, y)"
proof -
  show "mixin7_base(gle)" by unfold_locales
  note reflexive = this[unfolded mixin7_base_def mixin_def]
  show "reflexive.less(gle, x, y) <-> gless(x, y)"
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

interpretation le7: mixin7_inherited gle
  by unfold_locales

lemmas (in mixin7_inherited) less_thm7 = less_def

thm le7.less_thm7  (* before, mixin not applied *)
lemma "reflexive.less(gle, x, y) <-> gle(x, y) & x ~= y"
  by (rule le7.less_thm7)

sublocale mixin7_inherited < mixin7_base
  by unfold_locales

lemmas (in mixin7_inherited) less_thm7b = less_def

thm le7.less_thm7b  (* after, mixin applied *)
lemma "gless(x, y) <-> gle(x, y) & x ~= y"
  by (rule le7.less_thm7b)


text {* This locale will be interpreted in later theories. *}

locale mixin_thy_merge = le: reflexive le + le': reflexive le' for le le'


subsection {* Mixins in sublocale *}

text {* Simulate a specification of left groups where unit and inverse are defined
  rather than specified.  This is possible, but not in FOL, due to the lack of a
  selection operator. *}

axiomatization glob_one and glob_inv
  where glob_lone: "prod(glob_one(prod), x) = x"
    and glob_linv: "prod(glob_inv(prod, x), x) = glob_one(prod)"

locale dgrp = semi
begin

definition one where "one = glob_one(prod)"

lemma lone: "one ** x = x"
  unfolding one_def by (rule glob_lone)

definition inv where "inv(x) = glob_inv(prod, x)"

lemma linv: "inv(x) ** x = one"
  unfolding one_def inv_def by (rule glob_linv)

end

sublocale lgrp < "def": dgrp
  where one_equation: "dgrp.one(prod) = one" and inv_equation: "dgrp.inv(prod, x) = inv(x)"
proof -
  show "dgrp(prod)" by unfold_locales
  from this interpret d: dgrp .
  -- Unit
  have "dgrp.one(prod) = glob_one(prod)" by (rule d.one_def)
  also have "... = glob_one(prod) ** one" by (simp add: rone)
  also have "... = one" by (simp add: glob_lone)
  finally show "dgrp.one(prod) = one" .
  -- Inverse
  then have "dgrp.inv(prod, x) ** x = inv(x) ** x" by (simp add: glob_linv d.linv linv)
  then show "dgrp.inv(prod, x) = inv(x)" by (simp add: rcancel)
qed

print_locale! lgrp

context lgrp begin

text {* Equations stored in target *}

lemma "dgrp.one(prod) = one" by (rule one_equation)
lemma "dgrp.inv(prod, x) = inv(x)" by (rule inv_equation)

text {* Mixins applied *}

lemma "one = glob_one(prod)" by (rule one_def)
lemma "inv(x) = glob_inv(prod, x)" by (rule inv_def)

end

text {* Interpreted versions *}

lemma "0 = glob_one (op +)" by (rule int.def.one_def)
lemma "- x = glob_inv(op +, x)" by (rule int.def.inv_def)


section {* Interpretation in proofs *}

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
    print_dependencies! lgrp "op +" 0 minus + lgrp "op +" zero minus
  }
  assume "!!x zero. zero + x = x" "!!x zero. (-x) + x = zero"
  then interpret local_free: lgrp "op +" zero "minus" for zero
    by unfold_locales
  thm local_free.lone [where ?zero = 0]
qed

lemma True
proof
  {
    fix pand and pnot and por
    assume passoc: "!!x y z. pand(pand(x, y), z) <-> pand(x, pand(y, z))"
      and pnotnot: "!!x. pnot(pnot(x)) <-> x"
      and por_def: "!!x y. por(x, y) <-> pnot(pand(pnot(x), pnot(y)))"
    interpret loc: logic_o pand pnot
      where por_eq: "!!x y. logic_o.lor_o(pand, pnot, x, y) <-> por(x, y)"  (* FIXME *)
    proof -
      show logic_o: "PROP logic_o(pand, pnot)" using passoc pnotnot by unfold_locales
      fix x y
      show "logic_o.lor_o(pand, pnot, x, y) <-> por(x, y)"
        by (unfold logic_o.lor_o_def [OF logic_o]) (rule por_def [symmetric])
    qed
    print_interps logic_o
    have "!!x y. por(x, y) <-> pnot(pand(pnot(x), pnot(y)))" by (rule loc.lor_o_def)
  }
qed

end
