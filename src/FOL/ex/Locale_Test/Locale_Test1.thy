(*  Title:      FOL/ex/Locale_Test/Locale_Test1.thy
    Author:     Clemens Ballarin, TU Muenchen

Test environment for the locale implementation.
*)

theory Locale_Test1
imports FOL
begin

typedecl int
instance int :: \<open>term\<close> ..

consts plus :: \<open>int => int => int\<close> (infixl \<open>+\<close> 60)
  zero :: \<open>int\<close> (\<open>0\<close>)
  minus :: \<open>int => int\<close> (\<open>- _\<close>)

axiomatization where
  int_assoc: \<open>(x + y::int) + z = x + (y + z)\<close> and
  int_zero: \<open>0 + x = x\<close> and
  int_minus: \<open>(-x) + x = 0\<close> and
  int_minus2: \<open>-(-x) = x\<close>

section \<open>Inference of parameter types\<close>

locale param1 = fixes p
print_locale! param1

locale param2 = fixes p :: \<open>'b\<close>
print_locale! param2

(*
locale param_top = param2 r for r :: "'b :: {}"
  Fails, cannot generalise parameter.
*)

locale param3 = fixes p (infix \<open>..\<close> 50)
print_locale! param3

locale param4 = fixes p :: \<open>'a => 'a => 'a\<close> (infix \<open>..\<close> 50)
print_locale! param4


subsection \<open>Incremental type constraints\<close>

locale constraint1 =
  fixes  prod (infixl \<open>**\<close> 65)
  assumes l_id: \<open>x ** y = x\<close>
  assumes assoc: \<open>(x ** y) ** z = x ** (y ** z)\<close>
print_locale! constraint1

locale constraint2 =
  fixes p and q
  assumes \<open>p = q\<close>
print_locale! constraint2


section \<open>Inheritance\<close>

locale semi =
  fixes prod (infixl \<open>**\<close> 65)
  assumes assoc: \<open>(x ** y) ** z = x ** (y ** z)\<close>
print_locale! semi thm semi_def

locale lgrp = semi +
  fixes one and inv
  assumes lone: \<open>one ** x = x\<close>
    and linv: \<open>inv(x) ** x = one\<close>
print_locale! lgrp thm lgrp_def lgrp_axioms_def

locale add_lgrp = semi \<open>(++)\<close> for sum (infixl \<open>++\<close> 60) +
  fixes zero and neg
  assumes lzero: \<open>zero ++ x = x\<close>
    and lneg: \<open>neg(x) ++ x = zero\<close>
print_locale! add_lgrp thm add_lgrp_def add_lgrp_axioms_def

locale rev_lgrp = semi \<open>%x y. y ++ x\<close> for sum (infixl \<open>++\<close> 60)
print_locale! rev_lgrp thm rev_lgrp_def

locale hom = f: semi \<open>f\<close> + g: semi \<open>g\<close> for f and g
print_locale! hom thm hom_def

locale perturbation = semi + d: semi \<open>%x y. delta(x) ** delta(y)\<close> for delta
print_locale! perturbation thm perturbation_def

locale pert_hom = d1: perturbation \<open>f\<close> \<open>d1\<close> + d2: perturbation \<open>f\<close> \<open>d2\<close> for f d1 d2
print_locale! pert_hom thm pert_hom_def

text \<open>Alternative expression, obtaining nicer names in \<open>semi f\<close>.\<close>
locale pert_hom' = semi \<open>f\<close> + d1: perturbation \<open>f\<close> \<open>d1\<close> + d2: perturbation \<open>f\<close> \<open>d2\<close> for f d1 d2
print_locale! pert_hom' thm pert_hom'_def


section \<open>Syntax declarations\<close>

locale logic =
  fixes land (infixl \<open>&&\<close> 55)
    and lnot (\<open>-- _\<close> [60] 60)
  assumes assoc: \<open>(x && y) && z = x && (y && z)\<close>
    and notnot: \<open>-- (-- x) = x\<close>
begin

definition lor (infixl \<open>||\<close> 50) where
  \<open>x || y = --(-- x && -- y)\<close>

end
print_locale! logic

locale use_decl = l: logic + semi \<open>(||)\<close>
print_locale! use_decl thm use_decl_def

locale extra_type =
  fixes a :: \<open>'a\<close>
    and P :: \<open>'a => 'b => o\<close>
begin

definition test :: \<open>'a => o\<close>
  where \<open>test(x) \<longleftrightarrow> (\<forall>b. P(x, b))\<close>

end

term \<open>extra_type.test\<close> thm extra_type.test_def

interpretation var?: extra_type \<open>0\<close> \<open>%x y. x = 0\<close> .

thm var.test_def


text \<open>Under which circumstances notation remains active.\<close>

ML \<open>
  fun check_syntax ctxt thm expected =
    let
      val obtained =
        Pretty.pure_string_of (Thm.pretty_thm (Config.put show_markup false ctxt) thm);
    in
      if obtained <> expected
      then error ("Theorem syntax '" ^ obtained ^ "' obtained, but '" ^ expected ^ "' expected.")
      else ()
    end;
\<close>

declare [[show_hyps]]

locale "syntax" =
  fixes p1 :: \<open>'a => 'b\<close>
    and p2 :: \<open>'b => o\<close>
begin

definition d1 :: \<open>'a => o\<close> (\<open>D1'(_')\<close>) where \<open>d1(x) \<longleftrightarrow> \<not> p2(p1(x))\<close>
definition d2 :: \<open>'b => o\<close> (\<open>D2'(_')\<close>) where \<open>d2(x) \<longleftrightarrow> \<not> p2(x)\<close>

thm d1_def d2_def

end

thm syntax.d1_def syntax.d2_def

locale syntax' = "syntax" \<open>p1\<close> \<open>p2\<close> for p1 :: \<open>'a => 'a\<close> and p2 :: \<open>'a => o\<close>
begin

thm d1_def d2_def  (* should print as "D1(?x) <-> ..." and "D2(?x) <-> ..." *)

ML \<open>
  check_syntax \<^context> @{thm d1_def} "D1(?x) \<longleftrightarrow> \<not> p2(p1(?x))";
  check_syntax \<^context> @{thm d2_def} "D2(?x) \<longleftrightarrow> \<not> p2(?x)";
\<close>

end

locale syntax'' = "syntax" \<open>p3\<close> \<open>p2\<close> for p3 :: \<open>'a => 'b\<close> and p2 :: \<open>'b => o\<close>
begin

thm d1_def d2_def
  (* should print as "d1(?x) <-> ..." and "D2(?x) <-> ..." *)

ML \<open>
  check_syntax \<^context> @{thm d1_def} "d1(?x) \<longleftrightarrow> \<not> p2(p3(?x))";
  check_syntax \<^context> @{thm d2_def} "D2(?x) \<longleftrightarrow> \<not> p2(?x)";
\<close>

end


section \<open>Foundational versions of theorems\<close>

thm logic.assoc
thm logic.lor_def


section \<open>Defines\<close>

locale logic_def =
  fixes land (infixl \<open>&&\<close> 55)
    and lor (infixl \<open>||\<close> 50)
    and lnot (\<open>-- _\<close> [60] 60)
  assumes assoc: \<open>(x && y) && z = x && (y && z)\<close>
    and notnot: \<open>-- (-- x) = x\<close>
  defines \<open>x || y == --(-- x && -- y)\<close>
begin

thm lor_def

lemma \<open>x || y = --(-- x && --y)\<close>
  by (unfold lor_def) (rule refl)

end

(* Inheritance of defines *)

locale logic_def2 = logic_def
begin

lemma \<open>x || y = --(-- x && --y)\<close>
  by (unfold lor_def) (rule refl)

end


section \<open>Notes\<close>

(* A somewhat arcane homomorphism example *)

definition semi_hom where
  \<open>semi_hom(prod, sum, h) \<longleftrightarrow> (\<forall>x y. h(prod(x, y)) = sum(h(x), h(y)))\<close>

lemma semi_hom_mult:
  \<open>semi_hom(prod, sum, h) \<Longrightarrow> h(prod(x, y)) = sum(h(x), h(y))\<close>
  by (simp add: semi_hom_def)

locale semi_hom_loc = prod: semi \<open>prod\<close> + sum: semi \<open>sum\<close>
  for prod and sum and h +
  assumes semi_homh: \<open>semi_hom(prod, sum, h)\<close>
  notes semi_hom_mult = semi_hom_mult [OF semi_homh]

thm semi_hom_loc.semi_hom_mult
(* unspecified, attribute not applied in background theory !!! *)

lemma (in semi_hom_loc) \<open>h(prod(x, y)) = sum(h(x), h(y))\<close>
  by (rule semi_hom_mult)

(* Referring to facts from within a context specification *)

lemma
  assumes x: \<open>P \<longleftrightarrow> P\<close>
  notes y = x
  shows \<open>True\<close> ..


section \<open>Theorem statements\<close>

lemma (in lgrp) lcancel:
  \<open>x ** y = x ** z \<longleftrightarrow> y = z\<close>
proof
  assume \<open>x ** y = x ** z\<close>
  then have \<open>inv(x) ** x ** y = inv(x) ** x ** z\<close> by (simp add: assoc)
  then show \<open>y = z\<close> by (simp add: lone linv)
qed simp
print_locale! lgrp


locale rgrp = semi +
  fixes one and inv
  assumes rone: \<open>x ** one = x\<close>
    and rinv: \<open>x ** inv(x) = one\<close>
begin

lemma rcancel:
  \<open>y ** x = z ** x \<longleftrightarrow> y = z\<close>
proof
  assume \<open>y ** x = z ** x\<close>
  then have \<open>y ** (x ** inv(x)) = z ** (x ** inv(x))\<close>
    by (simp add: assoc [symmetric])
  then show \<open>y = z\<close> by (simp add: rone rinv)
qed simp

end
print_locale! rgrp


subsection \<open>Patterns\<close>

lemma (in rgrp)
  assumes \<open>y ** x = z ** x\<close> (is \<open>?a\<close>)
  shows \<open>y = z\<close> (is \<open>?t\<close>)
proof -
  txt \<open>Weird proof involving patterns from context element and conclusion.\<close>
  have *: \<open>?t\<close> if \<open>?a\<close>
  proof -
    from that have \<open>y ** (x ** inv(x)) = z ** (x ** inv(x))\<close>
      by (simp add: assoc [symmetric])
    then show ?thesis by (simp add: rone rinv)
  qed
  show \<open>?t\<close> by (rule * [OF \<open>?a\<close>])
qed


section \<open>Interpretation between locales: sublocales\<close>

sublocale lgrp < right?: rgrp
print_facts
proof unfold_locales
  show rone: \<open>x ** one = x\<close> for x
  proof -
    have \<open>inv(x) ** x ** one = inv(x) ** x\<close> by (simp add: linv lone)
    then show ?thesis by (simp add: assoc lcancel)
  qed
  show \<open>x ** inv(x) = one\<close> for x
  proof -
    have \<open>inv(x) ** x ** inv(x) = inv(x) ** one\<close>
      by (simp add: linv lone rone)
    then show ?thesis by (simp add: assoc lcancel)
  qed
qed

(* effect on printed locale *)

print_locale! lgrp

(* use of derived theorem *)

lemma (in lgrp)
  \<open>y ** x = z ** x \<longleftrightarrow> y = z\<close>
  apply (rule rcancel)
  done

(* circular interpretation *)

sublocale rgrp < left: lgrp
proof unfold_locales
  show lone: \<open>one ** x = x\<close> for x
  proof -
    have \<open>one ** (x ** inv(x)) = x ** inv(x)\<close> by (simp add: rinv rone)
    then show ?thesis by (simp add: assoc [symmetric] rcancel)
  qed
  show \<open>inv(x) ** x = one\<close> for x
  proof -
    have \<open>inv(x) ** (x ** inv(x)) = one ** inv(x)\<close>
      by (simp add: rinv lone rone)
    then show \<open>inv(x) ** x = one\<close> by (simp add: assoc [symmetric] rcancel)
  qed
qed

(* effect on printed locale *)

print_locale! rgrp
print_locale! lgrp


(* Duality *)

locale order =
  fixes less :: \<open>'a => 'a => o\<close> (infix \<open><<\<close> 50)
  assumes refl: \<open>x << x\<close>
    and trans: \<open>[| x << y; y << z |] ==> x << z\<close>

sublocale order < dual: order \<open>%x y. y << x\<close>
  apply unfold_locales apply (rule refl) apply (blast intro: trans)
  done

print_locale! order  (* Only two instances of order. *)

locale order' =
  fixes less :: \<open>'a => 'a => o\<close> (infix \<open><<\<close> 50)
  assumes refl: \<open>x << x\<close>
    and trans: \<open>[| x << y; y << z |] ==> x << z\<close>

locale order_with_def = order'
begin

definition greater :: \<open>'a => 'a => o\<close> (infix \<open>>>\<close> 50) where
  \<open>x >> y \<longleftrightarrow> y << x\<close>

end

sublocale order_with_def < dual: order' \<open>(>>)\<close>
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
  assumes eq: \<open>A \<longleftrightarrow> B \<longleftrightarrow> C \<longleftrightarrow> D \<longleftrightarrow> E\<close>

sublocale A5 < 1: A5 _ _ \<open>D\<close> \<open>E\<close> \<open>C\<close>
print_facts
  using eq apply (blast intro: A5.intro) done

sublocale A5 < 2: A5 \<open>C\<close> _ \<open>E\<close> _ \<open>A\<close>
print_facts
  using eq apply (blast intro: A5.intro) done

sublocale A5 < 3: A5 \<open>B\<close> \<open>C\<close> \<open>A\<close> _ _
print_facts
  using eq apply (blast intro: A5.intro) done

(* Any even permutation of parameters is subsumed by the above. *)

print_locale! A5


(* Free arguments of instance *)

locale trivial =
  fixes P and Q :: \<open>o\<close>
  assumes Q: \<open>P \<longleftrightarrow> P \<longleftrightarrow> Q\<close>
begin

lemma Q_triv: \<open>Q\<close> using Q by fast

end

sublocale trivial < x: trivial \<open>x\<close> _
  apply unfold_locales using Q by fast

print_locale! trivial

context trivial
begin
thm x.Q [where ?x = \<open>True\<close>]
end

sublocale trivial < y: trivial \<open>Q\<close> \<open>Q\<close>
  by unfold_locales
  (* Succeeds since previous interpretation is more general. *)

print_locale! trivial  (* No instance for y created (subsumed). *)


subsection \<open>Sublocale, then interpretation in theory\<close>

interpretation int?: lgrp \<open>(+)\<close> \<open>0\<close> \<open>minus\<close>
proof unfold_locales
qed (rule int_assoc int_zero int_minus)+

thm int.assoc int.semi_axioms

interpretation int2?: semi \<open>(+)\<close>
  by unfold_locales  (* subsumed, thm int2.assoc not generated *)

ML \<open>(Global_Theory.get_thms \<^theory> "int2.assoc";
    raise Fail "thm int2.assoc was generated")
  handle ERROR _ => ([]:thm list);\<close>

thm int.lone int.right.rone
  (* the latter comes through the sublocale relation *)


subsection \<open>Interpretation in theory, then sublocale\<close>

interpretation fol: logic \<open>(+)\<close> \<open>minus\<close>
  by unfold_locales (rule int_assoc int_minus2)+

locale logic2 =
  fixes land (infixl \<open>&&\<close> 55)
    and lnot (\<open>-- _\<close> [60] 60)
  assumes assoc: \<open>(x && y) && z = x && (y && z)\<close>
    and notnot: \<open>-- (-- x) = x\<close>
begin

definition lor (infixl \<open>||\<close> 50) where
  \<open>x || y = --(-- x && -- y)\<close>

end

sublocale logic < two: logic2
  by unfold_locales (rule assoc notnot)+

thm fol.two.assoc


subsection \<open>Declarations and sublocale\<close>

locale logic_a = logic
locale logic_b = logic

sublocale logic_a < logic_b
  by unfold_locales


subsection \<open>Interpretation\<close>

subsection \<open>Rewrite morphism\<close>

locale logic_o =
  fixes land (infixl \<open>&&\<close> 55)
    and lnot (\<open>-- _\<close> [60] 60)
  assumes assoc_o: \<open>(x && y) && z \<longleftrightarrow> x && (y && z)\<close>
    and notnot_o: \<open>-- (-- x) \<longleftrightarrow> x\<close>
begin

definition lor_o (infixl \<open>||\<close> 50) where
  \<open>x || y \<longleftrightarrow> --(-- x && -- y)\<close>

end

interpretation x: logic_o \<open>(\<and>)\<close> \<open>Not\<close>
  rewrites bool_logic_o: \<open>x.lor_o(x, y) \<longleftrightarrow> x \<or> y\<close>
proof -
  show bool_logic_o: \<open>PROP logic_o((\<and>), Not)\<close> by unfold_locales fast+
  show \<open>logic_o.lor_o((\<and>), Not, x, y) \<longleftrightarrow> x \<or> y\<close>
    by (unfold logic_o.lor_o_def [OF bool_logic_o]) fast
qed

thm x.lor_o_def bool_logic_o

lemma lor_triv: \<open>z \<longleftrightarrow> z\<close> ..

lemma (in logic_o) lor_triv: \<open>x || y \<longleftrightarrow> x || y\<close> by fast

thm lor_triv [where z = \<open>True\<close>] (* Check strict prefix. *)
  x.lor_triv


subsection \<open>Rewrite morphisms in expressions\<close>

interpretation y: logic_o \<open>(\<or>)\<close> \<open>Not\<close> rewrites bool_logic_o2: \<open>logic_o.lor_o((\<or>), Not, x, y) \<longleftrightarrow> x \<and> y\<close>
proof -
  show bool_logic_o: \<open>PROP logic_o((\<or>), Not)\<close> by unfold_locales fast+
  show \<open>logic_o.lor_o((\<or>), Not, x, y) \<longleftrightarrow> x \<and> y\<close> unfolding logic_o.lor_o_def [OF bool_logic_o] by fast
qed


subsection \<open>Inheritance of rewrite morphisms\<close>

locale reflexive =
  fixes le :: \<open>'a => 'a => o\<close> (infix \<open>\<sqsubseteq>\<close> 50)
  assumes refl: \<open>x \<sqsubseteq> x\<close>
begin

definition less (infix \<open>\<sqsubset>\<close> 50) where \<open>x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y\<close>

end

axiomatization
  gle :: \<open>'a => 'a => o\<close> and gless :: \<open>'a => 'a => o\<close> and
  gle' :: \<open>'a => 'a => o\<close> and gless' :: \<open>'a => 'a => o\<close>
where
  grefl: \<open>gle(x, x)\<close> and gless_def: \<open>gless(x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close> and
  grefl': \<open>gle'(x, x)\<close> and gless'_def: \<open>gless'(x, y) \<longleftrightarrow> gle'(x, y) \<and> x \<noteq> y\<close>

text \<open>Setup\<close>

locale mixin = reflexive
begin
lemmas less_thm = less_def
end

interpretation le: mixin \<open>gle\<close> rewrites \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
proof -
  show \<open>mixin(gle)\<close> by unfold_locales (rule grefl)
  note reflexive = this[unfolded mixin_def]
  show \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

text \<open>Rewrite morphism propagated along the locale hierarchy\<close>

locale mixin2 = mixin
begin
lemmas less_thm2 = less_def
end

interpretation le: mixin2 \<open>gle\<close>
  by unfold_locales

thm le.less_thm2  (* rewrite morphism applied *)
lemma \<open>gless(x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close>
  by (rule le.less_thm2)

text \<open>Rewrite morphism does not leak to a side branch.\<close>

locale mixin3 = reflexive
begin
lemmas less_thm3 = less_def
end

interpretation le: mixin3 \<open>gle\<close>
  by unfold_locales

thm le.less_thm3  (* rewrite morphism not applied *)
lemma \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close> by (rule le.less_thm3)

text \<open>Rewrite morphism only available in original context\<close>

locale mixin4_base = reflexive

locale mixin4_mixin = mixin4_base

interpretation le: mixin4_mixin \<open>gle\<close>
  rewrites \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
proof -
  show \<open>mixin4_mixin(gle)\<close> by unfold_locales (rule grefl)
  note reflexive = this[unfolded mixin4_mixin_def mixin4_base_def mixin_def]
  show \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

locale mixin4_copy = mixin4_base
begin
lemmas less_thm4 = less_def
end

locale mixin4_combined = le1?: mixin4_mixin \<open>le'\<close> + le2?: mixin4_copy \<open>le\<close> for le' le
begin
lemmas less_thm4' = less_def
end

interpretation le4: mixin4_combined \<open>gle'\<close> \<open>gle\<close>
  by unfold_locales (rule grefl')

thm le4.less_thm4' (* rewrite morphism not applied *)
lemma \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close>
  by (rule le4.less_thm4')

text \<open>Inherited rewrite morphism applied to new theorem\<close>

locale mixin5_base = reflexive

locale mixin5_inherited = mixin5_base

interpretation le5: mixin5_base \<open>gle\<close>
  rewrites \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
proof -
  show \<open>mixin5_base(gle)\<close> by unfold_locales
  note reflexive = this[unfolded mixin5_base_def mixin_def]
  show \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

interpretation le5: mixin5_inherited \<open>gle\<close>
  by unfold_locales

lemmas (in mixin5_inherited) less_thm5 = less_def

thm le5.less_thm5  (* rewrite morphism applied *)
lemma \<open>gless(x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close>
  by (rule le5.less_thm5)

text \<open>Rewrite morphism pushed down to existing inherited locale\<close>

locale mixin6_base = reflexive

locale mixin6_inherited = mixin5_base

interpretation le6: mixin6_base \<open>gle\<close>
  by unfold_locales
interpretation le6: mixin6_inherited \<open>gle\<close>
  by unfold_locales
interpretation le6: mixin6_base \<open>gle\<close>
  rewrites \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
proof -
  show \<open>mixin6_base(gle)\<close> by unfold_locales
  note reflexive = this[unfolded mixin6_base_def mixin_def]
  show \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

lemmas (in mixin6_inherited) less_thm6 = less_def

thm le6.less_thm6  (* mixin applied *)
lemma \<open>gless(x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close>
  by (rule le6.less_thm6)

text \<open>Existing rewrite morphism inherited through sublocale relation\<close>

locale mixin7_base = reflexive

locale mixin7_inherited = reflexive

interpretation le7: mixin7_base \<open>gle\<close>
  rewrites \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
proof -
  show \<open>mixin7_base(gle)\<close> by unfold_locales
  note reflexive = this[unfolded mixin7_base_def mixin_def]
  show \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gless(x, y)\<close>
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

interpretation le7: mixin7_inherited \<open>gle\<close>
  by unfold_locales

lemmas (in mixin7_inherited) less_thm7 = less_def

thm le7.less_thm7  (* before, rewrite morphism not applied *)
lemma \<open>reflexive.less(gle, x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close>
  by (rule le7.less_thm7)

sublocale mixin7_inherited < mixin7_base
  by unfold_locales

lemmas (in mixin7_inherited) less_thm7b = less_def

thm le7.less_thm7b  (* after, mixin applied *)
lemma \<open>gless(x, y) \<longleftrightarrow> gle(x, y) \<and> x \<noteq> y\<close>
  by (rule le7.less_thm7b)


text \<open>This locale will be interpreted in later theories.\<close>

locale mixin_thy_merge = le: reflexive \<open>le\<close> + le': reflexive \<open>le'\<close> for le le'


subsection \<open>Rewrite morphisms in sublocale\<close>

text \<open>Simulate a specification of left groups where unit and inverse are defined
  rather than specified.  This is possible, but not in FOL, due to the lack of a
  selection operator.\<close>

axiomatization glob_one and glob_inv
  where glob_lone: \<open>prod(glob_one(prod), x) = x\<close>
    and glob_linv: \<open>prod(glob_inv(prod, x), x) = glob_one(prod)\<close>

locale dgrp = semi
begin

definition one where \<open>one = glob_one(prod)\<close>

lemma lone: \<open>one ** x = x\<close>
  unfolding one_def by (rule glob_lone)

definition inv where \<open>inv(x) = glob_inv(prod, x)\<close>

lemma linv: \<open>inv(x) ** x = one\<close>
  unfolding one_def inv_def by (rule glob_linv)

end

sublocale lgrp < def?: dgrp
  rewrites one_equation: \<open>dgrp.one(prod) = one\<close> and inv_equation: \<open>dgrp.inv(prod, x) = inv(x)\<close>
proof -
  show \<open>dgrp(prod)\<close> by unfold_locales
  from this interpret d: dgrp .
  \<comment> \<open>Unit\<close>
  have \<open>dgrp.one(prod) = glob_one(prod)\<close> by (rule d.one_def)
  also have \<open>... = glob_one(prod) ** one\<close> by (simp add: rone)
  also have \<open>... = one\<close> by (simp add: glob_lone)
  finally show \<open>dgrp.one(prod) = one\<close> .
  \<comment> \<open>Inverse\<close>
  then have \<open>dgrp.inv(prod, x) ** x = inv(x) ** x\<close> by (simp add: glob_linv d.linv linv)
  then show \<open>dgrp.inv(prod, x) = inv(x)\<close> by (simp add: rcancel)
qed

print_locale! lgrp

context lgrp
begin

text \<open>Equations stored in target\<close>

lemma \<open>dgrp.one(prod) = one\<close> by (rule one_equation)
lemma \<open>dgrp.inv(prod, x) = inv(x)\<close> by (rule inv_equation)

text \<open>Rewrite morphisms applied\<close>

lemma \<open>one = glob_one(prod)\<close> by (rule one_def)
lemma \<open>inv(x) = glob_inv(prod, x)\<close> by (rule inv_def)

end

text \<open>Interpreted versions\<close>

lemma \<open>0 = glob_one ((+))\<close> by (rule int.def.one_def)
lemma \<open>- x = glob_inv((+), x)\<close> by (rule int.def.inv_def)

text \<open>Roundup applies rewrite morphisms at declaration level in DFS tree\<close>

locale roundup = fixes x assumes true: \<open>x \<longleftrightarrow> True\<close>

sublocale roundup \<subseteq> sub: roundup \<open>x\<close> rewrites \<open>x \<longleftrightarrow> True \<and> True\<close>
  apply unfold_locales apply (simp add: true) done
lemma (in roundup) \<open>True \<and> True \<longleftrightarrow> True\<close> by (rule sub.true)


section \<open>Interpretation in named contexts\<close>

locale container
begin
interpretation "private": roundup \<open>True\<close> by unfold_locales rule
lemmas true_copy = private.true
end

context container
begin
ML \<open>(Context.>> (fn generic => let val context = Context.proof_of generic
  val _ = Proof_Context.get_thms context "private.true" in generic end);
  raise Fail "thm private.true was persisted")
  handle ERROR _ => ([]:thm list);\<close>
thm true_copy
end


section \<open>Interpretation in proofs\<close>

notepad
begin
  interpret "local": lgrp \<open>(+)\<close> \<open>0\<close> \<open>minus\<close>
    by unfold_locales  (* subsumed *)
  {
    fix zero :: \<open>int\<close>
    assume \<open>!!x. zero + x = x\<close> \<open>!!x. (-x) + x = zero\<close>
    then interpret local_fixed: lgrp \<open>(+)\<close> \<open>zero\<close> \<open>minus\<close>
      by unfold_locales
    thm local_fixed.lone
  }
  assume \<open>!!x zero. zero + x = x\<close> \<open>!!x zero. (-x) + x = zero\<close>
  then interpret local_free: lgrp \<open>(+)\<close> \<open>zero\<close> \<open>minus\<close> for zero
    by unfold_locales
  thm local_free.lone [where ?zero = \<open>0\<close>]
end

notepad
begin
  {
    fix pand and pnot and por
    assume passoc: \<open>\<And>x y z. pand(pand(x, y), z) \<longleftrightarrow> pand(x, pand(y, z))\<close>
      and pnotnot: \<open>\<And>x. pnot(pnot(x)) \<longleftrightarrow> x\<close>
      and por_def: \<open>\<And>x y. por(x, y) \<longleftrightarrow> pnot(pand(pnot(x), pnot(y)))\<close>
    interpret loc: logic_o \<open>pand\<close> \<open>pnot\<close>
      rewrites por_eq: \<open>\<And>x y. logic_o.lor_o(pand, pnot, x, y) \<longleftrightarrow> por(x, y)\<close>  (* FIXME *)
    proof -
      show logic_o: \<open>PROP logic_o(pand, pnot)\<close> using passoc pnotnot by unfold_locales
      fix x y
      show \<open>logic_o.lor_o(pand, pnot, x, y) \<longleftrightarrow> por(x, y)\<close>
        by (unfold logic_o.lor_o_def [OF logic_o]) (rule por_def [symmetric])
    qed
    print_interps logic_o
    have \<open>\<And>x y. por(x, y) \<longleftrightarrow> pnot(pand(pnot(x), pnot(y)))\<close> by (rule loc.lor_o_def)
  }
end

end
