(*  Title:      FOL/ex/LocaleTest.thy
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright (c) 2005 by Clemens Ballarin

Collection of regression tests for locales.
*)

header {* Test of Locale Interpretation *}

theory LocaleTest
imports FOL
begin

ML {* set quick_and_dirty *}    (* allow for thm command in batch mode *)
ML {* set Toplevel.debug *}
ML {* set show_hyps *}
ML {* set show_sorts *}


section {* Context Elements and Locale Expressions *}

text {* Naming convention for global objects: prefixes L and l *}

subsection {* Renaming with Syntax *}

locale (open) LS = var mult +
  assumes "mult(x, y) = mult(y, x)"

print_locale LS

locale LS' = LS mult (infixl "**" 60)

print_locale LS'

locale LT = var mult (infixl "**" 60) +
  assumes "x ** y = y ** x"

locale LU = LT mult (infixl "**" 60) + LT add (infixl "++" 55) + var h +
  assumes hom: "h(x ** y) = h(x) ++ h(y)"

locale LV = LU _ add


subsection {* Constrains *}

locale LZ = fixes a (structure)
locale LZ' = LZ +
  constrains a :: "'a => 'b"
  assumes "a (x :: 'a) = a (y)"
print_locale LZ'


section {* Interpretation *}

text {* Naming convention for global objects: prefixes I and i *}

text {* interpretation input syntax *}

locale IL
locale IM = fixes a and b and c

interpretation test [simp]: IL + IM a b c [x y z] .

print_interps IL    (* output: test *)
print_interps IM    (* output: test *)

interpretation test [simp]: IL print_interps IM .

interpretation IL .

text {* Processing of locale expression *}

locale IA = fixes a assumes asm_A: "a = a"

locale (open) IB = fixes b assumes asm_B [simp]: "b = b"

locale IC = IA + IB + assumes asm_C: "c = c"
  (* TODO: independent type var in c, prohibit locale declaration *)

locale ID = IA + IB + fixes d defines def_D: "d == (a = b)"

theorem (in IA)
  includes ID
  shows True ..

theorem (in ID) True ..

typedecl i
arities i :: "term"


interpretation i1: IC ["X::i" "Y::i"] by (auto intro: IA.intro IC_axioms.intro)

print_interps IA  (* output: i1 *)

(* possible accesses *)
thm i1.a.asm_A thm LocaleTest.i1.a.asm_A
thm i1.asm_A thm LocaleTest.i1.asm_A


(* without prefix *)

interpretation IC ["W::i" "Z::i"] .  (* subsumed by i1: IC *)
interpretation IC ["W::'a" "Z::i"] by (auto intro: IA.intro IC_axioms.intro)
  (* subsumes i1: IA and i1: IC *)


print_interps IA  (* output: <no prefix>, i1 *)

(* possible accesses *)
thm asm_C thm a_b.asm_C thm LocaleTest.a_b.asm_C thm LocaleTest.a_b.asm_C


interpretation i2: ID [X "Y::i" "Y = X"] by (simp add: eq_commute)

print_interps IA  (* output: <no prefix>, i1 *)
print_interps ID  (* output: i2 *)


interpretation i3: ID [X "Y::i"] .

(* duplicate: not registered *)

(* thm i3.a.asm_A *)


print_interps IA  (* output: <no prefix>, i1 *)
print_interps IB  (* output: i1 *)
print_interps IC  (* output: <no prefix, i1 *)
print_interps ID  (* output: i2, i3 *)

(* schematic vars in instantiation not permitted *)
(*
interpretation i4: IA ["?x::?'a1"] apply (rule IA.intro) apply rule done
print_interps IA
*)

interpretation i10: ID + ID a' b' d' [X "Y::i" _ u "v::i" _] .

corollary (in ID) th_x: True ..

(* possible accesses: for each registration *)

thm i2.th_x thm i3.th_x

lemma (in ID) th_y: "d == (a = b)" .

thm i2.th_y thm i3.th_y

lemmas (in ID) th_z = th_y

thm i2.th_z


subsection {* Interpretation in Proof Contexts *}

locale IF = fixes f assumes asm_F: "f & f --> f"

theorem True
proof -
  fix alpha::i and beta::'a and gamma::o
  (* FIXME: omitting type of beta leads to error later at interpret i6 *)
  have alpha_A: "IA(alpha)" by (auto intro: IA.intro)
  interpret i5: IA [alpha] .  (* subsumed *)
  print_interps IA  (* output: <no prefix>, i1 *)
  interpret i6: IC [alpha beta] by (auto intro: IC_axioms.intro)
  print_interps IA   (* output: <no prefix>, i1 *)
  print_interps IC   (* output: <no prefix>, i1, i6 *)
  interpret i11: IF [gamma] by (fast intro: IF.intro)
  thm i11.asm_F      (* gamma is a Free *)
qed rule

theorem (in IA) True
proof -
  print_interps IA
  fix beta and gamma
  interpret i9: ID [a beta _]
    (* no proof obligation for IA !!! *)
    apply - apply (rule refl) apply assumption done
qed rule


(* Definition involving free variable *)

ML {* reset show_sorts *}

locale IE = fixes e defines e_def: "e(x) == x & x"
  notes e_def2 = e_def

lemma (in IE) True thm e_def by fast

interpretation i7: IE ["%x. x"] by simp

thm i7.e_def2 (* has no premise *)

locale IE' = fixes e defines e_def: "e == (%x. x & x)"
  notes e_def2 = e_def

interpretation i7': IE' ["(%x. x)"] by simp

thm i7'.e_def2

(* Definition involving free variable in assm *)

locale (open) IG = fixes g assumes asm_G: "g --> x"
  notes asm_G2 = asm_G

interpretation i8: IG ["False"] by fast

thm i8.asm_G2

text {* Locale without assumptions *}

locale IL1 = notes rev_conjI [intro] = conjI [THEN iffD1 [OF conj_commute]]

lemma "[| P; Q |] ==> P & Q"
proof -
  interpret my: IL1 .          txt {* No chained fact required. *}
  assume Q and P               txt {* order reversed *}
  then show "P & Q" ..         txt {* Applies @{thm my.rev_conjI}. *}
qed

locale IL11 = notes rev_conjI = conjI [THEN iffD1 [OF conj_commute]]

lemma "[| P; Q |] ==> P & Q"
proof -
  interpret [intro]: IL11 .     txt {* Attribute supplied at instantiation. *}
  assume Q and P
  then show "P & Q" ..
qed

subsection {* Simple locale with assumptions *}

consts ibin :: "[i, i] => i" (infixl "#" 60)

axioms i_assoc: "(x # y) # z = x # (y # z)"
  i_comm: "x # y = y # x"

locale IL2 =
  fixes OP (infixl "+" 60)
  assumes assoc: "(x + y) + z = x + (y + z)"
    and comm: "x + y = y + x"

lemma (in IL2) lcomm: "x + (y + z) = y + (x + z)"
proof -
  have "x + (y + z) = (x + y) + z" by (simp add: assoc)
  also have "... = (y + x) + z" by (simp add: comm)
  also have "... = y + (x + z)" by (simp add: assoc)
  finally show ?thesis .
qed

lemmas (in IL2) AC = comm assoc lcomm

lemma "(x::i) # y # z # w = y # x # w # z"
proof -
  interpret my: IL2 ["op #"] by (rule IL2.intro [of "op #", OF i_assoc i_comm])
    txt {* Chained fact required to discharge assumptions of @{text IL2}
      and instantiate parameters. *}
  show ?thesis by (simp only: my.OP.AC)  (* or simply AC *)
qed

subsection {* Nested locale with assumptions *}

locale IL3 =
  fixes OP (infixl "+" 60)
  assumes assoc: "(x + y) + z = x + (y + z)"

locale IL4 = IL3 +
  assumes comm: "x + y = y + x"

lemma (in IL4) lcomm: "x + (y + z) = y + (x + z)"
proof -
  have "x + (y + z) = (x + y) + z" by (simp add: assoc)
  also have "... = (y + x) + z" by (simp add: comm)
  also have "... = y + (x + z)" by (simp add: assoc)
  finally show ?thesis .
qed

lemmas (in IL4) AC = comm assoc lcomm

lemma "(x::i) # y # z # w = y # x # w # z"
proof -
  interpret my: IL4 ["op #"]
    by (auto intro: IL3.intro IL4_axioms.intro i_assoc i_comm)
  show ?thesis by (simp only: my.OP.AC)  (* or simply AC *)
qed

text {* Locale with definition *}

text {* This example is admittedly not very creative :-) *}

locale IL5 = IL4 + var A +
  defines A_def: "A == True"

lemma (in IL5) lem: A
  by (unfold A_def) rule

lemma "IL5(op #) ==> True"
proof -
  assume "IL5(op #)"
  then interpret IL5 ["op #"] by (auto intro: IL5.axioms)
  show ?thesis by (rule lem)  (* lem instantiated to True *)
qed

text {* Interpretation in a context with target *}

lemma (in IL4)
  fixes A (infixl "$" 60)
  assumes A: "IL4(A)"
  shows "(x::i) $ y $ z $ w = y $ x $ w $ z"
proof -
  from A interpret A: IL4 ["A"] by (auto intro: IL4.axioms)
  show ?thesis by (simp only: A.OP.AC)
qed


section {* Interpretation in Locales *}

text {* Naming convention for global objects: prefixes R and r *}

locale (open) Rsemi = var prod (infixl "**" 65) +
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"

locale (open) Rlgrp = Rsemi + var one + var inv +
  assumes lone: "one ** x = x"
    and linv: "inv(x) ** x = one"

lemma (in Rlgrp) lcancel:
  "x ** y = x ** z <-> y = z"
proof
  assume "x ** y = x ** z"
  then have "inv(x) ** x ** y = inv(x) ** x ** z" by (simp add: assoc)
  then show "y = z" by (simp add: lone linv)
qed simp

locale (open) Rrgrp = Rsemi + var one + var inv +
  assumes rone: "x ** one = x"
    and rinv: "x ** inv(x) = one"

lemma (in Rrgrp) rcancel:
  "y ** x = z ** x <-> y = z"
proof
  assume "y ** x = z ** x"
  then have "y ** (x ** inv(x)) = z ** (x ** inv(x))"
    by (simp add: assoc [symmetric])
  then show "y = z" by (simp add: rone rinv)
qed simp

interpretation Rlgrp < Rrgrp
  proof - (* (rule Rrgrp_axioms.intro) *)
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

print_locale Rlgrp

(* use of derived theorem *)

lemma (in Rlgrp)
  "y ** x = z ** x <-> y = z"
  apply (rule rcancel)
  print_interps Rrgrp thm lcancel rcancel
  done

(* circular interpretation *)

interpretation Rrgrp < Rlgrp
  proof -
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

print_locale Rrgrp
print_locale Rlgrp

(* locale with many parameters ---
   interpretations generate alternating group A5 *)

locale RA5 = var A + var B + var C + var D + var E +
  assumes eq: "A <-> B <-> C <-> D <-> E"

interpretation RA5 < RA5 _ _ D E C
print_facts
print_interps RA5
  using A_B_C_D_E.eq apply (blast intro: RA5.intro) done

interpretation RA5 < RA5 C _ E _ A
print_facts
print_interps RA5
  using A_B_C_D_E.eq apply (blast intro: RA5.intro) done

interpretation RA5 < RA5 B C A _ _
print_facts
print_interps RA5
  using A_B_C_D_E.eq apply (blast intro: RA5.intro) done

lemma (in RA5) True
print_facts
print_interps RA5
  ..

interpretation RA5 < RA5 _ C D B _ .
  (* Any even permutation of parameters is subsumed by the above. *)

(* circle of three locales, forward direction *)

locale (open) RA1 = var A + var B + assumes p: "A <-> B"
locale (open) RA2 = var A + var B + assumes q: "A & B | ~ A & ~ B"
locale (open) RA3 = var A + var B + assumes r: "(A --> B) & (B --> A)"

interpretation RA1 < RA2
  print_facts
  using p apply fast done
interpretation RA2 < RA3
  print_facts
  using q apply fast done
interpretation RA3 < RA1
  print_facts
  using r apply fast done

(* circle of three locales, backward direction *)

locale (open) RB1 = var A + var B + assumes p: "A <-> B"
locale (open) RB2 = var A + var B + assumes q: "A & B | ~ A & ~ B"
locale (open) RB3 = var A + var B + assumes r: "(A --> B) & (B --> A)"

interpretation RB1 < RB2
  print_facts
  using p apply fast done
interpretation RB3 < RB1
  print_facts
  using r apply fast done
interpretation RB2 < RB3
  print_facts
  using q apply fast done

lemma (in RB1) True
  print_facts
  ..


(* Group example revisited, with predicates *)

locale Rpsemi = var prod (infixl "**" 65) +
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"

locale Rplgrp = Rpsemi + var one + var inv +
  assumes lone: "one ** x = x"
    and linv: "inv(x) ** x = one"

lemma (in Rplgrp) lcancel:
  "x ** y = x ** z <-> y = z"
proof
  assume "x ** y = x ** z"
  then have "inv(x) ** x ** y = inv(x) ** x ** z" by (simp add: assoc)
  then show "y = z" by (simp add: lone linv)
qed simp

locale Rprgrp = Rpsemi + var one + var inv +
  assumes rone: "x ** one = x"
    and rinv: "x ** inv(x) = one"

lemma (in Rprgrp) rcancel:
  "y ** x = z ** x <-> y = z"
proof
  assume "y ** x = z ** x"
  then have "y ** (x ** inv(x)) = z ** (x ** inv(x))"
    by (simp add: assoc [symmetric])
  then show "y = z" by (simp add: rone rinv)
qed simp

interpretation Rplgrp < Rprgrp
  proof (rule Rprgrp_axioms.intro)
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

print_locale Rplgrp

(* use of derived theorem *)

(* doesn't work yet
lemma (in Rplgrp)
  "y ** x = z ** x <-> y = z"
  apply (rule rcancel)
  print_interps Rprgrp thm lcancel rcancel
  done
*)

(* circular interpretation *)

interpretation Rprgrp < Rplgrp
  proof (rule Rplgrp_axioms.intro)
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

print_locale Rprgrp
print_locale Rplgrp

end

(* Known problems:
- var vs. fixes in locale to be interpreted (interpretation command)
  (possibly caused by early registrations)
- registrations too early -> proper after qed
- predicate generation in group example, thms have wrong hyps
- reprocess registrations in theory (after qed)
*)
