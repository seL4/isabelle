(*  Title:      FOL/ex/LocaleTest.thy
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright (c) 2005 by Clemens Ballarin

Collection of regression tests for locales.
*)

header {* Test of Locale instantiation *}

theory LocaleTest = FOL:

(* registration input syntax *)

locale L
locale M = fixes a and b and c

registration test [simp]: L + M a b c [x y z] .

print_registrations L
print_registrations M

registration test [simp]: L .

registration L .

(* processing of locale expression *)

ML {* reset show_hyps *}

locale A = fixes a assumes asm_A: "a = a"

locale (open) B = fixes b assumes asm_B [simp]: "b = b"

locale C = A + B + assumes asm_C: "c = c"
  (* TODO: independent type var in c, prohibit locale declaration *)

locale D = A + B + fixes d defines def_D: "d == (a = b)"

ML {* set show_sorts *}

typedecl i
arities i :: "term"

ML {* set Toplevel.debug *}

registration p1: C ["X::'b" "Y"] by (auto intro: A.intro C_axioms.intro)
  (* both X and Y get type 'b since 'b is the internal type of parameter b,
     not wanted, but put up with for now. *)

ML {* set show_hyps *}

print_registrations A

(* thm asm_A a.asm_A p1.a.asm_A *)

(*
registration p2: D [X Y Z] sorry

print_registrations D
*)

registration p3: D [X Y] by (auto intro: A.intro)

print_registrations A
print_registrations B
print_registrations C
print_registrations D

(* not permitted
registration p4: A ["?x10"] apply (rule A.intro) apply rule done

print_registrations A
*)

end
