(*  Title:      HOL/Nitpick_Examples/Datatype_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick applied to datatypes.
*)

header {* Examples Featuring Nitpick Applied to Datatypes *}

theory Datatype_Nits
imports Main
begin

nitpick_params [verbose, card = 1\<emdash>8, max_potential = 0,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

primrec rot where
"rot Nibble0 = Nibble1" | "rot Nibble1 = Nibble2" | "rot Nibble2 = Nibble3" |
"rot Nibble3 = Nibble4" | "rot Nibble4 = Nibble5" | "rot Nibble5 = Nibble6" |
"rot Nibble6 = Nibble7" | "rot Nibble7 = Nibble8" | "rot Nibble8 = Nibble9" |
"rot Nibble9 = NibbleA" | "rot NibbleA = NibbleB" | "rot NibbleB = NibbleC" |
"rot NibbleC = NibbleD" | "rot NibbleD = NibbleE" | "rot NibbleE = NibbleF" |
"rot NibbleF = Nibble0"

lemma "rot n \<noteq> n"
nitpick [card = 1\<emdash>8,16, verbose, expect = none]
sorry

lemma "rot Nibble2 \<noteq> Nibble3"
nitpick [card = 1, expect = none]
nitpick [card = 2, max Nibble4 = 0, expect = genuine]
nitpick [card = 2, max Nibble2 = 0, expect = none]
oops

lemma "(rot ^^ 15) n \<noteq> n"
nitpick [card = 17, expect = none]
sorry

lemma "(rot ^^ 15) n = n"
nitpick [card = 17, expect = genuine]
oops

lemma "(rot ^^ 16) n = n"
nitpick [card = 17, expect = none]
oops

datatype ('a, 'b) pd = Pd "'a \<times> 'b"

fun fs where
"fs (Pd (a, _)) = a"

fun sn where
"sn (Pd (_, b)) = b"

lemma "fs (Pd p) = fst p"
nitpick [card = 12, expect = none]
sorry

lemma "fs (Pd p) = snd p"
nitpick [expect = genuine]
oops

lemma "sn (Pd p) = snd p"
nitpick [card = 12, expect = none]
sorry

lemma "sn (Pd p) = fst p"
nitpick [expect = genuine]
oops

lemma "fs (Pd ((a, b), (c, d))) = (a, b)"
nitpick [expect = none]
sorry

lemma "fs (Pd ((a, b), (c, d))) = (c, d)"
nitpick [expect = genuine]
oops

datatype ('a, 'b) fn = Fn "'a \<Rightarrow> 'b"

fun app where
"app (Fn f) x = f x"

lemma "app (Fn g) y = g y"
nitpick [expect = none]
sorry

lemma "app (Fn g) y = g' y"
nitpick [expect = genuine]
oops

lemma "app (Fn g) y = g y'"
nitpick [expect = genuine]
oops

end
