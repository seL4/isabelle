(*  Title:      HOL/Nitpick_Examples/Record_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick applied to records.
*)

header {* Examples Featuring Nitpick Applied to Records *}

theory Record_Nits
imports Main
begin

nitpick_params [verbose, card = 1\<emdash>6, max_potential = 0,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

record point2d =
  xc :: int
  yc :: int

(* FIXME: Invalid intermediate term
lemma "\<lparr>xc = x, yc = y\<rparr> = p\<lparr>xc := x, yc := y\<rparr>"
nitpick [expect = none]
sorry

lemma "\<lparr>xc = x, yc = y\<rparr> = p\<lparr>xc := x\<rparr>"
nitpick [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y\<rparr> \<noteq> p"
nitpick [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y\<rparr> = p"
nitpick [expect = genuine]
oops

record point3d = point2d +
  zc :: int

lemma "\<lparr>xc = x, yc = y, zc = z\<rparr> = p\<lparr>xc := x, yc := y, zc := z\<rparr>"
nitpick [expect = none]
sorry

lemma "\<lparr>xc = x, yc = y, zc = z\<rparr> = p\<lparr>xc := x\<rparr>"
nitpick [expect = genuine]
oops

lemma "\<lparr>xc = x, yc = y, zc = z\<rparr> = p\<lparr>zc := z\<rparr>"
nitpick [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z\<rparr> \<noteq> p"
nitpick [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z\<rparr> = p"
nitpick [expect = genuine]
oops

record point4d = point3d +
  wc :: int

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>xc := x, yc := y, zc := z, wc := w\<rparr>"
nitpick [expect = none]
sorry

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>xc := x\<rparr>"
nitpick [expect = genuine]
oops

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>zc := z\<rparr>"
nitpick [expect = genuine]
oops

lemma "\<lparr>xc = x, yc = y, zc = z, wc = w\<rparr> = p\<lparr>wc := w\<rparr>"
nitpick [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z, wc := w\<rparr> \<noteq> p"
nitpick [expect = genuine]
oops

lemma "p\<lparr>xc := x, yc := y, zc := z, wc := w\<rparr> = p"
nitpick [expect = genuine]
oops
*)

end
