(*  Title:      HOL/Lex/RegSet_of_nat_DA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversion of deterministic automata into regular sets.

To generate a regual expression, the alphabet must be finite.
regexp needs to be supplied with an 'a list for a unique order

add_Atom d i j r a = (if d a i = j then Union r (Atom a) else r)
atoms d i j as = foldl (add_Atom d i j) Empty as

regexp as d i j 0 = (if i=j then Union (Star Empty) (atoms d i j as)
                        else atoms d i j as
*)

theory RegSet_of_nat_DA = RegSet + DA:

types 'a nat_next = "'a => nat => nat"

syntax deltas :: "'a nat_next => 'a list => nat => nat"
translations "deltas" == "foldl2"

consts trace :: "'a nat_next => nat => 'a list => nat list"
primrec
"trace d i [] = []"
"trace d i (x#xs) = d x i # trace d (d x i) xs"

(* conversion a la Warshall *)

consts regset :: "'a nat_next => nat => nat => nat => 'a list set"
primrec
"regset d i j 0 = (if i=j then insert [] {[a] | a. d a i = j}
                          else {[a] | a. d a i = j})"
"regset d i j (Suc k) = regset d i j k Un
                        conc (regset d i k k)
                             (conc (star(regset d k k k))
                                   (regset d k j k))"

constdefs
 regset_of_DA :: "('a,nat)da => nat => 'a list set"
"regset_of_DA A k == UN j:{j. j<k & fin A j}. regset (next A) (start A) j k"

 bounded :: "'a => nat => bool"
"bounded d k == !n. n < k --> (!x. d x n < k)"

declare
  in_set_butlast_appendI[simp,intro] less_SucI[simp] image_eqI[simp]

(* Lists *)

lemma butlast_empty[iff]:
  "(butlast xs = []) = (case xs of [] => True | y#ys => ys=[])"
by (case_tac "xs") simp_all

lemma in_set_butlast_concatI:
 "x:set(butlast xs) ==> xs:set xss ==> x:set(butlast(concat xss))"
apply (induct "xss")
 apply simp
apply (simp add: butlast_append del: ball_simps)
apply (rule conjI)
 apply (clarify)
 apply (erule disjE)
  apply (blast)
 apply (subgoal_tac "xs=[]")
  apply simp
 apply (blast)
apply (blast dest: in_set_butlastD)
done

(* Regular sets *)

(* The main lemma:
   how to decompose a trace into a prefix, a list of loops and a suffix.
*)
lemma decompose[rule_format]:
 "!i. k : set(trace d i xs) --> (EX pref mids suf.
  xs = pref @ concat mids @ suf &
  deltas d pref i = k & (!n:set(butlast(trace d i pref)). n ~= k) &
  (!mid:set mids. (deltas d mid k = k) &
                  (!n:set(butlast(trace d k mid)). n ~= k)) &
  (!n:set(butlast(trace d k suf)). n ~= k))"
apply (induct "xs")
 apply (simp)
apply (rename_tac a as)
apply (intro strip)
apply (case_tac "d a i = k")
 apply (rule_tac x = "[a]" in exI)
 apply simp
 apply (case_tac "k : set(trace d (d a i) as)")
  apply (erule allE)
  apply (erule impE)
   apply (assumption)
  apply (erule exE)+
  apply (rule_tac x = "pref#mids" in exI)
  apply (rule_tac x = "suf" in exI)
  apply simp
 apply (rule_tac x = "[]" in exI)
 apply (rule_tac x = "as" in exI)
 apply simp
 apply (blast dest: in_set_butlastD)
apply simp
apply (erule allE)
apply (erule impE)
 apply (assumption)
apply (erule exE)+
apply (rule_tac x = "a#pref" in exI)
apply (rule_tac x = "mids" in exI)
apply (rule_tac x = "suf" in exI)
apply simp
done

lemma length_trace[simp]: "!!i. length(trace d i xs) = length xs"
by (induct "xs") simp_all

lemma deltas_append[simp]:
  "!!i. deltas d (xs@ys) i = deltas d ys (deltas d xs i)"
by (induct "xs") simp_all

lemma trace_append[simp]:
  "!!i. trace d i (xs@ys) = trace d i xs @ trace d (deltas d xs i) ys"
by (induct "xs") simp_all

lemma trace_concat[simp]:
 "(!xs: set xss. deltas d xs i = i) ==>
  trace d i (concat xss) = concat (map (trace d i) xss)"
by (induct "xss") simp_all

lemma trace_is_Nil[simp]: "!!i. (trace d i xs = []) = (xs = [])"
by (case_tac "xs") simp_all

lemma trace_is_Cons_conv[simp]:
 "(trace d i xs = n#ns) =
  (case xs of [] => False | y#ys => n = d y i & ns = trace d n ys)"
apply (case_tac "xs")
apply simp_all
apply (blast)
done

lemma set_trace_conv:
 "!!i. set(trace d i xs) =
  (if xs=[] then {} else insert(deltas d xs i)(set(butlast(trace d i xs))))"
apply (induct "xs")
 apply (simp)
apply (simp add: insert_commute)
done

lemma deltas_concat[simp]:
 "(!mid:set mids. deltas d mid k = k) ==> deltas d (concat mids) k = k"
by (induct mids) simp_all

lemma lem: "[| n < Suc k; n ~= k |] ==> n < k"
by arith

lemma regset_spec:
 "!!i j xs. xs : regset d i j k =
        ((!n:set(butlast(trace d i xs)). n < k) & deltas d xs i = j)"
apply (induct k)
 apply(simp split: list.split)
 apply(fastsimp)
apply (simp add: conc_def)
apply (rule iffI)
 apply (erule disjE)
  apply simp
 apply (erule exE conjE)+
 apply simp
 apply (subgoal_tac
      "(!m:set(butlast(trace d n xsb)). m < Suc n) & deltas d xsb n = n")
  apply (simp add: set_trace_conv butlast_append ball_Un)
 apply (erule star.induct)
  apply (simp)
 apply (simp add: set_trace_conv butlast_append ball_Un)
apply (case_tac "n : set(butlast(trace d i xs))")
 prefer 2 apply (rule disjI1)
 apply (blast intro:lem)
apply (rule disjI2)
apply (drule in_set_butlastD[THEN decompose])
apply (clarify)
apply (rule_tac x = "pref" in exI)
apply simp
apply (rule conjI)
 apply (rule ballI)
 apply (rule lem)
  prefer 2 apply simp
 apply (drule bspec) prefer 2 apply assumption
 apply simp
apply (rule_tac x = "concat mids" in exI)
apply (simp)
apply (rule conjI)
 apply (rule concat_in_star)
 apply simp
 apply (rule ballI)
 apply (rule ballI)
 apply (rule lem)
  prefer 2 apply simp
 apply (drule bspec) prefer 2 apply assumption
 apply (simp add: image_eqI in_set_butlast_concatI)
apply (rule ballI)
apply (rule lem)
 apply auto
done

lemma trace_below:
 "bounded d k ==> !i. i < k --> (!n:set(trace d i xs). n < k)"
apply (unfold bounded_def)
apply (induct "xs")
 apply simp
apply (simp (no_asm))
apply (blast)
done

lemma regset_below:
 "[| bounded d k; i < k; j < k |] ==>
  regset d i j k = {xs. deltas d xs i = j}"
apply (rule set_ext)
apply (simp add: regset_spec)
apply (blast dest: trace_below in_set_butlastD)
done

lemma deltas_below:
 "!!i. bounded d k ==> i < k ==> deltas d w i < k"
apply (unfold bounded_def)
apply (induct "w")
 apply simp_all
done

lemma regset_DA_equiv:
 "[| bounded (next A) k; start A < k; j < k |] ==> \
\ w : regset_of_DA A k = accepts A w"
apply(unfold regset_of_DA_def)
apply (simp cong: conj_cong
            add: regset_below deltas_below accepts_def delta_def)
done

end
