(*  Title:      HOL/Lex/AutoChopper.thy
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM

auto_chopper turns an automaton into a chopper. Tricky, because primrec.

is_auto_chopper requires its argument to produce longest_prefix_choppers
wrt the language accepted by the automaton.

Main result: auto_chopper satisfies the is_auto_chopper specification.

WARNING: auto_chopper is exponential(?)
if the recursive calls in the penultimate argument are evaluated eagerly.

A more efficient version is defined in AutoChopper1.

But both versions are far too specific. Better development in Scanner.thy and
its antecedents.
*)

theory AutoChopper = DA + Chopper:

constdefs
 is_auto_chopper :: "(('a,'s)da => 'a chopper) => bool"
"is_auto_chopper(chopperf) ==
    !A. is_longest_prefix_chopper(accepts A)(chopperf A)"

consts
  acc :: "('a,'s)da \<Rightarrow> 's \<Rightarrow> 'a list list * 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list
          \<Rightarrow> 'a list \<Rightarrow> 'a list list * 'a list"

primrec
  "acc A s r ps []     zs = (if ps=[] then r else (ps#fst(r),snd(r)))" 
  "acc A s r ps (x#xs) zs =
            (let t = next A x s
             in if fin A t
                then acc A t (acc A (start A) ([],xs) [] xs [])
                         (zs@[x]) xs (zs@[x])
                else acc A t r ps xs (zs@[x]))"

constdefs
 auto_chopper :: "('a,'s)da => 'a chopper"
"auto_chopper A xs == acc A (start A) ([],xs) [] xs []"

(* acc_prefix is an auxiliary notion for the proof *)
constdefs
 acc_prefix :: "('a,'s)da => 'a list => 's => bool"
"acc_prefix A xs s \<equiv> \<exists>us. us \<le> xs \<and> us \<noteq> [] \<and> fin A (delta A us s)"

(*
Main result: auto_chopper satisfies the is_auto_chopper specification.
*)

declare
  ex_simps[simp del] all_simps[simp del] split_paired_All[simp del]
  Let_def[simp]

lemma acc_prefix_Nil[simp]: "~acc_prefix A [] s"
by(simp add:acc_prefix_def)

lemma acc_prefix_Cons[simp]:
 "acc_prefix A (x#xs) s = (fin A (next A x s) | acc_prefix A xs (next A x s))"
apply (simp add: prefix_Cons acc_prefix_def)
apply safe
  apply (simp)
  apply (case_tac "zs = []")
   apply (simp)
  apply (fast)
 apply (rule_tac x = "[x]" in exI)
 apply (simp add:eq_sym_conv)
apply (rule_tac x = "x#us" in exI)
apply (simp)
done

lemma accept_not_Nil[simp]:
  "!!st us p y ys. acc A st p (ys@[y]) xs us \<noteq> ([],zs)"
by (induct xs) simp_all

lemma no_acc:
  "!!st us. acc A st ([],ys) [] xs us = ([], zs) \<Longrightarrow>
            zs = ys \<and> (\<forall>ys. ys \<noteq> [] \<and> ys \<le> xs \<longrightarrow> ~fin A (delta A ys st))"
apply (induct xs)
 apply (simp cong: conj_cong)
apply (simp add: prefix_Cons cong: conj_cong split:split_if_asm)
apply (intro strip)
apply (elim conjE exE)
apply (simp)
apply (case_tac "zsa = []")
 apply (simp)
apply (fast)
done

lemma ex_special: "EX x. P(f(x)) ==> EX y. P(y)"
by (fast)

lemma step2_a:
"!!r erk l rst st ys yss zs::'a list.
 acc A st (l,rst) erk xs r = (ys#yss, zs) \<Longrightarrow>
 ys@concat(yss)@zs = (if acc_prefix A xs st then r@xs else erk@concat(l)@rst)"
apply (induct "xs")
 apply (simp cong: conj_cong split:split_if_asm)
apply (simp split:split_if_asm)
apply (rule_tac p = "acc A (start A) ([],list) [] list []" in PairE)
apply (rename_tac vss lrst)
apply (simp)
apply (case_tac vss)
 apply (simp)
 apply (fast dest!: no_acc)
apply (simp)
done

lemma step2_b:
 "!!st erk r l rest ys yss zs. acc A st (l,rest) erk xs r = (ys#yss, zs) \<Longrightarrow>
       if acc_prefix A xs st then ys \<noteq> []
\      else ys \<noteq> [] \<or> (erk=[] \<and> (l,rest) = (ys#yss,zs))"
apply (simp)
apply (induct "xs")
 apply (simp cong: conj_cong split:split_if_asm)
apply (simp cong: conj_cong split:split_if_asm)
apply (rule_tac p = "acc A (start A) ([],list) [] list []" in PairE)
apply (rename_tac vss lrst)
apply (simp)
apply (case_tac "acc_prefix A list (next A a st)")
 apply (simp)
apply (subgoal_tac "r @ [a] \<noteq> []")
 apply (fast)
apply (simp)
done

lemma step2_c:
 "!!st erk r l rest ys yss zs. acc A st (l,rest) erk xs r = (ys#yss, zs) \<Longrightarrow>
  if acc_prefix A xs st then EX g. ys = r@g & fin A (delta A g st)
  else (erk \<noteq> [] & erk=ys) | (erk=[] & (l,rest) = (ys#yss,zs))"
apply (simp)
apply (induct "xs")
 apply (simp cong: conj_cong split:split_if_asm)
apply (simp cong: conj_cong split:split_if_asm)
 apply (rule_tac p = "acc A (start A) ([],list) [] list []" in PairE)
 apply (rename_tac vss lrst)
 apply (simp)
 apply (case_tac "acc_prefix A list (next A a st)")
  apply (rule_tac f = "%k. a#k" in ex_special)
  apply (simp)
  apply (rule_tac t = "%k. ys=r@a#k" and s = "%k. ys=(r@[a])@k" in subst)
   apply (simp)
  apply (fast)
 apply (rule_tac x = "[a]" in exI)
 apply (simp)
 apply (subgoal_tac "r @ [a] ~= []")
  apply (rule sym)
  apply (fast)
 apply (simp)
apply (intro strip)
apply (rule_tac f = "%k. a#k" in ex_special)
apply (simp)
apply (rule_tac t = "%k. ys=r@a#k" and s = "%k. ys=(r@[a])@k" in subst)
 apply (simp)
apply (fast)
done

lemma step2_d:
 "!!st erk r l rest ys yss zs. acc A st (l,rest) erk xs r = (ys#yss, zs) \<Longrightarrow>
  if acc_prefix A xs st
  then acc A (start A) ([],concat(yss)@zs) [] (concat(yss)@zs) [] = (yss,zs)
  else (erk~=[] & (l,rest)=(yss,zs)) | (erk=[] & (l, rest)=(ys#yss,zs))"
apply (simp)
apply (induct "xs")
 apply (simp cong: conj_cong split:split_if_asm)
apply (simp cong: conj_cong split:split_if_asm)
apply (rule_tac p = "acc A (start A) ([],list) [] list []" in PairE)
apply (rename_tac vss lrst)
apply (simp)
apply (case_tac "acc_prefix A list (next A a st)")
 apply (simp)
apply (subgoal_tac "acc A (start A) ([],list) [] list [] = (yss,zs)")
 prefer 2
 apply (simp)
 apply (subgoal_tac "r@[a] ~= []")
  apply (fast)
 apply (simp)
apply (subgoal_tac "concat(yss) @ zs = list")
 apply (simp)
apply (case_tac "yss = []")
 apply (simp)
 apply (fast dest!: no_acc)
apply (erule neq_Nil_conv[THEN iffD1, THEN exE])
apply (auto simp add:step2_a)
done

lemma step2_e:
"!!st erk r p ys yss zs. acc A st p erk xs r = (ys#yss, zs) \<Longrightarrow>
  if acc_prefix A xs st
  then ? g. ys=r@g & (!as. as<=xs & g<=as & g~=as --> ~fin A (delta A as st))
  else (erk~=[] & ys=erk) | (erk=[] & (ys#yss,zs)=p)"
apply (simp)
apply (induct "xs")
 apply (simp cong: conj_cong split:split_if_asm)
apply (simp cong: conj_cong split:split_if_asm)
apply (case_tac "acc_prefix A list (next A a st)")
  apply (rule_tac f = "%k. a#k" in ex_special)
  apply (rule_tac t = "%k. ys=r@a#k" and s = "%k. ys=(r@[a])@k" in subst)
   apply (simp)
  apply (rule_tac P = "%k. ys = (r@[a])@k & (!as. as<=list & k<=as & k ~= as --> ~ fin A (delta A as (next A a st)))" in exE)
   apply fastsimp
  apply (rule_tac x = "x" in exI)
  apply (simp)
  apply (rule allI)
  apply (case_tac "as")
   apply (simp)
  apply (simp cong:conj_cong)
 apply (rule_tac f = "%k. a#k" in ex_special)
 apply (rule_tac t = "%k. ys=r@a#k" and s = "%k. ys=(r@[a])@k" in subst)
  apply (simp)
 apply(subgoal_tac "ys = r @ [a]")
  prefer 2 apply fastsimp
 apply(rule_tac x = "[]" in exI)
 apply simp
 apply (rule allI)
 apply (case_tac "as")
  apply (simp)
 apply (simp add: acc_prefix_def cong: conj_cong)
 apply (fastsimp)
apply (intro strip)
apply (rule_tac P = "%k. ys=(r@[a])@k & (!as. as<=list & k<=as & k~=as --> ~ fin A (delta A as (next A a st)))" in exE)
 apply rules
apply simp
apply(elim conjE exE)
apply (rule allI)
apply (case_tac as)
 apply (simp)
apply (simp cong: conj_cong)
done

declare split_paired_All[simp]

lemma auto_chopper_is_auto_chopper:
 "is_auto_chopper(auto_chopper)"
apply(unfold accepts_def is_auto_chopper_def auto_chopper_def
             Chopper.is_longest_prefix_chopper_def)
apply(rule no_acc allI impI conjI | assumption)+
 apply (rule mp)
  prefer 2 apply (erule step2_b)
 apply (simp)
apply (rule conjI)
 apply (rule mp)
  prefer 2 apply (erule step2_c)
 apply (simp)
apply (rule conjI)
 apply (simp add: step2_a)
apply (rule conjI)
 apply (rule mp)
  prefer 2 apply (erule step2_d)
 apply (simp)
apply (rule mp)
 prefer 2 apply (erule step2_e)
apply (simp)
done

end
