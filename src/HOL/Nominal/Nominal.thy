(* $Id$ *)

theory nominal 
imports Main
  uses ("nominal_package.ML") ("nominal_induct.ML") ("nominal_permeq.ML")
begin 

ML {* reset NameSpace.unique_names; *}

section {* Permutations *}
(*======================*)

types 
  'x prm = "('x \<times> 'x) list"

(* polymorphic operations for permutation and swapping*)
consts 
  perm :: "'x prm \<Rightarrow> 'a \<Rightarrow> 'a"     ("_ \<bullet> _" [80,80] 80)
  swap :: "('x \<times> 'x) \<Rightarrow> 'x \<Rightarrow> 'x"

(* permutation on sets *)
defs (overloaded)
  perm_set_def:  "pi\<bullet>(X::'a set) \<equiv> {pi\<bullet>a | a. a\<in>X}"

(* permutation on units and products *)
primrec (perm_unit)
  "pi\<bullet>()    = ()"

primrec (perm_prod)
  "pi\<bullet>(a,b) = (pi\<bullet>a,pi\<bullet>b)"

lemma perm_fst:
  "pi\<bullet>(fst x) = fst (pi\<bullet>x)"
 by (cases x, simp)

lemma perm_snd:
  "pi\<bullet>(snd x) = snd (pi\<bullet>x)"
 by (cases x, simp)

(* permutation on lists *)
primrec (perm_list)
  perm_nil_def:  "pi\<bullet>[]     = []"
  perm_cons_def: "pi\<bullet>(x#xs) = (pi\<bullet>x)#(pi\<bullet>xs)"

lemma perm_append:
  fixes pi :: "'x prm"
  and   l1 :: "'a list"
  and   l2 :: "'a list"
  shows "pi\<bullet>(l1@l2) = (pi\<bullet>l1)@(pi\<bullet>l2)"
  by (induct l1, auto)

lemma perm_rev:
  fixes pi :: "'x prm"
  and   l  :: "'a list"
  shows "pi\<bullet>(rev l) = rev (pi\<bullet>l)"
  by (induct l, simp_all add: perm_append)

(* permutation on functions *)
defs (overloaded)
  perm_fun_def: "pi\<bullet>(f::'a\<Rightarrow>'b) \<equiv> (\<lambda>x. pi\<bullet>f((rev pi)\<bullet>x))"

(* permutation on bools *)
primrec (perm_bool)
  perm_true_def:  "pi\<bullet>True  = True"
  perm_false_def: "pi\<bullet>False = False"

(* permutation on options *)
primrec (perm_option)
  perm_some_def:  "pi\<bullet>Some(x) = Some(pi\<bullet>x)"
  perm_none_def:  "pi\<bullet>None    = None"

(* a "private" copy of the option type used in the abstraction function *)
datatype 'a nOption = nSome 'a | nNone

primrec (perm_noption)
  perm_Nsome_def:  "pi\<bullet>nSome(x) = nSome(pi\<bullet>x)"
  perm_Nnone_def:  "pi\<bullet>nNone    = nNone"

(* permutation on characters (used in strings) *)
defs (overloaded)
  perm_char_def: "pi\<bullet>(s::char) \<equiv> s"

(* permutation on ints *)
defs (overloaded)
  perm_int_def:    "pi\<bullet>(i::int) \<equiv> i"

(* permutation on nats *)
defs (overloaded)
  perm_nat_def:    "pi\<bullet>(i::nat) \<equiv> i"

section {* permutation equality *}
(*==============================*)

constdefs
  prm_eq :: "'x prm \<Rightarrow> 'x prm \<Rightarrow> bool"  (" _ \<sim> _ " [80,80] 80)
  "pi1 \<sim> pi2 \<equiv> \<forall>a::'x. pi1\<bullet>a = pi2\<bullet>a"

section {* Support, Freshness and Supports*}
(*========================================*)
constdefs
   supp :: "'a \<Rightarrow> ('x set)"  
   "supp x \<equiv> {a . (infinite {b . [(a,b)]\<bullet>x \<noteq> x})}"

   fresh :: "'x \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<sharp> _" [80,80] 80)
   "a \<sharp> x \<equiv> a \<notin> supp x"

   supports :: "'x set \<Rightarrow> 'a \<Rightarrow> bool" (infixl 80)
   "S supports x \<equiv> \<forall>a b. (a\<notin>S \<and> b\<notin>S \<longrightarrow> [(a,b)]\<bullet>x=x)"

lemma supp_fresh_iff: 
  fixes x :: "'a"
  shows "(supp x) = {a::'x. \<not>a\<sharp>x}"
apply(simp add: fresh_def)
done

lemma supp_unit:
  shows "supp () = {}"
  by (simp add: supp_def)

lemma supp_prod: 
  fixes x :: "'a"
  and   y :: "'b"
  shows "(supp (x,y)) = (supp x)\<union>(supp y)"
  by  (force simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma supp_list_nil:
  shows "supp [] = {}"
apply(simp add: supp_def)
done

lemma supp_list_cons:
  fixes x  :: "'a"
  and   xs :: "'a list"
  shows "supp (x#xs) = (supp x)\<union>(supp xs)"
apply(auto simp add: supp_def Collect_imp_eq Collect_neg_eq)
done

lemma supp_list_append:
  fixes xs :: "'a list"
  and   ys :: "'a list"
  shows "supp (xs@ys) = (supp xs)\<union>(supp ys)"
  by (induct xs, auto simp add: supp_list_nil supp_list_cons)

lemma supp_list_rev:
  fixes xs :: "'a list"
  shows "supp (rev xs) = (supp xs)"
  by (induct xs, auto simp add: supp_list_append supp_list_cons supp_list_nil)

lemma supp_bool:
  fixes x  :: "bool"
  shows "supp (x) = {}"
  apply(case_tac "x")
  apply(simp_all add: supp_def)
done

lemma supp_some:
  fixes x :: "'a"
  shows "supp (Some x) = (supp x)"
  apply(simp add: supp_def)
  done

lemma supp_none:
  fixes x :: "'a"
  shows "supp (None) = {}"
  apply(simp add: supp_def)
  done

lemma supp_int:
  fixes i::"int"
  shows "supp (i) = {}"
  apply(simp add: supp_def perm_int_def)
  done

lemma fresh_prod:
  fixes a :: "'x"
  and   x :: "'a"
  and   y :: "'b"
  shows "a\<sharp>(x,y) = (a\<sharp>x \<and> a\<sharp>y)"
  by (simp add: fresh_def supp_prod)

lemma fresh_list_nil:
  fixes a :: "'x"
  shows "a\<sharp>([]::'a list)"
  by (simp add: fresh_def supp_list_nil) 

lemma fresh_list_cons:
  fixes a :: "'x"
  and   x :: "'a"
  and   xs :: "'a list"
  shows "a\<sharp>(x#xs) = (a\<sharp>x \<and> a\<sharp>xs)"
  by (simp add: fresh_def supp_list_cons)

lemma fresh_list_append:
  fixes a :: "'x"
  and   xs :: "'a list"
  and   ys :: "'a list"
  shows "a\<sharp>(xs@ys) = (a\<sharp>xs \<and> a\<sharp>ys)"
  by (simp add: fresh_def supp_list_append)

lemma fresh_list_rev:
  fixes a :: "'x"
  and   xs :: "'a list"
  shows "a\<sharp>(rev xs) = a\<sharp>xs"
  by (simp add: fresh_def supp_list_rev)

lemma fresh_none:
  fixes a :: "'x"
  shows "a\<sharp>None"
  apply(simp add: fresh_def supp_none)
  done

lemma fresh_some:
  fixes a :: "'x"
  and   x :: "'a"
  shows "a\<sharp>(Some x) = a\<sharp>x"
  apply(simp add: fresh_def supp_some)
  done

section {* Abstract Properties for Permutations and  Atoms *}
(*=========================================================*)

(* properties for being a permutation type *)
constdefs 
  "pt TYPE('a) TYPE('x) \<equiv> 
     (\<forall>(x::'a). ([]::'x prm)\<bullet>x = x) \<and> 
     (\<forall>(pi1::'x prm) (pi2::'x prm) (x::'a). (pi1@pi2)\<bullet>x = pi1\<bullet>(pi2\<bullet>x)) \<and> 
     (\<forall>(pi1::'x prm) (pi2::'x prm) (x::'a). pi1 \<sim> pi2 \<longrightarrow> pi1\<bullet>x = pi2\<bullet>x)"

(* properties for being an atom type *)
constdefs 
  "at TYPE('x) \<equiv> 
     (\<forall>(x::'x). ([]::'x prm)\<bullet>x = x) \<and>
     (\<forall>(a::'x) (b::'x) (pi::'x prm) (x::'x). ((a,b)#(pi::'x prm))\<bullet>x = swap (a,b) (pi\<bullet>x)) \<and> 
     (\<forall>(a::'x) (b::'x) (c::'x). swap (a,b) c = (if a=c then b else (if b=c then a else c))) \<and> 
     (infinite (UNIV::'x set))"

(* property of two atom-types being disjoint *)
constdefs
  "disjoint TYPE('x) TYPE('y) \<equiv> 
       (\<forall>(pi::'x prm)(x::'y). pi\<bullet>x = x) \<and> 
       (\<forall>(pi::'y prm)(x::'x). pi\<bullet>x = x)"

(* composition property of two permutation on a type 'a *)
constdefs
  "cp TYPE ('a) TYPE('x) TYPE('y) \<equiv> 
      (\<forall>(pi2::'y prm) (pi1::'x prm) (x::'a) . pi1\<bullet>(pi2\<bullet>x) = (pi1\<bullet>pi2)\<bullet>(pi1\<bullet>x))" 

(* property of having finite support *)
constdefs 
  "fs TYPE('a) TYPE('x) \<equiv> \<forall>(x::'a). finite ((supp x)::'x set)"

section {* Lemmas about the atom-type properties*}
(*==============================================*)

lemma at1: 
  fixes x::"'x"
  assumes a: "at TYPE('x)"
  shows "([]::'x prm)\<bullet>x = x"
  using a by (simp add: at_def)

lemma at2: 
  fixes a ::"'x"
  and   b ::"'x"
  and   x ::"'x"
  and   pi::"'x prm"
  assumes a: "at TYPE('x)"
  shows "((a,b)#pi)\<bullet>x = swap (a,b) (pi\<bullet>x)"
  using a by (simp only: at_def)

lemma at3: 
  fixes a ::"'x"
  and   b ::"'x"
  and   c ::"'x"
  assumes a: "at TYPE('x)"
  shows "swap (a,b) c = (if a=c then b else (if b=c then a else c))"
  using a by (simp only: at_def)

(* rules to calculate simple premutations *)
lemmas at_calc = at2 at1 at3

lemma at4: 
  assumes a: "at TYPE('x)"
  shows "infinite (UNIV::'x set)"
  using a by (simp add: at_def)

lemma at_append:
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   c   :: "'x"
  assumes at: "at TYPE('x)" 
  shows "(pi1@pi2)\<bullet>c = pi1\<bullet>(pi2\<bullet>c)"
proof (induct pi1)
  case Nil show ?case by (simp add: at1[OF at])
next
  case (Cons x xs)
  assume i: "(xs @ pi2)\<bullet>c  =  xs\<bullet>(pi2\<bullet>c)"
  have "(x#xs)@pi2 = x#(xs@pi2)" by simp
  thus ?case using i by (cases "x", simp add:  at2[OF at])
qed
 
lemma at_swap:
  fixes a :: "'x"
  and   b :: "'x"
  and   c :: "'x"
  assumes at: "at TYPE('x)" 
  shows "swap (a,b) (swap (a,b) c) = c"
  by (auto simp add: at3[OF at])

lemma at_rev_pi:
  fixes pi :: "'x prm"
  and   c  :: "'x"
  assumes at: "at TYPE('x)"
  shows "(rev pi)\<bullet>(pi\<bullet>c) = c"
proof(induct pi)
  case Nil show ?case by (simp add: at1[OF at])
next
  case (Cons x xs) thus ?case 
    by (cases "x", simp add: at2[OF at] at_append[OF at] at1[OF at] at_swap[OF at])
qed

lemma at_pi_rev:
  fixes pi :: "'x prm"
  and   x  :: "'x"
  assumes at: "at TYPE('x)"
  shows "pi\<bullet>((rev pi)\<bullet>x) = x"
  by (rule at_rev_pi[OF at, of "rev pi" _,simplified])

lemma at_bij1: 
  fixes pi :: "'x prm"
  and   x  :: "'x"
  and   y  :: "'x"
  assumes at: "at TYPE('x)"
  and     a:  "(pi\<bullet>x) = y"
  shows   "x=(rev pi)\<bullet>y"
proof -
  from a have "y=(pi\<bullet>x)" by (rule sym)
  thus ?thesis by (simp only: at_rev_pi[OF at])
qed

lemma at_bij2: 
  fixes pi :: "'x prm"
  and   x  :: "'x"
  and   y  :: "'x"
  assumes at: "at TYPE('x)"
  and     a:  "((rev pi)\<bullet>x) = y"
  shows   "x=pi\<bullet>y"
proof -
  from a have "y=((rev pi)\<bullet>x)" by (rule sym)
  thus ?thesis by (simp only: at_pi_rev[OF at])
qed

lemma at_bij:
  fixes pi :: "'x prm"
  and   x  :: "'x"
  and   y  :: "'x"
  assumes at: "at TYPE('x)"
  shows "(pi\<bullet>x = pi\<bullet>y) = (x=y)"
proof 
  assume "pi\<bullet>x = pi\<bullet>y" 
  hence  "x=(rev pi)\<bullet>(pi\<bullet>y)" by (rule at_bij1[OF at]) 
  thus "x=y" by (simp only: at_rev_pi[OF at])
next
  assume "x=y"
  thus "pi\<bullet>x = pi\<bullet>y" by simp
qed

lemma at_supp:
  fixes x :: "'x"
  assumes at: "at TYPE('x)"
  shows "supp x = {x}"
proof (simp add: supp_def Collect_conj_eq Collect_imp_eq at_calc[OF at], auto)
  assume f: "finite {b::'x. b \<noteq> x}"
  have a1: "{b::'x. b \<noteq> x} = UNIV-{x}" by force
  have a2: "infinite (UNIV::'x set)" by (rule at4[OF at])
  from f a1 a2 show False by force
qed

lemma at_fresh:
  fixes a :: "'x"
  and   b :: "'x"
  assumes at: "at TYPE('x)"
  shows "(a\<sharp>b) = (a\<noteq>b)" 
  by (simp add: at_supp[OF at] fresh_def)

lemma at_prm_fresh[rule_format]:
  fixes c :: "'x"
  and   pi:: "'x prm"
  assumes at: "at TYPE('x)"
  shows "c\<sharp>pi \<longrightarrow> pi\<bullet>c = c"
apply(induct pi)
apply(simp add: at1[OF at]) 
apply(force simp add: fresh_list_cons at2[OF at] fresh_prod at_fresh[OF at] at3[OF at])
done

lemma at_prm_rev_eq:
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  assumes at: "at TYPE('x)"
  shows a: "((rev pi1) \<sim> (rev pi2)) = (pi1 \<sim> pi2)"
proof (simp add: prm_eq_def, auto)
  fix x
  assume "\<forall>x::'x. (rev pi1)\<bullet>x = (rev pi2)\<bullet>x"
  hence "(rev (pi1::'x prm))\<bullet>(pi2\<bullet>(x::'x)) = (rev (pi2::'x prm))\<bullet>(pi2\<bullet>x)" by simp
  hence "(rev (pi1::'x prm))\<bullet>((pi2::'x prm)\<bullet>x) = (x::'x)" by (simp add: at_rev_pi[OF at])
  hence "(pi2::'x prm)\<bullet>x = (pi1::'x prm)\<bullet>x" by (simp add: at_bij2[OF at])
  thus "pi1 \<bullet> x  =  pi2 \<bullet> x" by simp
next
  fix x
  assume "\<forall>x::'x. pi1\<bullet>x = pi2\<bullet>x"
  hence "(pi1::'x prm)\<bullet>((rev pi2)\<bullet>x) = (pi2::'x prm)\<bullet>((rev pi2)\<bullet>(x::'x))" by simp
  hence "(pi1::'x prm)\<bullet>((rev pi2)\<bullet>(x::'x)) = x" by (simp add: at_pi_rev[OF at])
  hence "(rev pi2)\<bullet>x = (rev pi1)\<bullet>(x::'x)" by (simp add: at_bij1[OF at])
  thus "(rev pi1)\<bullet>x = (rev pi2)\<bullet>(x::'x)" by simp
qed
  
lemma at_prm_rev_eq1:
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  assumes at: "at TYPE('x)"
  shows "pi1 \<sim> pi2 \<Longrightarrow> (rev pi1) \<sim> (rev pi2)"
  by (simp add: at_prm_rev_eq[OF at])

lemma at_ds1:
  fixes a  :: "'x"
  assumes at: "at TYPE('x)"
  shows "[(a,a)] \<sim> []"
  by (force simp add: prm_eq_def at_calc[OF at])

lemma at_ds2: 
  fixes pi :: "'x prm"
  and   a  :: "'x"
  and   b  :: "'x"
  assumes at: "at TYPE('x)"
  shows "(pi@[((rev pi)\<bullet>a,(rev pi)\<bullet>b)]) \<sim> ([(a,b)]@pi)"
  by (force simp add: prm_eq_def at_append[OF at] at_bij[OF at] at_pi_rev[OF at] 
      at_rev_pi[OF at] at_calc[OF at])

lemma at_ds3: 
  fixes a  :: "'x"
  and   b  :: "'x"
  and   c  :: "'x"
  assumes at: "at TYPE('x)"
  and     a:  "distinct [a,b,c]"
  shows "[(a,c),(b,c),(a,c)] \<sim> [(a,b)]"
  using a by (force simp add: prm_eq_def at_calc[OF at])

lemma at_ds4: 
  fixes a  :: "'x"
  and   b  :: "'x"
  and   pi  :: "'x prm"
  assumes at: "at TYPE('x)"
  shows "(pi@[(a,(rev pi)\<bullet>b)]) \<sim> ([(pi\<bullet>a,b)]@pi)"
  by (force simp add: prm_eq_def at_append[OF at] at_calc[OF at] at_bij[OF at] 
      at_pi_rev[OF at] at_rev_pi[OF at])

lemma at_ds5: 
  fixes a  :: "'x"
  and   b  :: "'x"
  assumes at: "at TYPE('x)"
  shows "[(a,b)] \<sim> [(b,a)]"
  by (force simp add: prm_eq_def at_calc[OF at])

lemma at_ds6: 
  fixes a  :: "'x"
  and   b  :: "'x"
  and   c  :: "'x"
  assumes at: "at TYPE('x)"
  and     a: "distinct [a,b,c]"
  shows "[(a,c),(a,b)] \<sim> [(b,c),(a,c)]"
  using a by (force simp add: prm_eq_def at_calc[OF at])

lemma at_ds7:
  fixes pi :: "'x prm"
  assumes at: "at TYPE('x)"
  shows "((rev pi)@pi) \<sim> []"
  by (simp add: prm_eq_def at1[OF at] at_append[OF at] at_rev_pi[OF at])

lemma at_ds8_aux:
  fixes pi :: "'x prm"
  and   a  :: "'x"
  and   b  :: "'x"
  and   c  :: "'x"
  assumes at: "at TYPE('x)"
  shows "pi\<bullet>(swap (a,b) c) = swap (pi\<bullet>a,pi\<bullet>b) (pi\<bullet>c)"
  by (force simp add: at_calc[OF at] at_bij[OF at])

lemma at_ds8: 
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   a  :: "'x"
  and   b  :: "'x"
  assumes at: "at TYPE('x)"
  shows "(pi1@pi2) \<sim> ((pi1\<bullet>pi2)@pi1)"
apply(induct_tac pi2)
apply(simp add: prm_eq_def)
apply(auto simp add: prm_eq_def)
apply(simp add: at2[OF at])
apply(drule_tac x="aa" in spec)
apply(drule sym)
apply(simp)
apply(simp add: at_append[OF at])
apply(simp add: at2[OF at])
apply(simp add: at_ds8_aux[OF at])
done

lemma at_ds9: 
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   a  :: "'x"
  and   b  :: "'x"
  assumes at: "at TYPE('x)"
  shows " ((rev pi2)@(rev pi1)) \<sim> ((rev pi1)@(rev (pi1\<bullet>pi2)))"
apply(induct_tac pi2)
apply(simp add: prm_eq_def)
apply(auto simp add: prm_eq_def)
apply(simp add: at_append[OF at])
apply(simp add: at2[OF at] at1[OF at])
apply(drule_tac x="swap(pi1\<bullet>a,pi1\<bullet>b) aa" in spec)
apply(drule sym)
apply(simp)
apply(simp add: at_ds8_aux[OF at])
apply(simp add: at_rev_pi[OF at])
done

--"there always exists an atom not being in a finite set"
lemma ex_in_inf:
  fixes   A::"'x set"
  assumes at: "at TYPE('x)"
  and     fs: "finite A"
  shows "\<exists>c::'x. c\<notin>A"
proof -
  from  fs at4[OF at] have "infinite ((UNIV::'x set) - A)" 
    by (simp add: Diff_infinite_finite)
  hence "((UNIV::'x set) - A) \<noteq> ({}::'x set)" by (force simp only:)
  hence "\<exists>c::'x. c\<in>((UNIV::'x set) - A)" by force
  thus "\<exists>c::'x. c\<notin>A" by force
qed

--"there always exists a fresh name for an object with finite support"
lemma at_exists_fresh: 
  fixes  x :: "'a"
  assumes at: "at TYPE('x)"
  and     fs: "finite ((supp x)::'x set)"
  shows "\<exists>c::'x. c\<sharp>x"
  by (simp add: fresh_def, rule ex_in_inf[OF at, OF fs])

--"the at-props imply the pt-props"
lemma at_pt_inst:
  assumes at: "at TYPE('x)"
  shows "pt TYPE('x) TYPE('x)"
apply(auto simp only: pt_def)
apply(simp only: at1[OF at])
apply(simp only: at_append[OF at]) 
apply(simp add: prm_eq_def)
done

section {* finite support properties *}
(*===================================*)

lemma fs1:
  fixes x :: "'a"
  assumes a: "fs TYPE('a) TYPE('x)"
  shows "finite ((supp x)::'x set)"
  using a by (simp add: fs_def)

lemma fs_at_inst:
  fixes a :: "'x"
  assumes at: "at TYPE('x)"
  shows "fs TYPE('x) TYPE('x)"
apply(simp add: fs_def) 
apply(simp add: at_supp[OF at])
done

lemma fs_unit_inst:
  shows "fs TYPE(unit) TYPE('x)"
apply(simp add: fs_def)
apply(simp add: supp_unit)
done

lemma fs_prod_inst:
  assumes fsa: "fs TYPE('a) TYPE('x)"
  and     fsb: "fs TYPE('b) TYPE('x)"
  shows "fs TYPE('a\<times>'b) TYPE('x)"
apply(unfold fs_def)
apply(auto simp add: supp_prod)
apply(rule fs1[OF fsa])
apply(rule fs1[OF fsb])
done

lemma fs_list_inst:
  assumes fs: "fs TYPE('a) TYPE('x)"
  shows "fs TYPE('a list) TYPE('x)"
apply(simp add: fs_def, rule allI)
apply(induct_tac x)
apply(simp add: supp_list_nil)
apply(simp add: supp_list_cons)
apply(rule fs1[OF fs])
done

lemma fs_bool_inst:
  shows "fs TYPE(bool) TYPE('x)"
apply(simp add: fs_def, rule allI)
apply(simp add: supp_bool)
done

lemma fs_int_inst:
  shows "fs TYPE(int) TYPE('x)"
apply(simp add: fs_def, rule allI)
apply(simp add: supp_int)
done

section {* Lemmas about the permutation properties *}
(*=================================================*)

lemma pt1:
  fixes x::"'a"
  assumes a: "pt TYPE('a) TYPE('x)"
  shows "([]::'x prm)\<bullet>x = x"
  using a by (simp add: pt_def)

lemma pt2: 
  fixes pi1::"'x prm"
  and   pi2::"'x prm"
  and   x  ::"'a"
  assumes a: "pt TYPE('a) TYPE('x)"
  shows "(pi1@pi2)\<bullet>x = pi1\<bullet>(pi2\<bullet>x)"
  using a by (simp add: pt_def)

lemma pt3:
  fixes pi1::"'x prm"
  and   pi2::"'x prm"
  and   x  ::"'a"
  assumes a: "pt TYPE('a) TYPE('x)"
  shows "pi1 \<sim> pi2 \<Longrightarrow> pi1\<bullet>x = pi2\<bullet>x"
  using a by (simp add: pt_def)

lemma pt3_rev:
  fixes pi1::"'x prm"
  and   pi2::"'x prm"
  and   x  ::"'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pi1 \<sim> pi2 \<Longrightarrow> (rev pi1)\<bullet>x = (rev pi2)\<bullet>x"
  by (rule pt3[OF pt], simp add: at_prm_rev_eq[OF at])

section {* composition properties *}
(* ============================== *)
lemma cp1:
  fixes pi1::"'x prm"
  and   pi2::"'y prm"
  and   x  ::"'a"
  assumes cp: "cp TYPE ('a) TYPE('x) TYPE('y)"
  shows "pi1\<bullet>(pi2\<bullet>x) = (pi1\<bullet>pi2)\<bullet>(pi1\<bullet>x)"
  using cp by (simp add: cp_def)

lemma cp_pt_inst:
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "cp TYPE('a) TYPE('x) TYPE('x)"
apply(auto simp add: cp_def pt2[OF pt,symmetric])
apply(rule pt3[OF pt])
apply(rule at_ds8[OF at])
done

section {* permutation type instances *}
(* ===================================*)

lemma pt_set_inst:
  assumes pt: "pt TYPE('a) TYPE('x)"
  shows  "pt TYPE('a set) TYPE('x)"
apply(simp add: pt_def)
apply(simp_all add: perm_set_def)
apply(simp add: pt1[OF pt])
apply(force simp add: pt2[OF pt] pt3[OF pt])
done

lemma pt_list_nil: 
  fixes xs :: "'a list"
  assumes pt: "pt TYPE('a) TYPE ('x)"
  shows "([]::'x prm)\<bullet>xs = xs" 
apply(induct_tac xs)
apply(simp_all add: pt1[OF pt])
done

lemma pt_list_append: 
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   xs  :: "'a list"
  assumes pt: "pt TYPE('a) TYPE ('x)"
  shows "(pi1@pi2)\<bullet>xs = pi1\<bullet>(pi2\<bullet>xs)"
apply(induct_tac xs)
apply(simp_all add: pt2[OF pt])
done

lemma pt_list_prm_eq: 
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   xs  :: "'a list"
  assumes pt: "pt TYPE('a) TYPE ('x)"
  shows "pi1 \<sim> pi2  \<Longrightarrow> pi1\<bullet>xs = pi2\<bullet>xs"
apply(induct_tac xs)
apply(simp_all add: prm_eq_def pt3[OF pt])
done

lemma pt_list_inst:
  assumes pt: "pt TYPE('a) TYPE('x)"
  shows  "pt TYPE('a list) TYPE('x)"
apply(auto simp only: pt_def)
apply(rule pt_list_nil[OF pt])
apply(rule pt_list_append[OF pt])
apply(rule pt_list_prm_eq[OF pt],assumption)
done

lemma pt_unit_inst:
  shows  "pt TYPE(unit) TYPE('x)"
  by (simp add: pt_def)

lemma pt_prod_inst:
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  shows  "pt TYPE('a \<times> 'b) TYPE('x)"
  apply(auto simp add: pt_def)
  apply(rule pt1[OF pta])
  apply(rule pt1[OF ptb])
  apply(rule pt2[OF pta])
  apply(rule pt2[OF ptb])
  apply(rule pt3[OF pta],assumption)
  apply(rule pt3[OF ptb],assumption)
  done

lemma pt_fun_inst:
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at:  "at TYPE('x)"
  shows  "pt TYPE('a\<Rightarrow>'b) TYPE('x)"
apply(auto simp only: pt_def)
apply(simp_all add: perm_fun_def)
apply(simp add: pt1[OF pta] pt1[OF ptb])
apply(simp add: pt2[OF pta] pt2[OF ptb])
apply(subgoal_tac "(rev pi1) \<sim> (rev pi2)")(*A*)
apply(simp add: pt3[OF pta] pt3[OF ptb])
(*A*)
apply(simp add: at_prm_rev_eq[OF at])
done

lemma pt_option_inst:
  assumes pta: "pt TYPE('a) TYPE('x)"
  shows  "pt TYPE('a option) TYPE('x)"
apply(auto simp only: pt_def)
apply(case_tac "x")
apply(simp_all add: pt1[OF pta])
apply(case_tac "x")
apply(simp_all add: pt2[OF pta])
apply(case_tac "x")
apply(simp_all add: pt3[OF pta])
done

lemma pt_noption_inst:
  assumes pta: "pt TYPE('a) TYPE('x)"
  shows  "pt TYPE('a nOption) TYPE('x)"
apply(auto simp only: pt_def)
apply(case_tac "x")
apply(simp_all add: pt1[OF pta])
apply(case_tac "x")
apply(simp_all add: pt2[OF pta])
apply(case_tac "x")
apply(simp_all add: pt3[OF pta])
done

lemma pt_bool_inst:
  shows  "pt TYPE(bool) TYPE('x)"
  apply(auto simp add: pt_def)
  apply(case_tac "x=True", simp add: perm_bool_def, simp add: perm_bool_def)+
  done

lemma pt_prm_inst:
  assumes at: "at TYPE('x)"
  shows  "pt TYPE('x prm) TYPE('x)"
apply(rule pt_list_inst)
apply(rule pt_prod_inst)
apply(rule at_pt_inst[OF at])+
done

section {* further lemmas for permutation types *}
(*==============================================*)

lemma pt_rev_pi:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(rev pi)\<bullet>(pi\<bullet>x) = x"
proof -
  have "((rev pi)@pi) \<sim> ([]::'x prm)" by (simp add: at_ds7[OF at])
  hence "((rev pi)@pi)\<bullet>(x::'a) = ([]::'x prm)\<bullet>x" by (simp add: pt3[OF pt]) 
  thus ?thesis by (simp add: pt1[OF pt] pt2[OF pt])
qed

lemma pt_pi_rev:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pi\<bullet>((rev pi)\<bullet>x) = x"
  by (simp add: pt_rev_pi[OF pt, OF at,of "rev pi" "x",simplified])

lemma pt_bij1: 
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   y  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     a:  "(pi\<bullet>x) = y"
  shows   "x=(rev pi)\<bullet>y"
proof -
  from a have "y=(pi\<bullet>x)" by (rule sym)
  thus ?thesis by (simp only: pt_rev_pi[OF pt, OF at])
qed

lemma pt_bij2: 
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   y  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     a:  "x = (rev pi)\<bullet>y"
  shows   "(pi\<bullet>x)=y"
  using a by (simp add: pt_pi_rev[OF pt, OF at])

lemma pt_bij:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   y  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(pi\<bullet>x = pi\<bullet>y) = (x=y)"
proof 
  assume "pi\<bullet>x = pi\<bullet>y" 
  hence  "x=(rev pi)\<bullet>(pi\<bullet>y)" by (rule pt_bij1[OF pt, OF at]) 
  thus "x=y" by (simp only: pt_rev_pi[OF pt, OF at])
next
  assume "x=y"
  thus "pi\<bullet>x = pi\<bullet>y" by simp
qed

lemma pt_bij3:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   y  :: "'a"
  assumes a:  "x=y"
  shows "(pi\<bullet>x = pi\<bullet>y)"
using a by simp 

lemma pt_bij4:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   y  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     a:  "pi\<bullet>x = pi\<bullet>y"
  shows "x = y"
using a by (simp add: pt_bij[OF pt, OF at])

lemma pt_swap_bij:
  fixes a  :: "'x"
  and   b  :: "'x"
  and   x  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "[(a,b)]\<bullet>([(a,b)]\<bullet>x) = x"
  by (rule pt_bij2[OF pt, OF at], simp)

lemma pt_set_bij1:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   X  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "((pi\<bullet>x)\<in>X) = (x\<in>((rev pi)\<bullet>X))"
  by (force simp add: perm_set_def pt_rev_pi[OF pt, OF at] pt_pi_rev[OF pt, OF at])

lemma pt_set_bij1a:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   X  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(x\<in>(pi\<bullet>X)) = (((rev pi)\<bullet>x)\<in>X)"
  by (force simp add: perm_set_def pt_rev_pi[OF pt, OF at] pt_pi_rev[OF pt, OF at])

lemma pt_set_bij:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   X  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "((pi\<bullet>x)\<in>(pi\<bullet>X)) = (x\<in>X)"
  by (simp add: perm_set_def pt_set_bij1[OF pt, OF at] pt_bij[OF pt, OF at])

lemma pt_set_bij2:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   X  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     a:  "x\<in>X"
  shows "(pi\<bullet>x)\<in>(pi\<bullet>X)"
  using a by (simp add: pt_set_bij[OF pt, OF at])

lemma pt_set_bij3:
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   X  :: "'a set"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pi\<bullet>(x\<in>X) = (x\<in>X)"
apply(case_tac "x\<in>X = True")
apply(auto)
done

lemma pt_list_set_pi:
  fixes pi :: "'x prm"
  and   xs :: "'a list"
  assumes pt: "pt TYPE('a) TYPE('x)"
  shows "pi\<bullet>(set xs) = set (pi\<bullet>xs)"
by (induct xs, auto simp add: perm_set_def pt1[OF pt])

-- "some helper lemmas for the pt_perm_supp_ineq lemma"
lemma Collect_permI: 
  fixes pi :: "'x prm"
  and   x  :: "'a"
  assumes a: "\<forall>x. (P1 x = P2 x)" 
  shows "{pi\<bullet>x| x. P1 x} = {pi\<bullet>x| x. P2 x}"
  using a by force

lemma Infinite_cong:
  assumes a: "X = Y"
  shows "infinite X = infinite Y"
  using a by (simp)

lemma pt_set_eq_ineq:
  fixes pi :: "'y prm"
  assumes pt: "pt TYPE('x) TYPE('y)"
  and     at: "at TYPE('y)"
  shows "{pi\<bullet>x| x::'x. P x} = {x::'x. P ((rev pi)\<bullet>x)}"
  by (force simp only: pt_rev_pi[OF pt, OF at] pt_pi_rev[OF pt, OF at])

lemma pt_inject_on_ineq:
  fixes X  :: "'y set"
  and   pi :: "'x prm"
  assumes pt: "pt TYPE('y) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "inj_on (perm pi) X"
proof (unfold inj_on_def, intro strip)
  fix x::"'y" and y::"'y"
  assume "pi\<bullet>x = pi\<bullet>y"
  thus "x=y" by (simp add: pt_bij[OF pt, OF at])
qed

lemma pt_set_finite_ineq: 
  fixes X  :: "'x set"
  and   pi :: "'y prm"
  assumes pt: "pt TYPE('x) TYPE('y)"
  and     at: "at TYPE('y)"
  shows "finite (pi\<bullet>X) = finite X"
proof -
  have image: "(pi\<bullet>X) = (perm pi ` X)" by (force simp only: perm_set_def)
  show ?thesis
  proof (rule iffI)
    assume "finite (pi\<bullet>X)"
    hence "finite (perm pi ` X)" using image by (simp)
    thus "finite X" using pt_inject_on_ineq[OF pt, OF at] by (rule finite_imageD)
  next
    assume "finite X"
    hence "finite (perm pi ` X)" by (rule finite_imageI)
    thus "finite (pi\<bullet>X)" using image by (simp)
  qed
qed

lemma pt_set_infinite_ineq: 
  fixes X  :: "'x set"
  and   pi :: "'y prm"
  assumes pt: "pt TYPE('x) TYPE('y)"
  and     at: "at TYPE('y)"
  shows "infinite (pi\<bullet>X) = infinite X"
using pt at by (simp add: pt_set_finite_ineq)

lemma pt_perm_supp_ineq:
  fixes  pi  :: "'x prm"
  and    x   :: "'a"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  shows "(pi\<bullet>((supp x)::'y set)) = supp (pi\<bullet>x)" (is "?LHS = ?RHS")
proof -
  have "?LHS = {pi\<bullet>a | a. infinite {b. [(a,b)]\<bullet>x \<noteq> x}}" by (simp add: supp_def perm_set_def)
  also have "\<dots> = {pi\<bullet>a | a. infinite {pi\<bullet>b | b. [(a,b)]\<bullet>x \<noteq> x}}" 
  proof (rule Collect_permI, rule allI, rule iffI)
    fix a
    assume "infinite {b::'y. [(a,b)]\<bullet>x  \<noteq> x}"
    hence "infinite (pi\<bullet>{b::'y. [(a,b)]\<bullet>x \<noteq> x})" by (simp add: pt_set_infinite_ineq[OF ptb, OF at])
    thus "infinite {pi\<bullet>b |b::'y. [(a,b)]\<bullet>x  \<noteq> x}" by (simp add: perm_set_def)
  next
    fix a
    assume "infinite {pi\<bullet>b |b::'y. [(a,b)]\<bullet>x \<noteq> x}"
    hence "infinite (pi\<bullet>{b::'y. [(a,b)]\<bullet>x \<noteq> x})" by (simp add: perm_set_def)
    thus "infinite {b::'y. [(a,b)]\<bullet>x  \<noteq> x}" 
      by (simp add: pt_set_infinite_ineq[OF ptb, OF at])
  qed
  also have "\<dots> = {a. infinite {b::'y. [((rev pi)\<bullet>a,(rev pi)\<bullet>b)]\<bullet>x \<noteq> x}}" 
    by (simp add: pt_set_eq_ineq[OF ptb, OF at])
  also have "\<dots> = {a. infinite {b. pi\<bullet>([((rev pi)\<bullet>a,(rev pi)\<bullet>b)]\<bullet>x) \<noteq> (pi\<bullet>x)}}"
    by (simp add: pt_bij[OF pta, OF at])
  also have "\<dots> = {a. infinite {b. [(a,b)]\<bullet>(pi\<bullet>x) \<noteq> (pi\<bullet>x)}}"
  proof (rule Collect_cong, rule Infinite_cong, rule Collect_cong)
    fix a::"'y" and b::"'y"
    have "pi\<bullet>(([((rev pi)\<bullet>a,(rev pi)\<bullet>b)])\<bullet>x) = [(a,b)]\<bullet>(pi\<bullet>x)"
      by (simp add: cp1[OF cp] pt_pi_rev[OF ptb, OF at])
    thus "(pi\<bullet>([((rev pi)\<bullet>a,(rev pi)\<bullet>b)]\<bullet>x) \<noteq>  pi\<bullet>x) = ([(a,b)]\<bullet>(pi\<bullet>x) \<noteq> pi\<bullet>x)" by simp
  qed
  finally show "?LHS = ?RHS" by (simp add: supp_def) 
qed

lemma pt_perm_supp:
  fixes  pi  :: "'x prm"
  and    x   :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(pi\<bullet>((supp x)::'x set)) = supp (pi\<bullet>x)"
apply(rule pt_perm_supp_ineq)
apply(rule pt)
apply(rule at_pt_inst)
apply(rule at)+
apply(rule cp_pt_inst)
apply(rule pt)
apply(rule at)
done

lemma pt_supp_finite_pi:
  fixes  pi  :: "'x prm"
  and    x   :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     f: "finite ((supp x)::'x set)"
  shows "finite ((supp (pi\<bullet>x))::'x set)"
apply(simp add: pt_perm_supp[OF pt, OF at, symmetric])
apply(simp add: pt_set_finite_ineq[OF at_pt_inst[OF at], OF at])
apply(rule f)
done

lemma pt_fresh_left_ineq:  
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'y"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  shows "a\<sharp>(pi\<bullet>x) = ((rev pi)\<bullet>a)\<sharp>x"
apply(simp add: fresh_def)
apply(simp add: pt_set_bij1[OF ptb, OF at])
apply(simp add: pt_perm_supp_ineq[OF pta, OF ptb, OF at, OF cp])
done

lemma pt_fresh_right_ineq:  
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'y"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  shows "(pi\<bullet>a)\<sharp>x = a\<sharp>((rev pi)\<bullet>x)"
apply(simp add: fresh_def)
apply(simp add: pt_set_bij1[OF ptb, OF at])
apply(simp add: pt_perm_supp_ineq[OF pta, OF ptb, OF at, OF cp])
done

lemma pt_fresh_bij_ineq:
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'y"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  shows "(pi\<bullet>a)\<sharp>(pi\<bullet>x) = a\<sharp>x"
apply(simp add: pt_fresh_left_ineq[OF pta, OF ptb, OF at, OF cp])
apply(simp add: pt_rev_pi[OF ptb, OF at])
done

lemma pt_fresh_left:  
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "a\<sharp>(pi\<bullet>x) = ((rev pi)\<bullet>a)\<sharp>x"
apply(rule pt_fresh_left_ineq)
apply(rule pt)
apply(rule at_pt_inst)
apply(rule at)+
apply(rule cp_pt_inst)
apply(rule pt)
apply(rule at)
done

lemma pt_fresh_right:  
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(pi\<bullet>a)\<sharp>x = a\<sharp>((rev pi)\<bullet>x)"
apply(rule pt_fresh_right_ineq)
apply(rule pt)
apply(rule at_pt_inst)
apply(rule at)+
apply(rule cp_pt_inst)
apply(rule pt)
apply(rule at)
done

lemma pt_fresh_bij:
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(pi\<bullet>a)\<sharp>(pi\<bullet>x) = a\<sharp>x"
apply(rule pt_fresh_bij_ineq)
apply(rule pt)
apply(rule at_pt_inst)
apply(rule at)+
apply(rule cp_pt_inst)
apply(rule pt)
apply(rule at)
done

lemma pt_fresh_bij1:
  fixes  pi :: "'x prm"
  and     x :: "'a"
  and     a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     a:  "a\<sharp>x"
  shows "(pi\<bullet>a)\<sharp>(pi\<bullet>x)"
using a by (simp add: pt_fresh_bij[OF pt, OF at])

lemma pt_perm_fresh1:
  fixes a :: "'x"
  and   b :: "'x"
  and   x :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE ('x)"
  and     a1: "\<not>(a\<sharp>x)"
  and     a2: "b\<sharp>x"
  shows "[(a,b)]\<bullet>x \<noteq> x"
proof
  assume neg: "[(a,b)]\<bullet>x = x"
  from a1 have a1':"a\<in>(supp x)" by (simp add: fresh_def) 
  from a2 have a2':"b\<notin>(supp x)" by (simp add: fresh_def) 
  from a1' a2' have a3: "a\<noteq>b" by force
  from a1' have "([(a,b)]\<bullet>a)\<in>([(a,b)]\<bullet>(supp x))" 
    by (simp only: pt_set_bij[OF at_pt_inst[OF at], OF at])
  hence "b\<in>([(a,b)]\<bullet>(supp x))" by (simp add: at_append[OF at] at_calc[OF at])
  hence "b\<in>(supp ([(a,b)]\<bullet>x))" by (simp add: pt_perm_supp[OF pt,OF at])
  with a2' neg show False by simp
qed

-- "three helper lemmas for the perm_fresh_fresh-lemma"
lemma comprehension_neg_UNIV: "{b. \<not> P b} = UNIV - {b. P b}"
  by (auto)

lemma infinite_or_neg_infinite:
  assumes h:"infinite (UNIV::'a set)"
  shows "infinite {b::'a. P b} \<or> infinite {b::'a. \<not> P b}"
proof (subst comprehension_neg_UNIV, case_tac "finite {b. P b}")
  assume j:"finite {b::'a. P b}"
  have "infinite ((UNIV::'a set) - {b::'a. P b})"
    using Diff_infinite_finite[OF j h] by auto
  thus "infinite {b::'a. P b} \<or> infinite (UNIV - {b::'a. P b})" ..
next
  assume j:"infinite {b::'a. P b}"
  thus "infinite {b::'a. P b} \<or> infinite (UNIV - {b::'a. P b})" by simp
qed

--"the co-set of a finite set is infinte"
lemma finite_infinite:
  assumes a: "finite {b::'x. P b}"
  and     b: "infinite (UNIV::'x set)"        
  shows "infinite {b. \<not>P b}"
  using a and infinite_or_neg_infinite[OF b] by simp

lemma pt_fresh_fresh:
  fixes   x :: "'a"
  and     a :: "'x"
  and     b :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE ('x)"
  and     a1: "a\<sharp>x" and a2: "b\<sharp>x" 
  shows "[(a,b)]\<bullet>x=x"
proof (cases "a=b")
  assume c1: "a=b"
  have "[(a,a)] \<sim> []" by (rule at_ds1[OF at])
  hence "[(a,b)] \<sim> []" using c1 by simp
  hence "[(a,b)]\<bullet>x=([]::'x prm)\<bullet>x" by (rule pt3[OF pt])
  thus ?thesis by (simp only: pt1[OF pt])
next
  assume c2: "a\<noteq>b"
  from a1 have f1: "finite {c. [(a,c)]\<bullet>x \<noteq> x}" by (simp add: fresh_def supp_def)
  from a2 have f2: "finite {c. [(b,c)]\<bullet>x \<noteq> x}" by (simp add: fresh_def supp_def)
  from f1 and f2 have f3: "finite {c. perm [(a,c)] x \<noteq> x \<or> perm [(b,c)] x \<noteq> x}" 
    by (force simp only: Collect_disj_eq)
  have "infinite {c. [(a,c)]\<bullet>x = x \<and> [(b,c)]\<bullet>x = x}" 
    by (simp add: finite_infinite[OF f3,OF at4[OF at], simplified])
  hence "infinite ({c. [(a,c)]\<bullet>x = x \<and> [(b,c)]\<bullet>x = x}-{a,b})" 
    by (force dest: Diff_infinite_finite)
  hence "({c. [(a,c)]\<bullet>x = x \<and> [(b,c)]\<bullet>x = x}-{a,b}) \<noteq> {}" 
    by (auto iff del: finite_Diff_insert Diff_eq_empty_iff)
  hence "\<exists>c. c\<in>({c. [(a,c)]\<bullet>x = x \<and> [(b,c)]\<bullet>x = x}-{a,b})" by (force)
  then obtain c 
    where eq1: "[(a,c)]\<bullet>x = x" 
      and eq2: "[(b,c)]\<bullet>x = x" 
      and ineq: "a\<noteq>c \<and> b\<noteq>c"
    by (force)
  hence "[(a,c)]\<bullet>([(b,c)]\<bullet>([(a,c)]\<bullet>x)) = x" by simp 
  hence eq3: "[(a,c),(b,c),(a,c)]\<bullet>x = x" by (simp add: pt2[OF pt,symmetric])
  from c2 ineq have "[(a,c),(b,c),(a,c)] \<sim> [(a,b)]" by (simp add: at_ds3[OF at])
  hence "[(a,c),(b,c),(a,c)]\<bullet>x = [(a,b)]\<bullet>x" by (rule pt3[OF pt])
  thus ?thesis using eq3 by simp
qed

lemma pt_perm_compose:
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   x  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pi2\<bullet>(pi1\<bullet>x) = (pi2\<bullet>pi1)\<bullet>(pi2\<bullet>x)" 
proof -
  have "(pi2@pi1) \<sim> ((pi2\<bullet>pi1)@pi2)" by (rule at_ds8)
  hence "(pi2@pi1)\<bullet>x = ((pi2\<bullet>pi1)@pi2)\<bullet>x" by (rule pt3[OF pt])
  thus ?thesis by (simp add: pt2[OF pt])
qed

lemma pt_perm_compose_rev:
  fixes pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  and   x  :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(rev pi2)\<bullet>((rev pi1)\<bullet>x) = (rev pi1)\<bullet>(rev (pi1\<bullet>pi2)\<bullet>x)" 
proof -
  have "((rev pi2)@(rev pi1)) \<sim> ((rev pi1)@(rev (pi1\<bullet>pi2)))" by (rule at_ds9[OF at])
  hence "((rev pi2)@(rev pi1))\<bullet>x = ((rev pi1)@(rev (pi1\<bullet>pi2)))\<bullet>x" by (rule pt3[OF pt])
  thus ?thesis by (simp add: pt2[OF pt])
qed

section {* facts about supports *}
(*==============================*)

lemma supports_subset:
  fixes x  :: "'a"
  and   S1 :: "'x set"
  and   S2 :: "'x set"
  assumes  a: "S1 supports x"
  and      b: "S1\<subseteq>S2"
  shows "S2 supports x"
  using a b
  by (force simp add: "op supports_def")

lemma supp_supports:
  fixes x :: "'a"
  assumes  pt: "pt TYPE('a) TYPE('x)"
  and      at: "at TYPE ('x)"
  shows "((supp x)::'x set) supports x"
proof (unfold "op supports_def", intro strip)
  fix a b
  assume "(a::'x)\<notin>(supp x) \<and> (b::'x)\<notin>(supp x)"
  hence "a\<sharp>x" and "b\<sharp>x" by (auto simp add: fresh_def)
  thus "[(a,b)]\<bullet>x = x" by (rule pt_fresh_fresh[OF pt, OF at])
qed

lemma supp_is_subset:
  fixes S :: "'x set"
  and   x :: "'a"
  assumes a1: "S supports x"
  and     a2: "finite S"
  shows "(supp x)\<subseteq>S"
proof (rule ccontr)
  assume "\<not>(supp x \<subseteq> S)"
  hence "\<exists>a. a\<in>(supp x) \<and> a\<notin>S" by force
  then obtain a where b1: "a\<in>supp x" and b2: "a\<notin>S" by force
  from a1 b2 have "\<forall>b. (b\<notin>S \<longrightarrow> ([(a,b)]\<bullet>x = x))" by (unfold "op supports_def", force)
  with a1 have "{b. [(a,b)]\<bullet>x \<noteq> x}\<subseteq>S" by (unfold "op supports_def", force)
  with a2 have "finite {b. [(a,b)]\<bullet>x \<noteq> x}" by (simp add: finite_subset)
  hence "a\<notin>(supp x)" by (unfold supp_def, auto)
  with b1 show False by simp
qed

lemma supports_finite:
  fixes S :: "'x set"
  and   x :: "'a"
  assumes a1: "S supports x"
  and     a2: "finite S"
  shows "finite ((supp x)::'x set)"
proof -
  have "(supp x)\<subseteq>S" using a1 a2 by (rule supp_is_subset)
  thus ?thesis using a2 by (simp add: finite_subset)
qed
  
lemma supp_is_inter:
  fixes  x :: "'a"
  assumes  pt: "pt TYPE('a) TYPE('x)"
  and      at: "at TYPE ('x)"
  and      fs: "fs TYPE('a) TYPE('x)"
  shows "((supp x)::'x set) = (\<Inter> {S. finite S \<and> S supports x})"
proof (rule equalityI)
  show "((supp x)::'x set) \<subseteq> (\<Inter> {S. finite S \<and> S supports x})"
  proof (clarify)
    fix S c
    assume b: "c\<in>((supp x)::'x set)" and "finite (S::'x set)" and "S supports x"
    hence  "((supp x)::'x set)\<subseteq>S" by (simp add: supp_is_subset) 
    with b show "c\<in>S" by force
  qed
next
  show "(\<Inter> {S. finite S \<and> S supports x}) \<subseteq> ((supp x)::'x set)"
  proof (clarify, simp)
    fix c
    assume d: "\<forall>(S::'x set). finite S \<and> S supports x \<longrightarrow> c\<in>S"
    have "((supp x)::'x set) supports x" by (rule supp_supports[OF pt, OF at])
    with d fs1[OF fs] show "c\<in>supp x" by force
  qed
qed
    
lemma supp_is_least_supports:
  fixes S :: "'x set"
  and   x :: "'a"
  assumes  pt: "pt TYPE('a) TYPE('x)"
  and      at: "at TYPE ('x)"
  and      a1: "S supports x"
  and      a2: "finite S"
  and      a3: "\<forall>S'. (finite S' \<and> S' supports x) \<longrightarrow> S\<subseteq>S'"
  shows "S = (supp x)"
proof (rule equalityI)
  show "((supp x)::'x set)\<subseteq>S" using a1 a2 by (rule supp_is_subset)
next
  have s1: "((supp x)::'x set) supports x" by (rule supp_supports[OF pt, OF at])
  have "((supp x)::'x set)\<subseteq>S" using a1 a2 by (rule supp_is_subset)
  hence "finite ((supp x)::'x set)" using a2 by (simp add: finite_subset)
  with s1 a3 show "S\<subseteq>supp x" by force
qed

lemma supports_set:
  fixes S :: "'x set"
  and   X :: "'a set"
  assumes  pt: "pt TYPE('a) TYPE('x)"
  and      at: "at TYPE ('x)"
  and      a: "\<forall>x\<in>X. (\<forall>(a::'x) (b::'x). a\<notin>S\<and>b\<notin>S \<longrightarrow> ([(a,b)]\<bullet>x)\<in>X)"
  shows  "S supports X"
using a
apply(auto simp add: "op supports_def")
apply(simp add: pt_set_bij1a[OF pt, OF at])
apply(force simp add: pt_swap_bij[OF pt, OF at])
apply(simp add: pt_set_bij1a[OF pt, OF at])
done

lemma supports_fresh:
  fixes S :: "'x set"
  and   a :: "'x"
  and   x :: "'a"
  assumes a1: "S supports x"
  and     a2: "finite S"
  and     a3: "a\<notin>S"
  shows "a\<sharp>x"
proof (simp add: fresh_def)
  have "(supp x)\<subseteq>S" using a1 a2 by (rule supp_is_subset)
  thus "a\<notin>(supp x)" using a3 by force
qed

lemma at_fin_set_supports:
  fixes X::"'x set"
  assumes at: "at TYPE('x)"
  shows "X supports X"
proof (simp add: "op supports_def", intro strip)
  fix a b
  assume "a\<notin>X \<and> b\<notin>X"
  thus "[(a,b)]\<bullet>X = X" by (force simp add: perm_set_def at_calc[OF at])
qed

lemma at_fin_set_supp:
  fixes X::"'x set"
  assumes at: "at TYPE('x)"
  and     fs: "finite X"
  shows "(supp X) = X"
proof -
  have pt_set: "pt TYPE('x set) TYPE('x)" 
    by (rule pt_set_inst[OF at_pt_inst[OF at]])
  have X_supports_X: "X supports X" by (rule at_fin_set_supports[OF at])
  show ?thesis using  pt_set at X_supports_X fs
  proof (rule supp_is_least_supports[symmetric])
    show "\<forall>S'. finite S' \<and> S' supports X \<longrightarrow> X \<subseteq> S'"
    proof (auto)
      fix S'::"'x set" and x::"'x"
      assume f: "finite S'"
      and    s: "S' supports X"
      and    e1: "x\<in>X"
      show "x\<in>S'"
      proof (rule ccontr)
	assume e2: "x\<notin>S'"
	have "\<exists>b. b\<notin>(X\<union>S')" by (force intro: ex_in_inf[OF at] simp only: fs f)
	then obtain b where b1: "b\<notin>X" and b2: "b\<notin>S'" by (auto)
	from s e2 b2 have c1: "[(x,b)]\<bullet>X=X" by (simp add: "op supports_def")
	from e1 b1 have c2: "[(x,b)]\<bullet>X\<noteq>X" by (force simp add: perm_set_def at_calc[OF at])
	show "False" using c1 c2 by simp
      qed
    qed
  qed
qed

section {* Permutations acting on Functions *}
(*==========================================*)

lemma pt_fun_app_eq:
  fixes f  :: "'a\<Rightarrow>'b"
  and   x  :: "'a"
  and   pi :: "'x prm"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pi\<bullet>(f x) = (pi\<bullet>f)(pi\<bullet>x)"
  by (simp add: perm_fun_def pt_rev_pi[OF pt, OF at])


--"sometimes pt_fun_app_eq does to much; this lemma 'corrects it'"
lemma pt_perm:
  fixes x  :: "'a"
  and   pi1 :: "'x prm"
  and   pi2 :: "'x prm"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE ('x)"
  shows "(pi1\<bullet>perm pi2)(pi1\<bullet>x) = pi1\<bullet>(pi2\<bullet>x)" 
  by (simp add: pt_fun_app_eq[OF pt, OF at])


lemma pt_fun_eq:
  fixes f  :: "'a\<Rightarrow>'b"
  and   pi :: "'x prm"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(pi\<bullet>f = f) = (\<forall> x. pi\<bullet>(f x) = f (pi\<bullet>x))" (is "?LHS = ?RHS")
proof
  assume a: "?LHS"
  show "?RHS"
  proof
    fix x
    have "pi\<bullet>(f x) = (pi\<bullet>f)(pi\<bullet>x)" by (simp add: pt_fun_app_eq[OF pt, OF at])
    also have "\<dots> = f (pi\<bullet>x)" using a by simp
    finally show "pi\<bullet>(f x) = f (pi\<bullet>x)" by simp
  qed
next
  assume b: "?RHS"
  show "?LHS"
  proof (rule ccontr)
    assume "(pi\<bullet>f) \<noteq> f"
    hence "\<exists>c. (pi\<bullet>f) c \<noteq> f c" by (simp add: expand_fun_eq)
    then obtain c where b1: "(pi\<bullet>f) c \<noteq> f c" by force
    from b have "pi\<bullet>(f ((rev pi)\<bullet>c)) = f (pi\<bullet>((rev pi)\<bullet>c))" by force
    hence "(pi\<bullet>f)(pi\<bullet>((rev pi)\<bullet>c)) = f (pi\<bullet>((rev pi)\<bullet>c))" 
      by (simp add: pt_fun_app_eq[OF pt, OF at])
    hence "(pi\<bullet>f) c = f c" by (simp add: pt_pi_rev[OF pt, OF at])
    with b1 show "False" by simp
  qed
qed

-- "two helper lemmas for the equivariance of functions"
lemma pt_swap_eq_aux:
  fixes   y :: "'a"
  and    pi :: "'x prm"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     a: "\<forall>(a::'x) (b::'x). [(a,b)]\<bullet>y = y"
  shows "pi\<bullet>y = y"
proof(induct pi)
    case Nil show ?case by (simp add: pt1[OF pt])
  next
    case (Cons x xs)
    have "\<exists>a b. x=(a,b)" by force
    then obtain a b where p: "x=(a,b)" by force
    assume i: "xs\<bullet>y = y"
    have "x#xs = [x]@xs" by simp
    hence "(x#xs)\<bullet>y = ([x]@xs)\<bullet>y" by simp
    hence "(x#xs)\<bullet>y = [x]\<bullet>(xs\<bullet>y)" by (simp only: pt2[OF pt])
    thus ?case using a i p by (force)
  qed

lemma pt_swap_eq:
  fixes   y :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  shows "(\<forall>(a::'x) (b::'x). [(a,b)]\<bullet>y = y) = (\<forall>pi::'x prm. pi\<bullet>y = y)"
  by (force intro: pt_swap_eq_aux[OF pt])

lemma pt_eqvt_fun1a:
  fixes f     :: "'a\<Rightarrow>'b"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     a:   "((supp f)::'x set)={}"
  shows "\<forall>(pi::'x prm). pi\<bullet>f = f" 
proof (intro strip)
  fix pi
  have "\<forall>a b. a\<notin>((supp f)::'x set) \<and> b\<notin>((supp f)::'x set) \<longrightarrow> (([(a,b)]\<bullet>f) = f)" 
    by (intro strip, fold fresh_def, 
      simp add: pt_fresh_fresh[OF pt_fun_inst[OF pta, OF ptb, OF at],OF at])
  with a have "\<forall>(a::'x) (b::'x). ([(a,b)]\<bullet>f) = f" by force
  hence "\<forall>(pi::'x prm). pi\<bullet>f = f" 
    by (simp add: pt_swap_eq[OF pt_fun_inst[OF pta, OF ptb, OF at]])
  thus "(pi::'x prm)\<bullet>f = f" by simp
qed

lemma pt_eqvt_fun1b:
  fixes f     :: "'a\<Rightarrow>'b"
  assumes a: "\<forall>(pi::'x prm). pi\<bullet>f = f"
  shows "((supp f)::'x set)={}"
using a by (simp add: supp_def)

lemma pt_eqvt_fun1:
  fixes f     :: "'a\<Rightarrow>'b"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(((supp f)::'x set)={}) = (\<forall>(pi::'x prm). pi\<bullet>f = f)" (is "?LHS = ?RHS")
by (rule iffI, simp add: pt_eqvt_fun1a[OF pta, OF ptb, OF at], simp add: pt_eqvt_fun1b)

lemma pt_eqvt_fun2a:
  fixes f     :: "'a\<Rightarrow>'b"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at: "at TYPE('x)"
  assumes a: "((supp f)::'x set)={}"
  shows "\<forall>(pi::'x prm) (x::'a). pi\<bullet>(f x) = f(pi\<bullet>x)" 
proof (intro strip)
  fix pi x
  from a have b: "\<forall>(pi::'x prm). pi\<bullet>f = f" by (simp add: pt_eqvt_fun1[OF pta, OF ptb, OF at]) 
  have "(pi::'x prm)\<bullet>(f x) = (pi\<bullet>f)(pi\<bullet>x)" by (simp add: pt_fun_app_eq[OF pta, OF at]) 
  with b show "(pi::'x prm)\<bullet>(f x) = f (pi\<bullet>x)" by force 
qed

lemma pt_eqvt_fun2b:
  fixes f     :: "'a\<Rightarrow>'b"
  assumes pt1: "pt TYPE('a) TYPE('x)"
  and     pt2: "pt TYPE('b) TYPE('x)"
  and     at: "at TYPE('x)"
  assumes a: "\<forall>(pi::'x prm) (x::'a). pi\<bullet>(f x) = f(pi\<bullet>x)"
  shows "((supp f)::'x set)={}"
proof -
  from a have "\<forall>(pi::'x prm). pi\<bullet>f = f" by (simp add: pt_fun_eq[OF pt1, OF at, symmetric])
  thus ?thesis by (simp add: supp_def)
qed

lemma pt_eqvt_fun2:
  fixes f     :: "'a\<Rightarrow>'b"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(((supp f)::'x set)={}) = (\<forall>(pi::'x prm) (x::'a). pi\<bullet>(f x) = f(pi\<bullet>x))" 
by (rule iffI, 
    simp add: pt_eqvt_fun2a[OF pta, OF ptb, OF at], 
    simp add: pt_eqvt_fun2b[OF pta, OF ptb, OF at])

lemma pt_supp_fun_subset:
  fixes f :: "'a\<Rightarrow>'b"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at: "at TYPE('x)" 
  and     f1: "finite ((supp f)::'x set)"
  and     f2: "finite ((supp x)::'x set)"
  shows "supp (f x) \<subseteq> (((supp f)\<union>(supp x))::'x set)"
proof -
  have s1: "((supp f)\<union>((supp x)::'x set)) supports (f x)"
  proof (simp add: "op supports_def", fold fresh_def, auto)
    fix a::"'x" and b::"'x"
    assume "a\<sharp>f" and "b\<sharp>f"
    hence a1: "[(a,b)]\<bullet>f = f" 
      by (rule pt_fresh_fresh[OF pt_fun_inst[OF pta, OF ptb, OF at], OF at])
    assume "a\<sharp>x" and "b\<sharp>x"
    hence a2: "[(a,b)]\<bullet>x = x" by (rule pt_fresh_fresh[OF pta, OF at])
    from a1 a2 show "[(a,b)]\<bullet>(f x) = (f x)" by (simp add: pt_fun_app_eq[OF pta, OF at])
  qed
  from f1 f2 have "finite ((supp f)\<union>((supp x)::'x set))" by force
  with s1 show ?thesis by (rule supp_is_subset)
qed
      
lemma pt_empty_supp_fun_subset:
  fixes f :: "'a\<Rightarrow>'b"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('b) TYPE('x)"
  and     at:  "at TYPE('x)" 
  and     e:   "(supp f)=({}::'x set)"
  shows "supp (f x) \<subseteq> ((supp x)::'x set)"
proof (unfold supp_def, auto)
  fix a::"'x"
  assume a1: "finite {b. [(a, b)]\<bullet>x \<noteq> x}"
  assume "infinite {b. [(a, b)]\<bullet>(f x) \<noteq> f x}"
  hence a2: "infinite {b. f ([(a, b)]\<bullet>x) \<noteq> f x}" using e
    by (simp add: pt_eqvt_fun2[OF pta, OF ptb, OF at])
  have a3: "{b. f ([(a,b)]\<bullet>x) \<noteq> f x}\<subseteq>{b. [(a,b)]\<bullet>x \<noteq> x}" by force
  from a1 a2 a3 show False by (force dest: finite_subset)
qed

section {* Andy's freshness lemma *}
(*================================*)

lemma freshness_lemma:
  fixes h :: "'x\<Rightarrow>'a"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     at:  "at TYPE('x)" 
  and     f1:  "finite ((supp h)::'x set)"
  and     a: "\<exists>a::'x. (a\<sharp>h \<and> a\<sharp>(h a))"
  shows  "\<exists>fr::'a. \<forall>a::'x. a\<sharp>h \<longrightarrow> (h a) = fr"
proof -
  have ptb: "pt TYPE('x) TYPE('x)" by (simp add: at_pt_inst[OF at]) 
  have ptc: "pt TYPE('x\<Rightarrow>'a) TYPE('x)" by (simp add: pt_fun_inst[OF ptb, OF pta, OF at]) 
  from a obtain a0 where a1: "a0\<sharp>h" and a2: "a0\<sharp>(h a0)" by force
  show ?thesis
  proof
    let ?fr = "h (a0::'x)"
    show "\<forall>(a::'x). (a\<sharp>h \<longrightarrow> ((h a) = ?fr))" 
    proof (intro strip)
      fix a
      assume a3: "(a::'x)\<sharp>h"
      show "h (a::'x) = h a0"
      proof (cases "a=a0")
	case True thus "h (a::'x) = h a0" by simp
      next
	case False 
	assume "a\<noteq>a0"
	hence c1: "a\<notin>((supp a0)::'x set)" by  (simp add: fresh_def[symmetric] at_fresh[OF at])
	have c2: "a\<notin>((supp h)::'x set)" using a3 by (simp add: fresh_def)
	from c1 c2 have c3: "a\<notin>((supp h)\<union>((supp a0)::'x set))" by force
	have f2: "finite ((supp a0)::'x set)" by (simp add: at_supp[OF at])
	from f1 f2 have "((supp (h a0))::'x set)\<subseteq>((supp h)\<union>(supp a0))"
	  by (simp add: pt_supp_fun_subset[OF ptb, OF pta, OF at])
	hence "a\<notin>((supp (h a0))::'x set)" using c3 by force
	hence "a\<sharp>(h a0)" by (simp add: fresh_def) 
	with a2 have d1: "[(a0,a)]\<bullet>(h a0) = (h a0)" by (rule pt_fresh_fresh[OF pta, OF at])
	from a1 a3 have d2: "[(a0,a)]\<bullet>h = h" by (rule pt_fresh_fresh[OF ptc, OF at])
	from d1 have "h a0 = [(a0,a)]\<bullet>(h a0)" by simp
	also have "\<dots>= ([(a0,a)]\<bullet>h)([(a0,a)]\<bullet>a0)" by (simp add: pt_fun_app_eq[OF ptb, OF at])
	also have "\<dots> = h ([(a0,a)]\<bullet>a0)" using d2 by simp
	also have "\<dots> = h a" by (simp add: at_calc[OF at])
	finally show "h a = h a0" by simp
      qed
    qed
  qed
qed
	    
lemma freshness_lemma_unique:
  fixes h :: "'x\<Rightarrow>'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)" 
  and     f1: "finite ((supp h)::'x set)"
  and     a: "\<exists>(a::'x). (a\<sharp>h \<and> a\<sharp>(h a))"
  shows  "\<exists>!(fr::'a). \<forall>(a::'x). a\<sharp>h \<longrightarrow> (h a) = fr"
proof
  from pt at f1 a show "\<exists>fr::'a. \<forall>a::'x. a\<sharp>h \<longrightarrow> h a = fr" by (simp add: freshness_lemma)
next
  fix fr1 fr2
  assume b1: "\<forall>a::'x. a\<sharp>h \<longrightarrow> h a = fr1"
  assume b2: "\<forall>a::'x. a\<sharp>h \<longrightarrow> h a = fr2"
  from a obtain a where "(a::'x)\<sharp>h" by force 
  with b1 b2 have "h a = fr1 \<and> h a = fr2" by force
  thus "fr1 = fr2" by force
qed

-- "packaging the freshness lemma into a function"
constdefs
  fresh_fun :: "('x\<Rightarrow>'a)\<Rightarrow>'a"
  "fresh_fun (h) \<equiv> THE fr. (\<forall>(a::'x). a\<sharp>h \<longrightarrow> (h a) = fr)"

lemma fresh_fun_app:
  fixes h :: "'x\<Rightarrow>'a"
  and   a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)" 
  and     f1: "finite ((supp h)::'x set)"
  and     a: "\<exists>(a::'x). (a\<sharp>h \<and> a\<sharp>(h a))"
  and     b: "a\<sharp>h"
  shows "(fresh_fun h) = (h a)"
proof (unfold fresh_fun_def, rule the_equality)
  show "\<forall>(a'::'x). a'\<sharp>h \<longrightarrow> h a' = h a"
  proof (intro strip)
    fix a'::"'x"
    assume c: "a'\<sharp>h"
    from pt at f1 a have "\<exists>(fr::'a). \<forall>(a::'x). a\<sharp>h \<longrightarrow> (h a) = fr" by (rule freshness_lemma)
    with b c show "h a' = h a" by force
  qed
next
  fix fr::"'a"
  assume "\<forall>a. a\<sharp>h \<longrightarrow> h a = fr"
  with b show "fr = h a" by force
qed


lemma fresh_fun_supports:
  fixes h :: "'x\<Rightarrow>'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)" 
  and     f1: "finite ((supp h)::'x set)"
  and     a: "\<exists>(a::'x). (a\<sharp>h \<and> a\<sharp>(h a))"
  shows "((supp h)::'x set) supports (fresh_fun h)"
  apply(simp add: "op supports_def")
  apply(fold fresh_def)
  apply(auto)
  apply(subgoal_tac "\<exists>(a''::'x). a''\<sharp>(h,a,b)")(*A*)
  apply(erule exE)
  apply(simp add: fresh_prod)
  apply(auto)
  apply(rotate_tac 2)
  apply(drule fresh_fun_app[OF pt, OF at, OF f1, OF a])
  apply(simp add: at_fresh[OF at])
  apply(simp add: pt_fun_app_eq[OF at_pt_inst[OF at], OF at])
  apply(auto simp add: at_calc[OF at])
  apply(subgoal_tac "[(a, b)]\<bullet>h = h")(*B*)
  apply(simp)
  (*B*)
  apply(rule pt_fresh_fresh[OF pt_fun_inst[OF at_pt_inst[OF at], OF pt], OF at, OF at])
  apply(assumption)+
  (*A*)
  apply(rule at_exists_fresh[OF at])
  apply(simp add: supp_prod)
  apply(simp add: f1 at_supp[OF at])
  done

lemma fresh_fun_equiv:
  fixes h :: "'x\<Rightarrow>'a"
  and   pi:: "'x prm"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     at:  "at TYPE('x)" 
  and     f1:  "finite ((supp h)::'x set)"
  and     a1: "\<exists>(a::'x). (a\<sharp>h \<and> a\<sharp>(h a))"
  shows "pi\<bullet>(fresh_fun h) = fresh_fun(pi\<bullet>h)" (is "?LHS = ?RHS")
proof -
  have ptb: "pt TYPE('x) TYPE('x)" by (simp add: at_pt_inst[OF at]) 
  have ptc: "pt TYPE('x\<Rightarrow>'a) TYPE('x)" by (simp add: pt_fun_inst[OF ptb, OF pta, OF at]) 
  have f2: "finite ((supp (pi\<bullet>h))::'x set)"
  proof -
    from f1 have "finite (pi\<bullet>((supp h)::'x set))" by (simp add: pt_set_finite_ineq[OF ptb, OF at])
    thus ?thesis by (simp add: pt_perm_supp[OF ptc, OF at])
  qed
  from a1 obtain a' where c0: "a'\<sharp>h \<and> a'\<sharp>(h a')" by force
  hence c1: "a'\<sharp>h" and c2: "a'\<sharp>(h a')" by simp_all
  have c3: "(pi\<bullet>a')\<sharp>(pi\<bullet>h)" using c1 by (simp add: pt_fresh_bij[OF ptc, OF at])
  have c4: "(pi\<bullet>a')\<sharp>(pi\<bullet>h) (pi\<bullet>a')"
  proof -
    from c2 have "(pi\<bullet>a')\<sharp>(pi\<bullet>(h a'))" by (simp add: pt_fresh_bij[OF pta, OF at])
    thus ?thesis by (simp add: pt_fun_app_eq[OF ptb, OF at])
  qed
  have a2: "\<exists>(a::'x). (a\<sharp>(pi\<bullet>h) \<and> a\<sharp>((pi\<bullet>h) a))" using c3 c4 by force
  have d1: "?LHS = pi\<bullet>(h a')" using c1 a1 by (simp add: fresh_fun_app[OF pta, OF at, OF f1])
  have d2: "?RHS = (pi\<bullet>h) (pi\<bullet>a')" using c3 a2 by (simp add: fresh_fun_app[OF pta, OF at, OF f2])
  show ?thesis using d1 d2 by (simp add: pt_fun_app_eq[OF ptb, OF at])
qed
  
section {* disjointness properties *}
(*=================================*)
lemma dj_perm_forget:
  fixes pi::"'y prm"
  and   x ::"'x"
  assumes dj: "disjoint TYPE('x) TYPE('y)"
  shows "pi\<bullet>x=x"
  using dj by (simp add: disjoint_def)

lemma dj_perm_perm_forget:
  fixes pi1::"'x prm"
  and   pi2::"'y prm"
  assumes dj: "disjoint TYPE('x) TYPE('y)"
  shows "pi2\<bullet>pi1=pi1"
  using dj by (induct pi1, auto simp add: disjoint_def)

lemma dj_cp:
  fixes pi1::"'x prm"
  and   pi2::"'y prm"
  and   x  ::"'a"
  assumes cp: "cp TYPE ('a) TYPE('x) TYPE('y)"
  and     dj: "disjoint TYPE('y) TYPE('x)"
  shows "pi1\<bullet>(pi2\<bullet>x) = (pi2)\<bullet>(pi1\<bullet>x)"
  by (simp add: cp1[OF cp] dj_perm_perm_forget[OF dj])

lemma dj_supp:
  fixes a::"'x"
  assumes dj: "disjoint TYPE('x) TYPE('y)"
  shows "(supp a) = ({}::'y set)"
apply(simp add: supp_def dj_perm_forget[OF dj])
done


section {* composition instances *}
(* ============================= *)

lemma cp_list_inst:
  assumes c1: "cp TYPE ('a) TYPE('x) TYPE('y)"
  shows "cp TYPE ('a list) TYPE('x) TYPE('y)"
using c1
apply(simp add: cp_def)
apply(auto)
apply(induct_tac x)
apply(auto)
done

lemma cp_set_inst:
  assumes c1: "cp TYPE ('a) TYPE('x) TYPE('y)"
  shows "cp TYPE ('a set) TYPE('x) TYPE('y)"
using c1
apply(simp add: cp_def)
apply(auto)
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi2\<bullet>aa" in exI)
apply(auto)
done

lemma cp_option_inst:
  assumes c1: "cp TYPE ('a) TYPE('x) TYPE('y)"
  shows "cp TYPE ('a option) TYPE('x) TYPE('y)"
using c1
apply(simp add: cp_def)
apply(auto)
apply(case_tac x)
apply(auto)
done

lemma cp_noption_inst:
  assumes c1: "cp TYPE ('a) TYPE('x) TYPE('y)"
  shows "cp TYPE ('a nOption) TYPE('x) TYPE('y)"
using c1
apply(simp add: cp_def)
apply(auto)
apply(case_tac x)
apply(auto)
done

lemma cp_unit_inst:
  shows "cp TYPE (unit) TYPE('x) TYPE('y)"
apply(simp add: cp_def)
done

lemma cp_bool_inst:
  shows "cp TYPE (bool) TYPE('x) TYPE('y)"
apply(simp add: cp_def)
apply(rule allI)+
apply(induct_tac x)
apply(simp_all)
done

lemma cp_prod_inst:
  assumes c1: "cp TYPE ('a) TYPE('x) TYPE('y)"
  and     c2: "cp TYPE ('b) TYPE('x) TYPE('y)"
  shows "cp TYPE ('a\<times>'b) TYPE('x) TYPE('y)"
using c1 c2
apply(simp add: cp_def)
done

lemma cp_fun_inst:
  assumes c1: "cp TYPE ('a) TYPE('x) TYPE('y)"
  and     c2: "cp TYPE ('b) TYPE('x) TYPE('y)"
  and     pt: "pt TYPE ('y) TYPE('x)"
  and     at: "at TYPE ('x)"
  shows "cp TYPE ('a\<Rightarrow>'b) TYPE('x) TYPE('y)"
using c1 c2
apply(auto simp add: cp_def perm_fun_def expand_fun_eq)
apply(simp add: perm_rev[symmetric])
apply(simp add: pt_rev_pi[OF pt_list_inst[OF pt_prod_inst[OF pt, OF pt]], OF at])
done


section {* Abstraction function *}
(*==============================*)

lemma pt_abs_fun_inst:
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pt TYPE('x\<Rightarrow>('a nOption)) TYPE('x)"
  by (rule pt_fun_inst[OF at_pt_inst[OF at],OF pt_noption_inst[OF pt],OF at])

constdefs
  abs_fun :: "'x\<Rightarrow>'a\<Rightarrow>('x\<Rightarrow>('a nOption))" ("[_]._" [100,100] 100)
  "[a].x \<equiv> (\<lambda>b. (if b=a then nSome(x) else (if b\<sharp>x then nSome([(a,b)]\<bullet>x) else nNone)))"

lemma abs_fun_if: 
  fixes pi :: "'x prm"
  and   x  :: "'a"
  and   y  :: "'a"
  and   c  :: "bool"
  shows "pi\<bullet>(if c then x else y) = (if c then (pi\<bullet>x) else (pi\<bullet>y))"   
  by force

lemma abs_fun_pi_ineq:
  fixes a  :: "'y"
  and   x  :: "'a"
  and   pi :: "'x prm"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  shows "pi\<bullet>([a].x) = [(pi\<bullet>a)].(pi\<bullet>x)"
  apply(simp add: abs_fun_def perm_fun_def abs_fun_if)
  apply(simp only: expand_fun_eq)
  apply(rule allI)
  apply(subgoal_tac "(((rev pi)\<bullet>(xa::'y)) = (a::'y)) = (xa = pi\<bullet>a)")(*A*)
  apply(subgoal_tac "(((rev pi)\<bullet>xa)\<sharp>x) = (xa\<sharp>(pi\<bullet>x))")(*B*)
  apply(subgoal_tac "pi\<bullet>([(a,(rev pi)\<bullet>xa)]\<bullet>x) = [(pi\<bullet>a,xa)]\<bullet>(pi\<bullet>x)")(*C*)
  apply(simp)
(*C*)
  apply(simp add: cp1[OF cp])
  apply(simp add: pt_pi_rev[OF ptb, OF at])
(*B*)
  apply(simp add: pt_fresh_left_ineq[OF pta, OF ptb, OF at, OF cp])
(*A*)
  apply(rule iffI)
  apply(rule pt_bij2[OF ptb, OF at, THEN sym])
  apply(simp)
  apply(rule pt_bij2[OF ptb, OF at])
  apply(simp)
done

lemma abs_fun_pi:
  fixes a  :: "'x"
  and   x  :: "'a"
  and   pi :: "'x prm"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "pi\<bullet>([a].x) = [(pi\<bullet>a)].(pi\<bullet>x)"
apply(rule abs_fun_pi_ineq)
apply(rule pt)
apply(rule at_pt_inst)
apply(rule at)+
apply(rule cp_pt_inst)
apply(rule pt)
apply(rule at)
done

lemma abs_fun_eq1: 
  fixes x  :: "'a"
  and   y  :: "'a"
  and   a  :: "'x"
  shows "([a].x = [a].y) = (x = y)"
apply(auto simp add: abs_fun_def)
apply(auto simp add: expand_fun_eq)
apply(drule_tac x="a" in spec)
apply(simp)
done

lemma abs_fun_eq2:
  fixes x  :: "'a"
  and   y  :: "'a"
  and   a  :: "'x"
  and   b  :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
      and at: "at TYPE('x)"
      and a1: "a\<noteq>b" 
      and a2: "[a].x = [b].y" 
  shows "x=[(a,b)]\<bullet>y\<and>a\<sharp>y"
proof -
  from a2 have a3: 
         "\<forall>c::'x. (if c=a then nSome(x) else (if c\<sharp>x then nSome([(a,c)]\<bullet>x) else nNone))
                = (if c=b then nSome(y) else (if c\<sharp>y then nSome([(b,c)]\<bullet>y) else nNone))"
         (is "\<forall>c::'x. ?P c = ?Q c")
    by (force simp add: abs_fun_def expand_fun_eq)
  from a3 have "?P a = ?Q a" by (blast)
  hence a4: "nSome(x) = ?Q a" by simp
  from a3 have "?P b = ?Q b" by (blast)
  hence a5: "nSome(y) = ?P b" by simp
  show ?thesis using a4 a5
  proof (cases "a\<sharp>y")
    assume a6: "a\<sharp>y"
    hence a7: "x = [(b,a)]\<bullet>y" using a4 a1 by simp
    have "[(a,b)]\<bullet>y = [(b,a)]\<bullet>y" by (rule pt3[OF pt], rule at_ds5[OF at])
    thus ?thesis using a6 a7 by simp
  next
    assume "\<not>a\<sharp>y"
    hence "nSome(x) = nNone" using a1 a4 by simp
    hence False by force
    thus ?thesis by force
  qed
qed

lemma abs_fun_eq3: 
  fixes x  :: "'a"
  and   y  :: "'a"
  and   a   :: "'x"
  and   b   :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
      and at: "at TYPE('x)"
      and a1: "a\<noteq>b" 
      and a2: "x=[(a,b)]\<bullet>y" 
      and a3: "a\<sharp>y" 
  shows "[a].x =[b].y"
proof -
  show ?thesis using a1 a2 a3
    apply(auto simp add: abs_fun_def)
    apply(simp only: expand_fun_eq)
    apply(rule allI)
    apply(case_tac "x=a")
    apply(simp)
    apply(rule pt3[OF pt], rule at_ds5[OF at])
    apply(case_tac "x=b")
    apply(simp add: pt_swap_bij[OF pt, OF at])
    apply(simp add: at_calc[OF at] at_bij[OF at] pt_fresh_left[OF pt, OF at])
    apply(simp only: if_False)
    apply(simp add: at_calc[OF at] at_bij[OF at] pt_fresh_left[OF pt, OF at])
    apply(rule impI)
    apply(subgoal_tac "[(a,x)]\<bullet>([(a,b)]\<bullet>y) = [(b,x)]\<bullet>([(a,x)]\<bullet>y)")(*A*)
    apply(simp)
    apply(simp only:  pt_bij[OF pt, OF at])
    apply(rule pt_fresh_fresh[OF pt, OF at])
    apply(assumption)+
    (*A*)
    apply(simp only: pt2[OF pt, symmetric])
    apply(rule pt3[OF pt])
    apply(simp, rule at_ds6[OF at])
    apply(force)
    done
  qed

lemma abs_fun_eq: 
  fixes x  :: "'a"
  and   y  :: "'a"
  and   a  :: "'x"
  and   b  :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
      and at: "at TYPE('x)"
  shows "([a].x = [b].y) = ((a=b \<and> x=y)\<or>(a\<noteq>b \<and> x=[(a,b)]\<bullet>y \<and> a\<sharp>y))"
proof (rule iffI)
  assume b: "[a].x = [b].y"
  show "(a=b \<and> x=y)\<or>(a\<noteq>b \<and> x=[(a,b)]\<bullet>y \<and> a\<sharp>y)"
  proof (cases "a=b")
    case True with b show ?thesis by (simp add: abs_fun_eq1)
  next
    case False with b show ?thesis by (simp add: abs_fun_eq2[OF pt, OF at])
  qed
next
  assume "(a=b \<and> x=y)\<or>(a\<noteq>b \<and> x=[(a,b)]\<bullet>y \<and> a\<sharp>y)"
  thus "[a].x = [b].y"
  proof
    assume "a=b \<and> x=y" thus ?thesis by simp
  next
    assume "a\<noteq>b \<and> x=[(a,b)]\<bullet>y \<and> a\<sharp>y" 
    thus ?thesis by (simp add: abs_fun_eq3[OF pt, OF at])
  qed
qed

lemma abs_fun_supp_approx:
  fixes x :: "'a"
  and   a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "((supp ([a].x))::'x set) \<subseteq> (supp x)\<union>{a}"
proof -
  have "((supp ([a].x))::'x set) \<subseteq> (supp (x,a))" 
    proof 
      fix c
      assume "c\<in>((supp ([a].x))::'x set)"
      hence "infinite {b. [(c,b)]\<bullet>([a].x) \<noteq> [a].x}" by (simp add: supp_def)
      hence "infinite {b. [([(c,b)]\<bullet>a)].([(c,b)]\<bullet>x) \<noteq> [a].x}" by (simp add: abs_fun_pi[OF pt, OF at])
      moreover
      have "{b. [([(c,b)]\<bullet>a)].([(c,b)]\<bullet>x) \<noteq> [a].x} \<subseteq> {b. ([(c,b)]\<bullet>x,[(c,b)]\<bullet>a) \<noteq> (x, a)}"
	apply(rule subsetI)
	apply(simp only: mem_Collect_eq)
	apply(auto)
	done
      (*by force*)
      ultimately have "infinite {b. ([(c,b)]\<bullet>x,[(c,b)]\<bullet>a) \<noteq> (x, a)}" by (simp add: infinite_super)
      thus "c\<in>(supp (x,a))" by (simp add: supp_def)
    qed
  thus ?thesis by (simp add: supp_prod at_supp[OF at])
qed

lemma abs_fun_finite_supp:
  fixes x :: "'a"
  and   a :: "'x"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     f:  "finite ((supp x)::'x set)"
  shows "finite ((supp ([a].x))::'x set)"
proof -
  from f have f1: "finite (((supp x)::'x set)\<union>{a})" by force
  thus ?thesis using abs_fun_supp_approx[OF pt, OF at, of "a" "x"]
   by (simp add: finite_subset)
qed

lemma fresh_abs_funI1:
  fixes  x :: "'a"
  and    a :: "'x"
  and    b :: "'x"
  assumes pt:  "pt TYPE('a) TYPE('x)"
  and     at:   "at TYPE('x)"
  and f:  "finite ((supp x)::'x set)"
  and a1: "b\<sharp>x" 
  and a2: "a\<noteq>b"
  shows "b\<sharp>([a].x)"
  proof -
    have "\<exists>c::'x. c\<sharp>(b,a,x,[a].x)" 
    proof (rule at_exists_fresh[OF at], auto simp add: supp_prod at_supp[OF at] f)
      show "finite ((supp ([a].x))::'x set)" using f
	by (simp add: abs_fun_finite_supp[OF pt, OF at])	
    qed
    then obtain c where fr1: "c\<noteq>b"
                  and   fr2: "c\<noteq>a"
                  and   fr3: "c\<sharp>x"
                  and   fr4: "c\<sharp>([a].x)"
                  by (force simp add: fresh_prod at_fresh[OF at])
    have e: "[(c,b)]\<bullet>([a].x) = [a].([(c,b)]\<bullet>x)" using a2 fr1 fr2 
      by (force simp add: abs_fun_pi[OF pt, OF at] at_calc[OF at])
    from fr4 have "([(c,b)]\<bullet>c)\<sharp> ([(c,b)]\<bullet>([a].x))"
      by (simp add: pt_fresh_bij[OF pt_abs_fun_inst[OF pt, OF at], OF at])
    hence "b\<sharp>([a].([(c,b)]\<bullet>x))" using fr1 fr2 e  
      by (simp add: at_calc[OF at])
    thus ?thesis using a1 fr3 
      by (simp add: pt_fresh_fresh[OF pt, OF at])
qed

lemma fresh_abs_funE:
  fixes a :: "'x"
  and   b :: "'x"
  and   x :: "'a"
  assumes pt:  "pt TYPE('a) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     f:  "finite ((supp x)::'x set)"
  and     a1: "b\<sharp>([a].x)" 
  and     a2: "b\<noteq>a" 
  shows "b\<sharp>x"
proof -
  have "\<exists>c::'x. c\<sharp>(b,a,x,[a].x)"
  proof (rule at_exists_fresh[OF at], auto simp add: supp_prod at_supp[OF at] f)
    show "finite ((supp ([a].x))::'x set)" using f
      by (simp add: abs_fun_finite_supp[OF pt, OF at])	
  qed
  then obtain c where fr1: "b\<noteq>c"
                and   fr2: "c\<noteq>a"
                and   fr3: "c\<sharp>x"
                and   fr4: "c\<sharp>([a].x)" by (force simp add: fresh_prod at_fresh[OF at])
  have "[a].x = [(b,c)]\<bullet>([a].x)" using a1 fr4 
    by (simp add: pt_fresh_fresh[OF pt_abs_fun_inst[OF pt, OF at], OF at])
  hence "[a].x = [a].([(b,c)]\<bullet>x)" using fr2 a2 
    by (force simp add: abs_fun_pi[OF pt, OF at] at_calc[OF at])
  hence b: "([(b,c)]\<bullet>x) = x" by (simp add: abs_fun_eq1)
  from fr3 have "([(b,c)]\<bullet>c)\<sharp>([(b,c)]\<bullet>x)" 
    by (simp add: pt_fresh_bij[OF pt, OF at]) 
  thus ?thesis using b fr1 by (simp add: at_calc[OF at])
qed

lemma fresh_abs_funI2:
  fixes a :: "'x"
  and   x :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     f: "finite ((supp x)::'x set)"
  shows "a\<sharp>([a].x)"
proof -
  have "\<exists>c::'x. c\<sharp>(a,x)"
    by  (rule at_exists_fresh[OF at], auto simp add: supp_prod at_supp[OF at] f) 
  then obtain c where fr1: "a\<noteq>c" and fr1_sym: "c\<noteq>a" 
                and   fr2: "c\<sharp>x" by (force simp add: fresh_prod at_fresh[OF at])
  have "c\<sharp>([a].x)" using f fr1 fr2 by (simp add: fresh_abs_funI1[OF pt, OF at])
  hence "([(c,a)]\<bullet>c)\<sharp>([(c,a)]\<bullet>([a].x))" using fr1  
    by (simp only: pt_fresh_bij[OF pt_abs_fun_inst[OF pt, OF at], OF at])
  hence a: "a\<sharp>([c].([(c,a)]\<bullet>x))" using fr1_sym 
    by (simp add: abs_fun_pi[OF pt, OF at] at_calc[OF at])
  have "[c].([(c,a)]\<bullet>x) = ([a].x)" using fr1_sym fr2 
    by (simp add: abs_fun_eq[OF pt, OF at])
  thus ?thesis using a by simp
qed

lemma fresh_abs_fun_iff: 
  fixes a :: "'x"
  and   b :: "'x"
  and   x :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     f: "finite ((supp x)::'x set)"
  shows "(b\<sharp>([a].x)) = (b=a \<or> b\<sharp>x)" 
  by (auto  dest: fresh_abs_funE[OF pt, OF at,OF f] 
           intro: fresh_abs_funI1[OF pt, OF at,OF f] 
                  fresh_abs_funI2[OF pt, OF at,OF f])

lemma abs_fun_supp: 
  fixes a :: "'x"
  and   x :: "'a"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  and     f: "finite ((supp x)::'x set)"
  shows "supp ([a].x) = (supp x)-{a}"
 by (force simp add: supp_fresh_iff fresh_abs_fun_iff[OF pt, OF at, OF f])

(* maybe needs to be stated by supp -supp *)

lemma abs_fun_supp_ineq: 
  fixes a :: "'y"
  and   x :: "'a"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  and     dj:  "disjoint TYPE('y) TYPE('x)"
  shows "((supp ([a].x))::'x set) = (supp x)"
apply(auto simp add: supp_def)
apply(auto simp add: abs_fun_pi_ineq[OF pta, OF ptb, OF at, OF cp])
apply(auto simp add: dj_perm_forget[OF dj])
apply(auto simp add: abs_fun_eq1) 
done

lemma fresh_abs_fun_iff_ineq: 
  fixes a :: "'y"
  and   b :: "'x"
  and   x :: "'a"
  assumes pta: "pt TYPE('a) TYPE('x)"
  and     ptb: "pt TYPE('y) TYPE('x)"
  and     at:  "at TYPE('x)"
  and     cp:  "cp TYPE('a) TYPE('x) TYPE('y)"
  and     dj:  "disjoint TYPE('y) TYPE('x)"
  shows "b\<sharp>([a].x) = b\<sharp>x" 
  by (simp add: fresh_def abs_fun_supp_ineq[OF pta, OF ptb, OF at, OF cp, OF dj])

section {* abstraction type for the datatype package (not really needed anymore) *}
(*===============================================================================*)
consts
  "ABS_set" :: "('x\<Rightarrow>('a nOption)) set"
inductive ABS_set
  intros
  ABS_in: "(abs_fun a x)\<in>ABS_set"

typedef (ABS) ('x,'a) ABS = "ABS_set::('x\<Rightarrow>('a nOption)) set"
proof 
  fix x::"'a" and a::"'x"
  show "(abs_fun a x)\<in> ABS_set" by (rule ABS_in)
qed

syntax ABS :: "type \<Rightarrow> type \<Rightarrow> type" ("\<guillemotleft>_\<guillemotright>_" [1000,1000] 1000)


section {* Lemmas for Deciding Permutation Equations *}
(*===================================================*)

lemma perm_eq_app:
  fixes f  :: "'a\<Rightarrow>'b"
  and   x  :: "'a"
  and   pi :: "'x prm"
  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "(pi\<bullet>(f x)=y) = ((pi\<bullet>f)(pi\<bullet>x)=y)"
  by (simp add: pt_fun_app_eq[OF pt, OF at])

lemma perm_eq_lam:
  fixes f  :: "'a\<Rightarrow>'b"
  and   x  :: "'a"
  and   pi :: "'x prm"
  shows "((pi\<bullet>(\<lambda>x. f x))=y) = ((\<lambda>x. (pi\<bullet>(f ((rev pi)\<bullet>x))))=y)"
  by (simp add: perm_fun_def)


(***************************************)
(* setup for the individial atom-kinds *)
(* and nominal datatypes               *)
use "nominal_package.ML"
setup "NominalPackage.setup"

(*****************************************)
(* setup for induction principles method *)
use "nominal_induct.ML";
method_setup nominal_induct =
  {* nominal_induct_method *}
  {* nominal induction *}

(*******************************)
(* permutation equality tactic *)
use "nominal_permeq.ML";

method_setup perm_simp =
  {* perm_eq_meth *}
  {* tactic for deciding equalities involving permutations *}

method_setup perm_simp_debug =
  {* perm_eq_meth_debug *}
  {* tactic for deciding equalities involving permutations including debuging facilities *}

method_setup supports_simp =
  {* supports_meth *}
  {* tactic for deciding whether something supports semthing else *}

method_setup supports_simp_debug =
  {* supports_meth_debug *}
  {* tactic for deciding equalities involving permutations including debuging facilities *}

end


