(*  Title:      ZF/Arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

*)

(*"Difference" is subtraction of natural numbers.
  There are no negative numbers; we have
     m #- n = 0  iff  m<=n   and     m #- n = succ(k) iff m>n.
  Also, rec(m, 0, %z w.z) is pred(m).   
*)

header{*Arithmetic Operators and Their Definitions*} 

theory Arith = Univ:

text{*Proofs about elementary arithmetic: addition, multiplication, etc.*}

constdefs
  pred   :: "i=>i"    (*inverse of succ*)
    "pred(y) == nat_case(0, %x. x, y)"

  natify :: "i=>i"    (*coerces non-nats to nats*)
    "natify == Vrecursor(%f a. if a = succ(pred(a)) then succ(f`pred(a))
                                                    else 0)"

consts
  raw_add  :: "[i,i]=>i"
  raw_diff  :: "[i,i]=>i"
  raw_mult  :: "[i,i]=>i"

primrec
  "raw_add (0, n) = n"
  "raw_add (succ(m), n) = succ(raw_add(m, n))"

primrec
  raw_diff_0:     "raw_diff(m, 0) = m"
  raw_diff_succ:  "raw_diff(m, succ(n)) =
                     nat_case(0, %x. x, raw_diff(m, n))"

primrec
  "raw_mult(0, n) = 0"
  "raw_mult(succ(m), n) = raw_add (n, raw_mult(m, n))"

constdefs
  add :: "[i,i]=>i"                    (infixl "#+" 65)
    "m #+ n == raw_add (natify(m), natify(n))"

  diff :: "[i,i]=>i"                    (infixl "#-" 65)
    "m #- n == raw_diff (natify(m), natify(n))"

  mult :: "[i,i]=>i"                    (infixl "#*" 70)
    "m #* n == raw_mult (natify(m), natify(n))"

  raw_div  :: "[i,i]=>i"
    "raw_div (m, n) ==
       transrec(m, %j f. if j<n | n=0 then 0 else succ(f`(j#-n)))"

  raw_mod  :: "[i,i]=>i"
    "raw_mod (m, n) ==
       transrec(m, %j f. if j<n | n=0 then j else f`(j#-n))"

  div  :: "[i,i]=>i"                    (infixl "div" 70)
    "m div n == raw_div (natify(m), natify(n))"

  mod  :: "[i,i]=>i"                    (infixl "mod" 70)
    "m mod n == raw_mod (natify(m), natify(n))"

syntax (xsymbols)
  "mult"      :: "[i,i] => i"               (infixr "#\<times>" 70)

syntax (HTML output)
  "mult"      :: "[i, i] => i"               (infixr "#\<times>" 70)


declare rec_type [simp]
        nat_0_le [simp]


lemma zero_lt_lemma: "[| 0<k; k \<in> nat |] ==> \<exists>j\<in>nat. k = succ(j)"
apply (erule rev_mp)
apply (induct_tac "k", auto)
done

(* [| 0 < k; k \<in> nat; !!j. [| j \<in> nat; k = succ(j) |] ==> Q |] ==> Q *)
lemmas zero_lt_natE = zero_lt_lemma [THEN bexE, standard]


subsection{*@{text natify}, the Coercion to @{term nat}*}

lemma pred_succ_eq [simp]: "pred(succ(y)) = y"
by (unfold pred_def, auto)

lemma natify_succ: "natify(succ(x)) = succ(natify(x))"
by (rule natify_def [THEN def_Vrecursor, THEN trans], auto)

lemma natify_0 [simp]: "natify(0) = 0"
by (rule natify_def [THEN def_Vrecursor, THEN trans], auto)

lemma natify_non_succ: "\<forall>z. x ~= succ(z) ==> natify(x) = 0"
by (rule natify_def [THEN def_Vrecursor, THEN trans], auto)

lemma natify_in_nat [iff,TC]: "natify(x) \<in> nat"
apply (rule_tac a=x in eps_induct)
apply (case_tac "\<exists>z. x = succ(z)")
apply (auto simp add: natify_succ natify_non_succ)
done

lemma natify_ident [simp]: "n \<in> nat ==> natify(n) = n"
apply (induct_tac "n")
apply (auto simp add: natify_succ)
done

lemma natify_eqE: "[|natify(x) = y;  x \<in> nat|] ==> x=y"
by auto


(*** Collapsing rules: to remove natify from arithmetic expressions ***)

lemma natify_idem [simp]: "natify(natify(x)) = natify(x)"
by simp

(** Addition **)

lemma add_natify1 [simp]: "natify(m) #+ n = m #+ n"
by (simp add: add_def)

lemma add_natify2 [simp]: "m #+ natify(n) = m #+ n"
by (simp add: add_def)

(** Multiplication **)

lemma mult_natify1 [simp]: "natify(m) #* n = m #* n"
by (simp add: mult_def)

lemma mult_natify2 [simp]: "m #* natify(n) = m #* n"
by (simp add: mult_def)

(** Difference **)

lemma diff_natify1 [simp]: "natify(m) #- n = m #- n"
by (simp add: diff_def)

lemma diff_natify2 [simp]: "m #- natify(n) = m #- n"
by (simp add: diff_def)

(** Remainder **)

lemma mod_natify1 [simp]: "natify(m) mod n = m mod n"
by (simp add: mod_def)

lemma mod_natify2 [simp]: "m mod natify(n) = m mod n"
by (simp add: mod_def)


(** Quotient **)

lemma div_natify1 [simp]: "natify(m) div n = m div n"
by (simp add: div_def)

lemma div_natify2 [simp]: "m div natify(n) = m div n"
by (simp add: div_def)


subsection{*Typing rules*}

(** Addition **)

lemma raw_add_type: "[| m\<in>nat;  n\<in>nat |] ==> raw_add (m, n) \<in> nat"
by (induct_tac "m", auto)

lemma add_type [iff,TC]: "m #+ n \<in> nat"
by (simp add: add_def raw_add_type)

(** Multiplication **)

lemma raw_mult_type: "[| m\<in>nat;  n\<in>nat |] ==> raw_mult (m, n) \<in> nat"
apply (induct_tac "m")
apply (simp_all add: raw_add_type)
done

lemma mult_type [iff,TC]: "m #* n \<in> nat"
by (simp add: mult_def raw_mult_type)


(** Difference **)

lemma raw_diff_type: "[| m\<in>nat;  n\<in>nat |] ==> raw_diff (m, n) \<in> nat"
by (induct_tac "n", auto)

lemma diff_type [iff,TC]: "m #- n \<in> nat"
by (simp add: diff_def raw_diff_type)

lemma diff_0_eq_0 [simp]: "0 #- n = 0"
apply (unfold diff_def)
apply (rule natify_in_nat [THEN nat_induct], auto)
done

(*Must simplify BEFORE the induction: else we get a critical pair*)
lemma diff_succ_succ [simp]: "succ(m) #- succ(n) = m #- n"
apply (simp add: natify_succ diff_def)
apply (rule_tac x1 = n in natify_in_nat [THEN nat_induct], auto)
done

(*This defining property is no longer wanted*)
declare raw_diff_succ [simp del]

(*Natify has weakened this law, compared with the older approach*)
lemma diff_0 [simp]: "m #- 0 = natify(m)"
by (simp add: diff_def)

lemma diff_le_self: "m\<in>nat ==> (m #- n) le m"
apply (subgoal_tac " (m #- natify (n)) le m")
apply (rule_tac [2] m = m and n = "natify (n) " in diff_induct)
apply (erule_tac [6] leE)
apply (simp_all add: le_iff)
done


subsection{*Addition*}

(*Natify has weakened this law, compared with the older approach*)
lemma add_0_natify [simp]: "0 #+ m = natify(m)"
by (simp add: add_def)

lemma add_succ [simp]: "succ(m) #+ n = succ(m #+ n)"
by (simp add: natify_succ add_def)

lemma add_0: "m \<in> nat ==> 0 #+ m = m"
by simp

(*Associative law for addition*)
lemma add_assoc: "(m #+ n) #+ k = m #+ (n #+ k)"
apply (subgoal_tac "(natify(m) #+ natify(n)) #+ natify(k) =
                    natify(m) #+ (natify(n) #+ natify(k))")
apply (rule_tac [2] n = "natify(m)" in nat_induct)
apply auto
done

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
lemma add_0_right_natify [simp]: "m #+ 0 = natify(m)"
apply (subgoal_tac "natify(m) #+ 0 = natify(m)")
apply (rule_tac [2] n = "natify(m)" in nat_induct)
apply auto
done

lemma add_succ_right [simp]: "m #+ succ(n) = succ(m #+ n)"
apply (unfold add_def)
apply (rule_tac n = "natify(m) " in nat_induct)
apply (auto simp add: natify_succ)
done

lemma add_0_right: "m \<in> nat ==> m #+ 0 = m"
by auto

(*Commutative law for addition*)
lemma add_commute: "m #+ n = n #+ m"
apply (subgoal_tac "natify(m) #+ natify(n) = natify(n) #+ natify(m) ")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply auto
done

(*for a/c rewriting*)
lemma add_left_commute: "m#+(n#+k)=n#+(m#+k)"
apply (rule add_commute [THEN trans])
apply (rule add_assoc [THEN trans])
apply (rule add_commute [THEN subst_context])
done

(*Addition is an AC-operator*)
lemmas add_ac = add_assoc add_commute add_left_commute

(*Cancellation law on the left*)
lemma raw_add_left_cancel:
     "[| raw_add(k, m) = raw_add(k, n);  k\<in>nat |] ==> m=n"
apply (erule rev_mp)
apply (induct_tac "k", auto)
done

lemma add_left_cancel_natify: "k #+ m = k #+ n ==> natify(m) = natify(n)"
apply (unfold add_def)
apply (drule raw_add_left_cancel, auto)
done

lemma add_left_cancel:
     "[| i = j;  i #+ m = j #+ n;  m\<in>nat;  n\<in>nat |] ==> m = n"
by (force dest!: add_left_cancel_natify)

(*Thanks to Sten Agerholm*)
lemma add_le_elim1_natify: "k#+m le k#+n ==> natify(m) le natify(n)"
apply (rule_tac P = "natify(k) #+m le natify(k) #+n" in rev_mp)
apply (rule_tac [2] n = "natify(k) " in nat_induct)
apply auto
done

lemma add_le_elim1: "[| k#+m le k#+n; m \<in> nat; n \<in> nat |] ==> m le n"
by (drule add_le_elim1_natify, auto)

lemma add_lt_elim1_natify: "k#+m < k#+n ==> natify(m) < natify(n)"
apply (rule_tac P = "natify(k) #+m < natify(k) #+n" in rev_mp)
apply (rule_tac [2] n = "natify(k) " in nat_induct)
apply auto
done

lemma add_lt_elim1: "[| k#+m < k#+n; m \<in> nat; n \<in> nat |] ==> m < n"
by (drule add_lt_elim1_natify, auto)


subsection{*Monotonicity of Addition*}

(*strict, in 1st argument; proof is by rule induction on 'less than'.
  Still need j\<in>nat, for consider j = omega.  Then we can have i<omega,
  which is the same as i\<in>nat, but natify(j)=0, so the conclusion fails.*)
lemma add_lt_mono1: "[| i<j; j\<in>nat |] ==> i#+k < j#+k"
apply (frule lt_nat_in_nat, assumption)
apply (erule succ_lt_induct)
apply (simp_all add: leI)
done

text{*strict, in second argument*}
lemma add_lt_mono2: "[| i<j; j\<in>nat |] ==> k#+i < k#+j"
by (simp add: add_commute [of k] add_lt_mono1)

text{*A [clumsy] way of lifting < monotonicity to @{text "\<le>"} monotonicity*}
lemma Ord_lt_mono_imp_le_mono:
  assumes lt_mono: "!!i j. [| i<j; j:k |] ==> f(i) < f(j)"
      and ford:    "!!i. i:k ==> Ord(f(i))"
      and leij:    "i le j"
      and jink:    "j:k"
  shows "f(i) le f(j)"
apply (insert leij jink) 
apply (blast intro!: leCI lt_mono ford elim!: leE)
done

text{*@{text "\<le>"} monotonicity, 1st argument*}
lemma add_le_mono1: "[| i le j; j\<in>nat |] ==> i#+k le j#+k"
apply (rule_tac f = "%j. j#+k" in Ord_lt_mono_imp_le_mono, typecheck) 
apply (blast intro: add_lt_mono1 add_type [THEN nat_into_Ord])+
done

text{*@{text "\<le>"} monotonicity, both arguments*}
lemma add_le_mono: "[| i le j; k le l; j\<in>nat; l\<in>nat |] ==> i#+k le j#+l"
apply (rule add_le_mono1 [THEN le_trans], assumption+)
apply (subst add_commute, subst add_commute, rule add_le_mono1, assumption+)
done

text{*Combinations of less-than and less-than-or-equals*}

lemma add_lt_le_mono: "[| i<j; k\<le>l; j\<in>nat; l\<in>nat |] ==> i#+k < j#+l"
apply (rule add_lt_mono1 [THEN lt_trans2], assumption+)
apply (subst add_commute, subst add_commute, rule add_le_mono1, assumption+)
done

lemma add_le_lt_mono: "[| i\<le>j; k<l; j\<in>nat; l\<in>nat |] ==> i#+k < j#+l"
by (subst add_commute, subst add_commute, erule add_lt_le_mono, assumption+)

text{*Less-than: in other words, strict in both arguments*}
lemma add_lt_mono: "[| i<j; k<l; j\<in>nat; l\<in>nat |] ==> i#+k < j#+l"
apply (rule add_lt_le_mono) 
apply (auto intro: leI) 
done

(** Subtraction is the inverse of addition. **)

lemma diff_add_inverse: "(n#+m) #- n = natify(m)"
apply (subgoal_tac " (natify(n) #+ m) #- natify(n) = natify(m) ")
apply (rule_tac [2] n = "natify(n) " in nat_induct)
apply auto
done

lemma diff_add_inverse2: "(m#+n) #- n = natify(m)"
by (simp add: add_commute [of m] diff_add_inverse)

lemma diff_cancel: "(k#+m) #- (k#+n) = m #- n"
apply (subgoal_tac "(natify(k) #+ natify(m)) #- (natify(k) #+ natify(n)) =
                    natify(m) #- natify(n) ")
apply (rule_tac [2] n = "natify(k) " in nat_induct)
apply auto
done

lemma diff_cancel2: "(m#+k) #- (n#+k) = m #- n"
by (simp add: add_commute [of _ k] diff_cancel)

lemma diff_add_0: "n #- (n#+m) = 0"
apply (subgoal_tac "natify(n) #- (natify(n) #+ natify(m)) = 0")
apply (rule_tac [2] n = "natify(n) " in nat_induct)
apply auto
done

lemma pred_0 [simp]: "pred(0) = 0"
by (simp add: pred_def)

lemma eq_succ_imp_eq_m1: "[|i = succ(j); i\<in>nat|] ==> j = i #- 1 & j \<in>nat"
by simp 

lemma pred_Un_distrib:
    "[|i\<in>nat; j\<in>nat|] ==> pred(i Un j) = pred(i) Un pred(j)"
apply (erule_tac n=i in natE, simp) 
apply (erule_tac n=j in natE, simp) 
apply (simp add:  succ_Un_distrib [symmetric])
done

lemma pred_type [TC,simp]:
    "i \<in> nat ==> pred(i) \<in> nat"
by (simp add: pred_def split: split_nat_case)

lemma nat_diff_pred: "[|i\<in>nat; j\<in>nat|] ==> i #- succ(j) = pred(i #- j)";
apply (rule_tac m=i and n=j in diff_induct) 
apply (auto simp add: pred_def nat_imp_quasinat split: split_nat_case)
done

lemma diff_succ_eq_pred: "i #- succ(j) = pred(i #- j)";
apply (insert nat_diff_pred [of "natify(i)" "natify(j)"])
apply (simp add: natify_succ [symmetric]) 
done

lemma nat_diff_Un_distrib:
    "[|i\<in>nat; j\<in>nat; k\<in>nat|] ==> (i Un j) #- k = (i#-k) Un (j#-k)"
apply (rule_tac n=k in nat_induct) 
apply (simp_all add: diff_succ_eq_pred pred_Un_distrib) 
done

lemma diff_Un_distrib:
    "[|i\<in>nat; j\<in>nat|] ==> (i Un j) #- k = (i#-k) Un (j#-k)"
by (insert nat_diff_Un_distrib [of i j "natify(k)"], simp)

text{*We actually prove @{term "i #- j #- k = i #- (j #+ k)"}*}
lemma diff_diff_left [simplified]:
     "natify(i)#-natify(j)#-k = natify(i) #- (natify(j)#+k)";
by (rule_tac m="natify(i)" and n="natify(j)" in diff_induct, auto)


(** Lemmas for the CancelNumerals simproc **)

lemma eq_add_iff: "(u #+ m = u #+ n) <-> (0 #+ m = natify(n))"
apply auto
apply (blast dest: add_left_cancel_natify)
apply (simp add: add_def)
done

lemma less_add_iff: "(u #+ m < u #+ n) <-> (0 #+ m < natify(n))"
apply (auto simp add: add_lt_elim1_natify)
apply (drule add_lt_mono1)
apply (auto simp add: add_commute [of u])
done

lemma diff_add_eq: "((u #+ m) #- (u #+ n)) = ((0 #+ m) #- n)"
by (simp add: diff_cancel)

(*To tidy up the result of a simproc.  Only the RHS will be simplified.*)
lemma eq_cong2: "u = u' ==> (t==u) == (t==u')"
by auto

lemma iff_cong2: "u <-> u' ==> (t==u) == (t==u')"
by auto


subsection{*Multiplication*}

lemma mult_0 [simp]: "0 #* m = 0"
by (simp add: mult_def)

lemma mult_succ [simp]: "succ(m) #* n = n #+ (m #* n)"
by (simp add: add_def mult_def natify_succ raw_mult_type)

(*right annihilation in product*)
lemma mult_0_right [simp]: "m #* 0 = 0"
apply (unfold mult_def)
apply (rule_tac n = "natify(m) " in nat_induct)
apply auto
done

(*right successor law for multiplication*)
lemma mult_succ_right [simp]: "m #* succ(n) = m #+ (m #* n)"
apply (subgoal_tac "natify(m) #* succ (natify(n)) =
                    natify(m) #+ (natify(m) #* natify(n))")
apply (simp (no_asm_use) add: natify_succ add_def mult_def)
apply (rule_tac n = "natify(m) " in nat_induct)
apply (simp_all add: add_ac)
done

lemma mult_1_natify [simp]: "1 #* n = natify(n)"
by auto

lemma mult_1_right_natify [simp]: "n #* 1 = natify(n)"
by auto

lemma mult_1: "n \<in> nat ==> 1 #* n = n"
by simp

lemma mult_1_right: "n \<in> nat ==> n #* 1 = n"
by simp

(*Commutative law for multiplication*)
lemma mult_commute: "m #* n = n #* m"
apply (subgoal_tac "natify(m) #* natify(n) = natify(n) #* natify(m) ")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply auto
done

(*addition distributes over multiplication*)
lemma add_mult_distrib: "(m #+ n) #* k = (m #* k) #+ (n #* k)"
apply (subgoal_tac "(natify(m) #+ natify(n)) #* natify(k) =
                    (natify(m) #* natify(k)) #+ (natify(n) #* natify(k))")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply (simp_all add: add_assoc [symmetric])
done

(*Distributive law on the left*)
lemma add_mult_distrib_left: "k #* (m #+ n) = (k #* m) #+ (k #* n)"
apply (subgoal_tac "natify(k) #* (natify(m) #+ natify(n)) =
                    (natify(k) #* natify(m)) #+ (natify(k) #* natify(n))")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply (simp_all add: add_ac)
done

(*Associative law for multiplication*)
lemma mult_assoc: "(m #* n) #* k = m #* (n #* k)"
apply (subgoal_tac "(natify(m) #* natify(n)) #* natify(k) =
                    natify(m) #* (natify(n) #* natify(k))")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply (simp_all add: add_mult_distrib)
done

(*for a/c rewriting*)
lemma mult_left_commute: "m #* (n #* k) = n #* (m #* k)"
apply (rule mult_commute [THEN trans])
apply (rule mult_assoc [THEN trans])
apply (rule mult_commute [THEN subst_context])
done

lemmas mult_ac = mult_assoc mult_commute mult_left_commute


lemma lt_succ_eq_0_disj:
     "[| m\<in>nat; n\<in>nat |]
      ==> (m < succ(n)) <-> (m = 0 | (\<exists>j\<in>nat. m = succ(j) & j < n))"
by (induct_tac "m", auto)

lemma less_diff_conv [rule_format]:
     "[| j\<in>nat; k\<in>nat |] ==> \<forall>i\<in>nat. (i < j #- k) <-> (i #+ k < j)"
by (erule_tac m = k in diff_induct, auto)

lemmas nat_typechecks = rec_type nat_0I nat_1I nat_succI Ord_nat

ML
{*
val pred_def = thm "pred_def";
val raw_div_def = thm "raw_div_def";
val raw_mod_def = thm "raw_mod_def";
val div_def = thm "div_def";
val mod_def = thm "mod_def";

val zero_lt_natE = thm "zero_lt_natE";
val pred_succ_eq = thm "pred_succ_eq";
val natify_succ = thm "natify_succ";
val natify_0 = thm "natify_0";
val natify_non_succ = thm "natify_non_succ";
val natify_in_nat = thm "natify_in_nat";
val natify_ident = thm "natify_ident";
val natify_eqE = thm "natify_eqE";
val natify_idem = thm "natify_idem";
val add_natify1 = thm "add_natify1";
val add_natify2 = thm "add_natify2";
val mult_natify1 = thm "mult_natify1";
val mult_natify2 = thm "mult_natify2";
val diff_natify1 = thm "diff_natify1";
val diff_natify2 = thm "diff_natify2";
val mod_natify1 = thm "mod_natify1";
val mod_natify2 = thm "mod_natify2";
val div_natify1 = thm "div_natify1";
val div_natify2 = thm "div_natify2";
val raw_add_type = thm "raw_add_type";
val add_type = thm "add_type";
val raw_mult_type = thm "raw_mult_type";
val mult_type = thm "mult_type";
val raw_diff_type = thm "raw_diff_type";
val diff_type = thm "diff_type";
val diff_0_eq_0 = thm "diff_0_eq_0";
val diff_succ_succ = thm "diff_succ_succ";
val diff_0 = thm "diff_0";
val diff_le_self = thm "diff_le_self";
val add_0_natify = thm "add_0_natify";
val add_succ = thm "add_succ";
val add_0 = thm "add_0";
val add_assoc = thm "add_assoc";
val add_0_right_natify = thm "add_0_right_natify";
val add_succ_right = thm "add_succ_right";
val add_0_right = thm "add_0_right";
val add_commute = thm "add_commute";
val add_left_commute = thm "add_left_commute";
val raw_add_left_cancel = thm "raw_add_left_cancel";
val add_left_cancel_natify = thm "add_left_cancel_natify";
val add_left_cancel = thm "add_left_cancel";
val add_le_elim1_natify = thm "add_le_elim1_natify";
val add_le_elim1 = thm "add_le_elim1";
val add_lt_elim1_natify = thm "add_lt_elim1_natify";
val add_lt_elim1 = thm "add_lt_elim1";
val add_lt_mono1 = thm "add_lt_mono1";
val add_lt_mono2 = thm "add_lt_mono2";
val add_lt_mono = thm "add_lt_mono";
val Ord_lt_mono_imp_le_mono = thm "Ord_lt_mono_imp_le_mono";
val add_le_mono1 = thm "add_le_mono1";
val add_le_mono = thm "add_le_mono";
val diff_add_inverse = thm "diff_add_inverse";
val diff_add_inverse2 = thm "diff_add_inverse2";
val diff_cancel = thm "diff_cancel";
val diff_cancel2 = thm "diff_cancel2";
val diff_add_0 = thm "diff_add_0";
val eq_add_iff = thm "eq_add_iff";
val less_add_iff = thm "less_add_iff";
val diff_add_eq = thm "diff_add_eq";
val eq_cong2 = thm "eq_cong2";
val iff_cong2 = thm "iff_cong2";
val mult_0 = thm "mult_0";
val mult_succ = thm "mult_succ";
val mult_0_right = thm "mult_0_right";
val mult_succ_right = thm "mult_succ_right";
val mult_1_natify = thm "mult_1_natify";
val mult_1_right_natify = thm "mult_1_right_natify";
val mult_1 = thm "mult_1";
val mult_1_right = thm "mult_1_right";
val mult_commute = thm "mult_commute";
val add_mult_distrib = thm "add_mult_distrib";
val add_mult_distrib_left = thm "add_mult_distrib_left";
val mult_assoc = thm "mult_assoc";
val mult_left_commute = thm "mult_left_commute";
val lt_succ_eq_0_disj = thm "lt_succ_eq_0_disj";
val less_diff_conv = thm "less_diff_conv";

val add_ac = thms "add_ac";
val mult_ac = thms "mult_ac";
val nat_typechecks = thms "nat_typechecks";
*}

end
