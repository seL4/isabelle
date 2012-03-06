(*  Title:      ZF/ArithSimp.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge
*)

header{*Arithmetic with simplification*}

theory ArithSimp
imports Arith
uses "~~/src/Provers/Arith/cancel_numerals.ML"
      "~~/src/Provers/Arith/combine_numerals.ML"
      "arith_data.ML"
begin

subsection{*Difference*}

lemma diff_self_eq_0 [simp]: "m #- m = 0"
apply (subgoal_tac "natify (m) #- natify (m) = 0")
apply (rule_tac [2] natify_in_nat [THEN nat_induct], auto)
done

(**Addition is the inverse of subtraction**)

(*We need m:nat even if we replace the RHS by natify(m), for consider e.g.
  n=2, m=omega; then n + (m-n) = 2 + (0-2) = 2 \<noteq> 0 = natify(m).*)
lemma add_diff_inverse: "[| n \<le> m;  m:nat |] ==> n #+ (m#-n) = m"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp)
apply (rule_tac m = m and n = n in diff_induct, auto)
done

lemma add_diff_inverse2: "[| n \<le> m;  m:nat |] ==> (m#-n) #+ n = m"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (simp (no_asm_simp) add: add_commute add_diff_inverse)
done

(*Proof is IDENTICAL to that of add_diff_inverse*)
lemma diff_succ: "[| n \<le> m;  m:nat |] ==> succ(m) #- n = succ(m#-n)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp)
apply (rule_tac m = m and n = n in diff_induct)
apply (simp_all (no_asm_simp))
done

lemma zero_less_diff [simp]:
     "[| m: nat; n: nat |] ==> 0 < (n #- m)   \<longleftrightarrow>   m<n"
apply (rule_tac m = m and n = n in diff_induct)
apply (simp_all (no_asm_simp))
done


(** Difference distributes over multiplication **)

lemma diff_mult_distrib: "(m #- n) #* k = (m #* k) #- (n #* k)"
apply (subgoal_tac " (natify (m) #- natify (n)) #* natify (k) = (natify (m) #* natify (k)) #- (natify (n) #* natify (k))")
apply (rule_tac [2] m = "natify (m) " and n = "natify (n) " in diff_induct)
apply (simp_all add: diff_cancel)
done

lemma diff_mult_distrib2: "k #* (m #- n) = (k #* m) #- (k #* n)"
apply (simp (no_asm) add: mult_commute [of k] diff_mult_distrib)
done


subsection{*Remainder*}

(*We need m:nat even with natify*)
lemma div_termination: "[| 0<n;  n \<le> m;  m:nat |] ==> m #- n < m"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp)
apply (erule rev_mp)
apply (rule_tac m = m and n = n in diff_induct)
apply (simp_all (no_asm_simp) add: diff_le_self)
done

(*for mod and div*)
lemmas div_rls =
    nat_typechecks Ord_transrec_type apply_funtype
    div_termination [THEN ltD]
    nat_into_Ord not_lt_iff_le [THEN iffD1]

lemma raw_mod_type: "[| m:nat;  n:nat |] ==> raw_mod (m, n) \<in> nat"
apply (unfold raw_mod_def)
apply (rule Ord_transrec_type)
apply (auto simp add: nat_into_Ord [THEN Ord_0_lt_iff])
apply (blast intro: div_rls)
done

lemma mod_type [TC,iff]: "m mod n \<in> nat"
apply (unfold mod_def)
apply (simp (no_asm) add: mod_def raw_mod_type)
done


(** Aribtrary definitions for division by zero.  Useful to simplify
    certain equations **)

lemma DIVISION_BY_ZERO_DIV: "a div 0 = 0"
apply (unfold div_def)
apply (rule raw_div_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp))
done  (*NOT for adding to default simpset*)

lemma DIVISION_BY_ZERO_MOD: "a mod 0 = natify(a)"
apply (unfold mod_def)
apply (rule raw_mod_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp))
done  (*NOT for adding to default simpset*)

lemma raw_mod_less: "m<n ==> raw_mod (m,n) = m"
apply (rule raw_mod_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD])
done

lemma mod_less [simp]: "[| m<n; n \<in> nat |] ==> m mod n = m"
apply (frule lt_nat_in_nat, assumption)
apply (simp (no_asm_simp) add: mod_def raw_mod_less)
done

lemma raw_mod_geq:
     "[| 0<n; n \<le> m;  m:nat |] ==> raw_mod (m, n) = raw_mod (m#-n, n)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (rule raw_mod_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD] not_lt_iff_le [THEN iffD2], blast)
done


lemma mod_geq: "[| n \<le> m;  m:nat |] ==> m mod n = (m#-n) mod n"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (case_tac "n=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (simp add: mod_def raw_mod_geq nat_into_Ord [THEN Ord_0_lt_iff])
done


subsection{*Division*}

lemma raw_div_type: "[| m:nat;  n:nat |] ==> raw_div (m, n) \<in> nat"
apply (unfold raw_div_def)
apply (rule Ord_transrec_type)
apply (auto simp add: nat_into_Ord [THEN Ord_0_lt_iff])
apply (blast intro: div_rls)
done

lemma div_type [TC,iff]: "m div n \<in> nat"
apply (unfold div_def)
apply (simp (no_asm) add: div_def raw_div_type)
done

lemma raw_div_less: "m<n ==> raw_div (m,n) = 0"
apply (rule raw_div_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD])
done

lemma div_less [simp]: "[| m<n; n \<in> nat |] ==> m div n = 0"
apply (frule lt_nat_in_nat, assumption)
apply (simp (no_asm_simp) add: div_def raw_div_less)
done

lemma raw_div_geq: "[| 0<n;  n \<le> m;  m:nat |] ==> raw_div(m,n) = succ(raw_div(m#-n, n))"
apply (subgoal_tac "n \<noteq> 0")
prefer 2 apply blast
apply (frule lt_nat_in_nat, erule nat_succI)
apply (rule raw_div_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD] not_lt_iff_le [THEN iffD2] )
done

lemma div_geq [simp]:
     "[| 0<n;  n \<le> m;  m:nat |] ==> m div n = succ ((m#-n) div n)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (simp (no_asm_simp) add: div_def raw_div_geq)
done

declare div_less [simp] div_geq [simp]


(*A key result*)
lemma mod_div_lemma: "[| m: nat;  n: nat |] ==> (m div n)#*n #+ m mod n = m"
apply (case_tac "n=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (simp add: nat_into_Ord [THEN Ord_0_lt_iff])
apply (erule complete_induct)
apply (case_tac "x<n")
txt{*case x<n*}
apply (simp (no_asm_simp))
txt{*case @{term"n \<le> x"}*}
apply (simp add: not_lt_iff_le add_assoc mod_geq div_termination [THEN ltD] add_diff_inverse)
done

lemma mod_div_equality_natify: "(m div n)#*n #+ m mod n = natify(m)"
apply (subgoal_tac " (natify (m) div natify (n))#*natify (n) #+ natify (m) mod natify (n) = natify (m) ")
apply force
apply (subst mod_div_lemma, auto)
done

lemma mod_div_equality: "m: nat ==> (m div n)#*n #+ m mod n = m"
apply (simp (no_asm_simp) add: mod_div_equality_natify)
done


subsection{*Further Facts about Remainder*}

text{*(mainly for mutilated chess board)*}

lemma mod_succ_lemma:
     "[| 0<n;  m:nat;  n:nat |]
      ==> succ(m) mod n = (if succ(m mod n) = n then 0 else succ(m mod n))"
apply (erule complete_induct)
apply (case_tac "succ (x) <n")
txt{* case succ(x) < n *}
 apply (simp (no_asm_simp) add: nat_le_refl [THEN lt_trans] succ_neq_self)
 apply (simp add: ltD [THEN mem_imp_not_eq])
txt{* case @{term"n \<le> succ(x)"} *}
apply (simp add: mod_geq not_lt_iff_le)
apply (erule leE)
 apply (simp (no_asm_simp) add: mod_geq div_termination [THEN ltD] diff_succ)
txt{*equality case*}
apply (simp add: diff_self_eq_0)
done

lemma mod_succ:
  "n:nat ==> succ(m) mod n = (if succ(m mod n) = n then 0 else succ(m mod n))"
apply (case_tac "n=0")
 apply (simp (no_asm_simp) add: natify_succ DIVISION_BY_ZERO_MOD)
apply (subgoal_tac "natify (succ (m)) mod n = (if succ (natify (m) mod n) = n then 0 else succ (natify (m) mod n))")
 prefer 2
 apply (subst natify_succ)
 apply (rule mod_succ_lemma)
  apply (auto simp del: natify_succ simp add: nat_into_Ord [THEN Ord_0_lt_iff])
done

lemma mod_less_divisor: "[| 0<n;  n:nat |] ==> m mod n < n"
apply (subgoal_tac "natify (m) mod n < n")
apply (rule_tac [2] i = "natify (m) " in complete_induct)
apply (case_tac [3] "x<n", auto)
txt{* case @{term"n \<le> x"}*}
apply (simp add: mod_geq not_lt_iff_le div_termination [THEN ltD])
done

lemma mod_1_eq [simp]: "m mod 1 = 0"
by (cut_tac n = 1 in mod_less_divisor, auto)

lemma mod2_cases: "b<2 ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)"
apply (subgoal_tac "k mod 2: 2")
 prefer 2 apply (simp add: mod_less_divisor [THEN ltD])
apply (drule ltD, auto)
done

lemma mod2_succ_succ [simp]: "succ(succ(m)) mod 2 = m mod 2"
apply (subgoal_tac "m mod 2: 2")
 prefer 2 apply (simp add: mod_less_divisor [THEN ltD])
apply (auto simp add: mod_succ)
done

lemma mod2_add_more [simp]: "(m#+m#+n) mod 2 = n mod 2"
apply (subgoal_tac " (natify (m) #+natify (m) #+n) mod 2 = n mod 2")
apply (rule_tac [2] n = "natify (m) " in nat_induct)
apply auto
done

lemma mod2_add_self [simp]: "(m#+m) mod 2 = 0"
by (cut_tac n = 0 in mod2_add_more, auto)


subsection{*Additional theorems about @{text "\<le>"}*}

lemma add_le_self: "m:nat ==> m \<le> (m #+ n)"
apply (simp (no_asm_simp))
done

lemma add_le_self2: "m:nat ==> m \<le> (n #+ m)"
apply (simp (no_asm_simp))
done

(*** Monotonicity of Multiplication ***)

lemma mult_le_mono1: "[| i \<le> j; j:nat |] ==> (i#*k) \<le> (j#*k)"
apply (subgoal_tac "natify (i) #*natify (k) \<le> j#*natify (k) ")
apply (frule_tac [2] lt_nat_in_nat)
apply (rule_tac [3] n = "natify (k) " in nat_induct)
apply (simp_all add: add_le_mono)
done

(* @{text"\<le>"} monotonicity, BOTH arguments*)
lemma mult_le_mono: "[| i \<le> j; k \<le> l; j:nat; l:nat |] ==> i#*k \<le> j#*l"
apply (rule mult_le_mono1 [THEN le_trans], assumption+)
apply (subst mult_commute, subst mult_commute, rule mult_le_mono1, assumption+)
done

(*strict, in 1st argument; proof is by induction on k>0.
  I can't see how to relax the typing conditions.*)
lemma mult_lt_mono2: "[| i<j; 0<k; j:nat; k:nat |] ==> k#*i < k#*j"
apply (erule zero_lt_natE)
apply (frule_tac [2] lt_nat_in_nat)
apply (simp_all (no_asm_simp))
apply (induct_tac "x")
apply (simp_all (no_asm_simp) add: add_lt_mono)
done

lemma mult_lt_mono1: "[| i<j; 0<k; j:nat; k:nat |] ==> i#*k < j#*k"
apply (simp (no_asm_simp) add: mult_lt_mono2 mult_commute [of _ k])
done

lemma add_eq_0_iff [iff]: "m#+n = 0 \<longleftrightarrow> natify(m)=0 & natify(n)=0"
apply (subgoal_tac "natify (m) #+ natify (n) = 0 \<longleftrightarrow> natify (m) =0 & natify (n) =0")
apply (rule_tac [2] n = "natify (m) " in natE)
 apply (rule_tac [4] n = "natify (n) " in natE)
apply auto
done

lemma zero_lt_mult_iff [iff]: "0 < m#*n \<longleftrightarrow> 0 < natify(m) & 0 < natify(n)"
apply (subgoal_tac "0 < natify (m) #*natify (n) \<longleftrightarrow> 0 < natify (m) & 0 < natify (n) ")
apply (rule_tac [2] n = "natify (m) " in natE)
 apply (rule_tac [4] n = "natify (n) " in natE)
  apply (rule_tac [3] n = "natify (n) " in natE)
apply auto
done

lemma mult_eq_1_iff [iff]: "m#*n = 1 \<longleftrightarrow> natify(m)=1 & natify(n)=1"
apply (subgoal_tac "natify (m) #* natify (n) = 1 \<longleftrightarrow> natify (m) =1 & natify (n) =1")
apply (rule_tac [2] n = "natify (m) " in natE)
 apply (rule_tac [4] n = "natify (n) " in natE)
apply auto
done


lemma mult_is_zero: "[|m: nat; n: nat|] ==> (m #* n = 0) \<longleftrightarrow> (m = 0 | n = 0)"
apply auto
apply (erule natE)
apply (erule_tac [2] natE, auto)
done

lemma mult_is_zero_natify [iff]:
     "(m #* n = 0) \<longleftrightarrow> (natify(m) = 0 | natify(n) = 0)"
apply (cut_tac m = "natify (m) " and n = "natify (n) " in mult_is_zero)
apply auto
done


subsection{*Cancellation Laws for Common Factors in Comparisons*}

lemma mult_less_cancel_lemma:
     "[| k: nat; m: nat; n: nat |] ==> (m#*k < n#*k) \<longleftrightarrow> (0<k & m<n)"
apply (safe intro!: mult_lt_mono1)
apply (erule natE, auto)
apply (rule not_le_iff_lt [THEN iffD1])
apply (drule_tac [3] not_le_iff_lt [THEN [2] rev_iffD2])
prefer 5 apply (blast intro: mult_le_mono1, auto)
done

lemma mult_less_cancel2 [simp]:
     "(m#*k < n#*k) \<longleftrightarrow> (0 < natify(k) & natify(m) < natify(n))"
apply (rule iff_trans)
apply (rule_tac [2] mult_less_cancel_lemma, auto)
done

lemma mult_less_cancel1 [simp]:
     "(k#*m < k#*n) \<longleftrightarrow> (0 < natify(k) & natify(m) < natify(n))"
apply (simp (no_asm) add: mult_less_cancel2 mult_commute [of k])
done

lemma mult_le_cancel2 [simp]: "(m#*k \<le> n#*k) \<longleftrightarrow> (0 < natify(k) \<longrightarrow> natify(m) \<le> natify(n))"
apply (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym])
apply auto
done

lemma mult_le_cancel1 [simp]: "(k#*m \<le> k#*n) \<longleftrightarrow> (0 < natify(k) \<longrightarrow> natify(m) \<le> natify(n))"
apply (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym])
apply auto
done

lemma mult_le_cancel_le1: "k \<in> nat ==> k #* m \<le> k \<longleftrightarrow> (0 < k \<longrightarrow> natify(m) \<le> 1)"
by (cut_tac k = k and m = m and n = 1 in mult_le_cancel1, auto)

lemma Ord_eq_iff_le: "[| Ord(m); Ord(n) |] ==> m=n \<longleftrightarrow> (m \<le> n & n \<le> m)"
by (blast intro: le_anti_sym)

lemma mult_cancel2_lemma:
     "[| k: nat; m: nat; n: nat |] ==> (m#*k = n#*k) \<longleftrightarrow> (m=n | k=0)"
apply (simp (no_asm_simp) add: Ord_eq_iff_le [of "m#*k"] Ord_eq_iff_le [of m])
apply (auto simp add: Ord_0_lt_iff)
done

lemma mult_cancel2 [simp]:
     "(m#*k = n#*k) \<longleftrightarrow> (natify(m) = natify(n) | natify(k) = 0)"
apply (rule iff_trans)
apply (rule_tac [2] mult_cancel2_lemma, auto)
done

lemma mult_cancel1 [simp]:
     "(k#*m = k#*n) \<longleftrightarrow> (natify(m) = natify(n) | natify(k) = 0)"
apply (simp (no_asm) add: mult_cancel2 mult_commute [of k])
done


(** Cancellation law for division **)

lemma div_cancel_raw:
     "[| 0<n; 0<k; k:nat; m:nat; n:nat |] ==> (k#*m) div (k#*n) = m div n"
apply (erule_tac i = m in complete_induct)
apply (case_tac "x<n")
 apply (simp add: div_less zero_lt_mult_iff mult_lt_mono2)
apply (simp add: not_lt_iff_le zero_lt_mult_iff le_refl [THEN mult_le_mono]
          div_geq diff_mult_distrib2 [symmetric] div_termination [THEN ltD])
done

lemma div_cancel:
     "[| 0 < natify(n);  0 < natify(k) |] ==> (k#*m) div (k#*n) = m div n"
apply (cut_tac k = "natify (k) " and m = "natify (m)" and n = "natify (n)"
       in div_cancel_raw)
apply auto
done


subsection{*More Lemmas about Remainder*}

lemma mult_mod_distrib_raw:
     "[| k:nat; m:nat; n:nat |] ==> (k#*m) mod (k#*n) = k #* (m mod n)"
apply (case_tac "k=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (case_tac "n=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (simp add: nat_into_Ord [THEN Ord_0_lt_iff])
apply (erule_tac i = m in complete_induct)
apply (case_tac "x<n")
 apply (simp (no_asm_simp) add: mod_less zero_lt_mult_iff mult_lt_mono2)
apply (simp add: not_lt_iff_le zero_lt_mult_iff le_refl [THEN mult_le_mono]
         mod_geq diff_mult_distrib2 [symmetric] div_termination [THEN ltD])
done

lemma mod_mult_distrib2: "k #* (m mod n) = (k#*m) mod (k#*n)"
apply (cut_tac k = "natify (k) " and m = "natify (m)" and n = "natify (n)"
       in mult_mod_distrib_raw)
apply auto
done

lemma mult_mod_distrib: "(m mod n) #* k = (m#*k) mod (n#*k)"
apply (simp (no_asm) add: mult_commute mod_mult_distrib2)
done

lemma mod_add_self2_raw: "n \<in> nat ==> (m #+ n) mod n = m mod n"
apply (subgoal_tac " (n #+ m) mod n = (n #+ m #- n) mod n")
apply (simp add: add_commute)
apply (subst mod_geq [symmetric], auto)
done

lemma mod_add_self2 [simp]: "(m #+ n) mod n = m mod n"
apply (cut_tac n = "natify (n) " in mod_add_self2_raw)
apply auto
done

lemma mod_add_self1 [simp]: "(n#+m) mod n = m mod n"
apply (simp (no_asm_simp) add: add_commute mod_add_self2)
done

lemma mod_mult_self1_raw: "k \<in> nat ==> (m #+ k#*n) mod n = m mod n"
apply (erule nat_induct)
apply (simp_all (no_asm_simp) add: add_left_commute [of _ n])
done

lemma mod_mult_self1 [simp]: "(m #+ k#*n) mod n = m mod n"
apply (cut_tac k = "natify (k) " in mod_mult_self1_raw)
apply auto
done

lemma mod_mult_self2 [simp]: "(m #+ n#*k) mod n = m mod n"
apply (simp (no_asm) add: mult_commute mod_mult_self1)
done

(*Lemma for gcd*)
lemma mult_eq_self_implies_10: "m = m#*n ==> natify(n)=1 | m=0"
apply (subgoal_tac "m: nat")
 prefer 2
 apply (erule ssubst)
 apply simp
apply (rule disjCI)
apply (drule sym)
apply (rule Ord_linear_lt [of "natify(n)" 1])
apply simp_all
 apply (subgoal_tac "m #* n = 0", simp)
 apply (subst mult_natify2 [symmetric])
 apply (simp del: mult_natify2)
apply (drule nat_into_Ord [THEN Ord_0_lt, THEN [2] mult_lt_mono2], auto)
done

lemma less_imp_succ_add [rule_format]:
     "[| m<n; n: nat |] ==> \<exists>k\<in>nat. n = succ(m#+k)"
apply (frule lt_nat_in_nat, assumption)
apply (erule rev_mp)
apply (induct_tac "n")
apply (simp_all (no_asm) add: le_iff)
apply (blast elim!: leE intro!: add_0_right [symmetric] add_succ_right [symmetric])
done

lemma less_iff_succ_add:
     "[| m: nat; n: nat |] ==> (m<n) \<longleftrightarrow> (\<exists>k\<in>nat. n = succ(m#+k))"
by (auto intro: less_imp_succ_add)

lemma add_lt_elim2:
     "\<lbrakk>a #+ d = b #+ c; a < b; b \<in> nat; c \<in> nat; d \<in> nat\<rbrakk> \<Longrightarrow> c < d"
by (drule less_imp_succ_add, auto)

lemma add_le_elim2:
     "\<lbrakk>a #+ d = b #+ c; a \<le> b; b \<in> nat; c \<in> nat; d \<in> nat\<rbrakk> \<Longrightarrow> c \<le> d"
by (drule less_imp_succ_add, auto)


subsubsection{*More Lemmas About Difference*}

lemma diff_is_0_lemma:
     "[| m: nat; n: nat |] ==> m #- n = 0 \<longleftrightarrow> m \<le> n"
apply (rule_tac m = m and n = n in diff_induct, simp_all)
done

lemma diff_is_0_iff: "m #- n = 0 \<longleftrightarrow> natify(m) \<le> natify(n)"
by (simp add: diff_is_0_lemma [symmetric])

lemma nat_lt_imp_diff_eq_0:
     "[| a:nat; b:nat; a<b |] ==> a #- b = 0"
by (simp add: diff_is_0_iff le_iff)

lemma raw_nat_diff_split:
     "[| a:nat; b:nat |] ==>
      (P(a #- b)) \<longleftrightarrow> ((a < b \<longrightarrow>P(0)) & (\<forall>d\<in>nat. a = b #+ d \<longrightarrow> P(d)))"
apply (case_tac "a < b")
 apply (force simp add: nat_lt_imp_diff_eq_0)
apply (rule iffI, force, simp)
apply (drule_tac x="a#-b" in bspec)
apply (simp_all add: Ordinal.not_lt_iff_le add_diff_inverse)
done

lemma nat_diff_split:
   "(P(a #- b)) \<longleftrightarrow>
    (natify(a) < natify(b) \<longrightarrow>P(0)) & (\<forall>d\<in>nat. natify(a) = b #+ d \<longrightarrow> P(d))"
apply (cut_tac P=P and a="natify(a)" and b="natify(b)" in raw_nat_diff_split)
apply simp_all
done

text{*Difference and less-than*}

lemma diff_lt_imp_lt: "[|(k#-i) < (k#-j); i\<in>nat; j\<in>nat; k\<in>nat|] ==> j<i"
apply (erule rev_mp)
apply (simp split add: nat_diff_split, auto)
 apply (blast intro: add_le_self lt_trans1)
apply (rule not_le_iff_lt [THEN iffD1], auto)
apply (subgoal_tac "i #+ da < j #+ d", force)
apply (blast intro: add_le_lt_mono)
done

lemma lt_imp_diff_lt: "[|j<i; i\<le>k; k\<in>nat|] ==> (k#-i) < (k#-j)"
apply (frule le_in_nat, assumption)
apply (frule lt_nat_in_nat, assumption)
apply (simp split add: nat_diff_split, auto)
  apply (blast intro: lt_asym lt_trans2)
 apply (blast intro: lt_irrefl lt_trans2)
apply (rule not_le_iff_lt [THEN iffD1], auto)
apply (subgoal_tac "j #+ d < i #+ da", force)
apply (blast intro: add_lt_le_mono)
done


lemma diff_lt_iff_lt: "[|i\<le>k; j\<in>nat; k\<in>nat|] ==> (k#-i) < (k#-j) \<longleftrightarrow> j<i"
apply (frule le_in_nat, assumption)
apply (blast intro: lt_imp_diff_lt diff_lt_imp_lt)
done

end
