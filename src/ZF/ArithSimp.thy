(*  Title:      ZF/ArithSimp.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

*)

header{*Arithmetic with simplification*}

theory ArithSimp = Arith
files "arith_data.ML":

subsection{*Difference*}

lemma diff_self_eq_0 [simp]: "m #- m = 0"
apply (subgoal_tac "natify (m) #- natify (m) = 0")
apply (rule_tac [2] natify_in_nat [THEN nat_induct], auto)
done

(**Addition is the inverse of subtraction**)

(*We need m:nat even if we replace the RHS by natify(m), for consider e.g.
  n=2, m=omega; then n + (m-n) = 2 + (0-2) = 2 ~= 0 = natify(m).*)
lemma add_diff_inverse: "[| n le m;  m:nat |] ==> n #+ (m#-n) = m"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp)
apply (rule_tac m = m and n = n in diff_induct, auto)
done

lemma add_diff_inverse2: "[| n le m;  m:nat |] ==> (m#-n) #+ n = m"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (simp (no_asm_simp) add: add_commute add_diff_inverse)
done

(*Proof is IDENTICAL to that of add_diff_inverse*)
lemma diff_succ: "[| n le m;  m:nat |] ==> succ(m) #- n = succ(m#-n)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp)
apply (rule_tac m = m and n = n in diff_induct)
apply (simp_all (no_asm_simp))
done

lemma zero_less_diff [simp]:
     "[| m: nat; n: nat |] ==> 0 < (n #- m)   <->   m<n"
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
lemma div_termination: "[| 0<n;  n le m;  m:nat |] ==> m #- n < m"
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

lemma raw_mod_type: "[| m:nat;  n:nat |] ==> raw_mod (m, n) : nat"
apply (unfold raw_mod_def)
apply (rule Ord_transrec_type)
apply (auto simp add: nat_into_Ord [THEN Ord_0_lt_iff])
apply (blast intro: div_rls) 
done

lemma mod_type [TC,iff]: "m mod n : nat"
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

lemma mod_less [simp]: "[| m<n; n : nat |] ==> m mod n = m"
apply (frule lt_nat_in_nat, assumption)
apply (simp (no_asm_simp) add: mod_def raw_mod_less)
done

lemma raw_mod_geq:
     "[| 0<n; n le m;  m:nat |] ==> raw_mod (m, n) = raw_mod (m#-n, n)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (rule raw_mod_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD] not_lt_iff_le [THEN iffD2], blast)
done


lemma mod_geq: "[| n le m;  m:nat |] ==> m mod n = (m#-n) mod n"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (case_tac "n=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (simp add: mod_def raw_mod_geq nat_into_Ord [THEN Ord_0_lt_iff])
done


subsection{*Division*}

lemma raw_div_type: "[| m:nat;  n:nat |] ==> raw_div (m, n) : nat"
apply (unfold raw_div_def)
apply (rule Ord_transrec_type)
apply (auto simp add: nat_into_Ord [THEN Ord_0_lt_iff])
apply (blast intro: div_rls) 
done

lemma div_type [TC,iff]: "m div n : nat"
apply (unfold div_def)
apply (simp (no_asm) add: div_def raw_div_type)
done

lemma raw_div_less: "m<n ==> raw_div (m,n) = 0"
apply (rule raw_div_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD])
done

lemma div_less [simp]: "[| m<n; n : nat |] ==> m div n = 0"
apply (frule lt_nat_in_nat, assumption)
apply (simp (no_asm_simp) add: div_def raw_div_less)
done

lemma raw_div_geq: "[| 0<n;  n le m;  m:nat |] ==> raw_div(m,n) = succ(raw_div(m#-n, n))"
apply (subgoal_tac "n ~= 0")
prefer 2 apply blast
apply (frule lt_nat_in_nat, erule nat_succI)
apply (rule raw_div_def [THEN def_transrec, THEN trans])
apply (simp (no_asm_simp) add: div_termination [THEN ltD] not_lt_iff_le [THEN iffD2] ) 
done

lemma div_geq [simp]:
     "[| 0<n;  n le m;  m:nat |] ==> m div n = succ ((m#-n) div n)"
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
txt{*case n le x*}
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
txt{* case n le succ(x) *}
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
txt{* case n le x*}
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

lemma add_le_self: "m:nat ==> m le (m #+ n)"
apply (simp (no_asm_simp))
done

lemma add_le_self2: "m:nat ==> m le (n #+ m)"
apply (simp (no_asm_simp))
done

(*** Monotonicity of Multiplication ***)

lemma mult_le_mono1: "[| i le j; j:nat |] ==> (i#*k) le (j#*k)"
apply (subgoal_tac "natify (i) #*natify (k) le j#*natify (k) ")
apply (frule_tac [2] lt_nat_in_nat)
apply (rule_tac [3] n = "natify (k) " in nat_induct)
apply (simp_all add: add_le_mono)
done

(* le monotonicity, BOTH arguments*)
lemma mult_le_mono: "[| i le j; k le l; j:nat; l:nat |] ==> i#*k le j#*l"
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

lemma add_eq_0_iff [iff]: "m#+n = 0 <-> natify(m)=0 & natify(n)=0"
apply (subgoal_tac "natify (m) #+ natify (n) = 0 <-> natify (m) =0 & natify (n) =0")
apply (rule_tac [2] n = "natify (m) " in natE)
 apply (rule_tac [4] n = "natify (n) " in natE)
apply auto
done

lemma zero_lt_mult_iff [iff]: "0 < m#*n <-> 0 < natify(m) & 0 < natify(n)"
apply (subgoal_tac "0 < natify (m) #*natify (n) <-> 0 < natify (m) & 0 < natify (n) ")
apply (rule_tac [2] n = "natify (m) " in natE)
 apply (rule_tac [4] n = "natify (n) " in natE)
  apply (rule_tac [3] n = "natify (n) " in natE)
apply auto
done

lemma mult_eq_1_iff [iff]: "m#*n = 1 <-> natify(m)=1 & natify(n)=1"
apply (subgoal_tac "natify (m) #* natify (n) = 1 <-> natify (m) =1 & natify (n) =1")
apply (rule_tac [2] n = "natify (m) " in natE)
 apply (rule_tac [4] n = "natify (n) " in natE)
apply auto
done


lemma mult_is_zero: "[|m: nat; n: nat|] ==> (m #* n = 0) <-> (m = 0 | n = 0)"
apply auto
apply (erule natE)
apply (erule_tac [2] natE, auto)
done

lemma mult_is_zero_natify [iff]:
     "(m #* n = 0) <-> (natify(m) = 0 | natify(n) = 0)"
apply (cut_tac m = "natify (m) " and n = "natify (n) " in mult_is_zero)
apply auto
done


subsection{*Cancellation Laws for Common Factors in Comparisons*}

lemma mult_less_cancel_lemma:
     "[| k: nat; m: nat; n: nat |] ==> (m#*k < n#*k) <-> (0<k & m<n)"
apply (safe intro!: mult_lt_mono1)
apply (erule natE, auto)
apply (rule not_le_iff_lt [THEN iffD1])
apply (drule_tac [3] not_le_iff_lt [THEN [2] rev_iffD2])
prefer 5 apply (blast intro: mult_le_mono1, auto)
done

lemma mult_less_cancel2 [simp]:
     "(m#*k < n#*k) <-> (0 < natify(k) & natify(m) < natify(n))"
apply (rule iff_trans)
apply (rule_tac [2] mult_less_cancel_lemma, auto)
done

lemma mult_less_cancel1 [simp]:
     "(k#*m < k#*n) <-> (0 < natify(k) & natify(m) < natify(n))"
apply (simp (no_asm) add: mult_less_cancel2 mult_commute [of k])
done

lemma mult_le_cancel2 [simp]: "(m#*k le n#*k) <-> (0 < natify(k) --> natify(m) le natify(n))"
apply (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym])
apply auto
done

lemma mult_le_cancel1 [simp]: "(k#*m le k#*n) <-> (0 < natify(k) --> natify(m) le natify(n))"
apply (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym])
apply auto
done

lemma mult_le_cancel_le1: "k : nat ==> k #* m le k \<longleftrightarrow> (0 < k \<longrightarrow> natify(m) le 1)"
by (cut_tac k = k and m = m and n = 1 in mult_le_cancel1, auto)

lemma Ord_eq_iff_le: "[| Ord(m); Ord(n) |] ==> m=n <-> (m le n & n le m)"
by (blast intro: le_anti_sym)

lemma mult_cancel2_lemma:
     "[| k: nat; m: nat; n: nat |] ==> (m#*k = n#*k) <-> (m=n | k=0)"
apply (simp (no_asm_simp) add: Ord_eq_iff_le [of "m#*k"] Ord_eq_iff_le [of m])
apply (auto simp add: Ord_0_lt_iff)
done

lemma mult_cancel2 [simp]:
     "(m#*k = n#*k) <-> (natify(m) = natify(n) | natify(k) = 0)"
apply (rule iff_trans)
apply (rule_tac [2] mult_cancel2_lemma, auto)
done

lemma mult_cancel1 [simp]:
     "(k#*m = k#*n) <-> (natify(m) = natify(n) | natify(k) = 0)"
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
     "[| m<n; n: nat |] ==> EX k: nat. n = succ(m#+k)"
apply (frule lt_nat_in_nat, assumption)
apply (erule rev_mp)
apply (induct_tac "n")
apply (simp_all (no_asm) add: le_iff)
apply (blast elim!: leE intro!: add_0_right [symmetric] add_succ_right [symmetric])
done

lemma less_iff_succ_add:
     "[| m: nat; n: nat |] ==> (m<n) <-> (EX k: nat. n = succ(m#+k))"
by (auto intro: less_imp_succ_add)


subsubsection{*More Lemmas About Difference*}

lemma diff_is_0_lemma:
     "[| m: nat; n: nat |] ==> m #- n = 0 <-> m le n"
apply (rule_tac m = m and n = n in diff_induct, simp_all)
done

lemma diff_is_0_iff: "m #- n = 0 <-> natify(m) le natify(n)"
by (simp add: diff_is_0_lemma [symmetric])

lemma nat_lt_imp_diff_eq_0:
     "[| a:nat; b:nat; a<b |] ==> a #- b = 0"
by (simp add: diff_is_0_iff le_iff) 

lemma nat_diff_split:
     "[| a:nat; b:nat |] ==>  
      (P(a #- b)) <-> ((a < b -->P(0)) & (ALL d:nat. a = b #+ d --> P(d)))"
apply (case_tac "a < b")
 apply (force simp add: nat_lt_imp_diff_eq_0)
apply (rule iffI, force, simp) 
apply (drule_tac x="a#-b" in bspec)
apply (simp_all add: Ordinal.not_lt_iff_le add_diff_inverse) 
done


ML
{*
val diff_self_eq_0 = thm "diff_self_eq_0";
val add_diff_inverse = thm "add_diff_inverse";
val add_diff_inverse2 = thm "add_diff_inverse2";
val diff_succ = thm "diff_succ";
val zero_less_diff = thm "zero_less_diff";
val diff_mult_distrib = thm "diff_mult_distrib";
val diff_mult_distrib2 = thm "diff_mult_distrib2";
val div_termination = thm "div_termination";
val raw_mod_type = thm "raw_mod_type";
val mod_type = thm "mod_type";
val DIVISION_BY_ZERO_DIV = thm "DIVISION_BY_ZERO_DIV";
val DIVISION_BY_ZERO_MOD = thm "DIVISION_BY_ZERO_MOD";
val raw_mod_less = thm "raw_mod_less";
val mod_less = thm "mod_less";
val raw_mod_geq = thm "raw_mod_geq";
val mod_geq = thm "mod_geq";
val raw_div_type = thm "raw_div_type";
val div_type = thm "div_type";
val raw_div_less = thm "raw_div_less";
val div_less = thm "div_less";
val raw_div_geq = thm "raw_div_geq";
val div_geq = thm "div_geq";
val mod_div_equality_natify = thm "mod_div_equality_natify";
val mod_div_equality = thm "mod_div_equality";
val mod_succ = thm "mod_succ";
val mod_less_divisor = thm "mod_less_divisor";
val mod_1_eq = thm "mod_1_eq";
val mod2_cases = thm "mod2_cases";
val mod2_succ_succ = thm "mod2_succ_succ";
val mod2_add_more = thm "mod2_add_more";
val mod2_add_self = thm "mod2_add_self";
val add_le_self = thm "add_le_self";
val add_le_self2 = thm "add_le_self2";
val mult_le_mono1 = thm "mult_le_mono1";
val mult_le_mono = thm "mult_le_mono";
val mult_lt_mono2 = thm "mult_lt_mono2";
val mult_lt_mono1 = thm "mult_lt_mono1";
val add_eq_0_iff = thm "add_eq_0_iff";
val zero_lt_mult_iff = thm "zero_lt_mult_iff";
val mult_eq_1_iff = thm "mult_eq_1_iff";
val mult_is_zero = thm "mult_is_zero";
val mult_is_zero_natify = thm "mult_is_zero_natify";
val mult_less_cancel2 = thm "mult_less_cancel2";
val mult_less_cancel1 = thm "mult_less_cancel1";
val mult_le_cancel2 = thm "mult_le_cancel2";
val mult_le_cancel1 = thm "mult_le_cancel1";
val mult_le_cancel_le1 = thm "mult_le_cancel_le1";
val Ord_eq_iff_le = thm "Ord_eq_iff_le";
val mult_cancel2 = thm "mult_cancel2";
val mult_cancel1 = thm "mult_cancel1";
val div_cancel_raw = thm "div_cancel_raw";
val div_cancel = thm "div_cancel";
val mult_mod_distrib_raw = thm "mult_mod_distrib_raw";
val mod_mult_distrib2 = thm "mod_mult_distrib2";
val mult_mod_distrib = thm "mult_mod_distrib";
val mod_add_self2_raw = thm "mod_add_self2_raw";
val mod_add_self2 = thm "mod_add_self2";
val mod_add_self1 = thm "mod_add_self1";
val mod_mult_self1_raw = thm "mod_mult_self1_raw";
val mod_mult_self1 = thm "mod_mult_self1";
val mod_mult_self2 = thm "mod_mult_self2";
val mult_eq_self_implies_10 = thm "mult_eq_self_implies_10";
val less_imp_succ_add = thm "less_imp_succ_add";
val less_iff_succ_add = thm "less_iff_succ_add";
val diff_is_0_iff = thm "diff_is_0_iff";
val nat_lt_imp_diff_eq_0 = thm "nat_lt_imp_diff_eq_0";
val nat_diff_split = thm "nat_diff_split";
*}

end
