(*  Title:      ZF/IntDiv_ZF.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Here is the division algorithm in ML:

    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
               in  if 0<=r-b then (2*q+1, r-b) else (2*q, r)
           end

    fun negDivAlg (a,b) =
      if 0<=a+b then (~1,a+b)
      else let val (q,r) = negDivAlg(a, 2*b)
               in  if 0<=r-b then (2*q+1, r-b) else (2*q, r)
           end;

    fun negateSnd (q,r:int) = (q,~r);

    fun divAlg (a,b) = if 0<=a then
                          if b>0 then posDivAlg (a,b)
                           else if a=0 then (0,0)
                                else negateSnd (negDivAlg (~a,~b))
                       else
                          if 0<b then negDivAlg (a,b)
                          else        negateSnd (posDivAlg (~a,~b));
*)

header{*The Division Operators Div and Mod*}

theory IntDiv_ZF imports IntArith OrderArith begin

definition
  quorem :: "[i,i] => o"  where
    "quorem == %<a,b> <q,r>.
                      a = b$*q $+ r &
                      (#0$<b & #0$<=r & r$<b | ~(#0$<b) & b$<r & r $<= #0)"

definition
  adjust :: "[i,i] => i"  where
    "adjust(b) == %<q,r>. if #0 $<= r$-b then <#2$*q $+ #1,r$-b>
                          else <#2$*q,r>"


(** the division algorithm **)

definition
  posDivAlg :: "i => i"  where
(*for the case a>=0, b>0*)
(*recdef posDivAlg "inv_image less_than (%(a,b). nat_of(a $- b $+ #1))"*)
    "posDivAlg(ab) ==
       wfrec(measure(int*int, %<a,b>. nat_of (a $- b $+ #1)),
             ab,
             %<a,b> f. if (a$<b | b$<=#0) then <#0,a>
                       else adjust(b, f ` <a,#2$*b>))"


(*for the case a<0, b>0*)
definition
  negDivAlg :: "i => i"  where
(*recdef negDivAlg "inv_image less_than (%(a,b). nat_of(- a $- b))"*)
    "negDivAlg(ab) ==
       wfrec(measure(int*int, %<a,b>. nat_of ($- a $- b)),
             ab,
             %<a,b> f. if (#0 $<= a$+b | b$<=#0) then <#-1,a$+b>
                       else adjust(b, f ` <a,#2$*b>))"

(*for the general case @{term"b\<noteq>0"}*)

definition
  negateSnd :: "i => i"  where
    "negateSnd == %<q,r>. <q, $-r>"

  (*The full division algorithm considers all possible signs for a, b
    including the special case a=0, b<0, because negDivAlg requires a<0*)
definition
  divAlg :: "i => i"  where
    "divAlg ==
       %<a,b>. if #0 $<= a then
                  if #0 $<= b then posDivAlg (<a,b>)
                  else if a=#0 then <#0,#0>
                       else negateSnd (negDivAlg (<$-a,$-b>))
               else
                  if #0$<b then negDivAlg (<a,b>)
                  else         negateSnd (posDivAlg (<$-a,$-b>))"

definition
  zdiv  :: "[i,i]=>i"                    (infixl "zdiv" 70)  where
    "a zdiv b == fst (divAlg (<intify(a), intify(b)>))"

definition
  zmod  :: "[i,i]=>i"                    (infixl "zmod" 70)  where
    "a zmod b == snd (divAlg (<intify(a), intify(b)>))"


(** Some basic laws by Sidi Ehmety (need linear arithmetic!) **)

lemma zspos_add_zspos_imp_zspos: "[| #0 $< x;  #0 $< y |] ==> #0 $< x $+ y"
apply (rule_tac y = "y" in zless_trans)
apply (rule_tac [2] zdiff_zless_iff [THEN iffD1])
apply auto
done

lemma zpos_add_zpos_imp_zpos: "[| #0 $<= x;  #0 $<= y |] ==> #0 $<= x $+ y"
apply (rule_tac y = "y" in zle_trans)
apply (rule_tac [2] zdiff_zle_iff [THEN iffD1])
apply auto
done

lemma zneg_add_zneg_imp_zneg: "[| x $< #0;  y $< #0 |] ==> x $+ y $< #0"
apply (rule_tac y = "y" in zless_trans)
apply (rule zless_zdiff_iff [THEN iffD1])
apply auto
done

(* this theorem is used below *)
lemma zneg_or_0_add_zneg_or_0_imp_zneg_or_0:
     "[| x $<= #0;  y $<= #0 |] ==> x $+ y $<= #0"
apply (rule_tac y = "y" in zle_trans)
apply (rule zle_zdiff_iff [THEN iffD1])
apply auto
done

lemma zero_lt_zmagnitude: "[| #0 $< k; k \<in> int |] ==> 0 < zmagnitude(k)"
apply (drule zero_zless_imp_znegative_zminus)
apply (drule_tac [2] zneg_int_of)
apply (auto simp add: zminus_equation [of k])
apply (subgoal_tac "0 < zmagnitude ($# succ (n))")
 apply simp
apply (simp only: zmagnitude_int_of)
apply simp
done


(*** Inequality lemmas involving $#succ(m) ***)

lemma zless_add_succ_iff:
     "(w $< z $+ $# succ(m)) <-> (w $< z $+ $#m | intify(w) = z $+ $#m)"
apply (auto simp add: zless_iff_succ_zadd zadd_assoc int_of_add [symmetric])
apply (rule_tac [3] x = "0" in bexI)
apply (cut_tac m = "m" in int_succ_int_1)
apply (cut_tac m = "n" in int_succ_int_1)
apply simp
apply (erule natE)
apply auto
apply (rule_tac x = "succ (n) " in bexI)
apply auto
done

lemma zadd_succ_lemma:
     "z \<in> int ==> (w $+ $# succ(m) $<= z) <-> (w $+ $#m $< z)"
apply (simp only: not_zless_iff_zle [THEN iff_sym] zless_add_succ_iff)
apply (auto intro: zle_anti_sym elim: zless_asym
            simp add: zless_imp_zle not_zless_iff_zle)
done

lemma zadd_succ_zle_iff: "(w $+ $# succ(m) $<= z) <-> (w $+ $#m $< z)"
apply (cut_tac z = "intify (z)" in zadd_succ_lemma)
apply auto
done

(** Inequality reasoning **)

lemma zless_add1_iff_zle: "(w $< z $+ #1) <-> (w$<=z)"
apply (subgoal_tac "#1 = $# 1")
apply (simp only: zless_add_succ_iff zle_def)
apply auto
done

lemma add1_zle_iff: "(w $+ #1 $<= z) <-> (w $< z)"
apply (subgoal_tac "#1 = $# 1")
apply (simp only: zadd_succ_zle_iff)
apply auto
done

lemma add1_left_zle_iff: "(#1 $+ w $<= z) <-> (w $< z)"
apply (subst zadd_commute)
apply (rule add1_zle_iff)
done


(*** Monotonicity of Multiplication ***)

lemma zmult_mono_lemma: "k \<in> nat ==> i $<= j ==> i $* $#k $<= j $* $#k"
apply (induct_tac "k")
 prefer 2 apply (subst int_succ_int_1)
apply (simp_all (no_asm_simp) add: zadd_zmult_distrib2 zadd_zle_mono)
done

lemma zmult_zle_mono1: "[| i $<= j;  #0 $<= k |] ==> i$*k $<= j$*k"
apply (subgoal_tac "i $* intify (k) $<= j $* intify (k) ")
apply (simp (no_asm_use))
apply (rule_tac b = "intify (k)" in not_zneg_mag [THEN subst])
apply (rule_tac [3] zmult_mono_lemma)
apply auto
apply (simp add: znegative_iff_zless_0 not_zless_iff_zle [THEN iff_sym])
done

lemma zmult_zle_mono1_neg: "[| i $<= j;  k $<= #0 |] ==> j$*k $<= i$*k"
apply (rule zminus_zle_zminus [THEN iffD1])
apply (simp del: zmult_zminus_right
            add: zmult_zminus_right [symmetric] zmult_zle_mono1 zle_zminus)
done

lemma zmult_zle_mono2: "[| i $<= j;  #0 $<= k |] ==> k$*i $<= k$*j"
apply (drule zmult_zle_mono1)
apply (simp_all add: zmult_commute)
done

lemma zmult_zle_mono2_neg: "[| i $<= j;  k $<= #0 |] ==> k$*j $<= k$*i"
apply (drule zmult_zle_mono1_neg)
apply (simp_all add: zmult_commute)
done

(* $<= monotonicity, BOTH arguments*)
lemma zmult_zle_mono:
     "[| i $<= j;  k $<= l;  #0 $<= j;  #0 $<= k |] ==> i$*k $<= j$*l"
apply (erule zmult_zle_mono1 [THEN zle_trans])
apply assumption
apply (erule zmult_zle_mono2)
apply assumption
done


(** strict, in 1st argument; proof is by induction on k>0 **)

lemma zmult_zless_mono2_lemma [rule_format]:
     "[| i$<j; k \<in> nat |] ==> 0<k \<longrightarrow> $#k $* i $< $#k $* j"
apply (induct_tac "k")
 prefer 2
 apply (subst int_succ_int_1)
 apply (erule natE)
apply (simp_all add: zadd_zmult_distrib zadd_zless_mono zle_def)
apply (frule nat_0_le)
apply (subgoal_tac "i $+ (i $+ $# xa $* i) $< j $+ (j $+ $# xa $* j) ")
apply (simp (no_asm_use))
apply (rule zadd_zless_mono)
apply (simp_all (no_asm_simp) add: zle_def)
done

lemma zmult_zless_mono2: "[| i$<j;  #0 $< k |] ==> k$*i $< k$*j"
apply (subgoal_tac "intify (k) $* i $< intify (k) $* j")
apply (simp (no_asm_use))
apply (rule_tac b = "intify (k)" in not_zneg_mag [THEN subst])
apply (rule_tac [3] zmult_zless_mono2_lemma)
apply auto
apply (simp add: znegative_iff_zless_0)
apply (drule zless_trans, assumption)
apply (auto simp add: zero_lt_zmagnitude)
done

lemma zmult_zless_mono1: "[| i$<j;  #0 $< k |] ==> i$*k $< j$*k"
apply (drule zmult_zless_mono2)
apply (simp_all add: zmult_commute)
done

(* < monotonicity, BOTH arguments*)
lemma zmult_zless_mono:
     "[| i $< j;  k $< l;  #0 $< j;  #0 $< k |] ==> i$*k $< j$*l"
apply (erule zmult_zless_mono1 [THEN zless_trans])
apply assumption
apply (erule zmult_zless_mono2)
apply assumption
done

lemma zmult_zless_mono1_neg: "[| i $< j;  k $< #0 |] ==> j$*k $< i$*k"
apply (rule zminus_zless_zminus [THEN iffD1])
apply (simp del: zmult_zminus_right
            add: zmult_zminus_right [symmetric] zmult_zless_mono1 zless_zminus)
done

lemma zmult_zless_mono2_neg: "[| i $< j;  k $< #0 |] ==> k$*j $< k$*i"
apply (rule zminus_zless_zminus [THEN iffD1])
apply (simp del: zmult_zminus
            add: zmult_zminus [symmetric] zmult_zless_mono2 zless_zminus)
done


(** Products of zeroes **)

lemma zmult_eq_lemma:
     "[| m \<in> int; n \<in> int |] ==> (m = #0 | n = #0) <-> (m$*n = #0)"
apply (case_tac "m $< #0")
apply (auto simp add: not_zless_iff_zle zle_def neq_iff_zless)
apply (force dest: zmult_zless_mono1_neg zmult_zless_mono1)+
done

lemma zmult_eq_0_iff [iff]: "(m$*n = #0) <-> (intify(m) = #0 | intify(n) = #0)"
apply (simp add: zmult_eq_lemma)
done


(** Cancellation laws for k*m < k*n and m*k < n*k, also for @{text"\<le>"} and =,
    but not (yet?) for k*m < n*k. **)

lemma zmult_zless_lemma:
     "[| k \<in> int; m \<in> int; n \<in> int |]
      ==> (m$*k $< n$*k) <-> ((#0 $< k & m$<n) | (k $< #0 & n$<m))"
apply (case_tac "k = #0")
apply (auto simp add: neq_iff_zless zmult_zless_mono1 zmult_zless_mono1_neg)
apply (auto simp add: not_zless_iff_zle
                      not_zle_iff_zless [THEN iff_sym, of "m$*k"]
                      not_zle_iff_zless [THEN iff_sym, of m])
apply (auto elim: notE
            simp add: zless_imp_zle zmult_zle_mono1 zmult_zle_mono1_neg)
done

lemma zmult_zless_cancel2:
     "(m$*k $< n$*k) <-> ((#0 $< k & m$<n) | (k $< #0 & n$<m))"
apply (cut_tac k = "intify (k)" and m = "intify (m)" and n = "intify (n)"
       in zmult_zless_lemma)
apply auto
done

lemma zmult_zless_cancel1:
     "(k$*m $< k$*n) <-> ((#0 $< k & m$<n) | (k $< #0 & n$<m))"
by (simp add: zmult_commute [of k] zmult_zless_cancel2)

lemma zmult_zle_cancel2:
     "(m$*k $<= n$*k) <-> ((#0 $< k \<longrightarrow> m$<=n) & (k $< #0 \<longrightarrow> n$<=m))"
by (auto simp add: not_zless_iff_zle [THEN iff_sym] zmult_zless_cancel2)

lemma zmult_zle_cancel1:
     "(k$*m $<= k$*n) <-> ((#0 $< k \<longrightarrow> m$<=n) & (k $< #0 \<longrightarrow> n$<=m))"
by (auto simp add: not_zless_iff_zle [THEN iff_sym] zmult_zless_cancel1)

lemma int_eq_iff_zle: "[| m \<in> int; n \<in> int |] ==> m=n <-> (m $<= n & n $<= m)"
apply (blast intro: zle_refl zle_anti_sym)
done

lemma zmult_cancel2_lemma:
     "[| k \<in> int; m \<in> int; n \<in> int |] ==> (m$*k = n$*k) <-> (k=#0 | m=n)"
apply (simp add: int_eq_iff_zle [of "m$*k"] int_eq_iff_zle [of m])
apply (auto simp add: zmult_zle_cancel2 neq_iff_zless)
done

lemma zmult_cancel2 [simp]:
     "(m$*k = n$*k) <-> (intify(k) = #0 | intify(m) = intify(n))"
apply (rule iff_trans)
apply (rule_tac [2] zmult_cancel2_lemma)
apply auto
done

lemma zmult_cancel1 [simp]:
     "(k$*m = k$*n) <-> (intify(k) = #0 | intify(m) = intify(n))"
by (simp add: zmult_commute [of k] zmult_cancel2)


subsection{* Uniqueness and monotonicity of quotients and remainders *}

lemma unique_quotient_lemma:
     "[| b$*q' $+ r' $<= b$*q $+ r;  #0 $<= r';  #0 $< b;  r $< b |]
      ==> q' $<= q"
apply (subgoal_tac "r' $+ b $* (q'$-q) $<= r")
 prefer 2 apply (simp add: zdiff_zmult_distrib2 zadd_ac zcompare_rls)
apply (subgoal_tac "#0 $< b $* (#1 $+ q $- q') ")
 prefer 2
 apply (erule zle_zless_trans)
 apply (simp add: zdiff_zmult_distrib2 zadd_zmult_distrib2 zadd_ac zcompare_rls)
 apply (erule zle_zless_trans)
 apply (simp add: );
apply (subgoal_tac "b $* q' $< b $* (#1 $+ q)")
 prefer 2
 apply (simp add: zdiff_zmult_distrib2 zadd_zmult_distrib2 zadd_ac zcompare_rls)
apply (auto elim: zless_asym
        simp add: zmult_zless_cancel1 zless_add1_iff_zle zadd_ac zcompare_rls)
done

lemma unique_quotient_lemma_neg:
     "[| b$*q' $+ r' $<= b$*q $+ r;  r $<= #0;  b $< #0;  b $< r' |]
      ==> q $<= q'"
apply (rule_tac b = "$-b" and r = "$-r'" and r' = "$-r"
       in unique_quotient_lemma)
apply (auto simp del: zminus_zadd_distrib
            simp add: zminus_zadd_distrib [symmetric] zle_zminus zless_zminus)
done


lemma unique_quotient:
     "[| quorem (<a,b>, <q,r>);  quorem (<a,b>, <q',r'>);  b \<in> int; b \<noteq> #0;
         q \<in> int; q' \<in> int |] ==> q = q'"
apply (simp add: split_ifs quorem_def neq_iff_zless)
apply safe
apply simp_all
apply (blast intro: zle_anti_sym
             dest: zle_eq_refl [THEN unique_quotient_lemma]
                   zle_eq_refl [THEN unique_quotient_lemma_neg] sym)+
done

lemma unique_remainder:
     "[| quorem (<a,b>, <q,r>);  quorem (<a,b>, <q',r'>);  b \<in> int; b \<noteq> #0;
         q \<in> int; q' \<in> int;
         r \<in> int; r' \<in> int |] ==> r = r'"
apply (subgoal_tac "q = q'")
 prefer 2 apply (blast intro: unique_quotient)
apply (simp add: quorem_def)
done


subsection{*Correctness of posDivAlg,
           the Division Algorithm for @{text "a\<ge>0"} and @{text "b>0"} *}

lemma adjust_eq [simp]:
     "adjust(b, <q,r>) = (let diff = r$-b in
                          if #0 $<= diff then <#2$*q $+ #1,diff>
                                         else <#2$*q,r>)"
by (simp add: Let_def adjust_def)


lemma posDivAlg_termination:
     "[| #0 $< b; ~ a $< b |]
      ==> nat_of(a $- #2 $\<times> b $+ #1) < nat_of(a $- b $+ #1)"
apply (simp (no_asm) add: zless_nat_conj)
apply (simp add: not_zless_iff_zle zless_add1_iff_zle zcompare_rls)
done

lemmas posDivAlg_unfold = def_wfrec [OF posDivAlg_def wf_measure]

lemma posDivAlg_eqn:
     "[| #0 $< b; a \<in> int; b \<in> int |] ==>
      posDivAlg(<a,b>) =
       (if a$<b then <#0,a> else adjust(b, posDivAlg (<a, #2$*b>)))"
apply (rule posDivAlg_unfold [THEN trans])
apply (simp add: vimage_iff not_zless_iff_zle [THEN iff_sym])
apply (blast intro: posDivAlg_termination)
done

lemma posDivAlg_induct_lemma [rule_format]:
  assumes prem:
        "!!a b. [| a \<in> int; b \<in> int;
                   ~ (a $< b | b $<= #0) \<longrightarrow> P(<a, #2 $* b>) |] ==> P(<a,b>)"
  shows "<u,v> \<in> int*int \<longrightarrow> P(<u,v>)"
apply (rule_tac a = "<u,v>" in wf_induct)
apply (rule_tac A = "int*int" and f = "%<a,b>.nat_of (a $- b $+ #1)"
       in wf_measure)
apply clarify
apply (rule prem)
apply (drule_tac [3] x = "<xa, #2 $\<times> y>" in spec)
apply auto
apply (simp add: not_zle_iff_zless posDivAlg_termination)
done


lemma posDivAlg_induct [consumes 2]:
  assumes u_int: "u \<in> int"
      and v_int: "v \<in> int"
      and ih: "!!a b. [| a \<in> int; b \<in> int;
                     ~ (a $< b | b $<= #0) \<longrightarrow> P(a, #2 $* b) |] ==> P(a,b)"
  shows "P(u,v)"
apply (subgoal_tac "(%<x,y>. P (x,y)) (<u,v>)")
apply simp
apply (rule posDivAlg_induct_lemma)
apply (simp (no_asm_use))
apply (rule ih)
apply (auto simp add: u_int v_int)
done

(*FIXME: use intify in integ_of so that we always have @{term"integ_of w \<in> int"}.
    then this rewrite can work for all constants!!*)
lemma intify_eq_0_iff_zle: "intify(m) = #0 <-> (m $<= #0 & #0 $<= m)"
apply (simp (no_asm) add: int_eq_iff_zle)
done


subsection{* Some convenient biconditionals for products of signs *}

lemma zmult_pos: "[| #0 $< i; #0 $< j |] ==> #0 $< i $* j"
apply (drule zmult_zless_mono1)
apply auto
done

lemma zmult_neg: "[| i $< #0; j $< #0 |] ==> #0 $< i $* j"
apply (drule zmult_zless_mono1_neg)
apply auto
done

lemma zmult_pos_neg: "[| #0 $< i; j $< #0 |] ==> i $* j $< #0"
apply (drule zmult_zless_mono1_neg)
apply auto
done

(** Inequality reasoning **)

lemma int_0_less_lemma:
     "[| x \<in> int; y \<in> int |]
      ==> (#0 $< x $* y) <-> (#0 $< x & #0 $< y | x $< #0 & y $< #0)"
apply (auto simp add: zle_def not_zless_iff_zle zmult_pos zmult_neg)
apply (rule ccontr)
apply (rule_tac [2] ccontr)
apply (auto simp add: zle_def not_zless_iff_zle)
apply (erule_tac P = "#0$< x$* y" in rev_mp)
apply (erule_tac [2] P = "#0$< x$* y" in rev_mp)
apply (drule zmult_pos_neg, assumption)
 prefer 2
 apply (drule zmult_pos_neg, assumption)
apply (auto dest: zless_not_sym simp add: zmult_commute)
done

lemma int_0_less_mult_iff:
     "(#0 $< x $* y) <-> (#0 $< x & #0 $< y | x $< #0 & y $< #0)"
apply (cut_tac x = "intify (x)" and y = "intify (y)" in int_0_less_lemma)
apply auto
done

lemma int_0_le_lemma:
     "[| x \<in> int; y \<in> int |]
      ==> (#0 $<= x $* y) <-> (#0 $<= x & #0 $<= y | x $<= #0 & y $<= #0)"
by (auto simp add: zle_def not_zless_iff_zle int_0_less_mult_iff)

lemma int_0_le_mult_iff:
     "(#0 $<= x $* y) <-> ((#0 $<= x & #0 $<= y) | (x $<= #0 & y $<= #0))"
apply (cut_tac x = "intify (x)" and y = "intify (y)" in int_0_le_lemma)
apply auto
done

lemma zmult_less_0_iff:
     "(x $* y $< #0) <-> (#0 $< x & y $< #0 | x $< #0 & #0 $< y)"
apply (auto simp add: int_0_le_mult_iff not_zle_iff_zless [THEN iff_sym])
apply (auto dest: zless_not_sym simp add: not_zle_iff_zless)
done

lemma zmult_le_0_iff:
     "(x $* y $<= #0) <-> (#0 $<= x & y $<= #0 | x $<= #0 & #0 $<= y)"
by (auto dest: zless_not_sym
         simp add: int_0_less_mult_iff not_zless_iff_zle [THEN iff_sym])


(*Typechecking for posDivAlg*)
lemma posDivAlg_type [rule_format]:
     "[| a \<in> int; b \<in> int |] ==> posDivAlg(<a,b>) \<in> int * int"
apply (rule_tac u = "a" and v = "b" in posDivAlg_induct)
apply assumption+
apply (case_tac "#0 $< ba")
 apply (simp add: posDivAlg_eqn adjust_def integ_of_type
             split add: split_if_asm)
 apply clarify
 apply (simp add: int_0_less_mult_iff not_zle_iff_zless)
apply (simp add: not_zless_iff_zle)
apply (subst posDivAlg_unfold)
apply simp
done

(*Correctness of posDivAlg: it computes quotients correctly*)
lemma posDivAlg_correct [rule_format]:
     "[| a \<in> int; b \<in> int |]
      ==> #0 $<= a \<longrightarrow> #0 $< b \<longrightarrow> quorem (<a,b>, posDivAlg(<a,b>))"
apply (rule_tac u = "a" and v = "b" in posDivAlg_induct)
apply auto
   apply (simp_all add: quorem_def)
   txt{*base case: a<b*}
   apply (simp add: posDivAlg_eqn)
  apply (simp add: not_zless_iff_zle [THEN iff_sym])
 apply (simp add: int_0_less_mult_iff)
txt{*main argument*}
apply (subst posDivAlg_eqn)
apply (simp_all (no_asm_simp))
apply (erule splitE)
apply (rule posDivAlg_type)
apply (simp_all add: int_0_less_mult_iff)
apply (auto simp add: zadd_zmult_distrib2 Let_def)
txt{*now just linear arithmetic*}
apply (simp add: not_zle_iff_zless zdiff_zless_iff)
done


subsection{*Correctness of negDivAlg, the division algorithm for a<0 and b>0*}

lemma negDivAlg_termination:
     "[| #0 $< b; a $+ b $< #0 |]
      ==> nat_of($- a $- #2 $* b) < nat_of($- a $- b)"
apply (simp (no_asm) add: zless_nat_conj)
apply (simp add: zcompare_rls not_zle_iff_zless zless_zdiff_iff [THEN iff_sym]
                 zless_zminus)
done

lemmas negDivAlg_unfold = def_wfrec [OF negDivAlg_def wf_measure]

lemma negDivAlg_eqn:
     "[| #0 $< b; a \<in> int; b \<in> int |] ==>
      negDivAlg(<a,b>) =
       (if #0 $<= a$+b then <#-1,a$+b>
                       else adjust(b, negDivAlg (<a, #2$*b>)))"
apply (rule negDivAlg_unfold [THEN trans])
apply (simp (no_asm_simp) add: vimage_iff not_zless_iff_zle [THEN iff_sym])
apply (blast intro: negDivAlg_termination)
done

lemma negDivAlg_induct_lemma [rule_format]:
  assumes prem:
        "!!a b. [| a \<in> int; b \<in> int;
                   ~ (#0 $<= a $+ b | b $<= #0) \<longrightarrow> P(<a, #2 $* b>) |]
                ==> P(<a,b>)"
  shows "<u,v> \<in> int*int \<longrightarrow> P(<u,v>)"
apply (rule_tac a = "<u,v>" in wf_induct)
apply (rule_tac A = "int*int" and f = "%<a,b>.nat_of ($- a $- b)"
       in wf_measure)
apply clarify
apply (rule prem)
apply (drule_tac [3] x = "<xa, #2 $\<times> y>" in spec)
apply auto
apply (simp add: not_zle_iff_zless negDivAlg_termination)
done

lemma negDivAlg_induct [consumes 2]:
  assumes u_int: "u \<in> int"
      and v_int: "v \<in> int"
      and ih: "!!a b. [| a \<in> int; b \<in> int;
                         ~ (#0 $<= a $+ b | b $<= #0) \<longrightarrow> P(a, #2 $* b) |]
                      ==> P(a,b)"
  shows "P(u,v)"
apply (subgoal_tac " (%<x,y>. P (x,y)) (<u,v>)")
apply simp
apply (rule negDivAlg_induct_lemma)
apply (simp (no_asm_use))
apply (rule ih)
apply (auto simp add: u_int v_int)
done


(*Typechecking for negDivAlg*)
lemma negDivAlg_type:
     "[| a \<in> int; b \<in> int |] ==> negDivAlg(<a,b>) \<in> int * int"
apply (rule_tac u = "a" and v = "b" in negDivAlg_induct)
apply assumption+
apply (case_tac "#0 $< ba")
 apply (simp add: negDivAlg_eqn adjust_def integ_of_type
             split add: split_if_asm)
 apply clarify
 apply (simp add: int_0_less_mult_iff not_zle_iff_zless)
apply (simp add: not_zless_iff_zle)
apply (subst negDivAlg_unfold)
apply simp
done


(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b=0 rather than -1*)
lemma negDivAlg_correct [rule_format]:
     "[| a \<in> int; b \<in> int |]
      ==> a $< #0 \<longrightarrow> #0 $< b \<longrightarrow> quorem (<a,b>, negDivAlg(<a,b>))"
apply (rule_tac u = "a" and v = "b" in negDivAlg_induct)
  apply auto
   apply (simp_all add: quorem_def)
   txt{*base case: @{term "0$<=a$+b"}*}
   apply (simp add: negDivAlg_eqn)
  apply (simp add: not_zless_iff_zle [THEN iff_sym])
 apply (simp add: int_0_less_mult_iff)
txt{*main argument*}
apply (subst negDivAlg_eqn)
apply (simp_all (no_asm_simp))
apply (erule splitE)
apply (rule negDivAlg_type)
apply (simp_all add: int_0_less_mult_iff)
apply (auto simp add: zadd_zmult_distrib2 Let_def)
txt{*now just linear arithmetic*}
apply (simp add: not_zle_iff_zless zdiff_zless_iff)
done


subsection{* Existence shown by proving the division algorithm to be correct *}

(*the case a=0*)
lemma quorem_0: "[|b \<noteq> #0;  b \<in> int|] ==> quorem (<#0,b>, <#0,#0>)"
by (force simp add: quorem_def neq_iff_zless)

lemma posDivAlg_zero_divisor: "posDivAlg(<a,#0>) = <#0,a>"
apply (subst posDivAlg_unfold)
apply simp
done

lemma posDivAlg_0 [simp]: "posDivAlg (<#0,b>) = <#0,#0>"
apply (subst posDivAlg_unfold)
apply (simp add: not_zle_iff_zless)
done


(*Needed below.  Actually it's an equivalence.*)
lemma linear_arith_lemma: "~ (#0 $<= #-1 $+ b) ==> (b $<= #0)"
apply (simp add: not_zle_iff_zless)
apply (drule zminus_zless_zminus [THEN iffD2])
apply (simp add: zadd_commute zless_add1_iff_zle zle_zminus)
done

lemma negDivAlg_minus1 [simp]: "negDivAlg (<#-1,b>) = <#-1, b$-#1>"
apply (subst negDivAlg_unfold)
apply (simp add: linear_arith_lemma integ_of_type vimage_iff)
done

lemma negateSnd_eq [simp]: "negateSnd (<q,r>) = <q, $-r>"
apply (unfold negateSnd_def)
apply auto
done

lemma negateSnd_type: "qr \<in> int * int ==> negateSnd (qr) \<in> int * int"
apply (unfold negateSnd_def)
apply auto
done

lemma quorem_neg:
     "[|quorem (<$-a,$-b>, qr);  a \<in> int;  b \<in> int;  qr \<in> int * int|]
      ==> quorem (<a,b>, negateSnd(qr))"
apply clarify
apply (auto elim: zless_asym simp add: quorem_def zless_zminus)
txt{*linear arithmetic from here on*}
apply (simp_all add: zminus_equation [of a] zminus_zless)
apply (cut_tac [2] z = "b" and w = "#0" in zless_linear)
apply (cut_tac [1] z = "b" and w = "#0" in zless_linear)
apply auto
apply (blast dest: zle_zless_trans)+
done

lemma divAlg_correct:
     "[|b \<noteq> #0;  a \<in> int;  b \<in> int|] ==> quorem (<a,b>, divAlg(<a,b>))"
apply (auto simp add: quorem_0 divAlg_def)
apply (safe intro!: quorem_neg posDivAlg_correct negDivAlg_correct
                    posDivAlg_type negDivAlg_type)
apply (auto simp add: quorem_def neq_iff_zless)
txt{*linear arithmetic from here on*}
apply (auto simp add: zle_def)
done

lemma divAlg_type: "[|a \<in> int;  b \<in> int|] ==> divAlg(<a,b>) \<in> int * int"
apply (auto simp add: divAlg_def)
apply (auto simp add: posDivAlg_type negDivAlg_type negateSnd_type)
done


(** intify cancellation **)

lemma zdiv_intify1 [simp]: "intify(x) zdiv y = x zdiv y"
apply (simp (no_asm) add: zdiv_def)
done

lemma zdiv_intify2 [simp]: "x zdiv intify(y) = x zdiv y"
apply (simp (no_asm) add: zdiv_def)
done

lemma zdiv_type [iff,TC]: "z zdiv w \<in> int"
apply (unfold zdiv_def)
apply (blast intro: fst_type divAlg_type)
done

lemma zmod_intify1 [simp]: "intify(x) zmod y = x zmod y"
apply (simp (no_asm) add: zmod_def)
done

lemma zmod_intify2 [simp]: "x zmod intify(y) = x zmod y"
apply (simp (no_asm) add: zmod_def)
done

lemma zmod_type [iff,TC]: "z zmod w \<in> int"
apply (unfold zmod_def)
apply (rule snd_type)
apply (blast intro: divAlg_type)
done


(** Arbitrary definitions for division by zero.  Useful to simplify
    certain equations **)

lemma DIVISION_BY_ZERO_ZDIV: "a zdiv #0 = #0"
apply (simp (no_asm) add: zdiv_def divAlg_def posDivAlg_zero_divisor)
done  (*NOT for adding to default simpset*)

lemma DIVISION_BY_ZERO_ZMOD: "a zmod #0 = intify(a)"
apply (simp (no_asm) add: zmod_def divAlg_def posDivAlg_zero_divisor)
done  (*NOT for adding to default simpset*)



(** Basic laws about division and remainder **)

lemma raw_zmod_zdiv_equality:
     "[| a \<in> int; b \<in> int |] ==> a = b $* (a zdiv b) $+ (a zmod b)"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (cut_tac a = "a" and b = "b" in divAlg_correct)
apply (auto simp add: quorem_def zdiv_def zmod_def split_def)
done

lemma zmod_zdiv_equality: "intify(a) = b $* (a zdiv b) $+ (a zmod b)"
apply (rule trans)
apply (rule_tac b = "intify (b)" in raw_zmod_zdiv_equality)
apply auto
done

lemma pos_mod: "#0 $< b ==> #0 $<= a zmod b & a zmod b $< b"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in divAlg_correct)
apply (auto simp add: intify_eq_0_iff_zle quorem_def zmod_def split_def)
apply (blast dest: zle_zless_trans)+
done

lemmas pos_mod_sign = pos_mod [THEN conjunct1]
  and pos_mod_bound = pos_mod [THEN conjunct2]

lemma neg_mod: "b $< #0 ==> a zmod b $<= #0 & b $< a zmod b"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in divAlg_correct)
apply (auto simp add: intify_eq_0_iff_zle quorem_def zmod_def split_def)
apply (blast dest: zle_zless_trans)
apply (blast dest: zless_trans)+
done

lemmas neg_mod_sign = neg_mod [THEN conjunct1]
  and neg_mod_bound = neg_mod [THEN conjunct2]


(** proving general properties of zdiv and zmod **)

lemma quorem_div_mod:
     "[|b \<noteq> #0;  a \<in> int;  b \<in> int |]
      ==> quorem (<a,b>, <a zdiv b, a zmod b>)"
apply (cut_tac a = "a" and b = "b" in zmod_zdiv_equality)
apply (auto simp add: quorem_def neq_iff_zless pos_mod_sign pos_mod_bound
                      neg_mod_sign neg_mod_bound)
done

(*Surely quorem(<a,b>,<q,r>) implies @{term"a \<in> int"}, but it doesn't matter*)
lemma quorem_div:
     "[| quorem(<a,b>,<q,r>);  b \<noteq> #0;  a \<in> int;  b \<in> int;  q \<in> int |]
      ==> a zdiv b = q"
by (blast intro: quorem_div_mod [THEN unique_quotient])

lemma quorem_mod:
     "[| quorem(<a,b>,<q,r>); b \<noteq> #0; a \<in> int; b \<in> int; q \<in> int; r \<in> int |]
      ==> a zmod b = r"
by (blast intro: quorem_div_mod [THEN unique_remainder])

lemma zdiv_pos_pos_trivial_raw:
     "[| a \<in> int;  b \<in> int;  #0 $<= a;  a $< b |] ==> a zdiv b = #0"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
(*linear arithmetic*)
apply (blast dest: zle_zless_trans)+
done

lemma zdiv_pos_pos_trivial: "[| #0 $<= a;  a $< b |] ==> a zdiv b = #0"
apply (cut_tac a = "intify (a)" and b = "intify (b)"
       in zdiv_pos_pos_trivial_raw)
apply auto
done

lemma zdiv_neg_neg_trivial_raw:
     "[| a \<in> int;  b \<in> int;  a $<= #0;  b $< a |] ==> a zdiv b = #0"
apply (rule_tac r = "a" in quorem_div)
apply (auto simp add: quorem_def)
(*linear arithmetic*)
apply (blast dest: zle_zless_trans zless_trans)+
done

lemma zdiv_neg_neg_trivial: "[| a $<= #0;  b $< a |] ==> a zdiv b = #0"
apply (cut_tac a = "intify (a)" and b = "intify (b)"
       in zdiv_neg_neg_trivial_raw)
apply auto
done

lemma zadd_le_0_lemma: "[| a$+b $<= #0;  #0 $< a;  #0 $< b |] ==> False"
apply (drule_tac z' = "#0" and z = "b" in zadd_zless_mono)
apply (auto simp add: zle_def)
apply (blast dest: zless_trans)
done

lemma zdiv_pos_neg_trivial_raw:
     "[| a \<in> int;  b \<in> int;  #0 $< a;  a$+b $<= #0 |] ==> a zdiv b = #-1"
apply (rule_tac r = "a $+ b" in quorem_div)
apply (auto simp add: quorem_def)
(*linear arithmetic*)
apply (blast dest: zadd_le_0_lemma zle_zless_trans)+
done

lemma zdiv_pos_neg_trivial: "[| #0 $< a;  a$+b $<= #0 |] ==> a zdiv b = #-1"
apply (cut_tac a = "intify (a)" and b = "intify (b)"
       in zdiv_pos_neg_trivial_raw)
apply auto
done

(*There is no zdiv_neg_pos_trivial because  #0 zdiv b = #0 would supersede it*)


lemma zmod_pos_pos_trivial_raw:
     "[| a \<in> int;  b \<in> int;  #0 $<= a;  a $< b |] ==> a zmod b = a"
apply (rule_tac q = "#0" in quorem_mod)
apply (auto simp add: quorem_def)
(*linear arithmetic*)
apply (blast dest: zle_zless_trans)+
done

lemma zmod_pos_pos_trivial: "[| #0 $<= a;  a $< b |] ==> a zmod b = intify(a)"
apply (cut_tac a = "intify (a)" and b = "intify (b)"
       in zmod_pos_pos_trivial_raw)
apply auto
done

lemma zmod_neg_neg_trivial_raw:
     "[| a \<in> int;  b \<in> int;  a $<= #0;  b $< a |] ==> a zmod b = a"
apply (rule_tac q = "#0" in quorem_mod)
apply (auto simp add: quorem_def)
(*linear arithmetic*)
apply (blast dest: zle_zless_trans zless_trans)+
done

lemma zmod_neg_neg_trivial: "[| a $<= #0;  b $< a |] ==> a zmod b = intify(a)"
apply (cut_tac a = "intify (a)" and b = "intify (b)"
       in zmod_neg_neg_trivial_raw)
apply auto
done

lemma zmod_pos_neg_trivial_raw:
     "[| a \<in> int;  b \<in> int;  #0 $< a;  a$+b $<= #0 |] ==> a zmod b = a$+b"
apply (rule_tac q = "#-1" in quorem_mod)
apply (auto simp add: quorem_def)
(*linear arithmetic*)
apply (blast dest: zadd_le_0_lemma zle_zless_trans)+
done

lemma zmod_pos_neg_trivial: "[| #0 $< a;  a$+b $<= #0 |] ==> a zmod b = a$+b"
apply (cut_tac a = "intify (a)" and b = "intify (b)"
       in zmod_pos_neg_trivial_raw)
apply auto
done

(*There is no zmod_neg_pos_trivial...*)


(*Simpler laws such as -a zdiv b = -(a zdiv b) FAIL*)

lemma zdiv_zminus_zminus_raw:
     "[|a \<in> int;  b \<in> int|] ==> ($-a) zdiv ($-b) = a zdiv b"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (subst quorem_div_mod [THEN quorem_neg, simplified, THEN quorem_div])
apply auto
done

lemma zdiv_zminus_zminus [simp]: "($-a) zdiv ($-b) = a zdiv b"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in zdiv_zminus_zminus_raw)
apply auto
done

(*Simpler laws such as -a zmod b = -(a zmod b) FAIL*)
lemma zmod_zminus_zminus_raw:
     "[|a \<in> int;  b \<in> int|] ==> ($-a) zmod ($-b) = $- (a zmod b)"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (subst quorem_div_mod [THEN quorem_neg, simplified, THEN quorem_mod])
apply auto
done

lemma zmod_zminus_zminus [simp]: "($-a) zmod ($-b) = $- (a zmod b)"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in zmod_zminus_zminus_raw)
apply auto
done


subsection{* division of a number by itself *}

lemma self_quotient_aux1: "[| #0 $< a; a = r $+ a$*q; r $< a |] ==> #1 $<= q"
apply (subgoal_tac "#0 $< a$*q")
apply (cut_tac w = "#0" and z = "q" in add1_zle_iff)
apply (simp add: int_0_less_mult_iff)
apply (blast dest: zless_trans)
(*linear arithmetic...*)
apply (drule_tac t = "%x. x $- r" in subst_context)
apply (drule sym)
apply (simp add: zcompare_rls)
done

lemma self_quotient_aux2: "[| #0 $< a; a = r $+ a$*q; #0 $<= r |] ==> q $<= #1"
apply (subgoal_tac "#0 $<= a$* (#1$-q)")
 apply (simp add: int_0_le_mult_iff zcompare_rls)
 apply (blast dest: zle_zless_trans)
apply (simp add: zdiff_zmult_distrib2)
apply (drule_tac t = "%x. x $- a $* q" in subst_context)
apply (simp add: zcompare_rls)
done

lemma self_quotient:
     "[| quorem(<a,a>,<q,r>);  a \<in> int;  q \<in> int;  a \<noteq> #0|] ==> q = #1"
apply (simp add: split_ifs quorem_def neq_iff_zless)
apply (rule zle_anti_sym)
apply safe
apply auto
prefer 4 apply (blast dest: zless_trans)
apply (blast dest: zless_trans)
apply (rule_tac [3] a = "$-a" and r = "$-r" in self_quotient_aux1)
apply (rule_tac a = "$-a" and r = "$-r" in self_quotient_aux2)
apply (rule_tac [6] zminus_equation [THEN iffD1])
apply (rule_tac [2] zminus_equation [THEN iffD1])
apply (force intro: self_quotient_aux1 self_quotient_aux2
  simp add: zadd_commute zmult_zminus)+
done

lemma self_remainder:
     "[|quorem(<a,a>,<q,r>); a \<in> int; q \<in> int; r \<in> int; a \<noteq> #0|] ==> r = #0"
apply (frule self_quotient)
apply (auto simp add: quorem_def)
done

lemma zdiv_self_raw: "[|a \<noteq> #0; a \<in> int|] ==> a zdiv a = #1"
apply (blast intro: quorem_div_mod [THEN self_quotient])
done

lemma zdiv_self [simp]: "intify(a) \<noteq> #0 ==> a zdiv a = #1"
apply (drule zdiv_self_raw)
apply auto
done

(*Here we have 0 zmod 0 = 0, also assumed by Knuth (who puts m zmod 0 = 0) *)
lemma zmod_self_raw: "a \<in> int ==> a zmod a = #0"
apply (case_tac "a = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (blast intro: quorem_div_mod [THEN self_remainder])
done

lemma zmod_self [simp]: "a zmod a = #0"
apply (cut_tac a = "intify (a)" in zmod_self_raw)
apply auto
done


subsection{* Computation of division and remainder *}

lemma zdiv_zero [simp]: "#0 zdiv b = #0"
apply (simp (no_asm) add: zdiv_def divAlg_def)
done

lemma zdiv_eq_minus1: "#0 $< b ==> #-1 zdiv b = #-1"
apply (simp (no_asm_simp) add: zdiv_def divAlg_def)
done

lemma zmod_zero [simp]: "#0 zmod b = #0"
apply (simp (no_asm) add: zmod_def divAlg_def)
done

lemma zdiv_minus1: "#0 $< b ==> #-1 zdiv b = #-1"
apply (simp (no_asm_simp) add: zdiv_def divAlg_def)
done

lemma zmod_minus1: "#0 $< b ==> #-1 zmod b = b $- #1"
apply (simp (no_asm_simp) add: zmod_def divAlg_def)
done

(** a positive, b positive **)

lemma zdiv_pos_pos: "[| #0 $< a;  #0 $<= b |]
      ==> a zdiv b = fst (posDivAlg(<intify(a), intify(b)>))"
apply (simp (no_asm_simp) add: zdiv_def divAlg_def)
apply (auto simp add: zle_def)
done

lemma zmod_pos_pos:
     "[| #0 $< a;  #0 $<= b |]
      ==> a zmod b = snd (posDivAlg(<intify(a), intify(b)>))"
apply (simp (no_asm_simp) add: zmod_def divAlg_def)
apply (auto simp add: zle_def)
done

(** a negative, b positive **)

lemma zdiv_neg_pos:
     "[| a $< #0;  #0 $< b |]
      ==> a zdiv b = fst (negDivAlg(<intify(a), intify(b)>))"
apply (simp (no_asm_simp) add: zdiv_def divAlg_def)
apply (blast dest: zle_zless_trans)
done

lemma zmod_neg_pos:
     "[| a $< #0;  #0 $< b |]
      ==> a zmod b = snd (negDivAlg(<intify(a), intify(b)>))"
apply (simp (no_asm_simp) add: zmod_def divAlg_def)
apply (blast dest: zle_zless_trans)
done

(** a positive, b negative **)

lemma zdiv_pos_neg:
     "[| #0 $< a;  b $< #0 |]
      ==> a zdiv b = fst (negateSnd(negDivAlg (<$-a, $-b>)))"
apply (simp (no_asm_simp) add: zdiv_def divAlg_def intify_eq_0_iff_zle)
apply auto
apply (blast dest: zle_zless_trans)+
apply (blast dest: zless_trans)
apply (blast intro: zless_imp_zle)
done

lemma zmod_pos_neg:
     "[| #0 $< a;  b $< #0 |]
      ==> a zmod b = snd (negateSnd(negDivAlg (<$-a, $-b>)))"
apply (simp (no_asm_simp) add: zmod_def divAlg_def intify_eq_0_iff_zle)
apply auto
apply (blast dest: zle_zless_trans)+
apply (blast dest: zless_trans)
apply (blast intro: zless_imp_zle)
done

(** a negative, b negative **)

lemma zdiv_neg_neg:
     "[| a $< #0;  b $<= #0 |]
      ==> a zdiv b = fst (negateSnd(posDivAlg(<$-a, $-b>)))"
apply (simp (no_asm_simp) add: zdiv_def divAlg_def)
apply auto
apply (blast dest!: zle_zless_trans)+
done

lemma zmod_neg_neg:
     "[| a $< #0;  b $<= #0 |]
      ==> a zmod b = snd (negateSnd(posDivAlg(<$-a, $-b>)))"
apply (simp (no_asm_simp) add: zmod_def divAlg_def)
apply auto
apply (blast dest!: zle_zless_trans)+
done

declare zdiv_pos_pos [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zdiv_neg_pos [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zdiv_pos_neg [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zdiv_neg_neg [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zmod_pos_pos [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zmod_neg_pos [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zmod_pos_neg [of "integ_of (v)" "integ_of (w)", simp] for v w
declare zmod_neg_neg [of "integ_of (v)" "integ_of (w)", simp] for v w
declare posDivAlg_eqn [of concl: "integ_of (v)" "integ_of (w)", simp] for v w
declare negDivAlg_eqn [of concl: "integ_of (v)" "integ_of (w)", simp] for v w


(** Special-case simplification **)

lemma zmod_1 [simp]: "a zmod #1 = #0"
apply (cut_tac a = "a" and b = "#1" in pos_mod_sign)
apply (cut_tac [2] a = "a" and b = "#1" in pos_mod_bound)
apply auto
(*arithmetic*)
apply (drule add1_zle_iff [THEN iffD2])
apply (rule zle_anti_sym)
apply auto
done

lemma zdiv_1 [simp]: "a zdiv #1 = intify(a)"
apply (cut_tac a = "a" and b = "#1" in zmod_zdiv_equality)
apply auto
done

lemma zmod_minus1_right [simp]: "a zmod #-1 = #0"
apply (cut_tac a = "a" and b = "#-1" in neg_mod_sign)
apply (cut_tac [2] a = "a" and b = "#-1" in neg_mod_bound)
apply auto
(*arithmetic*)
apply (drule add1_zle_iff [THEN iffD2])
apply (rule zle_anti_sym)
apply auto
done

lemma zdiv_minus1_right_raw: "a \<in> int ==> a zdiv #-1 = $-a"
apply (cut_tac a = "a" and b = "#-1" in zmod_zdiv_equality)
apply auto
apply (rule equation_zminus [THEN iffD2])
apply auto
done

lemma zdiv_minus1_right: "a zdiv #-1 = $-a"
apply (cut_tac a = "intify (a)" in zdiv_minus1_right_raw)
apply auto
done
declare zdiv_minus1_right [simp]


subsection{* Monotonicity in the first argument (divisor) *}

lemma zdiv_mono1: "[| a $<= a';  #0 $< b |] ==> a zdiv b $<= a' zdiv b"
apply (cut_tac a = "a" and b = "b" in zmod_zdiv_equality)
apply (cut_tac a = "a'" and b = "b" in zmod_zdiv_equality)
apply (rule unique_quotient_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all (no_asm_simp) add: pos_mod_sign pos_mod_bound)
done

lemma zdiv_mono1_neg: "[| a $<= a';  b $< #0 |] ==> a' zdiv b $<= a zdiv b"
apply (cut_tac a = "a" and b = "b" in zmod_zdiv_equality)
apply (cut_tac a = "a'" and b = "b" in zmod_zdiv_equality)
apply (rule unique_quotient_lemma_neg)
apply (erule subst)
apply (erule subst)
apply (simp_all (no_asm_simp) add: neg_mod_sign neg_mod_bound)
done


subsection{* Monotonicity in the second argument (dividend) *}

lemma q_pos_lemma:
     "[| #0 $<= b'$*q' $+ r'; r' $< b';  #0 $< b' |] ==> #0 $<= q'"
apply (subgoal_tac "#0 $< b'$* (q' $+ #1)")
 apply (simp add: int_0_less_mult_iff)
 apply (blast dest: zless_trans intro: zless_add1_iff_zle [THEN iffD1])
apply (simp add: zadd_zmult_distrib2)
apply (erule zle_zless_trans)
apply (erule zadd_zless_mono2)
done

lemma zdiv_mono2_lemma:
     "[| b$*q $+ r = b'$*q' $+ r';  #0 $<= b'$*q' $+ r';
         r' $< b';  #0 $<= r;  #0 $< b';  b' $<= b |]
      ==> q $<= q'"
apply (frule q_pos_lemma, assumption+)
apply (subgoal_tac "b$*q $< b$* (q' $+ #1)")
 apply (simp add: zmult_zless_cancel1)
 apply (force dest: zless_add1_iff_zle [THEN iffD1] zless_trans zless_zle_trans)
apply (subgoal_tac "b$*q = r' $- r $+ b'$*q'")
 prefer 2 apply (simp add: zcompare_rls)
apply (simp (no_asm_simp) add: zadd_zmult_distrib2)
apply (subst zadd_commute [of "b $\<times> q'"], rule zadd_zless_mono)
 prefer 2 apply (blast intro: zmult_zle_mono1)
apply (subgoal_tac "r' $+ #0 $< b $+ r")
 apply (simp add: zcompare_rls)
apply (rule zadd_zless_mono)
 apply auto
apply (blast dest: zless_zle_trans)
done


lemma zdiv_mono2_raw:
     "[| #0 $<= a;  #0 $< b';  b' $<= b;  a \<in> int |]
      ==> a zdiv b $<= a zdiv b'"
apply (subgoal_tac "#0 $< b")
 prefer 2 apply (blast dest: zless_zle_trans)
apply (cut_tac a = "a" and b = "b" in zmod_zdiv_equality)
apply (cut_tac a = "a" and b = "b'" in zmod_zdiv_equality)
apply (rule zdiv_mono2_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all add: pos_mod_sign pos_mod_bound)
done

lemma zdiv_mono2:
     "[| #0 $<= a;  #0 $< b';  b' $<= b |]
      ==> a zdiv b $<= a zdiv b'"
apply (cut_tac a = "intify (a)" in zdiv_mono2_raw)
apply auto
done

lemma q_neg_lemma:
     "[| b'$*q' $+ r' $< #0;  #0 $<= r';  #0 $< b' |] ==> q' $< #0"
apply (subgoal_tac "b'$*q' $< #0")
 prefer 2 apply (force intro: zle_zless_trans)
apply (simp add: zmult_less_0_iff)
apply (blast dest: zless_trans)
done



lemma zdiv_mono2_neg_lemma:
     "[| b$*q $+ r = b'$*q' $+ r';  b'$*q' $+ r' $< #0;
         r $< b;  #0 $<= r';  #0 $< b';  b' $<= b |]
      ==> q' $<= q"
apply (subgoal_tac "#0 $< b")
 prefer 2 apply (blast dest: zless_zle_trans)
apply (frule q_neg_lemma, assumption+)
apply (subgoal_tac "b$*q' $< b$* (q $+ #1)")
 apply (simp add: zmult_zless_cancel1)
 apply (blast dest: zless_trans zless_add1_iff_zle [THEN iffD1])
apply (simp (no_asm_simp) add: zadd_zmult_distrib2)
apply (subgoal_tac "b$*q' $<= b'$*q'")
 prefer 2
 apply (simp add: zmult_zle_cancel2)
 apply (blast dest: zless_trans)
apply (subgoal_tac "b'$*q' $+ r $< b $+ (b$*q $+ r)")
 prefer 2
 apply (erule ssubst)
 apply simp
 apply (drule_tac w' = "r" and z' = "#0" in zadd_zless_mono)
  apply (assumption)
 apply simp
apply (simp (no_asm_use) add: zadd_commute)
apply (rule zle_zless_trans)
 prefer 2 apply (assumption)
apply (simp (no_asm_simp) add: zmult_zle_cancel2)
apply (blast dest: zless_trans)
done

lemma zdiv_mono2_neg_raw:
     "[| a $< #0;  #0 $< b';  b' $<= b;  a \<in> int |]
      ==> a zdiv b' $<= a zdiv b"
apply (subgoal_tac "#0 $< b")
 prefer 2 apply (blast dest: zless_zle_trans)
apply (cut_tac a = "a" and b = "b" in zmod_zdiv_equality)
apply (cut_tac a = "a" and b = "b'" in zmod_zdiv_equality)
apply (rule zdiv_mono2_neg_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all add: pos_mod_sign pos_mod_bound)
done

lemma zdiv_mono2_neg: "[| a $< #0;  #0 $< b';  b' $<= b |]
      ==> a zdiv b' $<= a zdiv b"
apply (cut_tac a = "intify (a)" in zdiv_mono2_neg_raw)
apply auto
done



subsection{* More algebraic laws for zdiv and zmod *}

(** proving (a*b) zdiv c = a $* (b zdiv c) $+ a * (b zmod c) **)

lemma zmult1_lemma:
     "[| quorem(<b,c>, <q,r>);  c \<in> int;  c \<noteq> #0 |]
      ==> quorem (<a$*b, c>, <a$*q $+ (a$*r) zdiv c, (a$*r) zmod c>)"
apply (auto simp add: split_ifs quorem_def neq_iff_zless zadd_zmult_distrib2
                      pos_mod_sign pos_mod_bound neg_mod_sign neg_mod_bound)
apply (auto intro: raw_zmod_zdiv_equality)
done

lemma zdiv_zmult1_eq_raw:
     "[|b \<in> int;  c \<in> int|]
      ==> (a$*b) zdiv c = a$*(b zdiv c) $+ a$*(b zmod c) zdiv c"
apply (case_tac "c = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (rule quorem_div_mod [THEN zmult1_lemma, THEN quorem_div])
apply auto
done

lemma zdiv_zmult1_eq: "(a$*b) zdiv c = a$*(b zdiv c) $+ a$*(b zmod c) zdiv c"
apply (cut_tac b = "intify (b)" and c = "intify (c)" in zdiv_zmult1_eq_raw)
apply auto
done

lemma zmod_zmult1_eq_raw:
     "[|b \<in> int;  c \<in> int|] ==> (a$*b) zmod c = a$*(b zmod c) zmod c"
apply (case_tac "c = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (rule quorem_div_mod [THEN zmult1_lemma, THEN quorem_mod])
apply auto
done

lemma zmod_zmult1_eq: "(a$*b) zmod c = a$*(b zmod c) zmod c"
apply (cut_tac b = "intify (b)" and c = "intify (c)" in zmod_zmult1_eq_raw)
apply auto
done

lemma zmod_zmult1_eq': "(a$*b) zmod c = ((a zmod c) $* b) zmod c"
apply (rule trans)
apply (rule_tac b = " (b $* a) zmod c" in trans)
apply (rule_tac [2] zmod_zmult1_eq)
apply (simp_all (no_asm) add: zmult_commute)
done

lemma zmod_zmult_distrib: "(a$*b) zmod c = ((a zmod c) $* (b zmod c)) zmod c"
apply (rule zmod_zmult1_eq' [THEN trans])
apply (rule zmod_zmult1_eq)
done

lemma zdiv_zmult_self1 [simp]: "intify(b) \<noteq> #0 ==> (a$*b) zdiv b = intify(a)"
apply (simp (no_asm_simp) add: zdiv_zmult1_eq)
done

lemma zdiv_zmult_self2 [simp]: "intify(b) \<noteq> #0 ==> (b$*a) zdiv b = intify(a)"
apply (subst zmult_commute , erule zdiv_zmult_self1)
done

lemma zmod_zmult_self1 [simp]: "(a$*b) zmod b = #0"
apply (simp (no_asm) add: zmod_zmult1_eq)
done

lemma zmod_zmult_self2 [simp]: "(b$*a) zmod b = #0"
apply (simp (no_asm) add: zmult_commute zmod_zmult1_eq)
done


(** proving (a$+b) zdiv c =
            a zdiv c $+ b zdiv c $+ ((a zmod c $+ b zmod c) zdiv c) **)

lemma zadd1_lemma:
     "[| quorem(<a,c>, <aq,ar>);  quorem(<b,c>, <bq,br>);
         c \<in> int;  c \<noteq> #0 |]
      ==> quorem (<a$+b, c>, <aq $+ bq $+ (ar$+br) zdiv c, (ar$+br) zmod c>)"
apply (auto simp add: split_ifs quorem_def neq_iff_zless zadd_zmult_distrib2
                      pos_mod_sign pos_mod_bound neg_mod_sign neg_mod_bound)
apply (auto intro: raw_zmod_zdiv_equality)
done

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma zdiv_zadd1_eq_raw:
     "[|a \<in> int; b \<in> int; c \<in> int|] ==>
      (a$+b) zdiv c = a zdiv c $+ b zdiv c $+ ((a zmod c $+ b zmod c) zdiv c)"
apply (case_tac "c = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (blast intro: zadd1_lemma [OF quorem_div_mod quorem_div_mod,
                                 THEN quorem_div])
done

lemma zdiv_zadd1_eq:
     "(a$+b) zdiv c = a zdiv c $+ b zdiv c $+ ((a zmod c $+ b zmod c) zdiv c)"
apply (cut_tac a = "intify (a)" and b = "intify (b)" and c = "intify (c)"
       in zdiv_zadd1_eq_raw)
apply auto
done

lemma zmod_zadd1_eq_raw:
     "[|a \<in> int; b \<in> int; c \<in> int|]
      ==> (a$+b) zmod c = (a zmod c $+ b zmod c) zmod c"
apply (case_tac "c = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (blast intro: zadd1_lemma [OF quorem_div_mod quorem_div_mod,
                                 THEN quorem_mod])
done

lemma zmod_zadd1_eq: "(a$+b) zmod c = (a zmod c $+ b zmod c) zmod c"
apply (cut_tac a = "intify (a)" and b = "intify (b)" and c = "intify (c)"
       in zmod_zadd1_eq_raw)
apply auto
done

lemma zmod_div_trivial_raw:
     "[|a \<in> int; b \<in> int|] ==> (a zmod b) zdiv b = #0"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (auto simp add: neq_iff_zless pos_mod_sign pos_mod_bound
         zdiv_pos_pos_trivial neg_mod_sign neg_mod_bound zdiv_neg_neg_trivial)
done

lemma zmod_div_trivial [simp]: "(a zmod b) zdiv b = #0"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in zmod_div_trivial_raw)
apply auto
done

lemma zmod_mod_trivial_raw:
     "[|a \<in> int; b \<in> int|] ==> (a zmod b) zmod b = a zmod b"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (auto simp add: neq_iff_zless pos_mod_sign pos_mod_bound
       zmod_pos_pos_trivial neg_mod_sign neg_mod_bound zmod_neg_neg_trivial)
done

lemma zmod_mod_trivial [simp]: "(a zmod b) zmod b = a zmod b"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in zmod_mod_trivial_raw)
apply auto
done

lemma zmod_zadd_left_eq: "(a$+b) zmod c = ((a zmod c) $+ b) zmod c"
apply (rule trans [symmetric])
apply (rule zmod_zadd1_eq)
apply (simp (no_asm))
apply (rule zmod_zadd1_eq [symmetric])
done

lemma zmod_zadd_right_eq: "(a$+b) zmod c = (a $+ (b zmod c)) zmod c"
apply (rule trans [symmetric])
apply (rule zmod_zadd1_eq)
apply (simp (no_asm))
apply (rule zmod_zadd1_eq [symmetric])
done


lemma zdiv_zadd_self1 [simp]:
     "intify(a) \<noteq> #0 ==> (a$+b) zdiv a = b zdiv a $+ #1"
by (simp (no_asm_simp) add: zdiv_zadd1_eq)

lemma zdiv_zadd_self2 [simp]:
     "intify(a) \<noteq> #0 ==> (b$+a) zdiv a = b zdiv a $+ #1"
by (simp (no_asm_simp) add: zdiv_zadd1_eq)

lemma zmod_zadd_self1 [simp]: "(a$+b) zmod a = b zmod a"
apply (case_tac "a = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (simp (no_asm_simp) add: zmod_zadd1_eq)
done

lemma zmod_zadd_self2 [simp]: "(b$+a) zmod a = b zmod a"
apply (case_tac "a = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (simp (no_asm_simp) add: zmod_zadd1_eq)
done


subsection{* proving  a zdiv (b*c) = (a zdiv b) zdiv c *}

(*The condition c>0 seems necessary.  Consider that 7 zdiv ~6 = ~2 but
  7 zdiv 2 zdiv ~3 = 3 zdiv ~3 = ~1.  The subcase (a zdiv b) zmod c = 0 seems
  to cause particular problems.*)

(** first, four lemmas to bound the remainder for the cases b<0 and b>0 **)

lemma zdiv_zmult2_aux1:
     "[| #0 $< c;  b $< r;  r $<= #0 |] ==> b$*c $< b$*(q zmod c) $+ r"
apply (subgoal_tac "b $* (c $- q zmod c) $< r $* #1")
apply (simp add: zdiff_zmult_distrib2 zadd_commute zcompare_rls)
apply (rule zle_zless_trans)
apply (erule_tac [2] zmult_zless_mono1)
apply (rule zmult_zle_mono2_neg)
apply (auto simp add: zcompare_rls zadd_commute add1_zle_iff pos_mod_bound)
apply (blast intro: zless_imp_zle dest: zless_zle_trans)
done

lemma zdiv_zmult2_aux2:
     "[| #0 $< c;   b $< r;  r $<= #0 |] ==> b $* (q zmod c) $+ r $<= #0"
apply (subgoal_tac "b $* (q zmod c) $<= #0")
 prefer 2
 apply (simp add: zmult_le_0_iff pos_mod_sign)
 apply (blast intro: zless_imp_zle dest: zless_zle_trans)
(*arithmetic*)
apply (drule zadd_zle_mono)
apply assumption
apply (simp add: zadd_commute)
done

lemma zdiv_zmult2_aux3:
     "[| #0 $< c;  #0 $<= r;  r $< b |] ==> #0 $<= b $* (q zmod c) $+ r"
apply (subgoal_tac "#0 $<= b $* (q zmod c)")
 prefer 2
 apply (simp add: int_0_le_mult_iff pos_mod_sign)
 apply (blast intro: zless_imp_zle dest: zle_zless_trans)
(*arithmetic*)
apply (drule zadd_zle_mono)
apply assumption
apply (simp add: zadd_commute)
done

lemma zdiv_zmult2_aux4:
     "[| #0 $< c; #0 $<= r; r $< b |] ==> b $* (q zmod c) $+ r $< b $* c"
apply (subgoal_tac "r $* #1 $< b $* (c $- q zmod c)")
apply (simp add: zdiff_zmult_distrib2 zadd_commute zcompare_rls)
apply (rule zless_zle_trans)
apply (erule zmult_zless_mono1)
apply (rule_tac [2] zmult_zle_mono2)
apply (auto simp add: zcompare_rls zadd_commute add1_zle_iff pos_mod_bound)
apply (blast intro: zless_imp_zle dest: zle_zless_trans)
done

lemma zdiv_zmult2_lemma:
     "[| quorem (<a,b>, <q,r>);  a \<in> int;  b \<in> int;  b \<noteq> #0;  #0 $< c |]
      ==> quorem (<a,b$*c>, <q zdiv c, b$*(q zmod c) $+ r>)"
apply (auto simp add: zmult_ac zmod_zdiv_equality [symmetric] quorem_def
               neq_iff_zless int_0_less_mult_iff
               zadd_zmult_distrib2 [symmetric] zdiv_zmult2_aux1 zdiv_zmult2_aux2
               zdiv_zmult2_aux3 zdiv_zmult2_aux4)
apply (blast dest: zless_trans)+
done

lemma zdiv_zmult2_eq_raw:
     "[|#0 $< c;  a \<in> int;  b \<in> int|] ==> a zdiv (b$*c) = (a zdiv b) zdiv c"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (rule quorem_div_mod [THEN zdiv_zmult2_lemma, THEN quorem_div])
apply (auto simp add: intify_eq_0_iff_zle)
apply (blast dest: zle_zless_trans)
done

lemma zdiv_zmult2_eq: "#0 $< c ==> a zdiv (b$*c) = (a zdiv b) zdiv c"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in zdiv_zmult2_eq_raw)
apply auto
done

lemma zmod_zmult2_eq_raw:
     "[|#0 $< c;  a \<in> int;  b \<in> int|]
      ==> a zmod (b$*c) = b$*(a zdiv b zmod c) $+ a zmod b"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (rule quorem_div_mod [THEN zdiv_zmult2_lemma, THEN quorem_mod])
apply (auto simp add: intify_eq_0_iff_zle)
apply (blast dest: zle_zless_trans)
done

lemma zmod_zmult2_eq:
     "#0 $< c ==> a zmod (b$*c) = b$*(a zdiv b zmod c) $+ a zmod b"
apply (cut_tac a = "intify (a)" and b = "intify (b)" in zmod_zmult2_eq_raw)
apply auto
done

subsection{* Cancellation of common factors in "zdiv" *}

lemma zdiv_zmult_zmult1_aux1:
     "[| #0 $< b;  intify(c) \<noteq> #0 |] ==> (c$*a) zdiv (c$*b) = a zdiv b"
apply (subst zdiv_zmult2_eq)
apply auto
done

lemma zdiv_zmult_zmult1_aux2:
     "[| b $< #0;  intify(c) \<noteq> #0 |] ==> (c$*a) zdiv (c$*b) = a zdiv b"
apply (subgoal_tac " (c $* ($-a)) zdiv (c $* ($-b)) = ($-a) zdiv ($-b)")
apply (rule_tac [2] zdiv_zmult_zmult1_aux1)
apply auto
done

lemma zdiv_zmult_zmult1_raw:
     "[|intify(c) \<noteq> #0; b \<in> int|] ==> (c$*a) zdiv (c$*b) = a zdiv b"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (auto simp add: neq_iff_zless [of b]
  zdiv_zmult_zmult1_aux1 zdiv_zmult_zmult1_aux2)
done

lemma zdiv_zmult_zmult1: "intify(c) \<noteq> #0 ==> (c$*a) zdiv (c$*b) = a zdiv b"
apply (cut_tac b = "intify (b)" in zdiv_zmult_zmult1_raw)
apply auto
done

lemma zdiv_zmult_zmult2: "intify(c) \<noteq> #0 ==> (a$*c) zdiv (b$*c) = a zdiv b"
apply (drule zdiv_zmult_zmult1)
apply (auto simp add: zmult_commute)
done


subsection{* Distribution of factors over "zmod" *}

lemma zmod_zmult_zmult1_aux1:
     "[| #0 $< b;  intify(c) \<noteq> #0 |]
      ==> (c$*a) zmod (c$*b) = c $* (a zmod b)"
apply (subst zmod_zmult2_eq)
apply auto
done

lemma zmod_zmult_zmult1_aux2:
     "[| b $< #0;  intify(c) \<noteq> #0 |]
      ==> (c$*a) zmod (c$*b) = c $* (a zmod b)"
apply (subgoal_tac " (c $* ($-a)) zmod (c $* ($-b)) = c $* (($-a) zmod ($-b))")
apply (rule_tac [2] zmod_zmult_zmult1_aux1)
apply auto
done

lemma zmod_zmult_zmult1_raw:
     "[|b \<in> int; c \<in> int|] ==> (c$*a) zmod (c$*b) = c $* (a zmod b)"
apply (case_tac "b = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (case_tac "c = #0")
 apply (simp add: DIVISION_BY_ZERO_ZDIV DIVISION_BY_ZERO_ZMOD)
apply (auto simp add: neq_iff_zless [of b]
  zmod_zmult_zmult1_aux1 zmod_zmult_zmult1_aux2)
done

lemma zmod_zmult_zmult1: "(c$*a) zmod (c$*b) = c $* (a zmod b)"
apply (cut_tac b = "intify (b)" and c = "intify (c)" in zmod_zmult_zmult1_raw)
apply auto
done

lemma zmod_zmult_zmult2: "(a$*c) zmod (b$*c) = (a zmod b) $* c"
apply (cut_tac c = "c" in zmod_zmult_zmult1)
apply (auto simp add: zmult_commute)
done


(** Quotients of signs **)

lemma zdiv_neg_pos_less0: "[| a $< #0;  #0 $< b |] ==> a zdiv b $< #0"
apply (subgoal_tac "a zdiv b $<= #-1")
apply (erule zle_zless_trans)
apply (simp (no_asm))
apply (rule zle_trans)
apply (rule_tac a' = "#-1" in zdiv_mono1)
apply (rule zless_add1_iff_zle [THEN iffD1])
apply (simp (no_asm))
apply (auto simp add: zdiv_minus1)
done

lemma zdiv_nonneg_neg_le0: "[| #0 $<= a;  b $< #0 |] ==> a zdiv b $<= #0"
apply (drule zdiv_mono1_neg)
apply auto
done

lemma pos_imp_zdiv_nonneg_iff: "#0 $< b ==> (#0 $<= a zdiv b) <-> (#0 $<= a)"
apply auto
apply (drule_tac [2] zdiv_mono1)
apply (auto simp add: neq_iff_zless)
apply (simp (no_asm_use) add: not_zless_iff_zle [THEN iff_sym])
apply (blast intro: zdiv_neg_pos_less0)
done

lemma neg_imp_zdiv_nonneg_iff: "b $< #0 ==> (#0 $<= a zdiv b) <-> (a $<= #0)"
apply (subst zdiv_zminus_zminus [symmetric])
apply (rule iff_trans)
apply (rule pos_imp_zdiv_nonneg_iff)
apply auto
done

(*But not (a zdiv b $<= 0 iff a$<=0); consider a=1, b=2 when a zdiv b = 0.*)
lemma pos_imp_zdiv_neg_iff: "#0 $< b ==> (a zdiv b $< #0) <-> (a $< #0)"
apply (simp (no_asm_simp) add: not_zle_iff_zless [THEN iff_sym])
apply (erule pos_imp_zdiv_nonneg_iff)
done

(*Again the law fails for $<=: consider a = -1, b = -2 when a zdiv b = 0*)
lemma neg_imp_zdiv_neg_iff: "b $< #0 ==> (a zdiv b $< #0) <-> (#0 $< a)"
apply (simp (no_asm_simp) add: not_zle_iff_zless [THEN iff_sym])
apply (erule neg_imp_zdiv_nonneg_iff)
done

(*
 THESE REMAIN TO BE CONVERTED -- but aren't that useful!

 subsection{* Speeding up the division algorithm with shifting *}

 (** computing "zdiv" by shifting **)

 lemma pos_zdiv_mult_2: "#0 $<= a ==> (#1 $+ #2$*b) zdiv (#2$*a) = b zdiv a"
 apply (case_tac "a = #0")
 apply (subgoal_tac "#1 $<= a")
  apply (arith_tac 2)
 apply (subgoal_tac "#1 $< a $* #2")
  apply (arith_tac 2)
 apply (subgoal_tac "#2$* (#1 $+ b zmod a) $<= #2$*a")
  apply (rule_tac [2] zmult_zle_mono2)
 apply (auto simp add: zadd_commute zmult_commute add1_zle_iff pos_mod_bound)
 apply (subst zdiv_zadd1_eq)
 apply (simp (no_asm_simp) add: zdiv_zmult_zmult2 zmod_zmult_zmult2 zdiv_pos_pos_trivial)
 apply (subst zdiv_pos_pos_trivial)
 apply (simp (no_asm_simp) add: [zmod_pos_pos_trivial pos_mod_sign [THEN zadd_zle_mono1] RSN (2,zle_trans) ])
 apply (auto simp add: zmod_pos_pos_trivial)
 apply (subgoal_tac "#0 $<= b zmod a")
  apply (asm_simp_tac (simpset () add: pos_mod_sign) 2)
 apply arith
 done


 lemma neg_zdiv_mult_2: "a $<= #0 ==> (#1 $+ #2$*b) zdiv (#2$*a) <-> (b$+#1) zdiv a"
 apply (subgoal_tac " (#1 $+ #2$* ($-b-#1)) zdiv (#2 $* ($-a)) <-> ($-b-#1) zdiv ($-a)")
 apply (rule_tac [2] pos_zdiv_mult_2)
 apply (auto simp add: zmult_zminus_right)
 apply (subgoal_tac " (#-1 - (#2 $* b)) = - (#1 $+ (#2 $* b))")
 apply (Simp_tac 2)
 apply (asm_full_simp_tac (HOL_ss add: zdiv_zminus_zminus zdiff_def zminus_zadd_distrib [symmetric])
 done


 (*Not clear why this must be proved separately; probably integ_of causes
   simplification problems*)
 lemma lemma: "~ #0 $<= x ==> x $<= #0"
 apply auto
 done

 lemma zdiv_integ_of_BIT: "integ_of (v BIT b) zdiv integ_of (w BIT False) =
           (if ~b | #0 $<= integ_of w
            then integ_of v zdiv (integ_of w)
            else (integ_of v $+ #1) zdiv (integ_of w))"
 apply (simp_tac (global_simpset_of Int.thy add: zadd_assoc integ_of_BIT)
 apply (simp (no_asm_simp) del: bin_arith_extra_simps@bin_rel_simps add: zdiv_zmult_zmult1 pos_zdiv_mult_2 lemma neg_zdiv_mult_2)
 done

 declare zdiv_integ_of_BIT [simp]


 (** computing "zmod" by shifting (proofs resemble those for "zdiv") **)

 lemma pos_zmod_mult_2: "#0 $<= a ==> (#1 $+ #2$*b) zmod (#2$*a) = #1 $+ #2 $* (b zmod a)"
 apply (case_tac "a = #0")
 apply (subgoal_tac "#1 $<= a")
  apply (arith_tac 2)
 apply (subgoal_tac "#1 $< a $* #2")
  apply (arith_tac 2)
 apply (subgoal_tac "#2$* (#1 $+ b zmod a) $<= #2$*a")
  apply (rule_tac [2] zmult_zle_mono2)
 apply (auto simp add: zadd_commute zmult_commute add1_zle_iff pos_mod_bound)
 apply (subst zmod_zadd1_eq)
 apply (simp (no_asm_simp) add: zmod_zmult_zmult2 zmod_pos_pos_trivial)
 apply (rule zmod_pos_pos_trivial)
 apply (simp (no_asm_simp) # add: [zmod_pos_pos_trivial pos_mod_sign [THEN zadd_zle_mono1] RSN (2,zle_trans) ])
 apply (auto simp add: zmod_pos_pos_trivial)
 apply (subgoal_tac "#0 $<= b zmod a")
  apply (asm_simp_tac (simpset () add: pos_mod_sign) 2)
 apply arith
 done


 lemma neg_zmod_mult_2: "a $<= #0 ==> (#1 $+ #2$*b) zmod (#2$*a) = #2 $* ((b$+#1) zmod a) - #1"
 apply (subgoal_tac " (#1 $+ #2$* ($-b-#1)) zmod (#2$* ($-a)) = #1 $+ #2$* (($-b-#1) zmod ($-a))")
 apply (rule_tac [2] pos_zmod_mult_2)
 apply (auto simp add: zmult_zminus_right)
 apply (subgoal_tac " (#-1 - (#2 $* b)) = - (#1 $+ (#2 $* b))")
 apply (Simp_tac 2)
 apply (asm_full_simp_tac (HOL_ss add: zmod_zminus_zminus zdiff_def zminus_zadd_distrib [symmetric])
 apply (dtac (zminus_equation [THEN iffD1, symmetric])
 apply auto
 done

 lemma zmod_integ_of_BIT: "integ_of (v BIT b) zmod integ_of (w BIT False) =
           (if b then
                 if #0 $<= integ_of w
                 then #2 $* (integ_of v zmod integ_of w) $+ #1
                 else #2 $* ((integ_of v $+ #1) zmod integ_of w) - #1
            else #2 $* (integ_of v zmod integ_of w))"
 apply (simp_tac (global_simpset_of Int.thy add: zadd_assoc integ_of_BIT)
 apply (simp (no_asm_simp) del: bin_arith_extra_simps@bin_rel_simps add: zmod_zmult_zmult1 pos_zmod_mult_2 lemma neg_zmod_mult_2)
 done

 declare zmod_integ_of_BIT [simp]
*)

end

