(*  Title:      HOL/IntDiv.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"

Here is the division algorithm in ML:

    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
	       in  if 0<=r-b then (2*q+1, r-b) else (2*q, r)
	   end;

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

Goal "[| #0 $< k; k: int |] ==> 0 < zmagnitude(k)";
by (dtac zero_zless_imp_znegative_zminus 1);
by (dtac zneg_int_of 2);
by (auto_tac (claset(), simpset() addsimps [inst "x" "k" zminus_equation]));  
by (subgoal_tac "0 < zmagnitude($# succ(x))" 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset_of Arith.thy addsimps [zmagnitude_int_of]) 1);
qed "zero_lt_zmagnitude";


(*** Inequality lemmas involving $#succ(m) ***)

Goal "(w $< z $+ $# succ(m)) <-> (w $< z $+ $#m | intify(w) = z $+ $#m)"; 
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_succ_zadd, zadd_assoc, 
                                  int_of_add RS sym]));
by (res_inst_tac [("x","0")] bexI 3);
by (TRYALL (dtac sym));
by (cut_inst_tac [("m","m")] int_succ_int_1 1);
by (cut_inst_tac [("m","n")] int_succ_int_1 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("n","x")] natE 1);
by Auto_tac;
by (res_inst_tac [("x","succ(x)")] bexI 1);
by Auto_tac;  
qed "zless_add_succ_iff";

Goal "z : int ==> (w $+ $# succ(m) $<= z) <-> (w $+ $#m $< z)";
by (asm_simp_tac (simpset_of Int.thy addsimps
                  [not_zless_iff_zle RS iff_sym, zless_add_succ_iff]) 1);
by (auto_tac (claset() addIs [zle_anti_sym] addEs [zless_asym],
	      simpset() addsimps [zless_imp_zle, not_zless_iff_zle]));
qed "lemma";

Goal "(w $+ $# succ(m) $<= z) <-> (w $+ $#m $< z)";
by (cut_inst_tac [("z","intify(z)")] lemma 1);
by Auto_tac;  
qed "zadd_succ_zle_iff";

(** Inequality reasoning **)

Goal "(w $< z $+ #1) <-> (w$<=z)";
by (subgoal_tac "#1 = $# 1" 1);
by (asm_simp_tac (simpset_of Int.thy 
                  addsimps [zless_add_succ_iff, zle_def]) 1);
by Auto_tac;  
qed "zless_add1_iff_zle";

Goal "(w $+ #1 $<= z) <-> (w $< z)";
by (subgoal_tac "#1 = $# 1" 1);
by (asm_simp_tac (simpset_of Int.thy addsimps [zadd_succ_zle_iff]) 1);
by Auto_tac;  
qed "add1_zle_iff";

Goal "(#1 $+ w $<= z) <-> (w $< z)";
by (stac zadd_commute 1);
by (rtac add1_zle_iff 1);
qed "add1_left_zle_iff";


(*** Monotonicity results ***)

Goal "(v$+z $< w$+z) <-> (v $< w)";
by (Simp_tac 1);
qed "zadd_right_cancel_zless";

Goal "(z$+v $< z$+w) <-> (v $< w)";
by (Simp_tac 1);
qed "zadd_left_cancel_zless";

Addsimps [zadd_right_cancel_zless, zadd_left_cancel_zless];

Goal "(v$+z $<= w$+z) <-> (v $<= w)";
by (Simp_tac 1);
qed "zadd_right_cancel_zle";

Goal "(z$+v $<= z$+w) <-> (v $<= w)";
by (Simp_tac 1);
qed "zadd_left_cancel_zle";

Addsimps [zadd_right_cancel_zle, zadd_left_cancel_zle];

(*"v $<= w ==> v$+z $<= w$+z"*)
bind_thm ("zadd_zless_mono1", zadd_right_cancel_zless RS iffD2);

(*"v $<= w ==> z$+v $<= z$+w"*)
bind_thm ("zadd_zless_mono2", zadd_left_cancel_zless RS iffD2);

(*"v $<= w ==> v$+z $<= w$+z"*)
bind_thm ("zadd_zle_mono1", zadd_right_cancel_zle RS iffD2);

(*"v $<= w ==> z$+v $<= z$+w"*)
bind_thm ("zadd_zle_mono2", zadd_left_cancel_zle RS iffD2);

Goal "[| w' $<= w; z' $<= z |] ==> w' $+ z' $<= w $+ z";
by (etac (zadd_zle_mono1 RS zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zle_mono";

Goal "[| w' $< w; z' $<= z |] ==> w' $+ z' $< w $+ z";
by (etac (zadd_zless_mono1 RS zless_zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zless_mono";


(*** Monotonicity of Multiplication ***)

Goal "k : nat ==> i $<= j ==> i $* $#k $<= j $* $#k";
by (induct_tac "k" 1);
by (stac int_succ_int_1 2);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2, zadd_zle_mono])));
val lemma = result();

Goal "[| i $<= j;  #0 $<= k |] ==> i$*k $<= j$*k";
by (subgoal_tac "i $* intify(k) $<= j $* intify(k)" 1);
by (Full_simp_tac 1);
by (res_inst_tac [("b", "intify(k)")] (not_zneg_mag RS subst) 1);
by (rtac lemma 3);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [znegative_iff_zless_0, 
                                           not_zless_iff_zle RS iff_sym]) 1);
qed "zmult_zle_mono1";

Goal "[| i $<= j;  k $<= #0 |] ==> j$*k $<= i$*k";
by (rtac (zminus_zle_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() delsimps [zmult_zminus_right]
                            addsimps [zmult_zminus_right RS sym,
				      zmult_zle_mono1, zle_zminus]) 1);
qed "zmult_zle_mono1_neg";

Goal "[| i $<= j;  #0 $<= k |] ==> k$*i $<= k$*j";
by (dtac zmult_zle_mono1 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zle_mono2";

Goal "[| i $<= j;  k $<= #0 |] ==> k$*j $<= k$*i";
by (dtac zmult_zle_mono1_neg 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zle_mono2_neg";

(* $<= monotonicity, BOTH arguments*)
Goal "[| i $<= j;  k $<= l;  #0 $<= j;  #0 $<= k |] ==> i$*k $<= j$*l";
by (etac (zmult_zle_mono1 RS zle_trans) 1);
by (assume_tac 1);
by (etac zmult_zle_mono2 1);
by (assume_tac 1);
qed "zmult_zle_mono";


(** strict, in 1st argument; proof is by induction on k>0 **)

Goal "[| i$<j; k : nat |] ==> 0<k --> $#k $* i $< $#k $* j";
by (induct_tac "k" 1);
by (stac int_succ_int_1 2);
by (etac natE 2);
by (ALLGOALS (asm_full_simp_tac
	      (simpset() addsimps [zadd_zmult_distrib, zadd_zless_mono, 
				   zle_def])));
by (ftac nat_0_le 1);
by (mp_tac 1);
by (subgoal_tac "i $+ (i $+ $# xa $* i) $< j $+ (j $+ $# xa $* j)" 1);
by (Full_simp_tac 1);
by (rtac zadd_zless_mono 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [zle_def])));
val lemma = result() RS mp;

Goal "[| i$<j;  #0 $< k |] ==> k$*i $< k$*j";
by (subgoal_tac "intify(k) $* i $< intify(k) $* j" 1);
by (Full_simp_tac 1);
by (res_inst_tac [("b", "intify(k)")] (not_zneg_mag RS subst) 1);
by (rtac lemma 3);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [znegative_iff_zless_0]) 1);
by (dtac zless_trans 1 THEN assume_tac 1);
by (auto_tac (claset(), simpset() addsimps [zero_lt_zmagnitude]));  
qed "zmult_zless_mono2";

Goal "[| i$<j;  #0 $< k |] ==> i$*k $< j$*k";
by (dtac zmult_zless_mono2 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zless_mono1";

(* < monotonicity, BOTH arguments*)
Goal "[| i $< j;  k $< l;  #0 $< j;  #0 $< k |] ==> i$*k $< j$*l";
by (etac (zmult_zless_mono1 RS zless_trans) 1);
by (assume_tac 1);
by (etac zmult_zless_mono2 1);
by (assume_tac 1);
qed "zmult_zless_mono";

Goal "[| i $< j;  k $< #0 |] ==> j$*k $< i$*k";
by (rtac (zminus_zless_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() delsimps [zmult_zminus_right]
                            addsimps [zmult_zminus_right RS sym,
				      zmult_zless_mono1, zless_zminus]) 1);
qed "zmult_zless_mono1_neg";

Goal "[| i $< j;  k $< #0 |] ==> k$*j $< k$*i";
by (rtac (zminus_zless_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() delsimps [zmult_zminus]
                            addsimps [zmult_zminus RS sym,
				      zmult_zless_mono2, zless_zminus]) 1);
qed "zmult_zless_mono2_neg";

Goal "[| m: int; n: int |] ==> (m$*n = #0) <-> (m = #0 | n = #0)";
by (case_tac "m $< #0" 1);
by (auto_tac (claset(), 
     simpset() addsimps [not_zless_iff_zle, zle_def, neq_iff_zless])); 
by (REPEAT 
    (force_tac (claset() addDs [zmult_zless_mono1_neg, zmult_zless_mono1], 
		simpset()) 1));
val lemma = result();

Goal "(m$*n = #0) <-> (intify(m) = #0 | intify(n) = #0)";
by (asm_full_simp_tac (simpset() addsimps [lemma RS iff_sym]) 1);
qed "zmult_eq_0_iff";


(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

Goal "[| k: int; m: int; n: int |] \
\     ==> (m$*k $< n$*k) <-> ((#0 $< k & m$<n) | (k $< #0 & n$<m))";
by (case_tac "k = #0" 1);
by (auto_tac (claset(), simpset() addsimps [neq_iff_zless, 
                              zmult_zless_mono1, zmult_zless_mono1_neg]));  
by (auto_tac (claset(), 
      simpset() addsimps [not_zless_iff_zle,
			  inst "w1" "m$*k" (not_zle_iff_zless RS iff_sym),
			  inst "w1" "m" (not_zle_iff_zless RS iff_sym)]));
by (ALLGOALS (etac notE));
by (auto_tac (claset(), simpset() addsimps [zless_imp_zle, zmult_zle_mono1,
                                            zmult_zle_mono1_neg]));  
val lemma = result();

Goal "(m$*k $< n$*k) <-> ((#0 $< k & m$<n) | (k $< #0 & n$<m))";
by (cut_inst_tac [("k","intify(k)"),("m","intify(m)"),("n","intify(n)")]
                 lemma 1);
by Auto_tac;  
qed "zmult_zless_cancel2";

Goal "(k$*m $< k$*n) <-> ((#0 $< k & m$<n) | (k $< #0 & n$<m))";
by (simp_tac (simpset() addsimps [inst "z" "k" zmult_commute, 
                                  zmult_zless_cancel2]) 1);
qed "zmult_zless_cancel1";

Goal "(m$*k $<= n$*k) <-> ((#0 $< k --> m$<=n) & (k $< #0 --> n$<=m))";
by (simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym, 
                                  zmult_zless_cancel2]) 1);
by Auto_tac;  
qed "zmult_zle_cancel2";

Goal "(k$*m $<= k$*n) <-> ((#0 $< k --> m$<=n) & (k $< #0 --> n$<=m))";
by (simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym, 
                                  zmult_zless_cancel1]) 1);
by Auto_tac;  
qed "zmult_zle_cancel1";

Goal "[| m: int; n: int |] ==> m=n <-> (m $<= n & n $<= m)";
by (blast_tac (claset() addIs [zle_refl,zle_anti_sym]) 1); 
qed "int_eq_iff_zle";

Goal "[| k: int; m: int; n: int |] ==> (m$*k = n$*k) <-> (k=#0 | m=n)";
by (asm_simp_tac (simpset() addsimps [inst "m" "m$*k" int_eq_iff_zle,
                                      inst "m" "m" int_eq_iff_zle]) 1); 
by (auto_tac (claset(), 
              simpset() addsimps [zmult_zle_cancel2, neq_iff_zless]));  
val lemma = result();

Goal "(m$*k = n$*k) <-> (intify(k) = #0 | intify(m) = intify(n))";
by (rtac iff_trans 1);
by (rtac lemma 2);
by Auto_tac;  
qed "zmult_cancel2";

Goal "(k$*m = k$*n) <-> (intify(k) = #0 | intify(m) = intify(n))";
by (simp_tac (simpset() addsimps [inst "z" "k" zmult_commute, 
                                  zmult_cancel2]) 1);
qed "zmult_cancel1";
Addsimps [zmult_cancel1, zmult_cancel2];


(*** Uniqueness and monotonicity of quotients and remainders ***)


Goal "[| b$*q' $+ r' $<= b$*q $+ r;  #0 $<= r';  #0 $< b;  r $< b |] \
\     ==> q' $<= q";
by (subgoal_tac "r' $+ b $* (q'$-q) $<= r" 1);
by (full_simp_tac 
    (simpset() addsimps [zdiff_zmult_distrib2]@zadd_ac@zcompare_rls) 2);
by (subgoal_tac "#0 $< b $* (#1 $+ q $- q')" 1);
by (etac zle_zless_trans 2);
by (full_simp_tac 
    (simpset() addsimps [zdiff_zmult_distrib2,
			 zadd_zmult_distrib2]@zadd_ac@zcompare_rls) 2);
by (etac zle_zless_trans 2);
by (Asm_simp_tac 2);
by (subgoal_tac "b $* q' $< b $* (#1 $+ q)" 1);
by (full_simp_tac
    (simpset() addsimps [zdiff_zmult_distrib2,
			 zadd_zmult_distrib2]@zadd_ac@zcompare_rls) 2);
by (auto_tac (claset() addEs [zless_asym], 
              simpset() addsimps [zmult_zless_cancel1, zless_add1_iff_zle]@
                                 zadd_ac@zcompare_rls));
qed "unique_quotient_lemma";

Goal "[| b$*q' $+ r' $<= b$*q $+ r;  r $<= #0;  b $< #0;  b $< r' |] \
\     ==> q $<= q'";
by (res_inst_tac [("b", "$-b"), ("r", "$-r'"), ("r'", "$-r")] 
    unique_quotient_lemma 1);
by (auto_tac (claset(), 
	      simpset() delsimps [zminus_zadd_distrib]
			addsimps [zminus_zadd_distrib RS sym,
	                          zle_zminus, zless_zminus])); 
qed "unique_quotient_lemma_neg";


Goal "[| quorem (<a,b>, <q,r>);  quorem (<a,b>, <q',r'>);  b: int; b ~= #0; \
\        q: int; q' : int |] ==> q = q'";
by (asm_full_simp_tac 
    (simpset() addsimps split_ifs@
                        [quorem_def, neq_iff_zless]) 1);
by Safe_tac; 
by (ALLGOALS Asm_full_simp_tac);
by (REPEAT 
    (blast_tac (claset() addIs [zle_anti_sym]
			 addDs [zle_eq_refl RS unique_quotient_lemma, 
				zle_eq_refl RS unique_quotient_lemma_neg,
				sym]) 1));
qed "unique_quotient";

Goal "[| quorem (<a,b>, <q,r>);  quorem (<a,b>, <q',r'>);  b: int; b ~= #0; \
\        q: int; q' : int; \
\        r: int; r' : int |] ==> r = r'";
by (subgoal_tac "q = q'" 1);
by (blast_tac (claset() addIs [unique_quotient]) 2);
by (asm_full_simp_tac (simpset() addsimps [quorem_def]) 1);
by Auto_tac;  
qed "unique_remainder";


(*** Correctness of posDivAlg, the division algorithm for a>=0 and b>0 ***)


Goal "adjust(a, b, <q,r>) = (let diff = r$-b in \
\                         if #0 $<= diff then <#2$*q $+ #1,diff>  \
\                                       else <#2$*q,r>)";
by (simp_tac (simpset() addsimps [Let_def,adjust_def]) 1);
qed "adjust_eq";
Addsimps [adjust_eq];


Goal "\\<lbrakk>#0 $< b; \\<not> a $< b\\<rbrakk>   \
\     \\<Longrightarrow> nat_of(a $- #2 $\\<times> b $+ #1) < nat_of(a $- b $+ #1)";
by (simp_tac (simpset() addsimps [zless_nat_conj]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_zless_iff_zle,
                       zless_add1_iff_zle]@zcompare_rls) 1); 
qed "posDivAlg_termination";

val lemma = wf_measure RS (posDivAlg_def RS def_wfrec RS trans);

Goal "[| #0 $< b; a: int; b: int |] ==> \
\     posDivAlg(<a,b>) =      \
\      (if a$<b then <#0,a> else adjust(a, b, posDivAlg (<a, #2$*b>)))";
by (rtac lemma 1);
by (asm_simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 1);
by (asm_simp_tac (simpset() addsimps [vimage_iff, posDivAlg_termination]) 1); 
qed "posDivAlg_eqn";

val [prem] =
Goal "[| !!a b. [| a: int; b: int; \
\                  ~ (a $< b | b $<= #0) --> P(<a, #2 $* b>) |] \
\               ==> P(<a,b>) |] \
\     ==> <u,v>: int*int \\<longrightarrow> P(<u,v>)"; 
by (res_inst_tac [("a","<u,v>")] wf_induct 1);
by (res_inst_tac [("A","int*int"), ("f","%<a,b>.nat_of (a $- b $+ #1)")] 
                 wf_measure 1);
by (Clarify_tac 1);
by (rtac prem 1);
by (dres_inst_tac [("x","<xa, #2 $\\<times> y>")] spec 3); 
by Auto_tac;  
by (asm_full_simp_tac (simpset() addsimps [not_zle_iff_zless, 
                                           posDivAlg_termination]) 1); 
val lemma = result() RS mp;


val prems =
Goal "[| u: int; v: int; \
\        !!a b. [| a: int; b: int; ~ (a $< b | b $<= #0) --> P(a, #2 $* b) |] \
\             ==> P(a,b) |] \
\     ==> P(u,v)";
by (subgoal_tac "(%<x,y>. P(x,y))(<u,v>)" 1);
by (Asm_full_simp_tac 1); 
by (rtac lemma 1);
by (simp_tac (simpset() addsimps prems) 2);
by (Full_simp_tac 1);  
by (resolve_tac prems 1);
by Auto_tac;  
qed "posDivAlg_induct";

(**TO BE COMPLETED**)

