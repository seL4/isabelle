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

Goal "[| #0 $< k; k \\<in> int |] ==> 0 < zmagnitude(k)";
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

Goal "z \\<in> int ==> (w $+ $# succ(m) $<= z) <-> (w $+ $#m $< z)";
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


(*** Monotonicity of Multiplication ***)

Goal "k \\<in> nat ==> i $<= j ==> i $* $#k $<= j $* $#k";
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

Goal "[| i$<j; k \\<in> nat |] ==> 0<k --> $#k $* i $< $#k $* j";
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


(** Products of zeroes **)

Goal "[| m \\<in> int; n \\<in> int |] ==> (m$*n = #0) <-> (m = #0 | n = #0)";
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
AddIffs [zmult_eq_0_iff];


(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

Goal "[| k \\<in> int; m \\<in> int; n \\<in> int |] \
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

Goal "[| m \\<in> int; n \\<in> int |] ==> m=n <-> (m $<= n & n $<= m)";
by (blast_tac (claset() addIs [zle_refl,zle_anti_sym]) 1); 
qed "int_eq_iff_zle";

Goal "[| k \\<in> int; m \\<in> int; n \\<in> int |] ==> (m$*k = n$*k) <-> (k=#0 | m=n)";
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


Goal "[| quorem (<a,b>, <q,r>);  quorem (<a,b>, <q',r'>);  b \\<in> int; b ~= #0; \
\        q \\<in> int; q' \\<in> int |] ==> q = q'";
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

Goal "[| quorem (<a,b>, <q,r>);  quorem (<a,b>, <q',r'>);  b \\<in> int; b ~= #0; \
\        q \\<in> int; q' \\<in> int; \
\        r \\<in> int; r' \\<in> int |] ==> r = r'";
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


Goal "[| #0 $< b; \\<not> a $< b |]   \
\     ==> nat_of(a $- #2 $\\<times> b $+ #1) < nat_of(a $- b $+ #1)";
by (simp_tac (simpset() addsimps [zless_nat_conj]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_zless_iff_zle,
                       zless_add1_iff_zle]@zcompare_rls) 1); 
qed "posDivAlg_termination";

val posDivAlg_unfold = wf_measure RS (posDivAlg_def RS def_wfrec);

Goal "[| #0 $< b; a \\<in> int; b \\<in> int |] ==> \
\     posDivAlg(<a,b>) =      \
\      (if a$<b then <#0,a> else adjust(a, b, posDivAlg (<a, #2$*b>)))";
by (rtac (posDivAlg_unfold RS trans) 1);
by (asm_simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 1);
by (asm_simp_tac (simpset() addsimps [vimage_iff, posDivAlg_termination]) 1); 
qed "posDivAlg_eqn";

val [prem] =
Goal "[| !!a b. [| a \\<in> int; b \\<in> int; \
\                  ~ (a $< b | b $<= #0) --> P(<a, #2 $* b>) |] \
\               ==> P(<a,b>) |] \
\     ==> <u,v> \\<in> int*int --> P(<u,v>)"; 
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
Goal "[| u \\<in> int; v \\<in> int; \
\        !!a b. [| a \\<in> int; b \\<in> int; ~ (a $< b | b $<= #0) --> P(a, #2 $* b) |] \
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

(*FIXME: use intify in integ_of so that we always have integ_of w \\<in> int.
    then this rewrite can work for ALL constants!!*)
Goal "intify(m) = #0 <-> (m $<= #0 & #0 $<= m)";
by (simp_tac (simpset() addsimps [int_eq_iff_zle]) 1); 
qed "intify_eq_0_iff_zle";


(*** Some convenient biconditionals for products of signs ***)

Goal "[| #0 $< i; #0 $< j |] ==> #0 $< i $* j";
by (dtac zmult_zless_mono1 1);
by Auto_tac; 
qed "zmult_pos";

Goal "[| i $< #0; j $< #0 |] ==> #0 $< i $* j";
by (dtac zmult_zless_mono1_neg 1);
by Auto_tac; 
qed "zmult_neg";

Goal "[| #0 $< i; j $< #0 |] ==> i $* j $< #0";
by (dtac zmult_zless_mono1_neg 1);
by Auto_tac; 
qed "zmult_pos_neg";

(** Inequality reasoning **)

Goal "[| x \\<in> int; y \\<in> int |] \
\     ==> (#0 $< x $* y) <-> (#0 $< x & #0 $< y | x $< #0 & y $< #0)";
by (auto_tac (claset(), 
              simpset() addsimps [zle_def, not_zless_iff_zle,
	                          zmult_pos, zmult_neg]));
by (ALLGOALS (rtac ccontr)); 
by (auto_tac (claset(), 
	      simpset() addsimps [zle_def, not_zless_iff_zle]));
by (ALLGOALS (eres_inst_tac [("P","#0$< x$* y")] rev_mp)); 
by (ALLGOALS (dtac zmult_pos_neg THEN' assume_tac));
by (auto_tac (claset() addDs [zless_not_sym], 
              simpset() addsimps [zmult_commute]));  
val lemma = result();

Goal "(#0 $< x $* y) <-> (#0 $< x & #0 $< y | x $< #0 & y $< #0)";
by (cut_inst_tac [("x","intify(x)"),("y","intify(y)")] lemma 1);
by Auto_tac; 
qed "int_0_less_mult_iff";

Goal "[| x \\<in> int; y \\<in> int |] \
\     ==> (#0 $<= x $* y) <-> (#0 $<= x & #0 $<= y | x $<= #0 & y $<= #0)";
by (auto_tac (claset(), 
              simpset() addsimps [zle_def, not_zless_iff_zle,  
                                  int_0_less_mult_iff]));
val lemma = result();

Goal "(#0 $<= x $* y) <-> ((#0 $<= x & #0 $<= y) | (x $<= #0 & y $<= #0))";
by (cut_inst_tac [("x","intify(x)"),("y","intify(y)")] lemma 1);
by Auto_tac;  
qed "int_0_le_mult_iff";

Goal "(x $* y $< #0) <-> (#0 $< x & y $< #0 | x $< #0 & #0 $< y)";
by (auto_tac (claset(), 
              simpset() addsimps [int_0_le_mult_iff, 
                                  not_zle_iff_zless RS iff_sym]));
by (auto_tac (claset() addDs [zless_not_sym],  
              simpset() addsimps [not_zle_iff_zless]));
qed "zmult_less_0_iff";

Goal "(x $* y $<= #0) <-> (#0 $<= x & y $<= #0 | x $<= #0 & #0 $<= y)";
by (auto_tac (claset() addDs [zless_not_sym], 
              simpset() addsimps [int_0_less_mult_iff, 
                                  not_zless_iff_zle RS iff_sym]));
qed "zmult_le_0_iff";


(*Typechecking for posDivAlg*)
Goal "[| a \\<in> int; b \\<in> int |] ==> posDivAlg(<a,b>) \\<in> int * int";
by (res_inst_tac [("u", "a"), ("v", "b")] posDivAlg_induct 1);
by (TRYALL assume_tac);
by (case_tac "#0 $< ba" 1);
by (asm_simp_tac (simpset() addsimps [posDivAlg_eqn,adjust_def,integ_of_type]
                            addsplits [split_if_asm]) 1);
by (Clarify_tac 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [int_0_less_mult_iff, not_zle_iff_zless]) 1); 
by (asm_full_simp_tac (simpset() addsimps [not_zless_iff_zle]) 1);
by (stac posDivAlg_unfold 1); 
by (Asm_full_simp_tac 1); 
qed_spec_mp "posDivAlg_type";

(*Correctness of posDivAlg: it computes quotients correctly*)
Goal "[| a \\<in> int; b \\<in> int |] \
\     ==> #0 $<= a --> #0 $< b --> quorem (<a,b>, posDivAlg(<a,b>))";
by (res_inst_tac [("u", "a"), ("v", "b")] posDivAlg_induct 1);
by Auto_tac;
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [quorem_def])));
(*base case: a<b*)
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 3); 
by (asm_full_simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 2); 
by (asm_full_simp_tac (simpset() addsimps [posDivAlg_eqn]) 1);
(*main argument*)
by (stac posDivAlg_eqn 1);
by (ALLGOALS Asm_simp_tac);
by (etac splitE 1);
by (rtac posDivAlg_type 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff])));
by (auto_tac (claset(), simpset() addsimps [zadd_zmult_distrib2, Let_def]));
(*now just linear arithmetic*)
by (asm_full_simp_tac 
    (simpset() addsimps [not_zle_iff_zless, zdiff_zless_iff]) 1); 
qed_spec_mp "posDivAlg_correct";


(*** Correctness of negDivAlg, the division algorithm for a<0 and b>0 ***)

Goal "[| #0 $< b; \\<not> #0 $<= a $+ b |]   \
\     ==> nat_of($- a $- #2 $\\<times> b) < nat_of($- a $- b)";
by (simp_tac (simpset() addsimps [zless_nat_conj]) 1);
by (asm_full_simp_tac (simpset() addsimps zcompare_rls @ 
           [not_zle_iff_zless, zless_zdiff_iff RS iff_sym, zless_zminus]) 1); 
qed "negDivAlg_termination";

val negDivAlg_unfold = wf_measure RS (negDivAlg_def RS def_wfrec);

Goal "[| #0 $< b; a \\<in> int; b \\<in> int |] ==> \
\     negDivAlg(<a,b>) =      \
\      (if #0 $<= a$+b then <#-1,a$+b> \
\                      else adjust(a, b, negDivAlg (<a, #2$*b>)))";
by (rtac (negDivAlg_unfold RS trans) 1);
by (asm_simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 1);
by (asm_simp_tac (simpset() addsimps [not_zle_iff_zless, vimage_iff, 
                                      negDivAlg_termination]) 1); 
qed "negDivAlg_eqn";

val [prem] =
Goal "[| !!a b. [| a \\<in> int; b \\<in> int; \
\                  ~ (#0 $<= a $+ b | b $<= #0) --> P(<a, #2 $* b>) |] \
\               ==> P(<a,b>) |] \
\     ==> <u,v> \\<in> int*int --> P(<u,v>)"; 
by (res_inst_tac [("a","<u,v>")] wf_induct 1);
by (res_inst_tac [("A","int*int"), ("f","%<a,b>.nat_of ($- a $- b)")] 
                 wf_measure 1);
by (Clarify_tac 1);
by (rtac prem 1);
by (dres_inst_tac [("x","<xa, #2 $\\<times> y>")] spec 3); 
by Auto_tac;  
by (asm_full_simp_tac (simpset() addsimps [not_zle_iff_zless, 
                                           negDivAlg_termination]) 1); 
val lemma = result() RS mp;

val prems =
Goal "[| u \\<in> int; v \\<in> int; \
\        !!a b. [| a \\<in> int; b \\<in> int; \
\                  ~ (#0 $<= a $+ b | b $<= #0) --> P(a, #2 $* b) |] \
\               ==> P(a,b) |] \
\     ==> P(u,v)";
by (subgoal_tac "(%<x,y>. P(x,y))(<u,v>)" 1);
by (Asm_full_simp_tac 1); 
by (rtac lemma 1);
by (simp_tac (simpset() addsimps prems) 2);
by (Full_simp_tac 1);  
by (resolve_tac prems 1);
by Auto_tac;  
qed "negDivAlg_induct";


(*Typechecking for negDivAlg*)
Goal "[| a \\<in> int; b \\<in> int |] ==> negDivAlg(<a,b>) \\<in> int * int";
by (res_inst_tac [("u", "a"), ("v", "b")] negDivAlg_induct 1);
by (TRYALL assume_tac);
by (case_tac "#0 $< ba" 1);
by (asm_simp_tac (simpset() addsimps [negDivAlg_eqn,adjust_def,integ_of_type]
                            addsplits [split_if_asm]) 1);
by (Clarify_tac 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [int_0_less_mult_iff, not_zle_iff_zless]) 1); 
by (asm_full_simp_tac (simpset() addsimps [not_zless_iff_zle]) 1);
by (stac negDivAlg_unfold 1); 
by (Asm_full_simp_tac 1); 
qed "negDivAlg_type";


(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b=0 rather than -1*)
Goal "[| a \\<in> int; b \\<in> int |] \
\     ==> a $< #0 --> #0 $< b --> quorem (<a,b>, negDivAlg(<a,b>))";
by (res_inst_tac [("u", "a"), ("v", "b")] negDivAlg_induct 1);
by Auto_tac;
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [quorem_def])));
(*base case: 0$<=a$+b*)
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 3); 
by (asm_full_simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 2); 
by (asm_full_simp_tac (simpset() addsimps [negDivAlg_eqn]) 1);
(*main argument*)
by (stac negDivAlg_eqn 1);
by (ALLGOALS Asm_simp_tac);
by (etac splitE 1);
by (rtac negDivAlg_type 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff])));
by (auto_tac (claset(), simpset() addsimps [zadd_zmult_distrib2, Let_def]));
(*now just linear arithmetic*)
by (asm_full_simp_tac 
    (simpset() addsimps [not_zle_iff_zless, zdiff_zless_iff]) 1); 
qed_spec_mp "negDivAlg_correct";


(*** Existence shown by proving the division algorithm to be correct ***)

(*the case a=0*)
Goal "[|b \\<noteq> #0;  b \\<in> int|] ==> quorem (<#0,b>, <#0,#0>)";
by (rotate_tac ~1 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, neq_iff_zless]));
qed "quorem_0";

Goal "posDivAlg(<a,#0>) = <#0,a>";
by (stac posDivAlg_unfold 1);
by (Simp_tac 1); 
qed "posDivAlg_zero_divisor";

Goal "posDivAlg (<#0,b>) = <#0,#0>";
by (stac posDivAlg_unfold 1);
by (simp_tac (simpset() addsimps [not_zle_iff_zless]) 1); 
qed "posDivAlg_0";
Addsimps [posDivAlg_0];

Goal "negDivAlg (<#-1,b>) = <#-1, b$-#1>";
by (stac negDivAlg_unfold 1);
by Auto_tac;
(*ALL the rest is linear arithmetic: to notice the contradiction*)
by (asm_full_simp_tac (simpset() addsimps [not_zle_iff_zless]) 1); 
by (dtac (zminus_zless_zminus RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps [zadd_commute, zless_add1_iff_zle, 
                                           zle_zminus]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_zle_iff_zless RS iff_sym]) 1); 
qed "negDivAlg_minus1";
Addsimps [negDivAlg_minus1];

Goalw [negateSnd_def] "negateSnd (<q,r>) = <q, $-r>";
by Auto_tac;
qed "negateSnd_eq";
Addsimps [negateSnd_eq];

Goalw [negateSnd_def] "qr \\<in> int * int ==> negateSnd (qr) \\<in> int * int";
by Auto_tac;
qed "negateSnd_type";

Goal "[|quorem (<$-a,$-b>, qr);  a \\<in> int;  b \\<in> int;  qr \\<in> int * int|]  \
\     ==> quorem (<a,b>, negateSnd(qr))";
by (Clarify_tac 1); 
by (auto_tac (claset() addEs [zless_asym], 
              simpset() addsimps [quorem_def, zless_zminus]));
(*linear arithmetic from here on*)
by (ALLGOALS
    (asm_full_simp_tac
     (simpset() addsimps [inst "x" "a" zminus_equation, zminus_zless])));
by (ALLGOALS (cut_inst_tac [("z","b"),("w","#0")] zless_linear));
by Auto_tac;  
by (ALLGOALS (blast_tac (claset() addDs [zle_zless_trans]))); 
qed "quorem_neg";

Goal "[|b \\<noteq> #0;  a \\<in> int;  b \\<in> int|] ==> quorem (<a,b>, divAlg(<a,b>))";
by (rotate_tac 1 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_0, divAlg_def]));
by (REPEAT_FIRST (ares_tac [quorem_neg, posDivAlg_correct, negDivAlg_correct,
                            posDivAlg_type, negDivAlg_type]));
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, neq_iff_zless]));
(*linear arithmetic from here on*)
by (auto_tac (claset(), simpset() addsimps [zle_def]));  
qed "divAlg_correct";

Goal "[|a \\<in> int;  b \\<in> int|] ==> divAlg(<a,b>) \\<in> int * int";
by (auto_tac (claset(), simpset() addsimps [divAlg_def]));
by (auto_tac (claset(), 
      simpset() addsimps [posDivAlg_type, negDivAlg_type, negateSnd_type]));
qed "divAlg_type";


(** intify cancellation **)

Goal "intify(x) zdiv y = x zdiv y";
by (simp_tac (simpset() addsimps [zdiv_def]) 1);
qed "zdiv_intify1";

Goal "x zdiv intify(y) = x zdiv y";
by (simp_tac (simpset() addsimps [zdiv_def]) 1);
qed "zdiv_intify2";
Addsimps [zdiv_intify1, zdiv_intify2];

Goalw [zdiv_def] "z zdiv w \\<in> int";
by (blast_tac (claset() addIs [fst_type, divAlg_type]) 1); 
qed "zdiv_type";
AddIffs [zdiv_type];  AddTCs [zdiv_type];

Goal "intify(x) zmod y = x zmod y";
by (simp_tac (simpset() addsimps [zmod_def]) 1);
qed "zmod_intify1";

Goal "x zmod intify(y) = x zmod y";
by (simp_tac (simpset() addsimps [zmod_def]) 1);
qed "zmod_intify2";
Addsimps [zmod_intify1, zmod_intify2];

Goalw [zmod_def] "z zmod w \\<in> int";
by (rtac snd_type 1); 
by (blast_tac (claset() addIs [divAlg_type]) 1); 
qed "zmod_type";
AddIffs [zmod_type];  AddTCs [zmod_type];


(** Arbitrary definitions for division by zero.  Useful to simplify 
    certain equations **)

Goal "a zdiv #0 = #0";
by (simp_tac
    (simpset() addsimps [zdiv_def, divAlg_def, posDivAlg_zero_divisor]) 1);
qed "DIVISION_BY_ZERO_ZDIV";  (*NOT for adding to default simpset*)

Goal "a zmod #0 = intify(a)";
by (simp_tac
    (simpset() addsimps [zmod_def, divAlg_def, posDivAlg_zero_divisor]) 1);
qed "DIVISION_BY_ZERO_ZMOD";  (*NOT for adding to default simpset*)

fun zdiv_undefined_case_tac s i =
  case_tac s i THEN 
  asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO_ZDIV, 
				    DIVISION_BY_ZERO_ZMOD]) i;


(** Basic laws about division and remainder **)

Goal "[| a \\<in> int; b \\<in> int |] ==> a = b $* (a zdiv b) $+ (a zmod b)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (cut_inst_tac [("a","a"),("b","b")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, zdiv_def, zmod_def, split_def]));
qed "raw_zmod_zdiv_equality";  

Goal "intify(a) = b $* (a zdiv b) $+ (a zmod b)";
by (rtac trans 1); 
by (res_inst_tac [("b","intify(b)")] raw_zmod_zdiv_equality 1); 
by Auto_tac;  
qed "zmod_zdiv_equality";  

Goal "#0 $< b ==> #0 $<= a zmod b & a zmod b $< b";
by (cut_inst_tac [("a","intify(a)"),("b","intify(b)")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [intify_eq_0_iff_zle, quorem_def, zmod_def, 
                                  split_def]));
by (ALLGOALS (blast_tac (claset() addDs [zle_zless_trans]))); 
bind_thm ("pos_mod_sign", result() RS conjunct1);
bind_thm ("pos_mod_bound", result() RS conjunct2);

Goal "b $< #0 ==> a zmod b $<= #0 & b $< a zmod b";
by (cut_inst_tac [("a","intify(a)"),("b","intify(b)")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [intify_eq_0_iff_zle, quorem_def, zmod_def, 
                                  split_def]));
by (blast_tac (claset() addDs [zle_zless_trans]) 1); 
by (ALLGOALS (blast_tac (claset() addDs [zless_trans]))); 
bind_thm ("neg_mod_sign", result() RS conjunct1);
bind_thm ("neg_mod_bound", result() RS conjunct2);


(** proving general properties of zdiv and zmod **)

Goal "[|b \\<noteq> #0;  a \\<in> int;  b \\<in> int |] \
\     ==> quorem (<a,b>, <a zdiv b, a zmod b>)";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (rotate_tac 1 1);
by (auto_tac
    (claset(),
     simpset() addsimps [quorem_def, neq_iff_zless, 
			 pos_mod_sign,pos_mod_bound,
			 neg_mod_sign, neg_mod_bound]));
qed "quorem_div_mod";

(*Surely quorem(<a,b>,<q,r>) implies a \\<in> int, but it doesn't matter*)
Goal "[| quorem(<a,b>,<q,r>);  b \\<noteq> #0;  a \\<in> int;  b \\<in> int;  q \\<in> int |] \
\     ==> a zdiv b = q";
by (blast_tac (claset() addIs [quorem_div_mod RS unique_quotient]) 1); 
qed "quorem_div";

Goal "[| quorem(<a,b>,<q,r>);  b \\<noteq> #0;  a \\<in> int;  b \\<in> int;  q \\<in> int;  r \\<in> int |] ==> a zmod b = r";
by (blast_tac (claset() addIs [quorem_div_mod RS unique_remainder]) 1); 
qed "quorem_mod";

Goal "[| a \\<in> int;  b \\<in> int;  #0 $<= a;  a $< b |] ==> a zdiv b = #0";
by (rtac quorem_div 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
(*linear arithmetic*)
by (ALLGOALS (blast_tac (claset() addDs [zle_zless_trans])));
qed "zdiv_pos_pos_trivial_raw";

Goal "[| #0 $<= a;  a $< b |] ==> a zdiv b = #0";
by (cut_inst_tac [("a", "intify(a)"), ("b", "intify(b)")]
    zdiv_pos_pos_trivial_raw 1);
by Auto_tac;  
qed "zdiv_pos_pos_trivial";

Goal "[| a \\<in> int;  b \\<in> int;  a $<= #0;  b $< a |] ==> a zdiv b = #0";
by (res_inst_tac [("r","a")] quorem_div 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
(*linear arithmetic*)
by (ALLGOALS (blast_tac (claset() addDs [zle_zless_trans, zless_trans])));
qed "zdiv_neg_neg_trivial_raw";

Goal "[| a $<= #0;  b $< a |] ==> a zdiv b = #0";
by (cut_inst_tac [("a", "intify(a)"), ("b", "intify(b)")]
    zdiv_neg_neg_trivial_raw 1);
by Auto_tac;  
qed "zdiv_neg_neg_trivial";

Goal "[| a$+b $<= #0;  #0 $< a;  #0 $< b |] ==> False";
by (dres_inst_tac [("z'","#0"), ("z","b")] zadd_zless_mono 1);
by (auto_tac (claset(), simpset() addsimps [zle_def]));  
by (blast_tac (claset() addDs [zless_trans]) 1);
qed "zadd_le_0_lemma";

Goal "[| a \\<in> int;  b \\<in> int;  #0 $< a;  a$+b $<= #0 |] ==> a zdiv b = #-1";
by (res_inst_tac [("r","a $+ b ")] quorem_div 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
(*linear arithmetic*)
by (ALLGOALS (blast_tac (claset() addDs [zadd_le_0_lemma, zle_zless_trans])));
qed "zdiv_pos_neg_trivial_raw";

Goal "[| #0 $< a;  a$+b $<= #0 |] ==> a zdiv b = #-1";
by (cut_inst_tac [("a", "intify(a)"), ("b", "intify(b)")]
    zdiv_pos_neg_trivial_raw 1);
by Auto_tac;  
qed "zdiv_pos_neg_trivial";

(*There is no zdiv_neg_pos_trivial because  #0 zdiv b = #0 would supersede it*)


Goal "[| a \\<in> int;  b \\<in> int;  #0 $<= a;  a $< b |] ==> a zmod b = a";
by (res_inst_tac [("q","#0")] quorem_mod 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
(*linear arithmetic*)
by (ALLGOALS (blast_tac (claset() addDs [zle_zless_trans])));
qed "zmod_pos_pos_trivial_raw";

Goal "[| #0 $<= a;  a $< b |] ==> a zmod b = intify(a)";
by (cut_inst_tac [("a", "intify(a)"), ("b", "intify(b)")]
    zmod_pos_pos_trivial_raw 1);
by Auto_tac;  
qed "zmod_pos_pos_trivial";

Goal "[| a \\<in> int;  b \\<in> int;  a $<= #0;  b $< a |] ==> a zmod b = a";
by (res_inst_tac [("q","#0")] quorem_mod 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
(*linear arithmetic*)
by (ALLGOALS (blast_tac (claset() addDs [zle_zless_trans, zless_trans])));
qed "zmod_neg_neg_trivial_raw";

Goal "[| a $<= #0;  b $< a |] ==> a zmod b = intify(a)";
by (cut_inst_tac [("a", "intify(a)"), ("b", "intify(b)")]
    zmod_neg_neg_trivial_raw 1);
by Auto_tac;  
qed "zmod_neg_neg_trivial";

Goal "[| a \\<in> int;  b \\<in> int;  #0 $< a;  a$+b $<= #0 |] ==> a zmod b = a$+b";
by (res_inst_tac [("q","#-1")] quorem_mod 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
(*linear arithmetic*)
by (ALLGOALS (blast_tac (claset() addDs [zadd_le_0_lemma, zle_zless_trans])));
qed "zmod_pos_neg_trivial_raw";

Goal "[| #0 $< a;  a$+b $<= #0 |] ==> a zmod b = a$+b";
by (cut_inst_tac [("a", "intify(a)"), ("b", "intify(b)")]
    zmod_pos_neg_trivial_raw 1);
by Auto_tac;  
qed "zmod_pos_neg_trivial";

(*There is no zmod_neg_pos_trivial...*)


(*Simpler laws such as -a zdiv b = -(a zdiv b) FAIL*)

Goal "[|a \\<in> int;  b \\<in> int|] ==> ($-a) zdiv ($-b) = a zdiv b";
by (zdiv_undefined_case_tac "b = #0" 1);
by (stac ((simplify(simpset()) (quorem_div_mod RS quorem_neg)) 
	  RS quorem_div) 1);
by Auto_tac;
qed "zdiv_zminus_zminus_raw";

Goal "($-a) zdiv ($-b) = a zdiv b";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)")] 
    zdiv_zminus_zminus_raw 1);
by Auto_tac;  
qed "zdiv_zminus_zminus";
Addsimps [zdiv_zminus_zminus];

(*Simpler laws such as -a zmod b = -(a zmod b) FAIL*)
Goal "[|a \\<in> int;  b \\<in> int|] ==> ($-a) zmod ($-b) = $- (a zmod b)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (stac ((simplify(simpset()) (quorem_div_mod RS quorem_neg)) 
	  RS quorem_mod) 1);
by Auto_tac;
qed "zmod_zminus_zminus_raw";

Goal "($-a) zmod ($-b) = $- (a zmod b)";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)")] 
    zmod_zminus_zminus_raw 1);
by Auto_tac;  
qed "zmod_zminus_zminus";
Addsimps [zmod_zminus_zminus];


(*** division of a number by itself ***)

Goal "[| #0 $< a; a = r $+ a$*q; r $< a |] ==> #1 $<= q";
by (subgoal_tac "#0 $< a$*q" 1);
by (cut_inst_tac [("w","#0"),("z","q")] add1_zle_iff 1);
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 1);
by (blast_tac (claset() addDs [zless_trans]) 1);
(*linear arithmetic...*)
by (dres_inst_tac [("t","%x. x $- r")] subst_context 1);
by (dtac sym 1);  
by (asm_full_simp_tac (simpset() addsimps zcompare_rls) 1); 
val lemma1 = result();

Goal "[| #0 $< a; a = r $+ a$*q; #0 $<= r |] ==> q $<= #1";
by (subgoal_tac "#0 $<= a$*(#1$-q)" 1);
by (asm_simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 2);
by (dres_inst_tac [("t","%x. x $- a $* q")] subst_context 2);
by (asm_full_simp_tac (simpset() addsimps zcompare_rls) 2); 
by (asm_full_simp_tac (simpset() addsimps int_0_le_mult_iff::zcompare_rls) 1); 
by (blast_tac (claset() addDs [zle_zless_trans]) 1);
val lemma2 = result();

Goal "[| quorem(<a,a>,<q,r>);  a \\<in> int;  q \\<in> int;  a \\<noteq> #0|] ==> q = #1";
by (asm_full_simp_tac 
    (simpset() addsimps split_ifs@[quorem_def, neq_iff_zless]) 1);
by (rtac zle_anti_sym 1);
by Safe_tac;
by Auto_tac;
by (blast_tac (claset() addDs [zless_trans]) 4); 
by (blast_tac (claset() addDs [zless_trans]) 1);
by (res_inst_tac [("a", "$-a"),("r", "$-r")] lemma1 3);
by (res_inst_tac [("a", "$-a"),("r", "$-r")] lemma2 1);
by (rtac (zminus_equation RS iffD1) 6); 
by (rtac (zminus_equation RS iffD1) 2); 
by (REPEAT (force_tac  (claset() addIs [lemma1,lemma2], 
	      simpset() addsimps [zadd_commute, zmult_zminus]) 1));
qed "self_quotient";

Goal "[|quorem(<a,a>,<q,r>); a \\<in> int; q \\<in> int; r \\<in> int; a \\<noteq> #0|] ==> r = #0";
by (ftac self_quotient 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));  
qed "self_remainder";

Goal "[|a \\<noteq> #0; a \\<in> int|] ==> a zdiv a = #1";
by (blast_tac (claset() addIs [quorem_div_mod RS self_quotient]) 1); 
qed "zdiv_self_raw";

Goal "intify(a) \\<noteq> #0 ==> a zdiv a = #1";
by (dtac zdiv_self_raw 1); 
by Auto_tac;  
qed "zdiv_self";
Addsimps [zdiv_self];

(*Here we have 0 zmod 0 = 0, also assumed by Knuth (who puts m zmod 0 = 0) *)
Goal "a \\<in> int ==> a zmod a = #0";
by (zdiv_undefined_case_tac "a = #0" 1);
by (blast_tac (claset() addIs [quorem_div_mod RS self_remainder]) 1); 
qed "zmod_self_raw";

Goal "a zmod a = #0";
by (cut_inst_tac [("a","intify(a)")] zmod_self_raw 1);
by Auto_tac;  
qed "zmod_self";
Addsimps [zmod_self];


(*** Computation of division and remainder ***)

Goal "#0 zdiv b = #0";
by (simp_tac (simpset() addsimps [zdiv_def, divAlg_def]) 1);
qed "zdiv_zero";

Goal "#0 $< b ==> #-1 zdiv b = #-1";
by (asm_simp_tac (simpset() addsimps [zdiv_def, divAlg_def]) 1);
qed "zdiv_eq_minus1";

Goal "#0 zmod b = #0";
by (simp_tac (simpset() addsimps [zmod_def, divAlg_def]) 1);
qed "zmod_zero";

Addsimps [zdiv_zero, zmod_zero];

Goal "#0 $< b ==> #-1 zdiv b = #-1";
by (asm_simp_tac (simpset() addsimps [zdiv_def, divAlg_def]) 1);
qed "zdiv_minus1";

Goal "#0 $< b ==> #-1 zmod b = b $- #1";
by (asm_simp_tac (simpset() addsimps [zmod_def, divAlg_def]) 1);
qed "zmod_minus1";

(** a positive, b positive **)

Goal "[| #0 $< a;  #0 $<= b |] \
\     ==> a zdiv b = fst (posDivAlg(<intify(a), intify(b)>))";
by (asm_simp_tac (simpset() addsimps [zdiv_def, divAlg_def]) 1);
by (auto_tac (claset(), simpset() addsimps [zle_def]));  
qed "zdiv_pos_pos";

Goal "[| #0 $< a;  #0 $<= b |] \
\     ==> a zmod b = snd (posDivAlg(<intify(a), intify(b)>))";
by (asm_simp_tac (simpset() addsimps [zmod_def, divAlg_def]) 1);
by (auto_tac (claset(), simpset() addsimps [zle_def]));  
qed "zmod_pos_pos";

(** a negative, b positive **)

Goal "[| a $< #0;  #0 $< b |] \
\     ==> a zdiv b = fst (negDivAlg(<intify(a), intify(b)>))";
by (asm_simp_tac (simpset() addsimps [zdiv_def, divAlg_def]) 1);
by (blast_tac (claset() addDs [zle_zless_trans]) 1);
qed "zdiv_neg_pos";

Goal "[| a $< #0;  #0 $< b |] \
\     ==> a zmod b = snd (negDivAlg(<intify(a), intify(b)>))";
by (asm_simp_tac (simpset() addsimps [zmod_def, divAlg_def]) 1);
by (blast_tac (claset() addDs [zle_zless_trans]) 1);
qed "zmod_neg_pos";

(** a positive, b negative **)

Goal "[| #0 $< a;  b $< #0 |] \
\     ==> a zdiv b = fst (negateSnd(negDivAlg (<$-a, $-b>)))";
by (asm_simp_tac
    (simpset() addsimps [zdiv_def, divAlg_def, intify_eq_0_iff_zle]) 1);
by Auto_tac;  
by (REPEAT (blast_tac (claset() addDs [zle_zless_trans]) 1));
by (blast_tac (claset() addDs [zless_trans]) 1);
by (blast_tac (claset() addIs [zless_imp_zle]) 1); 
qed "zdiv_pos_neg";

Goal "[| #0 $< a;  b $< #0 |] \
\     ==> a zmod b = snd (negateSnd(negDivAlg (<$-a, $-b>)))";
by (asm_simp_tac 
    (simpset() addsimps [zmod_def, divAlg_def, intify_eq_0_iff_zle]) 1);
by Auto_tac;  
by (REPEAT (blast_tac (claset() addDs [zle_zless_trans]) 1));
by (blast_tac (claset() addDs [zless_trans]) 1);
by (blast_tac (claset() addIs [zless_imp_zle]) 1); 
qed "zmod_pos_neg";

(** a negative, b negative **)

Goal "[| a $< #0;  b $<= #0 |] \
\     ==> a zdiv b = fst (negateSnd(posDivAlg(<$-a, $-b>)))";
by (asm_simp_tac (simpset() addsimps [zdiv_def, divAlg_def]) 1);
by Auto_tac;  
by (REPEAT (blast_tac (claset() addSDs [zle_zless_trans]) 1));
qed "zdiv_neg_neg";

Goal "[| a $< #0;  b $<= #0 |] \
\     ==> a zmod b = snd (negateSnd(posDivAlg(<$-a, $-b>)))";
by (asm_simp_tac (simpset() addsimps [zmod_def, divAlg_def]) 1);
by Auto_tac;  
by (REPEAT (blast_tac (claset() addSDs [zle_zless_trans]) 1));
qed "zmod_neg_neg";

Addsimps (map (read_instantiate_sg (sign_of (the_context ()))
	       [("a", "integ_of (?v)"), ("b", "integ_of (?w)")])
	  [zdiv_pos_pos, zdiv_neg_pos, zdiv_pos_neg, zdiv_neg_neg,
	   zmod_pos_pos, zmod_neg_pos, zmod_pos_neg, zmod_neg_neg,
	   posDivAlg_eqn, negDivAlg_eqn]);


(** Special-case simplification **)

Goal "a zmod #1 = #0";
by (cut_inst_tac [("a","a"),("b","#1")] pos_mod_sign 1);
by (cut_inst_tac [("a","a"),("b","#1")] pos_mod_bound 2);
by Auto_tac;
(*arithmetic*)
by (dtac (add1_zle_iff RS iffD2) 1);
by (rtac zle_anti_sym 1); 
by Auto_tac;  
qed "zmod_1";
Addsimps [zmod_1];

Goal "a zdiv #1 = intify(a)";
by (cut_inst_tac [("a","a"),("b","#1")] zmod_zdiv_equality 1);
by Auto_tac;
qed "zdiv_1";
Addsimps [zdiv_1];

Goal "a zmod #-1 = #0";
by (cut_inst_tac [("a","a"),("b","#-1")] neg_mod_sign 1);
by (cut_inst_tac [("a","a"),("b","#-1")] neg_mod_bound 2);
by Auto_tac;
(*arithmetic*)
by (dtac (add1_zle_iff RS iffD2) 1);
by (rtac zle_anti_sym 1); 
by Auto_tac;  
qed "zmod_minus1_right";
Addsimps [zmod_minus1_right];

Goal "a \\<in> int ==> a zdiv #-1 = $-a";
by (cut_inst_tac [("a","a"),("b","#-1")] zmod_zdiv_equality 1);
by Auto_tac;
by (rtac (equation_zminus RS iffD2) 1); 
by Auto_tac;  
qed "zdiv_minus1_right_raw";

Goal "a zdiv #-1 = $-a";
by (cut_inst_tac [("a","intify(a)")] zdiv_minus1_right_raw 1);
by Auto_tac;
qed "zdiv_minus1_right";
Addsimps [zdiv_minus1_right];


(*** Monotonicity in the first argument (divisor) ***)

Goal "[| a $<= a';  #0 $< b |] ==> a zdiv b $<= a' zdiv b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a'"),("b","b")] zmod_zdiv_equality 1);
by (rtac unique_quotient_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono1";

Goal "[| a $<= a';  b $< #0 |] ==> a' zdiv b $<= a zdiv b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a'"),("b","b")] zmod_zdiv_equality 1);
by (rtac unique_quotient_lemma_neg 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [neg_mod_sign,neg_mod_bound])));
qed "zdiv_mono1_neg";


(*** Monotonicity in the second argument (dividend) ***)

Goal "[| b$*q $+ r = b'$*q' $+ r';  #0 $<= b'$*q' $+ r';  \
\        r' $< b';  #0 $<= r;  #0 $< b';  b' $<= b |]  \
\     ==> q $<= q'";
by (subgoal_tac "#0 $<= q'" 1);
 by (subgoal_tac "#0 $< b'$*(q' $+ #1)" 2);
  by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 3);
  by (etac zle_zless_trans 3); 
  by (etac zadd_zless_mono2 3);
 by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 2);
 by (blast_tac (claset() addDs [zless_trans]
                         addIs  [zless_add1_iff_zle RS iffD1]) 2);
by (subgoal_tac "b$*q $< b$*(q' $+ #1)" 1);
 by (asm_full_simp_tac (simpset() addsimps [zmult_zless_cancel1]) 1);
 by (force_tac (claset() addDs  [zless_add1_iff_zle RS iffD1,
                                 zless_trans, zless_zle_trans], 
                simpset()) 1); 
by (subgoal_tac "b$*q = r' $- r $+ b'$*q'" 1);
 by (asm_simp_tac (simpset() addsimps zcompare_rls) 2); 
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
by (stac zadd_commute 1 THEN rtac zadd_zless_mono 1);
 by (blast_tac (claset() addIs [zmult_zle_mono1]) 2);
by (subgoal_tac "r' $+ #0 $< b $+ r" 1);
 by (asm_full_simp_tac (simpset() addsimps zcompare_rls) 1); 
by (rtac zadd_zless_mono 1); 
 by Auto_tac;  
by (blast_tac (claset() addDs [zless_zle_trans]) 1); 
qed "zdiv_mono2_lemma";

Goal "[| #0 $<= a;  #0 $< b';  b' $<= b;  a \\<in> int |]  \
\     ==> a zdiv b $<= a zdiv b'";
by (subgoal_tac "#0 $< b" 1);
 by (blast_tac (claset() addDs [zless_zle_trans]) 2); 
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a"),("b","b'")] zmod_zdiv_equality 1);
by (rtac zdiv_mono2_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS
    (asm_full_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono2_raw";

Goal "[| #0 $<= a;  #0 $< b';  b' $<= b |]  \
\     ==> a zdiv b $<= a zdiv b'";
by (cut_inst_tac [("a","intify(a)")] zdiv_mono2_raw 1);
by Auto_tac;  
qed "zdiv_mono2";

Goal "[| b$*q $+ r = b'$*q' $+ r';  b'$*q' $+ r' $< #0;  \
\        r $< b;  #0 $<= r';  #0 $< b';  b' $<= b |]  \
\     ==> q' $<= q";
by (subgoal_tac "#0 $< b" 1);
 by (blast_tac (claset() addDs [zless_zle_trans]) 2); 
by (subgoal_tac "q' $< #0" 1);
 by (subgoal_tac "b'$*q' $< #0" 2);
  by (force_tac (claset() addIs [zle_zless_trans], simpset()) 3); 
 by (asm_full_simp_tac (simpset() addsimps [zmult_less_0_iff]) 2);
 by (blast_tac (claset() addDs [zless_trans]) 2);
by (subgoal_tac "b$*q' $< b$*(q $+ #1)" 1);
 by (asm_full_simp_tac (simpset() addsimps [zmult_zless_cancel1]) 1);
 by (blast_tac (claset() addDs [zless_trans, zless_add1_iff_zle RS iffD1]) 1);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
by (subgoal_tac "b$*q' $<= b'$*q'" 1);
 by (asm_simp_tac (simpset() addsimps [zmult_zle_cancel2]) 2);
 by (blast_tac (claset() addDs [zless_trans]) 2);
by (subgoal_tac "b'$*q' $+ r $< b $+ (b$*q $+ r)" 1);
 by (etac ssubst 2);
 by (Asm_simp_tac 2);
 by (dres_inst_tac [("w'","r"),("z'","#0")] zadd_zless_mono 2);
  by (assume_tac 2);
 by (Asm_full_simp_tac 2);
by (full_simp_tac (simpset() addsimps [zadd_commute]) 1); 
by (rtac zle_zless_trans 1); 
by (assume_tac 2);
 by (asm_simp_tac (simpset() addsimps [zmult_zle_cancel2]) 1);
by (blast_tac (claset() addDs [zless_trans]) 1);
qed "zdiv_mono2_neg_lemma";

Goal "[| a $< #0;  #0 $< b';  b' $<= b;  a \\<in> int |]  \
\     ==> a zdiv b' $<= a zdiv b";
by (subgoal_tac "#0 $< b" 1);
 by (blast_tac (claset() addDs [zless_zle_trans]) 2); 
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a"),("b","b'")] zmod_zdiv_equality 1);
by (rtac zdiv_mono2_neg_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS
    (asm_full_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono2_neg_raw";

Goal "[| a $< #0;  #0 $< b';  b' $<= b |]  \
\     ==> a zdiv b' $<= a zdiv b";
by (cut_inst_tac [("a","intify(a)")] zdiv_mono2_neg_raw 1);
by Auto_tac;  
qed "zdiv_mono2_neg";



(*** More algebraic laws for zdiv and zmod ***)

(** proving (a*b) zdiv c = a $* (b zdiv c) $+ a * (b zmod c) **)

Goal "[| quorem(<b,c>, <q,r>);  c \\<in> int;  c \\<noteq> #0 |] \
\     ==> quorem (<a$*b, c>, <a$*q $+ (a$*r) zdiv c, (a$*r) zmod c>)";
by (auto_tac
    (claset(),
     simpset() addsimps split_ifs@
			[quorem_def, neq_iff_zless, 
			 zadd_zmult_distrib2,
			 pos_mod_sign,pos_mod_bound,
			 neg_mod_sign, neg_mod_bound]));
by (ALLGOALS (rtac raw_zmod_zdiv_equality));
by Auto_tac;  
qed "zmult1_lemma";

Goal "[|b \\<in> int;  c \\<in> int|] \
\     ==> (a$*b) zdiv c = a$*(b zdiv c) $+ a$*(b zmod c) zdiv c";
by (zdiv_undefined_case_tac "c = #0" 1);
by (rtac (quorem_div_mod RS zmult1_lemma RS quorem_div) 1); 
by Auto_tac;  
qed "zdiv_zmult1_eq_raw";

Goal "(a$*b) zdiv c = a$*(b zdiv c) $+ a$*(b zmod c) zdiv c";
by (cut_inst_tac [("b","intify(b)"), ("c","intify(c)")] zdiv_zmult1_eq_raw 1);
by Auto_tac;  
qed "zdiv_zmult1_eq";

Goal "[|b \\<in> int;  c \\<in> int|] ==> (a$*b) zmod c = a$*(b zmod c) zmod c";
by (zdiv_undefined_case_tac "c = #0" 1);
by (rtac (quorem_div_mod RS zmult1_lemma RS quorem_mod) 1); 
by Auto_tac;  
qed "zmod_zmult1_eq_raw";

Goal "(a$*b) zmod c = a$*(b zmod c) zmod c";
by (cut_inst_tac [("b","intify(b)"), ("c","intify(c)")] zmod_zmult1_eq_raw 1);
by Auto_tac;  
qed "zmod_zmult1_eq";

Goal "(a$*b) zmod c = ((a zmod c) $* b) zmod c";
by (rtac trans 1);
by (res_inst_tac [("b", "(b $* a) zmod c")] trans 1);
by (rtac zmod_zmult1_eq 2);
by (ALLGOALS (simp_tac (simpset() addsimps [zmult_commute])));
qed "zmod_zmult1_eq'";

Goal "(a$*b) zmod c = ((a zmod c) $* (b zmod c)) zmod c";
by (rtac (zmod_zmult1_eq' RS trans) 1);
by (rtac zmod_zmult1_eq 1);
qed "zmod_zmult_distrib";

Goal "intify(b) \\<noteq> #0 ==> (a$*b) zdiv b = intify(a)";
by (asm_simp_tac (simpset() addsimps [zdiv_zmult1_eq]) 1);
qed "zdiv_zmult_self1";
Addsimps [zdiv_zmult_self1];

Goal "intify(b) \\<noteq> #0 ==> (b$*a) zdiv b = intify(a)";
by (stac zmult_commute 1 THEN etac zdiv_zmult_self1 1);
qed "zdiv_zmult_self2";
Addsimps [zdiv_zmult_self2];

Goal "(a$*b) zmod b = #0";
by (simp_tac (simpset() addsimps [zmod_zmult1_eq]) 1);
qed "zmod_zmult_self1";
Addsimps [zmod_zmult_self1];

Goal "(b$*a) zmod b = #0";
by (simp_tac (simpset() addsimps [zmult_commute, zmod_zmult1_eq]) 1);
qed "zmod_zmult_self2";
Addsimps [zmod_zmult_self2];


(** proving (a$+b) zdiv c = 
            a zdiv c $+ b zdiv c $+ ((a zmod c $+ b zmod c) zdiv c) **)

Goal "[| quorem(<a,c>, <aq,ar>);  quorem(<b,c>, <bq,br>);  \
\        c \\<in> int;  c \\<noteq> #0 |] \
\     ==> quorem (<a$+b, c>, <aq $+ bq $+ (ar$+br) zdiv c, (ar$+br) zmod c>)";
by (auto_tac
    (claset(),
     simpset() addsimps split_ifs@
			[quorem_def, neq_iff_zless, 
			 zadd_zmult_distrib2,
			 pos_mod_sign,pos_mod_bound,
			 neg_mod_sign, neg_mod_bound]));
by (ALLGOALS (rtac raw_zmod_zdiv_equality));
by Auto_tac;  
val zadd1_lemma = result();

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
Goal "[|a \\<in> int; b \\<in> int; c \\<in> int|] ==> \
\     (a$+b) zdiv c = a zdiv c $+ b zdiv c $+ ((a zmod c $+ b zmod c) zdiv c)";
by (zdiv_undefined_case_tac "c = #0" 1);
by (blast_tac (claset() addIs [[quorem_div_mod,quorem_div_mod]
			       MRS zadd1_lemma RS quorem_div]) 1);
qed "zdiv_zadd1_eq_raw";

Goal "(a$+b) zdiv c = a zdiv c $+ b zdiv c $+ ((a zmod c $+ b zmod c) zdiv c)";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)"), ("c","intify(c)")] 
    zdiv_zadd1_eq_raw 1);
by Auto_tac;  
qed "zdiv_zadd1_eq";

Goal "[|a \\<in> int; b \\<in> int; c \\<in> int|]  \
\     ==> (a$+b) zmod c = (a zmod c $+ b zmod c) zmod c";
by (zdiv_undefined_case_tac "c = #0" 1);
by (blast_tac (claset() addIs [[quorem_div_mod,quorem_div_mod]
			       MRS zadd1_lemma RS quorem_mod]) 1);
qed "zmod_zadd1_eq_raw";

Goal "(a$+b) zmod c = (a zmod c $+ b zmod c) zmod c";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)"), ("c","intify(c)")] 
    zmod_zadd1_eq_raw 1);
by Auto_tac;  
qed "zmod_zadd1_eq";

Goal "[|a \\<in> int; b \\<in> int|] ==> (a zmod b) zdiv b = #0";
by (zdiv_undefined_case_tac "b = #0" 1);
by (auto_tac (claset(), 
      simpset() addsimps [neq_iff_zless, 
			  pos_mod_sign, pos_mod_bound, zdiv_pos_pos_trivial, 
			  neg_mod_sign, neg_mod_bound, zdiv_neg_neg_trivial]));
qed "zmod_div_trivial_raw";

Goal "(a zmod b) zdiv b = #0";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)")]
    zmod_div_trivial_raw 1);
by Auto_tac;  
qed "zmod_div_trivial";
Addsimps [zmod_div_trivial];

Goal "[|a \\<in> int; b \\<in> int|] ==> (a zmod b) zmod b = a zmod b";
by (zdiv_undefined_case_tac "b = #0" 1);
by (auto_tac (claset(), 
       simpset() addsimps [neq_iff_zless, 
			   pos_mod_sign, pos_mod_bound, zmod_pos_pos_trivial, 
			   neg_mod_sign, neg_mod_bound, zmod_neg_neg_trivial]));
qed "zmod_mod_trivial_raw";

Goal "(a zmod b) zmod b = a zmod b";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)")]
    zmod_mod_trivial_raw 1);
by Auto_tac;  
qed "zmod_mod_trivial";
Addsimps [zmod_mod_trivial];

Goal "(a$+b) zmod c = ((a zmod c) $+ b) zmod c";
by (rtac (trans RS sym) 1);
by (rtac zmod_zadd1_eq 1);
by (Simp_tac 1);
by (rtac (zmod_zadd1_eq RS sym) 1);
qed "zmod_zadd_left_eq";

Goal "(a$+b) zmod c = (a $+ (b zmod c)) zmod c";
by (rtac (trans RS sym) 1);
by (rtac zmod_zadd1_eq 1);
by (Simp_tac 1);
by (rtac (zmod_zadd1_eq RS sym) 1);
qed "zmod_zadd_right_eq";


Goal "intify(a) \\<noteq> #0 ==> (a$+b) zdiv a = b zdiv a $+ #1";
by (asm_simp_tac (simpset() addsimps [zdiv_zadd1_eq]) 1);
qed "zdiv_zadd_self1";
Addsimps [zdiv_zadd_self1];

Goal "intify(a) \\<noteq> #0 ==> (b$+a) zdiv a = b zdiv a $+ #1";
by (asm_simp_tac (simpset() addsimps [zdiv_zadd1_eq]) 1);
qed "zdiv_zadd_self2";
Addsimps [zdiv_zadd_self2];

Goal "(a$+b) zmod a = b zmod a";
by (zdiv_undefined_case_tac "a = #0" 1);
by (asm_simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1);
qed "zmod_zadd_self1";

Goal "(b$+a) zmod a = b zmod a";
by (zdiv_undefined_case_tac "a = #0" 1);
by (asm_simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1);
qed "zmod_zadd_self2";
Addsimps [zmod_zadd_self1, zmod_zadd_self2];


(*** proving  a zdiv (b*c) = (a zdiv b) zdiv c ***)

(*The condition c>0 seems necessary.  Consider that 7 zdiv ~6 = ~2 but
  7 zdiv 2 zdiv ~3 = 3 zdiv ~3 = ~1.  The subcase (a zdiv b) zmod c = 0 seems
  to cause particular problems.*)

(** first, four lemmas to bound the remainder for the cases b<0 and b>0 **)

Goal "[| #0 $< c;  b $< r;  r $<= #0 |] ==> b$*c $< b$*(q zmod c) $+ r";
by (subgoal_tac "b $* (c $- q zmod c) $< r $* #1" 1);
by (asm_full_simp_tac
    (simpset() addsimps [zdiff_zmult_distrib2, zadd_commute]@zcompare_rls) 1);
by (rtac zle_zless_trans 1);
by (etac zmult_zless_mono1 2);
by (rtac zmult_zle_mono2_neg 1);
by (auto_tac
    (claset(),
     simpset() addsimps zcompare_rls@
			[zadd_commute, add1_zle_iff, pos_mod_bound]));
by (blast_tac (claset() addIs [zless_imp_zle]
			addDs [zless_zle_trans]) 1);
val lemma1 = result();

Goal "[| #0 $< c;   b $< r;  r $<= #0 |] ==> b $* (q zmod c) $+ r $<= #0";
by (subgoal_tac "b $* (q zmod c) $<= #0" 1);
by (asm_simp_tac (simpset() addsimps [zmult_le_0_iff, pos_mod_sign]) 2);
by (blast_tac (claset() addIs [zless_imp_zle]
			addDs [zless_zle_trans]) 2);
(*arithmetic*)
by (dtac zadd_zle_mono 1); 
by (assume_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [zadd_commute]) 1); 
val lemma2 = result();

Goal "[| #0 $< c;  #0 $<= r;  r $< b |] ==> #0 $<= b $* (q zmod c) $+ r";
by (subgoal_tac "#0 $<= b $* (q zmod c)" 1);
by (asm_simp_tac (simpset() addsimps [int_0_le_mult_iff, pos_mod_sign]) 2);
by (blast_tac (claset() addIs [zless_imp_zle]
			addDs [zle_zless_trans]) 2);
(*arithmetic*)
by (dtac zadd_zle_mono 1); 
by (assume_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [zadd_commute]) 1); 
val lemma3 = result();

Goal "[| #0 $< c; #0 $<= r; r $< b |] ==> b $* (q zmod c) $+ r $< b $* c";
by (subgoal_tac "r $* #1 $< b $* (c $- q zmod c)" 1);
by (asm_full_simp_tac
    (simpset() addsimps [zdiff_zmult_distrib2, zadd_commute]@zcompare_rls) 1);
by (rtac zless_zle_trans 1);
by (etac zmult_zless_mono1 1);
by (rtac zmult_zle_mono2 2);
by (auto_tac
    (claset(),
     simpset() addsimps zcompare_rls@
			[zadd_commute, add1_zle_iff, pos_mod_bound]));
by (blast_tac (claset() addIs [zless_imp_zle]
			addDs [zle_zless_trans]) 1);
val lemma4 = result();

Goal "[| quorem (<a,b>, <q,r>);  a \\<in> int;  b \\<in> int;  b \\<noteq> #0;  #0 $< c |] \
\     ==> quorem (<a,b$*c>, <q zdiv c, b$*(q zmod c) $+ r>)";
by (auto_tac  
    (claset(),
     simpset() addsimps zmult_ac@
			[zmod_zdiv_equality RS sym, quorem_def, neq_iff_zless,
			 int_0_less_mult_iff,
			 zadd_zmult_distrib2 RS sym,
			 lemma1, lemma2, lemma3, lemma4]));
by (ALLGOALS (blast_tac (claset() addDs [zless_trans])));
val lemma = result();

Goal "[|#0 $< c;  a \\<in> int;  b \\<in> int|] ==> a zdiv (b$*c) = (a zdiv b) zdiv c";
by (zdiv_undefined_case_tac "b = #0" 1);
by (rtac (quorem_div_mod RS lemma RS quorem_div) 1);
by (auto_tac (claset(), simpset() addsimps [intify_eq_0_iff_zle]));
by (blast_tac (claset() addDs [zle_zless_trans]) 1);
qed "zdiv_zmult2_eq_raw";

Goal "#0 $< c ==> a zdiv (b$*c) = (a zdiv b) zdiv c";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)")]
    zdiv_zmult2_eq_raw 1);
by Auto_tac;  
qed "zdiv_zmult2_eq";

Goal "[|#0 $< c;  a \\<in> int;  b \\<in> int|] \
\     ==> a zmod (b$*c) = b$*(a zdiv b zmod c) $+ a zmod b";
by (zdiv_undefined_case_tac "b = #0" 1);
by (rtac (quorem_div_mod RS lemma RS quorem_mod) 1);
by (auto_tac (claset(), simpset() addsimps [intify_eq_0_iff_zle]));
by (blast_tac (claset() addDs [zle_zless_trans]) 1);
qed "zmod_zmult2_eq_raw";

Goal "#0 $< c ==> a zmod (b$*c) = b$*(a zdiv b zmod c) $+ a zmod b";
by (cut_inst_tac [("a","intify(a)"), ("b","intify(b)")]
    zmod_zmult2_eq_raw 1);
by Auto_tac;  
qed "zmod_zmult2_eq";

(*** Cancellation of common factors in "zdiv" ***)

Goal "[| #0 $< b;  intify(c) \\<noteq> #0 |] ==> (c$*a) zdiv (c$*b) = a zdiv b";
by (stac zdiv_zmult2_eq 1);
by Auto_tac;
val lemma1 = result();

Goal "[| b $< #0;  intify(c) \\<noteq> #0 |] ==> (c$*a) zdiv (c$*b) = a zdiv b";
by (subgoal_tac "(c $* ($-a)) zdiv (c $* ($-b)) = ($-a) zdiv ($-b)" 1);
by (rtac lemma1 2);
by Auto_tac;
val lemma2 = result();

Goal "[|intify(c) \\<noteq> #0; b \\<in> int|] ==> (c$*a) zdiv (c$*b) = a zdiv b";
by (zdiv_undefined_case_tac "b = #0" 1);
by (auto_tac
    (claset(), 
     simpset() addsimps [read_instantiate [("x", "b")] neq_iff_zless, 
			 lemma1, lemma2]));
qed "zdiv_zmult_zmult1_raw";

Goal "intify(c) \\<noteq> #0 ==> (c$*a) zdiv (c$*b) = a zdiv b";
by (cut_inst_tac [("b","intify(b)")] zdiv_zmult_zmult1_raw 1);
by Auto_tac;  
qed "zdiv_zmult_zmult1";

Goal "intify(c) \\<noteq> #0 ==> (a$*c) zdiv (b$*c) = a zdiv b";
by (dtac zdiv_zmult_zmult1 1);
by (auto_tac (claset(), simpset() addsimps [zmult_commute]));
qed "zdiv_zmult_zmult2";


(*** Distribution of factors over "zmod" ***)

Goal "[| #0 $< b;  intify(c) \\<noteq> #0 |] \
\     ==> (c$*a) zmod (c$*b) = c $* (a zmod b)";
by (stac zmod_zmult2_eq 1);
by Auto_tac;
val lemma1 = result();

Goal "[| b $< #0;  intify(c) \\<noteq> #0 |] \
\     ==> (c$*a) zmod (c$*b) = c $* (a zmod b)";
by (subgoal_tac "(c $* ($-a)) zmod (c $* ($-b)) = c $* (($-a) zmod ($-b))" 1);
by (rtac lemma1 2);
by Auto_tac;
val lemma2 = result();

Goal "[|b \\<in> int; c \\<in> int|] ==> (c$*a) zmod (c$*b) = c $* (a zmod b)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (zdiv_undefined_case_tac "c = #0" 1);
by (auto_tac
    (claset(), 
     simpset() addsimps [read_instantiate [("x", "b")] neq_iff_zless, 
			 lemma1, lemma2]));
qed "zmod_zmult_zmult1_raw";

Goal "(c$*a) zmod (c$*b) = c $* (a zmod b)";
by (cut_inst_tac [("b","intify(b)"),("c","intify(c)")] 
    zmod_zmult_zmult1_raw 1);
by Auto_tac;  
qed "zmod_zmult_zmult1";

Goal "(a$*c) zmod (b$*c) = (a zmod b) $* c";
by (cut_inst_tac [("c","c")] zmod_zmult_zmult1 1);
by (auto_tac (claset(), simpset() addsimps [zmult_commute]));
qed "zmod_zmult_zmult2";


(** Quotients of signs **)

Goal "[| a $< #0;  #0 $< b |] ==> a zdiv b $< #0";
by (subgoal_tac "a zdiv b $<= #-1" 1);
by (etac zle_zless_trans 1); 
by (Simp_tac 1); 
by (rtac zle_trans 1);
by (res_inst_tac [("a'","#-1")]  zdiv_mono1 1);
by (rtac (zless_add1_iff_zle RS iffD1) 1); 
by (Simp_tac 1); 
by (auto_tac (claset(), simpset() addsimps [zdiv_minus1]));
qed "zdiv_neg_pos_less0";

Goal "[| #0 $<= a;  b $< #0 |] ==> a zdiv b $<= #0";
by (dtac zdiv_mono1_neg 1);
by Auto_tac;
qed "zdiv_nonneg_neg_le0";

Goal "#0 $< b ==> (#0 $<= a zdiv b) <-> (#0 $<= a)";
by Auto_tac;
by (dtac zdiv_mono1 2);
by (auto_tac (claset(), simpset() addsimps [neq_iff_zless]));
by (full_simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 1);
by (blast_tac (claset() addIs [zdiv_neg_pos_less0]) 1);
qed "pos_imp_zdiv_nonneg_iff";

Goal "b $< #0 ==> (#0 $<= a zdiv b) <-> (a $<= #0)";
by (stac (zdiv_zminus_zminus RS sym) 1);
by (rtac iff_trans 1); 
by (rtac pos_imp_zdiv_nonneg_iff 1); 
by Auto_tac;
qed "neg_imp_zdiv_nonneg_iff";

(*But not (a zdiv b $<= 0 iff a$<=0); consider a=1, b=2 when a zdiv b = 0.*)
Goal "#0 $< b ==> (a zdiv b $< #0) <-> (a $< #0)";
by (asm_simp_tac (simpset() addsimps [not_zle_iff_zless RS iff_sym]) 1);
by (etac pos_imp_zdiv_nonneg_iff 1); 
qed "pos_imp_zdiv_neg_iff";

(*Again the law fails for $<=: consider a = -1, b = -2 when a zdiv b = 0*)
Goal "b $< #0 ==> (a zdiv b $< #0) <-> (#0 $< a)";
by (asm_simp_tac (simpset() addsimps [not_zle_iff_zless RS iff_sym]) 1);
by (etac neg_imp_zdiv_nonneg_iff 1); 
qed "neg_imp_zdiv_neg_iff";

(*
 THESE REMAIN TO BE CONVERTED -- but aren't that useful!

 (*** Speeding up the division algorithm with shifting ***)

 (** computing "zdiv" by shifting **)

 Goal "#0 $<= a ==> (#1 $+ #2$*b) zdiv (#2$*a) = b zdiv a";
 by (zdiv_undefined_case_tac "a = #0" 1);
 by (subgoal_tac "#1 $<= a" 1);
  by (arith_tac 2);
 by (subgoal_tac "#1 $< a $* #2" 1);
  by (arith_tac 2);
 by (subgoal_tac "#2$*(#1 $+ b zmod a) $<= #2$*a" 1);
  by (rtac zmult_zle_mono2 2);
 by (auto_tac (claset(),
	       simpset() addsimps [zadd_commute, zmult_commute, 
				   add1_zle_iff, pos_mod_bound]));
 by (stac zdiv_zadd1_eq 1);
 by (asm_simp_tac (simpset() addsimps [zdiv_zmult_zmult2, zmod_zmult_zmult2, 
				       zdiv_pos_pos_trivial]) 1);
 by (stac zdiv_pos_pos_trivial 1);
 by (asm_simp_tac (simpset() 
	    addsimps [zmod_pos_pos_trivial,
		     pos_mod_sign RS zadd_zle_mono1 RSN (2,zle_trans)]) 1);
 by (auto_tac (claset(),
	       simpset() addsimps [zmod_pos_pos_trivial]));
 by (subgoal_tac "#0 $<= b zmod a" 1);
  by (asm_simp_tac (simpset() addsimps [pos_mod_sign]) 2);
 by (arith_tac 1);
 qed "pos_zdiv_mult_2";


 Goal "a $<= #0 ==> (#1 $+ #2$*b) zdiv (#2$*a) <-> (b$+#1) zdiv a";
 by (subgoal_tac "(#1 $+ #2$*($-b-#1)) zdiv (#2 $* ($-a)) <-> ($-b-#1) zdiv ($-a)" 1);
 by (rtac pos_zdiv_mult_2 2);
 by (auto_tac (claset(),
	       simpset() addsimps [zmult_zminus_right]));
 by (subgoal_tac "(#-1 - (#2 $* b)) = - (#1 $+ (#2 $* b))" 1);
 by (Simp_tac 2);
 by (asm_full_simp_tac (HOL_ss
			addsimps [zdiv_zminus_zminus, zdiff_def,
				  zminus_zadd_distrib RS sym]) 1);
 qed "neg_zdiv_mult_2";


 (*Not clear why this must be proved separately; probably integ_of causes
   simplification problems*)
 Goal "~ #0 $<= x ==> x $<= #0";
 by Auto_tac;
 val lemma = result();

 Goal "integ_of (v BIT b) zdiv integ_of (w BIT False) = \
 \         (if ~b | #0 $<= integ_of w                   \
 \          then integ_of v zdiv (integ_of w)    \
 \          else (integ_of v $+ #1) zdiv (integ_of w))";
 by (simp_tac (simpset_of Int.thy addsimps [zadd_assoc, integ_of_BIT]) 1);
 by (asm_simp_tac (simpset()
		   delsimps bin_arith_extra_simps@bin_rel_simps
		   addsimps [zdiv_zmult_zmult1,
			     pos_zdiv_mult_2, lemma, neg_zdiv_mult_2]) 1);
 qed "zdiv_integ_of_BIT";

 Addsimps [zdiv_integ_of_BIT];


 (** computing "zmod" by shifting (proofs resemble those for "zdiv") **)

 Goal "#0 $<= a ==> (#1 $+ #2$*b) zmod (#2$*a) = #1 $+ #2 $* (b zmod a)";
 by (zdiv_undefined_case_tac "a = #0" 1);
 by (subgoal_tac "#1 $<= a" 1);
  by (arith_tac 2);
 by (subgoal_tac "#1 $< a $* #2" 1);
  by (arith_tac 2);
 by (subgoal_tac "#2$*(#1 $+ b zmod a) $<= #2$*a" 1);
  by (rtac zmult_zle_mono2 2);
 by (auto_tac (claset(),
	       simpset() addsimps [zadd_commute, zmult_commute, 
				   add1_zle_iff, pos_mod_bound]));
 by (stac zmod_zadd1_eq 1);
 by (asm_simp_tac (simpset() addsimps [zmod_zmult_zmult2, 
				       zmod_pos_pos_trivial]) 1);
 by (rtac zmod_pos_pos_trivial 1);
 by (asm_simp_tac (simpset() 
 #		  addsimps [zmod_pos_pos_trivial,
		     pos_mod_sign RS zadd_zle_mono1 RSN (2,zle_trans)]) 1);
 by (auto_tac (claset(),
	       simpset() addsimps [zmod_pos_pos_trivial]));
 by (subgoal_tac "#0 $<= b zmod a" 1);
  by (asm_simp_tac (simpset() addsimps [pos_mod_sign]) 2);
 by (arith_tac 1);
 qed "pos_zmod_mult_2";


 Goal "a $<= #0 ==> (#1 $+ #2$*b) zmod (#2$*a) = #2 $* ((b$+#1) zmod a) - #1";
 by (subgoal_tac 
     "(#1 $+ #2$*($-b-#1)) zmod (#2$*($-a)) = #1 $+ #2$*(($-b-#1) zmod ($-a))" 1);
 by (rtac pos_zmod_mult_2 2);
 by (auto_tac (claset(),
	       simpset() addsimps [zmult_zminus_right]));
 by (subgoal_tac "(#-1 - (#2 $* b)) = - (#1 $+ (#2 $* b))" 1);
 by (Simp_tac 2);
 by (asm_full_simp_tac (HOL_ss
			addsimps [zmod_zminus_zminus, zdiff_def,
				  zminus_zadd_distrib RS sym]) 1);
 by (dtac (zminus_equation RS iffD1 RS sym) 1);
 by Auto_tac;
 qed "neg_zmod_mult_2";

 Goal "integ_of (v BIT b) zmod integ_of (w BIT False) = \
 \         (if b then \
 \               if #0 $<= integ_of w \
 \               then #2 $* (integ_of v zmod integ_of w) $+ #1    \
 \               else #2 $* ((integ_of v $+ #1) zmod integ_of w) - #1  \
 \          else #2 $* (integ_of v zmod integ_of w))";
 by (simp_tac (simpset_of Int.thy addsimps [zadd_assoc, integ_of_BIT]) 1);
 by (asm_simp_tac (simpset()
		   delsimps bin_arith_extra_simps@bin_rel_simps
		   addsimps [zmod_zmult_zmult1,
			     pos_zmod_mult_2, lemma, neg_zmod_mult_2]) 1);
 qed "zmod_integ_of_BIT";

 Addsimps [zmod_integ_of_BIT];
*)
