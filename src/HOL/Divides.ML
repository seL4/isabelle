(*  Title:      HOL/Divides.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)


(** Less-then properties **)

bind_thm ("wf_less_trans", [eq_reflection, wf_pred_nat RS wf_trancl] MRS 
                    def_wfrec RS trans);

Goal "(%m. m mod n) = wfrec (trancl pred_nat) \
\                           (%f j. if j<n | n=0 then j else f (j-n))";
by (simp_tac (simpset() addsimps [mod_def]) 1);
qed "mod_eq";

Goal "(%m. m div n) = wfrec (trancl pred_nat) \
\            (%f j. if j<n | n=0 then 0 else Suc (f (j-n)))";
by (simp_tac (simpset() addsimps [div_def]) 1);
qed "div_eq";


(** Aribtrary definitions for division by zero.  Useful to simplify 
    certain equations **)

Goal "a div 0 = (0::nat)";
by (rtac (div_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "DIVISION_BY_ZERO_DIV";  (*NOT for adding to default simpset*)

Goal "a mod 0 = (a::nat)";
by (rtac (mod_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "DIVISION_BY_ZERO_MOD";  (*NOT for adding to default simpset*)

fun div_undefined_case_tac s i =
  case_tac s i THEN 
  Full_simp_tac (i+1) THEN
  asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO_DIV, 
				    DIVISION_BY_ZERO_MOD]) i;

(*** Remainder ***)

Goal "m<n ==> m mod n = (m::nat)";
by (rtac (mod_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "mod_less";
Addsimps [mod_less];

Goal "~ m < (n::nat) ==> m mod n = (m-n) mod n";
by (div_undefined_case_tac "n=0" 1);
by (rtac (mod_eq RS wf_less_trans) 1);
by (asm_simp_tac (simpset() addsimps [diff_less, cut_apply, less_eq]) 1);
qed "mod_geq";

(*Avoids the ugly ~m<n above*)
Goal "(n::nat) <= m ==> m mod n = (m-n) mod n";
by (asm_simp_tac (simpset() addsimps [mod_geq, not_less_iff_le]) 1);
qed "le_mod_geq";

Goal "m mod (n::nat) = (if m<n then m else (m-n) mod n)";
by (asm_simp_tac (simpset() addsimps [mod_geq]) 1);
qed "mod_if";

Goal "m mod 1 = (0::nat)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mod_geq])));
qed "mod_1";
Addsimps [mod_1];

Goal "n mod n = (0::nat)";
by (div_undefined_case_tac "n=0" 1);
by (asm_simp_tac (simpset() addsimps [mod_geq]) 1);
qed "mod_self";
Addsimps [mod_self];

Goal "(m+n) mod n = m mod (n::nat)";
by (subgoal_tac "(n + m) mod n = (n+m-n) mod n" 1);
by (stac (mod_geq RS sym) 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_commute])));
qed "mod_add_self2";

Goal "(n+m) mod n = m mod (n::nat)";
by (asm_simp_tac (simpset() addsimps [add_commute, mod_add_self2]) 1);
qed "mod_add_self1";

Addsimps [mod_add_self1, mod_add_self2];

Goal "(m + k*n) mod n = m mod (n::nat)";
by (induct_tac "k" 1);
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps [read_instantiate [("y","n")] add_left_commute])));
qed "mod_mult_self1";

Goal "(m + n*k) mod n = m mod (n::nat)";
by (asm_simp_tac (simpset() addsimps [mult_commute, mod_mult_self1]) 1);
qed "mod_mult_self2";

Addsimps [mod_mult_self1, mod_mult_self2];

Goal "(m mod n) * (k::nat) = (m*k) mod (n*k)";
by (div_undefined_case_tac "n=0" 1);
by (div_undefined_case_tac "k=0" 1);
by (induct_thm_tac nat_less_induct "m" 1);
by (stac mod_if 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [mod_geq, 
				      diff_less, diff_mult_distrib]) 1);
qed "mod_mult_distrib";

Goal "(k::nat) * (m mod n) = (k*m) mod (k*n)";
by (asm_simp_tac 
    (simpset() addsimps [read_instantiate [("m","k")] mult_commute, 
			 mod_mult_distrib]) 1);
qed "mod_mult_distrib2";

Goal "(m*n) mod n = (0::nat)";
by (div_undefined_case_tac "n=0" 1);
by (induct_tac "m" 1);
by (Asm_simp_tac 1);
by (rename_tac "k" 1);
by (cut_inst_tac [("m","k*n"),("n","n")] mod_add_self2 1);
by (asm_full_simp_tac (simpset() addsimps [add_commute]) 1);
qed "mod_mult_self_is_0";

Goal "(n*m) mod n = (0::nat)";
by (simp_tac (simpset() addsimps [mult_commute, mod_mult_self_is_0]) 1);
qed "mod_mult_self1_is_0";
Addsimps [mod_mult_self_is_0, mod_mult_self1_is_0];


(*** Quotient ***)

Goal "m<n ==> m div n = (0::nat)";
by (rtac (div_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "div_less";
Addsimps [div_less];

Goal "[| 0<n;  ~m<n |] ==> m div n = Suc((m-n) div n)";
by (rtac (div_eq RS wf_less_trans) 1);
by (asm_simp_tac (simpset() addsimps [diff_less, cut_apply, less_eq]) 1);
qed "div_geq";

(*Avoids the ugly ~m<n above*)
Goal "[| 0<n;  n<=m |] ==> m div n = Suc((m-n) div n)";
by (asm_simp_tac (simpset() addsimps [div_geq, not_less_iff_le]) 1);
qed "le_div_geq";

Goal "0<n ==> m div n = (if m<n then 0 else Suc((m-n) div n))";
by (asm_simp_tac (simpset() addsimps [div_geq]) 1);
qed "div_if";


(*Main Result about quotient and remainder.*)
Goal "(m div n)*n + m mod n = (m::nat)";
by (div_undefined_case_tac "n=0" 1);
by (induct_thm_tac nat_less_induct "m" 1);
by (stac mod_if 1);
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps [add_assoc, div_geq,
				   add_diff_inverse, diff_less])));
qed "mod_div_equality";

(* a simple rearrangement of mod_div_equality: *)
Goal "(n::nat) * (m div n) = m - (m mod n)";
by (cut_inst_tac [("m","m"),("n","n")] mod_div_equality 1);
by (full_simp_tac (simpset() addsimps mult_ac) 1);
by (arith_tac 1);
qed "mult_div_cancel";

Goal "0<n ==> m mod n < (n::nat)";
by (induct_thm_tac nat_less_induct "m" 1);
by (case_tac "na<n" 1);
(*case n le na*)
by (asm_full_simp_tac (simpset() addsimps [mod_geq, diff_less]) 2);
(*case na<n*)
by (Asm_simp_tac 1);
qed "mod_less_divisor";
Addsimps [mod_less_divisor];

(*** More division laws ***)

Goal "0<n ==> (m*n) div n = (m::nat)";
by (cut_inst_tac [("m", "m*n"),("n","n")] mod_div_equality 1);
by Auto_tac;
qed "div_mult_self_is_m";

Goal "0<n ==> (n*m) div n = (m::nat)";
by (asm_simp_tac (simpset() addsimps [mult_commute, div_mult_self_is_m]) 1);
qed "div_mult_self1_is_m";
Addsimps [div_mult_self_is_m, div_mult_self1_is_m];

(*mod_mult_distrib2 above is the counterpart for remainder*)


(*** Proving facts about div and mod using quorem ***)

Goal "[| b*q' + r'  <= b*q + r;  0 < b;  r < b |] \
\     ==> q' <= (q::nat)";
by (rtac leI 1); 
by (stac less_iff_Suc_add 1);
by (auto_tac (claset(), simpset() addsimps [add_mult_distrib2]));   
qed "unique_quotient_lemma";

Goal "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  0 < b |] \
\     ==> q = q'";
by (asm_full_simp_tac 
    (simpset() addsimps split_ifs @ [Divides.quorem_def]) 1);
by Auto_tac;  
by (REPEAT 
    (blast_tac (claset() addIs [order_antisym]
			 addDs [order_eq_refl RS unique_quotient_lemma, 
				sym]) 1));
qed "unique_quotient";

Goal "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  0 < b |] \
\     ==> r = r'";
by (subgoal_tac "q = q'" 1);
by (blast_tac (claset() addIs [unique_quotient]) 2);
by (asm_full_simp_tac (simpset() addsimps [Divides.quorem_def]) 1);
qed "unique_remainder";

Goal "0 < b ==> quorem ((a, b), (a div b, a mod b))";
by (cut_inst_tac [("m","a"),("n","b")] mod_div_equality 1);
by (auto_tac
    (claset() addEs [sym],
     simpset() addsimps mult_ac@[Divides.quorem_def]));
qed "quorem_div_mod";

Goal "[| quorem((a,b),(q,r));  0 < b |] ==> a div b = q";
by (asm_simp_tac (simpset() addsimps [quorem_div_mod RS unique_quotient]) 1);
qed "quorem_div";

Goal "[| quorem((a,b),(q,r));  0 < b |] ==> a mod b = r";
by (asm_simp_tac (simpset() addsimps [quorem_div_mod RS unique_remainder]) 1);
qed "quorem_mod";

(** A dividend of zero **)

Goal "0 div m = (0::nat)";
by (div_undefined_case_tac "m=0" 1);
by (Asm_simp_tac 1);
qed "div_0"; 

Goal "0 mod m = (0::nat)";
by (div_undefined_case_tac "m=0" 1);
by (Asm_simp_tac 1);
qed "mod_0"; 
Addsimps [div_0, mod_0];

(** proving (a*b) div c = a * (b div c) + a * (b mod c) **)

Goal "[| quorem((b,c),(q,r));  0 < c |] \
\     ==> quorem ((a*b, c), (a*q + a*r div c, a*r mod c))";
by (cut_inst_tac [("m", "a*r"), ("n","c")] mod_div_equality 1);
by (auto_tac
    (claset(),
     simpset() addsimps split_ifs@mult_ac@
                        [Divides.quorem_def, add_mult_distrib2]));
val lemma = result();

Goal "(a*b) div c = a*(b div c) + a*(b mod c) div (c::nat)";
by (div_undefined_case_tac "c = 0" 1);
by (blast_tac (claset() addIs [quorem_div_mod RS lemma RS quorem_div]) 1);
qed "div_mult1_eq";

Goal "(a*b) mod c = a*(b mod c) mod (c::nat)";
by (div_undefined_case_tac "c = 0" 1);
by (blast_tac (claset() addIs [quorem_div_mod RS lemma RS quorem_mod]) 1);
qed "mod_mult1_eq";

Goal "(a*b) mod (c::nat) = ((a mod c) * b) mod c";
by (rtac trans 1);
by (res_inst_tac [("s","b*a mod c")] trans 1);
by (rtac mod_mult1_eq 2);
by (ALLGOALS (simp_tac (simpset() addsimps [mult_commute])));
qed "mod_mult1_eq'";

Goal "(a*b) mod (c::nat) = ((a mod c) * (b mod c)) mod c";
by (rtac (mod_mult1_eq' RS trans) 1);
by (rtac mod_mult1_eq 1);
qed "mod_mult_distrib_mod";

(** proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c) **)

Goal "[| quorem((a,c),(aq,ar));  quorem((b,c),(bq,br));  0 < c |] \
\     ==> quorem ((a+b, c), (aq + bq + (ar+br) div c, (ar+br) mod c))";
by (cut_inst_tac [("m", "ar+br"), ("n","c")] mod_div_equality 1);
by (auto_tac
    (claset(),
     simpset() addsimps split_ifs@mult_ac@
                        [Divides.quorem_def, add_mult_distrib2]));
val lemma = result();

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
Goal "(a+b) div (c::nat) = a div c + b div c + ((a mod c + b mod c) div c)";
by (div_undefined_case_tac "c = 0" 1);
by (blast_tac (claset() addIs [[quorem_div_mod,quorem_div_mod]
			       MRS lemma RS quorem_div]) 1);
qed "div_add1_eq";

Goal "(a+b) mod (c::nat) = (a mod c + b mod c) mod c";
by (div_undefined_case_tac "c = 0" 1);
by (blast_tac (claset() addIs [[quorem_div_mod,quorem_div_mod]
			       MRS lemma RS quorem_mod]) 1);
qed "mod_add1_eq";


(*** proving  a div (b*c) = (a div b) div c ***)

(** first, a lemma to bound the remainder **)

Goal "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c";
by (cut_inst_tac [("m","q"),("n","c")] mod_less_divisor 1);
by (dres_inst_tac [("m","q mod c")] less_imp_Suc_add 2); 
by Auto_tac;  
by (eres_inst_tac [("P","%x. ?lhs < ?rhs x")] ssubst 1); 
by (asm_simp_tac (simpset() addsimps [add_mult_distrib2]) 1);
val mod_lemma = result();

Goal "[| quorem ((a,b), (q,r));  0 < b;  0 < c |] \
\     ==> quorem ((a, b*c), (q div c, b*(q mod c) + r))";
by (cut_inst_tac [("m", "q"), ("n","c")] mod_div_equality 1);
by (auto_tac  
    (claset(),
     simpset() addsimps mult_ac@
                        [Divides.quorem_def, add_mult_distrib2 RS sym,
			 mod_lemma]));
val lemma = result();

Goal "a div (b*c) = (a div b) div (c::nat)";
by (div_undefined_case_tac "b=0" 1);
by (div_undefined_case_tac "c=0" 1);
by (force_tac (claset(),
	       simpset() addsimps [quorem_div_mod RS lemma RS quorem_div]) 1);
qed "div_mult2_eq";

Goal "a mod (b*c) = b*(a div b mod c) + a mod (b::nat)";
by (div_undefined_case_tac "b=0" 1);
by (div_undefined_case_tac "c=0" 1);
by (cut_inst_tac [("m", "a"), ("n","b")] mod_div_equality 1);
by (auto_tac (claset(),
	       simpset() addsimps [mult_commute, 
				   quorem_div_mod RS lemma RS quorem_mod]));
qed "mod_mult2_eq";


(*** Cancellation of common factors in "div" ***)

Goal "[| (0::nat) < b;  0 < c |] ==> (c*a) div (c*b) = a div b";
by (stac div_mult2_eq 1);
by Auto_tac;
val lemma1 = result();

Goal "(0::nat) < c ==> (c*a) div (c*b) = a div b";
by (div_undefined_case_tac "b = 0" 1);
by (auto_tac
    (claset(), 
     simpset() addsimps [read_instantiate [("x", "b")] linorder_neq_iff, 
			 lemma1, lemma2]));
qed "div_mult_mult1";

Goal "(0::nat) < c ==> (a*c) div (b*c) = a div b";
by (dtac div_mult_mult1 1);
by (auto_tac (claset(), simpset() addsimps [mult_commute]));
qed "div_mult_mult2";

Addsimps [div_mult_mult1, div_mult_mult2];


(*** Distribution of factors over "mod"

Could prove these as in Integ/IntDiv.ML, but we already have
mod_mult_distrib and mod_mult_distrib2 above!

Goal "(c*a) mod (c*b) = (c::nat) * (a mod b)";
qed "mod_mult_mult1";

Goal "(a*c) mod (b*c) = (a mod b) * (c::nat)";
qed "mod_mult_mult2";
 ***)

(*** Further facts about div and mod ***)

Goal "m div 1 = m";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [div_geq])));
qed "div_1";
Addsimps [div_1];

Goal "0<n ==> n div n = (1::nat)";
by (asm_simp_tac (simpset() addsimps [div_geq]) 1);
qed "div_self";
Addsimps [div_self];

Goal "0<n ==> (m+n) div n = Suc (m div n)";
by (subgoal_tac "(n + m) div n = Suc ((n+m-n) div n)" 1);
by (stac (div_geq RS sym) 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_commute])));
qed "div_add_self2";

Goal "0<n ==> (n+m) div n = Suc (m div n)";
by (asm_simp_tac (simpset() addsimps [add_commute, div_add_self2]) 1);
qed "div_add_self1";

Goal "!!n::nat. 0<n ==> (m + k*n) div n = k + m div n";
by (stac div_add1_eq 1); 
by (stac div_mult1_eq 1); 
by (Asm_simp_tac 1); 
qed "div_mult_self1";

Goal "0<n ==> (m + n*k) div n = k + m div (n::nat)";
by (asm_simp_tac (simpset() addsimps [mult_commute, div_mult_self1]) 1);
qed "div_mult_self2";

Addsimps [div_mult_self1, div_mult_self2];

(* Monotonicity of div in first argument *)
Goal "ALL m::nat. m <= n --> (m div k) <= (n div k)";
by (div_undefined_case_tac "k=0" 1);
by (induct_thm_tac nat_less_induct "n" 1);
by (Clarify_tac 1);
by (case_tac "n<k" 1);
(* 1  case n<k *)
by (Asm_simp_tac 1);
(* 2  case n >= k *)
by (case_tac "m<k" 1);
(* 2.1  case m<k *)
by (Asm_simp_tac 1);
(* 2.2  case m>=k *)
by (asm_simp_tac (simpset() addsimps [div_geq, diff_less, diff_le_mono]) 1);
qed_spec_mp "div_le_mono";

(* Antimonotonicity of div in second argument *)
Goal "!!m::nat. [| 0<m; m<=n |] ==> (k div n) <= (k div m)";
by (subgoal_tac "0<n" 1);
 by (Asm_simp_tac 2);
by (induct_thm_tac nat_less_induct "k" 1);
by (rename_tac "k" 1);
by (case_tac "k<n" 1);
 by (Asm_simp_tac 1);
by (subgoal_tac "~(k<m)" 1);
 by (Asm_simp_tac 2);
by (asm_simp_tac (simpset() addsimps [div_geq]) 1);
by (subgoal_tac "(k-n) div n <= (k-m) div n" 1);
 by (REPEAT (ares_tac [div_le_mono,diff_le_mono2] 2));
by (rtac le_trans 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [diff_less]) 1);
qed "div_le_mono2";

Goal "m div n <= (m::nat)";
by (div_undefined_case_tac "n=0" 1);
by (subgoal_tac "m div n <= m div 1" 1);
by (Asm_full_simp_tac 1);
by (rtac div_le_mono2 1);
by (ALLGOALS Asm_simp_tac);
qed "div_le_dividend";
Addsimps [div_le_dividend];

(* Similar for "less than" *)
Goal "!!n::nat. 1<n ==> (0 < m) --> (m div n < m)";
by (induct_thm_tac nat_less_induct "m" 1);
by (rename_tac "m" 1);
by (case_tac "m<n" 1);
 by (Asm_full_simp_tac 1);
by (subgoal_tac "0<n" 1);
 by (Asm_simp_tac 2);
by (asm_full_simp_tac (simpset() addsimps [div_geq]) 1);
by (case_tac "n<m" 1);
 by (subgoal_tac "(m-n) div n < (m-n)" 1);
  by (REPEAT (ares_tac [impI,less_trans_Suc] 1));
  by (asm_full_simp_tac (simpset() addsimps [diff_less]) 1);
 by (asm_full_simp_tac (simpset() addsimps [diff_less]) 1);
(* case n=m *)
by (subgoal_tac "m=n" 1);
 by (Asm_simp_tac 2);
by (Asm_simp_tac 1);
qed_spec_mp "div_less_dividend";
Addsimps [div_less_dividend];

(*** Further facts about mod (mainly for the mutilated chess board ***)

Goal "Suc(m) mod n = (if Suc(m mod n) = n then 0 else Suc(m mod n))";
by (div_undefined_case_tac "n=0" 1);
by (induct_thm_tac nat_less_induct "m" 1);
by (case_tac "Suc(na)<n" 1);
(* case Suc(na) < n *)
by (forward_tac [lessI RS less_trans] 1 
    THEN asm_simp_tac (simpset() addsimps [less_not_refl3]) 1);
(* case n <= Suc(na) *)
by (asm_full_simp_tac (simpset() addsimps [not_less_iff_le, le_Suc_eq, 
					   mod_geq]) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [Suc_diff_le, diff_less, le_mod_geq]));
qed "mod_Suc";


(************************************************)
(** Divides Relation                           **)
(************************************************)

Goalw [dvd_def] "n = m * k \\<Longrightarrow> m dvd n";
by (Blast_tac 1); 
qed "dvdI";

Goalw [dvd_def] "!!P. [|m dvd n;  !!k. n = m*k ==> P|] ==> P";
by (Blast_tac 1); 
qed "dvdE";

Goalw [dvd_def] "m dvd (0::nat)";
by (blast_tac (claset() addIs [mult_0_right RS sym]) 1);
qed "dvd_0_right";
AddIffs [dvd_0_right];

Goalw [dvd_def] "0 dvd m ==> m = (0::nat)";
by Auto_tac;
qed "dvd_0_left";

Goal "(0 dvd (m::nat)) = (m = 0)";
by (blast_tac (claset() addIs [dvd_0_left]) 1); 
qed "dvd_0_left_iff";
AddIffs [dvd_0_left_iff];

Goalw [dvd_def] "1 dvd (k::nat)";
by (Simp_tac 1);
qed "dvd_1_left";
AddIffs [dvd_1_left];

Goal "(m dvd 1) = (m = 1)";
by (simp_tac (simpset() addsimps [dvd_def]) 1); 
qed "dvd_1_iff_1";
Addsimps [dvd_1_iff_1];

Goalw [dvd_def] "m dvd (m::nat)";
by (blast_tac (claset() addIs [mult_1_right RS sym]) 1);
qed "dvd_refl";
Addsimps [dvd_refl];

Goalw [dvd_def] "[| m dvd n; n dvd p |] ==> m dvd (p::nat)";
by (blast_tac (claset() addIs [mult_assoc] ) 1);
qed "dvd_trans";

Goalw [dvd_def] "[| m dvd n; n dvd m |] ==> m = (n::nat)";
by (force_tac (claset() addDs [mult_eq_self_implies_10],
	       simpset() addsimps [mult_assoc, mult_eq_1_iff]) 1);
qed "dvd_anti_sym";

Goalw [dvd_def] "[| k dvd m; k dvd n |] ==> k dvd (m+n :: nat)";
by (blast_tac (claset() addIs [add_mult_distrib2 RS sym]) 1);
qed "dvd_add";

Goalw [dvd_def] "[| k dvd m; k dvd n |] ==> k dvd (m-n :: nat)";
by (blast_tac (claset() addIs [diff_mult_distrib2 RS sym]) 1);
qed "dvd_diff";

Goal "[| k dvd m-n; k dvd n; n<=m |] ==> k dvd (m::nat)";
by (etac (not_less_iff_le RS iffD2 RS add_diff_inverse RS subst) 1);
by (blast_tac (claset() addIs [dvd_add]) 1);
qed "dvd_diffD";

Goal "[| k dvd m-n; k dvd m; n<=m |] ==> k dvd (n::nat)";
by (dres_inst_tac [("m","m")] dvd_diff 1);
by Auto_tac;  
qed "dvd_diffD1";

Goalw [dvd_def] "k dvd n ==> k dvd (m*n :: nat)";
by (blast_tac (claset() addIs [mult_left_commute]) 1);
qed "dvd_mult";

Goal "k dvd m ==> k dvd (m*n :: nat)";
by (stac mult_commute 1);
by (etac dvd_mult 1);
qed "dvd_mult2";

(* k dvd (m*k) *)
AddIffs [dvd_refl RS dvd_mult, dvd_refl RS dvd_mult2];

Goal "(k dvd n + k) = (k dvd (n::nat))";
by (rtac iffI 1);
by (etac dvd_add 2);
by (rtac dvd_refl 2);
by (subgoal_tac "n = (n+k)-k" 1);
by  (Simp_tac 2);
by (etac ssubst 1);
by (etac dvd_diff 1);
by (rtac dvd_refl 1);
qed "dvd_reduce";

Goalw [dvd_def] "!!n::nat. [| f dvd m; f dvd n |] ==> f dvd m mod n";
by (div_undefined_case_tac "n=0" 1);
by Auto_tac; 
by (blast_tac (claset() addIs [mod_mult_distrib2 RS sym]) 1);  
qed "dvd_mod";

Goal "[| (k::nat) dvd m mod n;  k dvd n |] ==> k dvd m";
by (subgoal_tac "k dvd (m div n)*n + m mod n" 1);
by (asm_simp_tac (simpset() addsimps [dvd_add, dvd_mult]) 2);
by (asm_full_simp_tac (simpset() addsimps [mod_div_equality]) 1);
qed "dvd_mod_imp_dvd";

Goal "k dvd n ==> ((k::nat) dvd m mod n) = (k dvd m)";
by (blast_tac (claset() addIs [dvd_mod_imp_dvd, dvd_mod]) 1); 
qed "dvd_mod_iff";

Goalw [dvd_def]  "!!k::nat. [| k*m dvd k*n; 0<k |] ==> m dvd n";
by (etac exE 1);
by (asm_full_simp_tac (simpset() addsimps mult_ac) 1);
qed "dvd_mult_cancel";

Goal "0<m ==> (m*n dvd m) = (n=1)";
by Auto_tac;  
by (subgoal_tac "m*n dvd m*1" 1);
by (dtac dvd_mult_cancel 1); 
by Auto_tac;  
qed "dvd_mult_cancel1";

Goal "0<m ==> (n*m dvd m) = (n=1)";
by (stac mult_commute 1); 
by (etac dvd_mult_cancel1 1); 
qed "dvd_mult_cancel2";

Goalw [dvd_def] "[| i dvd m; j dvd n|] ==> i*j dvd (m*n :: nat)";
by (Clarify_tac 1);
by (res_inst_tac [("x","k*ka")] exI 1);
by (asm_simp_tac (simpset() addsimps mult_ac) 1);
qed "mult_dvd_mono";

Goalw [dvd_def] "(i*j :: nat) dvd k ==> i dvd k";
by (full_simp_tac (simpset() addsimps [mult_assoc]) 1);
by (Blast_tac 1);
qed "dvd_mult_left";

Goalw [dvd_def] "(i*j :: nat) dvd k ==> j dvd k";
by (Clarify_tac 1);
by (res_inst_tac [("x","i*k")] exI 1);
by (simp_tac (simpset() addsimps mult_ac) 1);
qed "dvd_mult_right";

Goalw [dvd_def] "[| k dvd n; 0 < n |] ==> k <= (n::nat)";
by (Clarify_tac 1);
by (ALLGOALS (full_simp_tac (simpset() addsimps [zero_less_mult_iff])));
by (etac conjE 1);
by (rtac le_trans 1);
by (rtac (le_refl RS mult_le_mono) 2);
by (etac Suc_leI 2);
by (Simp_tac 1);
qed "dvd_imp_le";

Goalw [dvd_def] "!!k::nat. (k dvd n) = (n mod k = 0)";
by (div_undefined_case_tac "k=0" 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [mult_commute]) 1);
by (res_inst_tac [("t","n"),("n1","k")] (mod_div_equality RS subst) 1);
by (stac mult_commute 1);
by (Asm_simp_tac 1);
qed "dvd_eq_mod_eq_0";

Goal "(m mod d = 0) = (EX q::nat. m = d*q)";
by (auto_tac (claset(), 
     simpset() addsimps [dvd_eq_mod_eq_0 RS sym, dvd_def]));  
qed "mod_eq_0_iff";
AddSDs [mod_eq_0_iff RS iffD1];

(*Loses information, namely we also have r<d provided d is nonzero*)
Goal "(m mod d = r) ==> EX q::nat. m = r + q*d";
by (cut_inst_tac [("m","m")] mod_div_equality 1);
by (full_simp_tac (simpset() addsimps add_ac) 1); 
by (blast_tac (claset() addIs [sym]) 1); 
qed "mod_eqD";

