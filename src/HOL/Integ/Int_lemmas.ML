(*  Title:      HOL/Integ/Int_lemmas.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order

And many further lemmas
*)

(* legacy ML bindings *)

structure Int =
struct
  val thy = the_context ();
  val zabs_def = thm "zabs_def";
  val nat_def  = thm "nat_def";
end;

open Int;

Goal "int 0 = (0::int)";
by (simp_tac (simpset() addsimps [Zero_int_def]) 1);
qed "int_0";

Goal "int 1 = 1";
by (simp_tac (simpset() addsimps [One_int_def]) 1); 
qed "int_1";

Goal "int (Suc 0) = 1";
by (simp_tac (simpset() addsimps [One_int_def, One_nat_def]) 1); 
qed "int_Suc0_eq_1";

Goalw [zdiff_def,zless_def] "neg x = (x < 0)";
by Auto_tac; 
qed "neg_eq_less_0"; 

Goalw [zle_def] "(~neg x) = (0 <= x)";
by (simp_tac (simpset() addsimps [neg_eq_less_0]) 1); 
qed "not_neg_eq_ge_0"; 

(** Needed to simplify inequalities when Numeral1 can get simplified to 1 **)

Goal "~ neg 0";
by (simp_tac (simpset() addsimps [One_int_def, neg_eq_less_0]) 1);  
qed "not_neg_0"; 

Goal "~ neg 1";
by (simp_tac (simpset() addsimps [One_int_def, neg_eq_less_0]) 1);  
qed "not_neg_1"; 

Goal "iszero 0";
by (simp_tac (simpset() addsimps [iszero_def]) 1);
qed "iszero_0"; 

Goal "~ iszero 1";
by (simp_tac (simpset() addsimps [Zero_int_def, One_int_def, One_nat_def, 
                                  iszero_def]) 1);
qed "not_iszero_1"; 

Goal "0 < (1::int)";
by (simp_tac (simpset() addsimps [Zero_int_def, One_int_def, One_nat_def]) 1); 
qed "int_0_less_1";

Goal "0 \\<noteq> (1::int)";
by (simp_tac (simpset() addsimps [Zero_int_def, One_int_def, One_nat_def]) 1); 
qed "int_0_neq_1";

Addsimps [int_0, int_1, int_0_neq_1];


(*** Abel_Cancel simproc on the integers ***)

(* Lemmas needed for the simprocs *)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
Goal "((x::int) + (y + z) = y + u) = ((x + z) = u)";
by (stac zadd_left_commute 1);
by (rtac zadd_left_cancel 1);
qed "zadd_cancel_21";

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
Goal "((x::int) + (y + z) = y) = (x = -z)";
by (stac zadd_left_commute 1);
by (res_inst_tac [("t", "y")] (zadd_0_right RS subst) 1
    THEN stac zadd_left_cancel 1);
by (simp_tac (simpset() addsimps [eq_zdiff_eq RS sym]) 1);
qed "zadd_cancel_end";


structure Int_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val sg_ref 		= Sign.self_ref (Theory.sign_of (the_context ()))
  val T		= HOLogic.intT
  val zero		= Const ("0", HOLogic.intT)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= zadd_cancel_21
  val add_cancel_end	= zadd_cancel_end
  val add_left_cancel	= zadd_left_cancel
  val add_assoc		= zadd_assoc
  val add_commute	= zadd_commute
  val add_left_commute	= zadd_left_commute
  val add_0		= zadd_0
  val add_0_right	= zadd_0_right

  val eq_diff_eq	= eq_zdiff_eq
  val eqI_rules		= [zless_eqI, zeq_eqI, zle_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= zdiff_def
  val minus_add_distrib	= zminus_zadd_distrib
  val minus_minus	= zminus_zminus
  val minus_0		= zminus_0
  val add_inverses	= [zadd_zminus_inverse, zadd_zminus_inverse2]
  val cancel_simps	= [zadd_zminus_cancel, zminus_zadd_cancel]
end;

structure Int_Cancel = Abel_Cancel (Int_Cancel_Data);

Addsimprocs [Int_Cancel.sum_conv, Int_Cancel.rel_conv];



(*** misc ***)

Goal "- (z - y) = y - (z::int)";
by (Simp_tac 1);
qed "zminus_zdiff_eq";
Addsimps [zminus_zdiff_eq];

Goal "(w<z) = neg(w-z)";
by (simp_tac (simpset() addsimps [zless_def]) 1);
qed "zless_eq_neg";

Goal "(w=z) = iszero(w-z)";
by (simp_tac (simpset() addsimps [iszero_def, zdiff_eq_eq]) 1);
qed "eq_eq_iszero";

Goal "(w<=z) = (~ neg(z-w))";
by (simp_tac (simpset() addsimps [zle_def, zless_def]) 1);
qed "zle_eq_not_neg";

(** Inequality reasoning **)

Goal "(w < z + (1::int)) = (w<z | w=z)";
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_Suc_zadd, int_Suc,
                                  gr0_conv_Suc, zero_reorient]));
by (res_inst_tac [("x","Suc n")] exI 1); 
by (simp_tac (simpset() addsimps [int_Suc]) 1); 
qed "zless_add1_eq";

Goal "(w + (1::int) <= z) = (w<z)";
by (asm_full_simp_tac (simpset() addsimps [zle_def, zless_add1_eq]) 1); 
by (auto_tac (claset() addIs [zle_anti_sym],
	      simpset() addsimps [order_less_imp_le, symmetric zle_def]));
qed "add1_zle_eq";

Goal "((1::int) + w <= z) = (w<z)";
by (stac zadd_commute 1);
by (rtac add1_zle_eq 1);
qed "add1_left_zle_eq";


(*** Monotonicity results ***)

Goal "(v+z < w+z) = (v < (w::int))";
by (Simp_tac 1);
qed "zadd_right_cancel_zless";

Goal "(z+v < z+w) = (v < (w::int))";
by (Simp_tac 1);
qed "zadd_left_cancel_zless";

Addsimps [zadd_right_cancel_zless, zadd_left_cancel_zless];

Goal "(v+z <= w+z) = (v <= (w::int))";
by (Simp_tac 1);
qed "zadd_right_cancel_zle";

Goal "(z+v <= z+w) = (v <= (w::int))";
by (Simp_tac 1);
qed "zadd_left_cancel_zle";

Addsimps [zadd_right_cancel_zle, zadd_left_cancel_zle];

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zless_mono1", zadd_right_cancel_zless RS iffD2);

(*"v<=w ==> z+v <= z+w"*)
bind_thm ("zadd_zless_mono2", zadd_left_cancel_zless RS iffD2);

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zle_mono1", zadd_right_cancel_zle RS iffD2);

(*"v<=w ==> z+v <= z+w"*)
bind_thm ("zadd_zle_mono2", zadd_left_cancel_zle RS iffD2);

Goal "[| w'<=w; z'<=z |] ==> w' + z' <= w + (z::int)";
by (etac (zadd_zle_mono1 RS zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zle_mono";

Goal "[| w'<w; z'<=z |] ==> w' + z' < w + (z::int)";
by (etac (zadd_zless_mono1 RS order_less_le_trans) 1);
by (Simp_tac 1);
qed "zadd_zless_mono";


(*** Comparison laws ***)

Goal "(- x < - y) = (y < (x::int))";
by (simp_tac (simpset() addsimps [zless_def, zdiff_def] @ zadd_ac) 1);
qed "zminus_zless_zminus"; 
Addsimps [zminus_zless_zminus];

Goal "(- x <= - y) = (y <= (x::int))";
by (simp_tac (simpset() addsimps [zle_def]) 1);
qed "zminus_zle_zminus"; 
Addsimps [zminus_zle_zminus];

(** The next several equations can make the simplifier loop! **)

Goal "(x < - y) = (y < - (x::int))";
by (simp_tac (simpset() addsimps [zless_def, zdiff_def] @ zadd_ac) 1);
qed "zless_zminus"; 

Goal "(- x < y) = (- y < (x::int))";
by (simp_tac (simpset() addsimps [zless_def, zdiff_def] @ zadd_ac) 1);
qed "zminus_zless"; 

Goal "(x <= - y) = (y <= - (x::int))";
by (simp_tac (simpset() addsimps [zle_def, zminus_zless]) 1);
qed "zle_zminus"; 

Goal "(- x <= y) = (- y <= (x::int))";
by (simp_tac (simpset() addsimps [zle_def, zless_zminus]) 1);
qed "zminus_zle"; 

Goal "(x = - y) = (y = - (x::int))";
by Auto_tac;
qed "equation_zminus";

Goal "(- x = y) = (- (y::int) = x)";
by Auto_tac;
qed "zminus_equation";


(** Instances of the equations above, for zero **)

(*instantiate a variable to zero and simplify*)
fun zero_instance v th = simplify (simpset()) (inst v "0" th);

Addsimps [zero_instance "x" zless_zminus,
          zero_instance "y" zminus_zless,
          zero_instance "x" zle_zminus,
          zero_instance "y" zminus_zle,
          zero_instance "x" equation_zminus,
          zero_instance "y" zminus_equation];


Goal "- (int (Suc n)) < 0";
by (simp_tac (simpset() addsimps [zless_def]) 1);
qed "negative_zless_0"; 

Goal "- (int (Suc n)) < int m";
by (rtac (negative_zless_0 RS order_less_le_trans) 1);
by (Simp_tac 1); 
qed "negative_zless"; 
AddIffs [negative_zless]; 

Goal "- int n <= 0";
by (simp_tac (simpset() addsimps [zminus_zle]) 1);
qed "negative_zle_0"; 

Goal "- int n <= int m";
by (simp_tac (simpset() addsimps [zless_def, zle_def, zdiff_def, zadd_int]) 1);
qed "negative_zle"; 
AddIffs [negative_zle]; 

Goal "~(0 <= - (int (Suc n)))";
by (stac zle_zminus 1);
by (Simp_tac 1);
qed "not_zle_0_negative"; 
Addsimps [not_zle_0_negative]; 

Goal "(int n <= - int m) = (n = 0 & m = 0)"; 
by Safe_tac; 
by (Simp_tac 3); 
by (dtac (zle_zminus RS iffD1) 2); 
by (ALLGOALS (dtac (negative_zle_0 RSN(2,zle_trans)))); 
by (ALLGOALS Asm_full_simp_tac); 
qed "int_zle_neg"; 

Goal "~(int n < - int m)";
by (simp_tac (simpset() addsimps [symmetric zle_def]) 1); 
qed "not_int_zless_negative"; 

Goal "(- int n = int m) = (n = 0 & m = 0)"; 
by (rtac iffI 1);
by (rtac (int_zle_neg RS iffD1) 1); 
by (dtac sym 1); 
by (ALLGOALS Asm_simp_tac); 
qed "negative_eq_positive"; 

Addsimps [negative_eq_positive, not_int_zless_negative]; 


Goal "(w <= z) = (EX n. z = w + int n)";
by (auto_tac (claset() addIs [inst "x" "0::nat" exI]
		       addSIs [not_sym RS not0_implies_Suc],
	      simpset() addsimps [zless_iff_Suc_zadd, int_le_less]));
qed "zle_iff_zadd";

Goal "abs (int m) = int m";
by (simp_tac (simpset() addsimps [Int.zabs_def]) 1); 
qed "abs_int_eq";
Addsimps [abs_int_eq];


(**** nat: magnitide of an integer, as a natural number ****)

Goalw [nat_def] "nat(int n) = n";
by Auto_tac;
qed "nat_int";
Addsimps [nat_int];

Goalw [nat_def] "nat(- (int n)) = 0";
by (auto_tac (claset(),
     simpset() addsimps [neg_eq_less_0, zero_reorient, zminus_zless])); 
qed "nat_zminus_int";
Addsimps [nat_zminus_int];

Goalw [Zero_int_def] "nat 0 = 0";
by (rtac nat_int 1);
qed "nat_zero";
Addsimps [nat_zero];

Goal "~ neg z ==> int (nat z) = z"; 
by (dtac (not_neg_eq_ge_0 RS iffD1) 1); 
by (dtac zle_imp_zless_or_eq 1); 
by (auto_tac (claset(), simpset() addsimps [zless_iff_Suc_zadd])); 
qed "not_neg_nat"; 

Goal "neg x ==> EX n. x = - (int (Suc n))"; 
by (auto_tac (claset(), 
	      simpset() addsimps [neg_eq_less_0, zless_iff_Suc_zadd,
				  zdiff_eq_eq RS sym, zdiff_def])); 
qed "negD"; 

Goalw [nat_def] "neg z ==> nat z = 0"; 
by Auto_tac; 
qed "neg_nat"; 

Goal "(m < nat z) = (int m < z)";
by (case_tac "neg z" 1);
by (etac (not_neg_nat RS subst) 2);
by (auto_tac (claset(), simpset() addsimps [neg_nat])); 
by (auto_tac (claset() addDs [order_less_trans], 
	      simpset() addsimps [neg_eq_less_0])); 
qed "zless_nat_eq_int_zless";

Goal "0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z <= 0 ==> nat z = 0"; 
by (auto_tac (claset(), 
	      simpset() addsimps [order_le_less, neg_eq_less_0, 
				  zle_def, neg_nat])); 
qed "nat_le_0"; 
Addsimps [nat_0_le, nat_le_0];

(*An alternative condition is  0 <= w  *)
Goal "0 < z ==> (nat w < nat z) = (w < z)";
by (stac (zless_int RS sym) 1);
by (asm_simp_tac (simpset() addsimps [not_neg_nat, not_neg_eq_ge_0, 
				      order_le_less]) 1);
by (case_tac "neg w" 1);
by (asm_simp_tac (simpset() addsimps [not_neg_nat]) 2);
by (asm_full_simp_tac (simpset() addsimps [neg_eq_less_0, neg_nat]) 1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
val lemma = result();

Goal "(nat w < nat z) = (0 < z & w < z)";
by (case_tac "0 < z" 1);
by (auto_tac (claset(), simpset() addsimps [lemma, linorder_not_less])); 
qed "zless_nat_conj";

(* a case theorem distinguishing non-negative and negative int *)  

val prems = Goal
     "[|!! n. z = int n ==> P;  !! n. z =  - (int (Suc n)) ==> P |] ==> P"; 
by (case_tac "neg z" 1); 
by (fast_tac (claset() addSDs [negD] addSEs prems) 1); 
by (dtac (not_neg_nat RS sym) 1);
by (eresolve_tac prems 1);
qed "int_cases"; 

fun int_case_tac x = res_inst_tac [("z",x)] int_cases; 


(*** Monotonicity of Multiplication ***)

Goal "i <= (j::int) ==> i * int k <= j * int k";
by (induct_tac "k" 1);
by (stac int_Suc 2);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2, zadd_zle_mono, 
                                       int_Suc0_eq_1])));
val lemma = result();

Goal "[| i <= j;  (0::int) <= k |] ==> i*k <= j*k";
by (res_inst_tac [("t", "k")] (not_neg_nat RS subst) 1);
by (etac lemma 2);
by (full_simp_tac (simpset() addsimps [not_neg_eq_ge_0]) 1);
qed "zmult_zle_mono1";

Goal "[| i <= j;  k <= (0::int) |] ==> j*k <= i*k";
by (rtac (zminus_zle_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() addsimps [zmult_zminus_right RS sym,
				      zmult_zle_mono1, zle_zminus]) 1);
qed "zmult_zle_mono1_neg";

Goal "[| i <= j;  (0::int) <= k |] ==> k*i <= k*j";
by (dtac zmult_zle_mono1 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zle_mono2";

Goal "[| i <= j;  k <= (0::int) |] ==> k*j <= k*i";
by (dtac zmult_zle_mono1_neg 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zle_mono2_neg";

(* <= monotonicity, BOTH arguments*)
Goal "[| i <= j;  k <= l;  (0::int) <= j;  (0::int) <= k |] ==> i*k <= j*l";
by (etac (zmult_zle_mono1 RS order_trans) 1);
by (assume_tac 1);
by (etac zmult_zle_mono2 1);
by (assume_tac 1);
qed "zmult_zle_mono";


(** strict, in 1st argument; proof is by induction on k>0 **)

Goal "i<j ==> 0<k --> int k * i < int k * j";
by (induct_tac "k" 1);
by (stac int_Suc 2);
by (case_tac "n=0" 2);
by (ALLGOALS (asm_full_simp_tac
	      (simpset() addsimps [zadd_zmult_distrib, zadd_zless_mono, 
				   int_Suc0_eq_1, order_le_less])));
val lemma = result();

Goal "[| i<j;  (0::int) < k |] ==> k*i < k*j";
by (res_inst_tac [("t", "k")] (not_neg_nat RS subst) 1);
by (etac (lemma RS mp) 2);
by (asm_simp_tac (simpset() addsimps [not_neg_eq_ge_0, 
				      order_le_less]) 1);
by (forward_tac [conjI RS (zless_nat_conj RS iffD2)] 1);
by Auto_tac;
qed "zmult_zless_mono2";

Goal "[| i<j;  (0::int) < k |] ==> i*k < j*k";
by (dtac zmult_zless_mono2 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zless_mono1";

(* < monotonicity, BOTH arguments*)
Goal "[| i < j;  k < l;  (0::int) < j;  (0::int) < k |] ==> i*k < j*l";
by (etac (zmult_zless_mono1 RS order_less_trans) 1);
by (assume_tac 1);
by (etac zmult_zless_mono2 1);
by (assume_tac 1);
qed "zmult_zless_mono";

Goal "[| i<j;  k < (0::int) |] ==> j*k < i*k";
by (rtac (zminus_zless_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() addsimps [zmult_zminus_right RS sym,
				      zmult_zless_mono1, zless_zminus]) 1);
qed "zmult_zless_mono1_neg";

Goal "[| i<j;  k < (0::int) |] ==> k*j < k*i";
by (rtac (zminus_zless_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() addsimps [zmult_zminus RS sym,
				      zmult_zless_mono2, zless_zminus]) 1);
qed "zmult_zless_mono2_neg";


Goal "(m*n = (0::int)) = (m = 0 | n = 0)";
by (case_tac "m < (0::int)" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [linorder_not_less, order_le_less, 
				  linorder_neq_iff])); 
by (REPEAT 
    (force_tac (claset() addDs [zmult_zless_mono1_neg, zmult_zless_mono1], 
		simpset()) 1));
qed "zmult_eq_0_iff";
AddIffs [zmult_eq_0_iff];


(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

Goal "(m*k < n*k) = (((0::int) < k & m<n) | (k < 0 & n<m))";
by (case_tac "k = (0::int)" 1);
by (auto_tac (claset(), simpset() addsimps [linorder_neq_iff, 
                              zmult_zless_mono1, zmult_zless_mono1_neg]));  
by (auto_tac (claset(), 
              simpset() addsimps [linorder_not_less,
				  inst "y1" "m*k" (linorder_not_le RS sym),
                                  inst "y1" "m" (linorder_not_le RS sym)]));
by (ALLGOALS (etac notE));
by (auto_tac (claset(), simpset() addsimps [order_less_imp_le, zmult_zle_mono1,
                                            zmult_zle_mono1_neg]));  
qed "zmult_zless_cancel2";


Goal "(k*m < k*n) = (((0::int) < k & m<n) | (k < 0 & n<m))";
by (simp_tac (simpset() addsimps [inst "z" "k" zmult_commute, 
                                  zmult_zless_cancel2]) 1);
qed "zmult_zless_cancel1";

Goal "(m*k <= n*k) = (((0::int) < k --> m<=n) & (k < 0 --> n<=m))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  zmult_zless_cancel2]) 1);
qed "zmult_zle_cancel2";

Goal "(k*m <= k*n) = (((0::int) < k --> m<=n) & (k < 0 --> n<=m))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  zmult_zless_cancel1]) 1);
qed "zmult_zle_cancel1";

Goal "(m*k = n*k) = (k = (0::int) | m=n)";
by (cut_facts_tac [linorder_less_linear] 1);
by Safe_tac;
by Auto_tac;  
by (REPEAT 
    (force_tac (claset() addD2 ("mono_neg", zmult_zless_mono1_neg)
                         addD2 ("mono_pos", zmult_zless_mono1), 
		simpset() addsimps [linorder_neq_iff]) 1));

qed "zmult_cancel2";

Goal "(k*m = k*n) = (k = (0::int) | m=n)";
by (simp_tac (simpset() addsimps [inst "z" "k" zmult_commute, 
                                  zmult_cancel2]) 1);
qed "zmult_cancel1";
Addsimps [zmult_cancel1, zmult_cancel2];


(*Analogous to zadd_int*)
Goal "n<=m --> int m - int n = int (m-n)";
by (induct_thm_tac diff_induct "m n" 1);
by (auto_tac (claset(), simpset() addsimps [int_Suc, symmetric zdiff_def])); 
qed_spec_mp "zdiff_int";
