(*  Title:      HOL/Integ/IntArith.thy
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow

Simprocs and decision procedure for linear arithmetic.
*)


(*** Simprocs for numeric literals ***)

(** Combining of literal coefficients in sums of products **)

Goal "(x < y) = (x-y < (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zless_iff_zdiff_zless_0";

Goal "(x = y) = (x-y = (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "eq_iff_zdiff_eq_0";

Goal "(x <= y) = (x-y <= (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zle_iff_zdiff_zle_0";


structure Int_CC_Data : COMBINE_COEFF_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy		= Bin.thy
  val T			= HOLogic.intT

  val trans		= trans
  val add_ac		= zadd_ac
  val diff_def		= zdiff_def
  val minus_add_distrib	= zminus_zadd_distrib
  val minus_minus	= zminus_zminus
  val mult_commute	= zmult_commute
  val mult_1_right	= zmult_1_right
  val add_mult_distrib = zadd_zmult_distrib2
  val diff_mult_distrib = zdiff_zmult_distrib2
  val mult_minus_right = zmult_zminus_right

  val rel_iff_rel_0_rls = [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

end;

structure Int_CC = Combine_Coeff (Int_CC_Data);

Addsimprocs [Int_CC.sum_conv, Int_CC.rel_conv];


(** Constant folding for integer plus and times **)

(*We do not need
    structure Int_Plus_Assoc = Assoc_Fold (Int_Plus_Assoc_Data);
  because cancel_coeffs does the same thing*)

structure Int_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.intT
  val plus   = Const ("op *", [HOLogic.intT,HOLogic.intT] ---> HOLogic.intT);
  val add_ac = zmult_ac
end;

structure Int_Times_Assoc = Assoc_Fold (Int_Times_Assoc_Data);

Addsimprocs [Int_Times_Assoc.conv];


(** The same for the naturals **)

structure Nat_Plus_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.natT
  val plus   = Const ("op +", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = add_ac
end;

structure Nat_Plus_Assoc = Assoc_Fold (Nat_Plus_Assoc_Data);

structure Nat_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.natT
  val plus   = Const ("op *", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = mult_ac
end;

structure Nat_Times_Assoc = Assoc_Fold (Nat_Times_Assoc_Data);

Addsimprocs [Nat_Plus_Assoc.conv, Nat_Times_Assoc.conv];



(*** decision procedure for linear arithmetic ***)

(*---------------------------------------------------------------------------*)
(* Linear arithmetic                                                         *)
(*---------------------------------------------------------------------------*)

(*
Instantiation of the generic linear arithmetic package for int.
*)

(* Update parameters of arithmetic prover *)
let

(* reduce contradictory <= to False *)
val add_rules = simp_thms @ bin_arith_simps @ bin_rel_simps @
                [int_0,zmult_0,zmult_0_right];

val simprocs = [Int_Cancel.sum_conv, Int_Cancel.rel_conv,
                Int_CC.sum_conv, Int_CC.rel_conv];

val add_mono_thms =
  map (fn s => prove_goal Int.thy s
                 (fn prems => [cut_facts_tac prems 1,
                      asm_simp_tac (simpset() addsimps [zadd_zle_mono]) 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::int)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::int)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::int)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::int)"
    ];

in
LA_Data_Ref.add_mono_thms := !LA_Data_Ref.add_mono_thms @ add_mono_thms;
LA_Data_Ref.lessD := !LA_Data_Ref.lessD @ [add1_zle_eq RS iffD2];
LA_Data_Ref.ss_ref := !LA_Data_Ref.ss_ref addsimps add_rules
                      addsimprocs simprocs;
LA_Data_Ref.discrete := !LA_Data_Ref.discrete @ [("IntDef.int",true)]
end;

let
val int_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of Int.thy) (s, HOLogic.boolT))
      ["(m::int) < n","(m::int) <= n", "(m::int) = n"];

val fast_int_arith_simproc = mk_simproc
  "fast_int_arith" int_arith_simproc_pats Fast_Arith.lin_arith_prover;
in
Addsimprocs [fast_int_arith_simproc]
end;

(* Some test data
Goal "!!a::int. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a-d+ #2 <= b+(-c)";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a+c+ #1 < b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b <= i+j; a<=b; i<=j |] \
\     ==> a+a <= j+j";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b < i+j; a<b; i<j |] \
\     ==> a+a - - #-1 < j+j - #3";
by (fast_arith_tac 1);
Goal "!!a::int. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> #6*a <= #5*l+i";
by (fast_arith_tac 1);
*)

(*---------------------------------------------------------------------------*)
(* End of linear arithmetic                                                  *)
(*---------------------------------------------------------------------------*)

(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::int)";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "add_number_of_left";

Goal "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::int)";
by (simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
qed "mult_number_of_left";

Addsimps [add_number_of_left, mult_number_of_left];

(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z + (#1::int)) = (w<=z | w = z + (#1::int))";
by (arith_tac 1);
qed "zle_add1_eq";

Goal "(w <= z - (#1::int)) = (w<(z::int))";
by (arith_tac 1);
qed "zle_diff1_eq";
Addsimps [zle_diff1_eq];

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w <= z; #0 <= v |] ==> w <= z + (v::int)";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd";

Goal "w <= z ==> w <= z + (#1::int)";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd1";

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w < z; #0 <= v |] ==> w < z + (v::int)";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd";

Goal "w < z ==> w < z + (#1::int)";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd1";

Goal "(w < z + #1) = (w<=(z::int))";
by (arith_tac 1);
qed "zle_add1_eq_le";
Addsimps [zle_add1_eq_le];

Goal "(z = z + w) = (w = (#0::int))";
by (arith_tac 1);
qed "zadd_left_cancel0";
Addsimps [zadd_left_cancel0];

(*LOOPS as a simprule!*)
Goal "[| w + v < z; #0 <= v |] ==> w < (z::int)";
by (fast_arith_tac 1);
qed "zless_zadd_imp_zless";

(*LOOPS as a simprule!  Analogous to Suc_lessD*)
Goal "w + #1 < z ==> w < (z::int)";
by (fast_arith_tac 1);
qed "zless_zadd1_imp_zless";

Goal "w + #-1 = w - (#1::int)";
by (Simp_tac 1);
qed "zplus_minus1_conv";


(* nat *)

Goal "#0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z <= #0 ==> nat z = 0"; 
by (case_tac "z = #0" 1);
by (asm_simp_tac (simpset() addsimps [nat_le_int0]) 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [neg_eq_less_0, neg_nat, linorder_neq_iff]) 1);
qed "nat_le_0"; 

Addsimps [nat_0_le, nat_le_0];

val [major,minor] = Goal "[| #0 <= z;  !!m. z = int m ==> P |] ==> P"; 
by (rtac (major RS nat_0_le RS sym RS minor) 1);
qed "nonneg_eq_int"; 

Goal "#0 <= w ==> (nat w = m) = (w = int m)";
by Auto_tac;
qed "nat_eq_iff";

Goal "#0 <= w ==> (nat w < m) = (w < int m)";
by (rtac iffI 1);
by (asm_full_simp_tac 
    (simpset() delsimps [zless_int] addsimps [zless_int RS sym]) 2);
by (etac (nat_0_le RS subst) 1);
by (Simp_tac 1);
qed "nat_less_iff";


(*Users don't want to see (int 0), int(Suc 0) or w + - z*)
Addsimps [int_0, int_Suc, symmetric zdiff_def];

Goal "nat #0 = 0";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_0";

Goal "nat #1 = 1";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_1";

Goal "nat #2 = 2";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_2";

Goal "#0 <= w ==> (nat w < nat z) = (w<z)";
by (case_tac "neg z" 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
by (auto_tac (claset() addIs [zless_trans], 
	      simpset() addsimps [neg_eq_less_0, zle_def]));
qed "nat_less_eq_zless";

Goal "#0 < w | #0 <= z ==> (nat w <= nat z) = (w<=z)";
by (auto_tac (claset(), 
	      simpset() addsimps [linorder_not_less RS sym, 
				  zless_nat_conj]));
qed "nat_le_eq_zle";

(*Analogous to zadd_int, but more easily provable using the arithmetic in Bin*)
Goal "n<=m --> int m - int n = int (m-n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by Auto_tac;
qed_spec_mp "zdiff_int";


(** Products of signs **)

Goal "(m::int) < #0 ==> (#0 < m*n) = (n < #0)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1_neg], simpset()) 2);
by (eres_inst_tac [("P", "#0 < m * n")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [inst "k" "m" zmult_zless_mono1_neg], 
	       simpset()addsimps [order_le_less, zmult_commute]) 1);
qed "neg_imp_zmult_pos_iff";

Goal "(m::int) < #0 ==> (m*n < #0) = (#0 < n)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1], simpset()) 2);
by (eres_inst_tac [("P", "m * n < #0")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [zmult_zless_mono1_neg], 
	       simpset() addsimps [order_le_less]) 1);
qed "neg_imp_zmult_neg_iff";

Goal "#0 < (m::int) ==> (m*n < #0) = (n < #0)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1_neg], simpset()) 2);
by (eres_inst_tac [("P", "m * n < #0")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [zmult_zless_mono1], 
	       simpset() addsimps [order_le_less]) 1);
qed "pos_imp_zmult_neg_iff";

Goal "#0 < (m::int) ==> (#0 < m*n) = (#0 < n)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1], simpset()) 2);
by (eres_inst_tac [("P", "#0 < m * n")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [inst "k" "m" zmult_zless_mono1], 
	       simpset() addsimps [order_le_less, zmult_commute]) 1);
qed "pos_imp_zmult_pos_iff";

(** <= versions of the theorems above **)

Goal "(m::int) < #0 ==> (m*n <= #0) = (#0 <= n)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      neg_imp_zmult_pos_iff]) 1);
qed "neg_imp_zmult_nonpos_iff";

Goal "(m::int) < #0 ==> (#0 <= m*n) = (n <= #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      neg_imp_zmult_neg_iff]) 1);
qed "neg_imp_zmult_nonneg_iff";

Goal "#0 < (m::int) ==> (m*n <= #0) = (n <= #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      pos_imp_zmult_pos_iff]) 1);
qed "pos_imp_zmult_nonpos_iff";

Goal "#0 < (m::int) ==> (#0 <= m*n) = (#0 <= n)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      pos_imp_zmult_neg_iff]) 1);
qed "pos_imp_zmult_nonneg_iff";
