(*  Title:      IntDef.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

*)

header{*The Integers as Equivalence Classes over Pairs of Natural Numbers*}

theory IntDef = Equiv + NatArith:
constdefs
  intrel :: "((nat * nat) * (nat * nat)) set"
    "intrel == {p. \<exists>x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1}"

typedef (Integ)
  int = "UNIV//intrel"
    by (auto simp add: quotient_def) 

instance int :: ord ..
instance int :: zero ..
instance int :: one ..
instance int :: plus ..
instance int :: times ..
instance int :: minus ..

constdefs

  int :: "nat => int"
  "int m == Abs_Integ(intrel `` {(m,0)})"

  neg   :: "int => bool"
  "neg(Z) == \<exists>x y. x<y & (x,y::nat):Rep_Integ(Z)"

  (*For simplifying equalities*)
  iszero :: "int => bool"
  "iszero z == z = (0::int)"
  
defs (overloaded)
  
  zminus_def:    "- Z == Abs_Integ(\<Union>(x,y) \<in> Rep_Integ(Z). intrel``{(y,x)})"

  Zero_int_def:  "0 == int 0"
  One_int_def:   "1 == int 1"

  zadd_def:
   "z + w == 
       Abs_Integ(\<Union>(x1,y1) \<in> Rep_Integ(z). \<Union>(x2,y2) \<in> Rep_Integ(w).   
		 intrel``{(x1+x2, y1+y2)})"

  zdiff_def:  "z - (w::int) == z + (-w)"

  zless_def:  "z<w == neg(z - w)"

  zle_def:    "z <= (w::int) == ~(w < z)"

  zmult_def:
   "z * w == 
       Abs_Integ(\<Union>(x1,y1) \<in> Rep_Integ(z). \<Union>(x2,y2) \<in> Rep_Integ(w).   
		 intrel``{(x1*x2 + y1*y2, x1*y2 + y1*x2)})"

lemma intrel_iff [simp]: "(((x1,y1),(x2,y2)) \<in>  intrel) = (x1+y2 = x2+y1)"
by (unfold intrel_def, blast)

lemma equiv_intrel: "equiv UNIV intrel"
by (unfold intrel_def equiv_def refl_def sym_def trans_def, auto)

lemmas equiv_intrel_iff =
       eq_equiv_class_iff [OF equiv_intrel UNIV_I UNIV_I, simp]

lemma intrel_in_integ [simp]: "intrel``{(x,y)}:Integ"
by (unfold Integ_def intrel_def quotient_def, fast)

lemma inj_on_Abs_Integ: "inj_on Abs_Integ Integ"
apply (rule inj_on_inverseI)
apply (erule Abs_Integ_inverse)
done

declare inj_on_Abs_Integ [THEN inj_on_iff, simp] 
        Abs_Integ_inverse [simp]

lemma inj_Rep_Integ: "inj(Rep_Integ)"
apply (rule inj_on_inverseI)
apply (rule Rep_Integ_inverse)
done


(** int: the injection from "nat" to "int" **)

lemma inj_int: "inj int"
apply (rule inj_onI)
apply (unfold int_def)
apply (drule inj_on_Abs_Integ [THEN inj_onD])
apply (rule intrel_in_integ)+
apply (drule eq_equiv_class)
apply (rule equiv_intrel, fast)
apply (simp add: intrel_def)
done


subsection{*zminus: unary negation on Integ*}

lemma zminus_congruent: "congruent intrel (%(x,y). intrel``{(y,x)})"
apply (unfold congruent_def intrel_def)
apply (auto simp add: add_ac)
done

lemma zminus: "- Abs_Integ(intrel``{(x,y)}) = Abs_Integ(intrel `` {(y,x)})"
by (simp add: zminus_def equiv_intrel [THEN UN_equiv_class] zminus_congruent)

(*Every integer can be written in the form Abs_Integ(...) *)
lemma eq_Abs_Integ: 
     "(!!x y. z = Abs_Integ(intrel``{(x,y)}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_Integ [unfolded Integ_def, THEN quotientE]) 
apply (drule_tac f = Abs_Integ in arg_cong)
apply (rule_tac p = x in PairE)
apply (simp add: Rep_Integ_inverse)
done

lemma zminus_zminus [simp]: "- (- z) = (z::int)"
apply (rule_tac z = z in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zminus)
done

lemma inj_zminus: "inj(%z::int. -z)"
apply (rule inj_onI)
apply (drule_tac f = uminus in arg_cong, simp)
done

lemma zminus_0 [simp]: "- 0 = (0::int)"
by (simp add: int_def Zero_int_def zminus)


subsection{*neg: the test for negative integers*}


lemma not_neg_int [simp]: "~ neg(int n)"
by (simp add: neg_def int_def)

lemma neg_zminus_int [simp]: "neg(- (int (Suc n)))"
by (simp add: neg_def int_def zminus)


subsection{*zadd: addition on Integ*}

lemma zadd: 
  "Abs_Integ(intrel``{(x1,y1)}) + Abs_Integ(intrel``{(x2,y2)}) =  
   Abs_Integ(intrel``{(x1+x2, y1+y2)})"
apply (simp add: zadd_def UN_UN_split_split_eq)
apply (subst equiv_intrel [THEN UN_equiv_class2])
apply (auto simp add: congruent2_def)
done

lemma zminus_zadd_distrib [simp]: "- (z + w) = (- z) + (- w::int)"
apply (rule_tac z = z in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zminus zadd)
done

lemma zadd_commute: "(z::int) + w = w + z"
apply (rule_tac z = z in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ)
apply (simp (no_asm_simp) add: add_ac zadd)
done

lemma zadd_assoc: "((z1::int) + z2) + z3 = z1 + (z2 + z3)"
apply (rule_tac z = z1 in eq_Abs_Integ)
apply (rule_tac z = z2 in eq_Abs_Integ)
apply (rule_tac z = z3 in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zadd add_assoc)
done

(*For AC rewriting*)
lemma zadd_left_commute: "x + (y + z) = y + ((x + z)  ::int)"
  apply (rule mk_left_commute [of "op +"])
  apply (rule zadd_assoc)
  apply (rule zadd_commute)
  done

(*Integer addition is an AC operator*)
lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute

lemmas zmult_ac = Ring_and_Field.mult_ac

lemma zadd_int: "(int m) + (int n) = int (m + n)"
by (simp add: int_def zadd)

lemma zadd_int_left: "(int m) + (int n + z) = int (m + n) + z"
by (simp add: zadd_int zadd_assoc [symmetric])

lemma int_Suc: "int (Suc m) = 1 + (int m)"
by (simp add: One_int_def zadd_int)

(*also for the instance declaration int :: plus_ac0*)
lemma zadd_0 [simp]: "(0::int) + z = z"
apply (unfold Zero_int_def int_def)
apply (rule_tac z = z in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zadd)
done

lemma zadd_0_right [simp]: "z + (0::int) = z"
by (rule trans [OF zadd_commute zadd_0])

lemma zadd_zminus_inverse [simp]: "z + (- z) = (0::int)"
apply (unfold int_def Zero_int_def)
apply (rule_tac z = z in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zminus zadd add_commute)
done

lemma zadd_zminus_inverse2 [simp]: "(- z) + z = (0::int)"
apply (rule zadd_commute [THEN trans])
apply (rule zadd_zminus_inverse)
done

lemma zadd_zminus_cancel [simp]: "z + (- z + w) = (w::int)"
by (simp add: zadd_assoc [symmetric] zadd_0)

lemma zminus_zadd_cancel [simp]: "(-z) + (z + w) = (w::int)"
by (simp add: zadd_assoc [symmetric] zadd_0)

lemma zdiff0 [simp]: "(0::int) - x = -x"
by (simp add: zdiff_def)

lemma zdiff0_right [simp]: "x - (0::int) = x"
by (simp add: zdiff_def)

lemma zdiff_self [simp]: "x - x = (0::int)"
by (simp add: zdiff_def Zero_int_def)


(** Lemmas **)

lemma zadd_assoc_cong: "(z::int) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
by (simp add: zadd_assoc [symmetric])

lemma zadd_assoc_swap: "(z::int) + (v + w) = v + (z + w)"
by (rule zadd_commute [THEN zadd_assoc_cong])


subsection{*zmult: multiplication on Integ*}

(*Congruence property for multiplication*)
lemma zmult_congruent2: "congruent2 intrel  
        (%p1 p2. (%(x1,y1). (%(x2,y2).    
                    intrel``{(x1*x2 + y1*y2, x1*y2 + y1*x2)}) p2) p1)"
apply (rule equiv_intrel [THEN congruent2_commuteI])
apply (rule_tac [2] p=w in PairE)  
apply (force simp add: add_ac mult_ac, clarify) 
apply (simp (no_asm_simp) del: equiv_intrel_iff add: add_ac mult_ac)
apply (rename_tac x1 x2 y1 y2 z1 z2)
apply (rule equiv_class_eq [OF equiv_intrel intrel_iff [THEN iffD2]])
apply (simp add: intrel_def)
apply (subgoal_tac "x1*z1 + y2*z1 = y1*z1 + x2*z1 & x1*z2 + y2*z2 = y1*z2 + x2*z2", arith)
apply (simp add: add_mult_distrib [symmetric])
done

lemma zmult: 
   "Abs_Integ((intrel``{(x1,y1)})) * Abs_Integ((intrel``{(x2,y2)})) =    
    Abs_Integ(intrel `` {(x1*x2 + y1*y2, x1*y2 + y1*x2)})"
apply (unfold zmult_def)
apply (simp (no_asm_simp) add: UN_UN_split_split_eq zmult_congruent2 equiv_intrel [THEN UN_equiv_class2])
done

lemma zmult_zminus: "(- z) * w = - (z * (w::int))"
apply (rule_tac z = z in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zminus zmult add_ac)
done

lemma zmult_commute: "(z::int) * w = w * z"
apply (rule_tac z = z in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zmult add_ac mult_ac)
done

lemma zmult_assoc: "((z1::int) * z2) * z3 = z1 * (z2 * z3)"
apply (rule_tac z = z1 in eq_Abs_Integ)
apply (rule_tac z = z2 in eq_Abs_Integ)
apply (rule_tac z = z3 in eq_Abs_Integ)
apply (simp (no_asm_simp) add: add_mult_distrib2 zmult add_ac mult_ac)
done

lemma zadd_zmult_distrib: "((z1::int) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule_tac z = z1 in eq_Abs_Integ)
apply (rule_tac z = z2 in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ)
apply (simp add: add_mult_distrib2 zadd zmult add_ac mult_ac)
done

lemma zmult_zminus_right: "w * (- z) = - (w * (z::int))"
by (simp add: zmult_commute [of w] zmult_zminus)

lemma zadd_zmult_distrib2: "(w::int) * (z1 + z2) = (w * z1) + (w * z2)"
by (simp add: zmult_commute [of w] zadd_zmult_distrib)

lemma zdiff_zmult_distrib: "((z1::int) - z2) * w = (z1 * w) - (z2 * w)"
apply (unfold zdiff_def)
apply (subst zadd_zmult_distrib)
apply (simp add: zmult_zminus)
done

lemma zdiff_zmult_distrib2: "(w::int) * (z1 - z2) = (w * z1) - (w * z2)"
by (simp add: zmult_commute [of w] zdiff_zmult_distrib)

lemmas int_distrib =
  zadd_zmult_distrib zadd_zmult_distrib2 
  zdiff_zmult_distrib zdiff_zmult_distrib2

lemma zmult_int: "(int m) * (int n) = int (m * n)"
by (simp add: int_def zmult)

lemma zmult_0 [simp]: "0 * z = (0::int)"
apply (unfold Zero_int_def int_def)
apply (rule_tac z = z in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zmult)
done

lemma zmult_1 [simp]: "(1::int) * z = z"
apply (unfold One_int_def int_def)
apply (rule_tac z = z in eq_Abs_Integ)
apply (simp (no_asm_simp) add: zmult)
done

lemma zmult_0_right [simp]: "z * 0 = (0::int)"
by (rule trans [OF zmult_commute zmult_0])

lemma zmult_1_right [simp]: "z * (1::int) = z"
by (rule trans [OF zmult_commute zmult_1])


(* Theorems about less and less_equal *)

(*This lemma allows direct proofs of other <-properties*)
lemma zless_iff_Suc_zadd: 
    "(w < z) = (\<exists>n. z = w + int(Suc n))"
apply (unfold zless_def neg_def zdiff_def int_def)
apply (rule_tac z = z in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ, clarify)
apply (simp add: zadd zminus)
apply (safe dest!: less_imp_Suc_add)
apply (rule_tac x = k in exI)
apply (simp_all add: add_ac)
done

lemma zless_zadd_Suc: "z < z + int (Suc n)"
by (auto simp add: zless_iff_Suc_zadd zadd_assoc zadd_int)

lemma zless_trans: "[| z1<z2; z2<z3 |] ==> z1 < (z3::int)"
by (auto simp add: zless_iff_Suc_zadd zadd_assoc zadd_int)

lemma zless_not_sym: "!!w::int. z<w ==> ~w<z"
apply (safe dest!: zless_iff_Suc_zadd [THEN iffD1])
apply (rule_tac z = z in eq_Abs_Integ, safe)
apply (simp add: int_def zadd)
done

(* [| n<m;  ~P ==> m<n |] ==> P *)
lemmas zless_asym = zless_not_sym [THEN swap, standard]

lemma zless_not_refl: "!!z::int. ~ z<z"
apply (rule zless_asym [THEN notI])
apply (assumption+)
done

(* z<z ==> R *)
lemmas zless_irrefl = zless_not_refl [THEN notE, standard, elim!]


(*"Less than" is a linear ordering*)
lemma zless_linear: 
    "z<w | z=w | w<(z::int)"
apply (unfold zless_def neg_def zdiff_def)
apply (rule_tac z = z in eq_Abs_Integ)
apply (rule_tac z = w in eq_Abs_Integ, safe)
apply (simp add: zadd zminus Image_iff Bex_def)
apply (rule_tac m1 = "x+ya" and n1 = "xa+y" in less_linear [THEN disjE])
apply (force simp add: add_ac)+
done

lemma int_neq_iff: "!!w::int. (w ~= z) = (w<z | z<w)"
by (cut_tac zless_linear, blast)

(*** eliminates ~= in premises ***)
lemmas int_neqE = int_neq_iff [THEN iffD1, THEN disjE, standard]

lemma int_int_eq [iff]: "(int m = int n) = (m = n)"
by (fast elim!: inj_int [THEN injD])

lemma int_eq_0_conv [simp]: "(int n = 0) = (n = 0)"
by (simp add: Zero_int_def)

lemma zless_int [simp]: "(int m < int n) = (m<n)"
by (simp add: less_iff_Suc_add zless_iff_Suc_zadd zadd_int)

lemma int_less_0_conv [simp]: "~ (int k < 0)"
by (simp add: Zero_int_def)

lemma zero_less_int_conv [simp]: "(0 < int n) = (0 < n)"
by (simp add: Zero_int_def)


(*** Properties of <= ***)

lemma zle_int [simp]: "(int m <= int n) = (m<=n)"
by (simp add: zle_def le_def)

lemma zero_zle_int [simp]: "(0 <= int n)"
by (simp add: Zero_int_def)

lemma int_le_0_conv [simp]: "(int n <= 0) = (n = 0)"
by (simp add: Zero_int_def)

lemma zle_imp_zless_or_eq: "z <= w ==> z < w | z=(w::int)"
apply (unfold zle_def)
apply (cut_tac zless_linear)
apply (blast elim: zless_asym)
done

lemma zless_or_eq_imp_zle: "z<w | z=w ==> z <= (w::int)"
apply (unfold zle_def)
apply (cut_tac zless_linear)
apply (blast elim: zless_asym)
done

lemma int_le_less: "(x <= (y::int)) = (x < y | x=y)"
apply (rule iffI) 
apply (erule zle_imp_zless_or_eq) 
apply (erule zless_or_eq_imp_zle) 
done

lemma zle_refl: "w <= (w::int)"
by (simp add: int_le_less)

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma zle_linear: "(z::int) <= w | w <= z"
apply (simp add: int_le_less)
apply (cut_tac zless_linear, blast)
done

(* Axiom 'order_trans of class 'order': *)
lemma zle_trans: "[| i <= j; j <= k |] ==> i <= (k::int)"
apply (drule zle_imp_zless_or_eq) 
apply (drule zle_imp_zless_or_eq) 
apply (rule zless_or_eq_imp_zle) 
apply (blast intro: zless_trans) 
done

lemma zle_anti_sym: "[| z <= w; w <= z |] ==> z = (w::int)"
apply (drule zle_imp_zless_or_eq) 
apply (drule zle_imp_zless_or_eq) 
apply (blast elim: zless_asym) 
done

(* Axiom 'order_less_le' of class 'order': *)
lemma int_less_le: "((w::int) < z) = (w <= z & w ~= z)"
apply (simp add: zle_def int_neq_iff)
apply (blast elim!: zless_asym)
done

lemma zadd_left_cancel [simp]: "!!w::int. (z + w' = z + w) = (w' = w)"
apply safe
apply (drule_tac f = "%x. x + (-z) " in arg_cong)
apply (simp add: Zero_int_def [symmetric] zadd_ac)
done

instance int :: order
proof qed (assumption | rule zle_refl zle_trans zle_anti_sym int_less_le)+

instance int :: plus_ac0
proof qed (rule zadd_commute zadd_assoc zadd_0)+

instance int :: linorder
proof qed (rule zle_linear)


ML
{*
val int_def = thm "int_def";
val neg_def = thm "neg_def";
val iszero_def = thm "iszero_def";
val Zero_int_def = thm "Zero_int_def";
val One_int_def = thm "One_int_def";
val zadd_def = thm "zadd_def";
val zdiff_def = thm "zdiff_def";
val zless_def = thm "zless_def";
val zle_def = thm "zle_def";
val zmult_def = thm "zmult_def";

val intrel_iff = thm "intrel_iff";
val equiv_intrel = thm "equiv_intrel";
val equiv_intrel_iff = thm "equiv_intrel_iff";
val intrel_in_integ = thm "intrel_in_integ";
val inj_on_Abs_Integ = thm "inj_on_Abs_Integ";
val inj_Rep_Integ = thm "inj_Rep_Integ";
val inj_int = thm "inj_int";
val zminus_congruent = thm "zminus_congruent";
val zminus = thm "zminus";
val eq_Abs_Integ = thm "eq_Abs_Integ";
val zminus_zminus = thm "zminus_zminus";
val inj_zminus = thm "inj_zminus";
val zminus_0 = thm "zminus_0";
val not_neg_int = thm "not_neg_int";
val neg_zminus_int = thm "neg_zminus_int";
val zadd = thm "zadd";
val zminus_zadd_distrib = thm "zminus_zadd_distrib";
val zadd_commute = thm "zadd_commute";
val zadd_assoc = thm "zadd_assoc";
val zadd_left_commute = thm "zadd_left_commute";
val zadd_ac = thms "zadd_ac";
val zmult_ac = thms "zmult_ac";
val zadd_int = thm "zadd_int";
val zadd_int_left = thm "zadd_int_left";
val int_Suc = thm "int_Suc";
val zadd_0 = thm "zadd_0";
val zadd_0_right = thm "zadd_0_right";
val zadd_zminus_inverse = thm "zadd_zminus_inverse";
val zadd_zminus_inverse2 = thm "zadd_zminus_inverse2";
val zadd_zminus_cancel = thm "zadd_zminus_cancel";
val zminus_zadd_cancel = thm "zminus_zadd_cancel";
val zdiff0 = thm "zdiff0";
val zdiff0_right = thm "zdiff0_right";
val zdiff_self = thm "zdiff_self";
val zadd_assoc_cong = thm "zadd_assoc_cong";
val zadd_assoc_swap = thm "zadd_assoc_swap";
val zmult_congruent2 = thm "zmult_congruent2";
val zmult = thm "zmult";
val zmult_zminus = thm "zmult_zminus";
val zmult_commute = thm "zmult_commute";
val zmult_assoc = thm "zmult_assoc";
val zadd_zmult_distrib = thm "zadd_zmult_distrib";
val zmult_zminus_right = thm "zmult_zminus_right";
val zadd_zmult_distrib2 = thm "zadd_zmult_distrib2";
val zdiff_zmult_distrib = thm "zdiff_zmult_distrib";
val zdiff_zmult_distrib2 = thm "zdiff_zmult_distrib2";
val int_distrib = thms "int_distrib";
val zmult_int = thm "zmult_int";
val zmult_0 = thm "zmult_0";
val zmult_1 = thm "zmult_1";
val zmult_0_right = thm "zmult_0_right";
val zmult_1_right = thm "zmult_1_right";
val zless_iff_Suc_zadd = thm "zless_iff_Suc_zadd";
val zless_zadd_Suc = thm "zless_zadd_Suc";
val zless_trans = thm "zless_trans";
val zless_not_sym = thm "zless_not_sym";
val zless_asym = thm "zless_asym";
val zless_not_refl = thm "zless_not_refl";
val zless_irrefl = thm "zless_irrefl";
val zless_linear = thm "zless_linear";
val int_neq_iff = thm "int_neq_iff";
val int_neqE = thm "int_neqE";
val int_int_eq = thm "int_int_eq";
val int_eq_0_conv = thm "int_eq_0_conv";
val zless_int = thm "zless_int";
val int_less_0_conv = thm "int_less_0_conv";
val zero_less_int_conv = thm "zero_less_int_conv";
val zle_int = thm "zle_int";
val zero_zle_int = thm "zero_zle_int";
val int_le_0_conv = thm "int_le_0_conv";
val zle_imp_zless_or_eq = thm "zle_imp_zless_or_eq";
val zless_or_eq_imp_zle = thm "zless_or_eq_imp_zle";
val int_le_less = thm "int_le_less";
val zle_refl = thm "zle_refl";
val zle_linear = thm "zle_linear";
val zle_trans = thm "zle_trans";
val zle_anti_sym = thm "zle_anti_sym";
val int_less_le = thm "int_less_le";
val zadd_left_cancel = thm "zadd_left_cancel";

val diff_less_eq = thm"diff_less_eq";
val less_diff_eq = thm"less_diff_eq";
val eq_diff_eq = thm"eq_diff_eq";
val diff_eq_eq = thm"diff_eq_eq";
val diff_le_eq = thm"diff_le_eq";
val le_diff_eq = thm"le_diff_eq";
val compare_rls = thms "compare_rls";
*}

end
