(*  Title:      ZF/Induct/Multiset
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory

A definitional theory of multisets, including a wellfoundedness 
proof for the multiset order.

The theory features ordinal multisets and the usual ordering.

*)

(* Properties of the original "restrict" from ZF.thy. *)

Goalw [funrestrict_def,lam_def]
    "[| f: Pi(C,B);  A<=C |] ==> funrestrict(f,A) <= f";
by (blast_tac (claset() addIs [apply_Pair]) 1);
qed "funrestrict_subset";

val prems = Goalw [funrestrict_def]
    "[| !!x. x:A ==> f`x: B(x) |] ==> funrestrict(f,A) : Pi(A,B)";  
by (rtac lam_type 1);
by (eresolve_tac prems 1);
qed "funrestrict_type";

Goal "[| f: Pi(C,B);  A<=C |] ==> funrestrict(f,A) : Pi(A,B)";  
by (blast_tac (claset() addIs [apply_type, funrestrict_type]) 1);
qed "funrestrict_type2";

Goalw [funrestrict_def] "a : A ==> funrestrict(f,A) ` a = f`a";
by (etac beta 1);
qed "funrestrict";

Goalw [funrestrict_def] "funrestrict(f,0) = 0";
by (Simp_tac 1);
qed "funrestrict_empty";

Addsimps [funrestrict, funrestrict_empty];

Goalw [funrestrict_def, lam_def] "domain(funrestrict(f,C)) = C";
by (Blast_tac 1);
qed "domain_funrestrict";
Addsimps [domain_funrestrict];

Goal "f : cons(a, b) -> B ==> f = cons(<a, f ` a>, funrestrict(f, b))";
by (rtac equalityI 1);
by (blast_tac (claset() addIs [apply_Pair, impOfSubs funrestrict_subset]) 2);
by (auto_tac (claset() addSDs [Pi_memberD],
	       simpset() addsimps [funrestrict_def, lam_def]));
qed "fun_cons_funrestrict_eq";

Addsimps [domain_of_fun];
Delrules [domainE];

(* The following tactic moves the condition `simp_cond' to the begining
   of the list of hypotheses and then makes simplifications accordingly *)

fun rotate_simp_tac simp_cond i =
(dres_inst_tac [("psi", simp_cond)] asm_rl i THEN rotate_tac ~1 i
 THEN Asm_full_simp_tac i);

(* A useful simplification rule *)

Goal "(f:A -> nat-{0}) <-> f:A->nat&(ALL a:A. f`a:nat & 0 < f`a)";
by Safe_tac;
by (res_inst_tac [("B1", "range(f)")] (Pi_mono RS subsetD) 4);
by (auto_tac (claset()  addSIs [Ord_0_lt]
                        addDs [apply_type, Diff_subset RS Pi_mono RS subsetD],
              simpset() addsimps [range_of_fun, apply_iff]));
qed "multiset_fun_iff";

(** The multiset space  **)
Goalw [multiset_def]
 "[| multiset(M); mset_of(M)<=A |] ==> M:Mult(A)";
by (auto_tac (claset(), simpset()
             addsimps [multiset_fun_iff, mset_of_def]));
by (rotate_simp_tac "M:?u" 1);
by (res_inst_tac [("B1","nat-{0}")] (FiniteFun_mono RS subsetD) 1);
by (ALLGOALS(Asm_simp_tac));
by (rtac (Finite_into_Fin RSN (2, Fin_mono RS subsetD) RS fun_FiniteFunI) 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [multiset_fun_iff])));
qed "multiset_into_Mult";

Goalw [multiset_def, mset_of_def]
 "M:Mult(A) ==> multiset(M) & mset_of(M)<=A";
by (ftac FiniteFun_is_fun 1);
by (dtac FiniteFun_domain_Fin 1);
by (ftac FinD 1);
by (Clarify_tac 1);
by (res_inst_tac [("x", "domain(M)")] exI 1);
by (blast_tac (claset() addIs [Fin_into_Finite]) 1);
qed "Mult_into_multiset";

Goal "M:Mult(A) <-> multiset(M) & mset_of(M)<=A";
by (blast_tac (claset() addDs [Mult_into_multiset]
                        addIs [multiset_into_Mult]) 1);
qed "Mult_iff_multiset";

Goal "multiset(M) <-> M:Mult(mset_of(M))";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "multiset_iff_Mult_mset_of";

(** multiset  **)

(* the empty multiset is 0 *)

Goal "multiset(0)";
by (auto_tac (claset() addIs (thms"FiniteFun.intros"), 
        simpset()  addsimps [multiset_iff_Mult_mset_of]));
qed "multiset_0";
Addsimps [multiset_0];

(** mset_of **)

Goalw [multiset_def, mset_of_def]
"multiset(M) ==> Finite(mset_of(M))";
by Auto_tac;
qed "multiset_set_of_Finite";
Addsimps [multiset_set_of_Finite];

Goalw [mset_of_def]
"mset_of(0) = 0";
by Auto_tac;
qed "mset_of_0";
AddIffs [mset_of_0];

Goalw [multiset_def, mset_of_def]
"multiset(M) ==> mset_of(M)=0 <-> M=0";
by Auto_tac;
qed "mset_is_0_iff";

Goalw [msingle_def, mset_of_def] 
  "mset_of({#a#}) = {a}";
by Auto_tac;
qed "mset_of_single";
AddIffs [mset_of_single];

Goalw [mset_of_def, munion_def]
 "mset_of(M +# N) = mset_of(M) Un mset_of(N)";
by Auto_tac;
qed "mset_of_union";
AddIffs [mset_of_union];

Goalw [multiset_def]
"multiset(M) ==> \
\ k:mset_of(M -# {#a#}) <-> (k=a & 1 < mcount(M,a)) | (k~= a & k:mset_of(M))";
by (rewrite_goals_tac [normalize_def, mset_of_def, msingle_def, 
                        mdiff_def, mcount_def]);
by (auto_tac (claset() addDs [domain_type] 
                       addIs [zero_less_diff RS iffD1],
              simpset() addsimps 
                     [multiset_fun_iff, apply_iff]));
qed "melem_diff_single";

Goalw [mdiff_def, multiset_def]
 "[| multiset(M); mset_of(M)<=A |] ==> mset_of(M -# N) <= A";
by (auto_tac (claset(), simpset() addsimps [normalize_def]));
by (rewtac mset_of_def);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [multiset_fun_iff])));
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(rotate_simp_tac "M:?u"));
by Auto_tac;
qed "mset_of_diff";
Addsimps [mset_of_diff];

(* msingle *)

Goalw [msingle_def] 
  "{#a#} ~= 0 & 0 ~= {#a#}";
by Auto_tac;
qed "msingle_not_0";
AddIffs [msingle_not_0];

Goalw [msingle_def]
 "({#a#} = {#b#}) <->  (a = b)";
by (auto_tac (claset() addEs [equalityE], simpset()));
qed "msingle_eq_iff";
AddIffs [msingle_eq_iff];

Goalw [multiset_def, msingle_def]  "multiset({#a#})";
by (res_inst_tac [("x", "{a}")] exI 1);
by (auto_tac (claset() addIs [Finite_cons, Finite_0, 
                              fun_extend3], simpset()));
qed "msingle_multiset";
AddIffs [msingle_multiset];

(** normalize **)

Goalw [normalize_def, funrestrict_def, mset_of_def]
 "normalize(normalize(f)) = normalize(f)";
by Auto_tac;
qed "normalize_idem";
AddIffs [normalize_idem];

Goalw [multiset_def] 
 "multiset(M) ==> normalize(M) = M";
by (rewrite_goals_tac [normalize_def, mset_of_def]);
by (auto_tac (claset(), simpset() 
          addsimps [funrestrict_def, multiset_fun_iff]));
qed "normalize_multiset";
Addsimps [normalize_multiset];

Goalw [multiset_def]
"[| f:A -> nat;  Finite(A) |] ==> multiset(normalize(f))";
by (rewrite_goals_tac [normalize_def, mset_of_def]);
by Auto_tac;
by (res_inst_tac [("x", "{x:A . 0<f`x}")] exI 1);
by (auto_tac (claset() addIs [Collect_subset RS subset_Finite,
                              funrestrict_type], simpset()));
qed "multiset_normalize";

(** Typechecking rules for union and difference of multisets **)

Goal "[| n:nat; m:nat |] ==> 0 < m #+ n <-> (0 < m | 0 < n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "zero_less_add";

(* union *)

Goalw [multiset_def]
"[| multiset(M); multiset(N) |] ==> multiset(M +# N)";
by (rewrite_goals_tac [munion_def, mset_of_def]);
by Auto_tac;
by (res_inst_tac [("x", "A Un Aa")] exI 1);
by (auto_tac (claset() addSIs [lam_type] addIs [Finite_Un], 
    simpset() addsimps [multiset_fun_iff, zero_less_add]));
qed "munion_multiset";
Addsimps [munion_multiset];

(* difference *)

Goalw [mdiff_def]
"multiset(M) ==> multiset(M -# N)";
by (res_inst_tac [("A", "mset_of(M)")] multiset_normalize 1);
by (asm_simp_tac (simpset() addsimps [multiset_set_of_Finite]) 2);
by (auto_tac (claset(), simpset() addsimps [mset_of_def, multiset_def]));
by (auto_tac (claset() addSIs [lam_type], 
           simpset() addsimps [multiset_fun_iff]));
qed "mdiff_multiset";
Addsimps [mdiff_multiset];

(** Algebraic properties of multisets **)

(* Union *)

Goalw [multiset_def]
  "multiset(M) ==> M +# 0 = M & 0 +# M = M";
by (auto_tac (claset(), simpset() addsimps [munion_def, mset_of_def]));
qed "munion_0";
Addsimps [munion_0];

Goalw [multiset_def]
  "[| multiset(M); multiset(N) |] ==> M +# N = N +# M";
by (rewrite_goals_tac [munion_def, mset_of_def]);
by (auto_tac (claset() addSIs [lam_cong],  simpset()));
qed "munion_commute";

Goalw [multiset_def]
"[|multiset(M); multiset(N); multiset(K)|] ==> (M +# N) +# K = M +# (N +# K)";
by (rewrite_goals_tac [munion_def, mset_of_def]);
by (rtac lam_cong 1);
by Auto_tac;
qed "munion_assoc";

Goalw [multiset_def]
"[|multiset(M); multiset(N); multiset(K)|]==> M +# (N +# K) = N +# (M +# K)";
by (rewrite_goals_tac [munion_def, mset_of_def]);
by (rtac lam_cong 1);
by Auto_tac;
qed "munion_lcommute";

val munion_ac = [munion_commute, munion_assoc, munion_lcommute];

(* Difference *)

Goalw [mdiff_def] "M -# M = 0";
by (simp_tac (simpset() addsimps
           [diff_self_eq_0, normalize_def, mset_of_def]) 1);
qed "mdiff_self_eq_0";
AddIffs [mdiff_self_eq_0];

Goalw [multiset_def] "multiset(M) ==> M -# 0 = M & 0 -# M = 0";
by (rewrite_goals_tac [mdiff_def, normalize_def]);
by (auto_tac (claset(), simpset() 
         addsimps [multiset_fun_iff, mset_of_def, funrestrict_def]));
qed "mdiff_0";
Addsimps [mdiff_0]; 

Goal "multiset(M) ==> M +# {#a#} -# {#a#} = M";
by (rewrite_goals_tac [multiset_def, munion_def, mdiff_def, 
                       msingle_def, normalize_def, mset_of_def]);
by (auto_tac (claset(), 
       simpset() addcongs [if_cong]
		 addsimps [ltD, multiset_fun_iff,
                           funrestrict_def, subset_Un_iff2 RS iffD1])); 
by (subgoal_tac "{x \\<in> A \\<union> {a} . x \\<noteq> a \\<and> x \\<in> A} = A" 2);
by (rtac fun_extension 1);
by Auto_tac; 
qed "mdiff_union_inverse2";
Addsimps [mdiff_union_inverse2];

(** Count of elements **)

Goalw [multiset_def] "multiset(M) ==> mcount(M, a):nat";
by (rewrite_goals_tac [mcount_def, mset_of_def]);
by (auto_tac (claset(), simpset() addsimps [multiset_fun_iff]));
qed "mcount_type";
AddTCs [mcount_type];
Addsimps [mcount_type];

Goalw [mcount_def]  "mcount(0, a) = 0";
by Auto_tac;
qed "mcount_0";
Addsimps [mcount_0];

Goalw [mcount_def, mset_of_def, msingle_def]
"mcount({#b#}, a) = (if a=b then 1 else 0)";
by Auto_tac;
qed "mcount_single";
Addsimps [mcount_single];

Goalw [multiset_def]
"[| multiset(M); multiset(N) |] \
\ ==>  mcount(M +# N, a) = mcount(M, a) #+ mcount (N, a)";
by (auto_tac (claset(), simpset() addsimps 
                      [multiset_fun_iff, mcount_def, 
                       munion_def, mset_of_def ]));
qed "mcount_union";
Addsimps [mcount_union];

Goalw [multiset_def]
"[| multiset(M); multiset(N) |] \
\ ==> mcount(M -# N, a) = mcount(M, a) #- mcount(N, a)";
by (auto_tac (claset() addSDs [not_lt_imp_le], 
      simpset() addsimps [mdiff_def, multiset_fun_iff, 
                          mcount_def, normalize_def, mset_of_def]));
qed "mcount_diff";
Addsimps [mcount_diff];

Goalw [multiset_def]
 "[| multiset(M); a:mset_of(M) |] ==> 0 < mcount(M, a)";
by (Clarify_tac 1);
by (rewrite_goals_tac [mcount_def, mset_of_def]);
by (rotate_simp_tac "M:?u" 1);
by (asm_full_simp_tac (simpset() addsimps [multiset_fun_iff]) 1); 
qed "mcount_elem";

(** msize **)

Goalw [msize_def] "msize(0) = #0";
by Auto_tac;
qed "msize_0";
AddIffs [msize_0];

Goalw [msize_def] "msize({#a#}) = #1";
by (rewrite_goals_tac [msingle_def, mcount_def, mset_of_def]);
by (auto_tac (claset(), simpset() addsimps [Finite_0]));
qed "msize_single";
AddIffs [msize_single];

Goalw [msize_def] "msize(M):int";
by Auto_tac;
qed "msize_type";
Addsimps [msize_type];
AddTCs [msize_type];

Goalw [msize_def] "multiset(M)==> #0 $<= msize(M)";
by (auto_tac (claset() addIs [g_zpos_imp_setsum_zpos], simpset()));
qed "msize_zpositive";

Goal "multiset(M) ==> EX n:nat. msize(M)= $# n";
by (rtac not_zneg_int_of 1);
by (ALLGOALS(asm_simp_tac 
      (simpset() addsimps [msize_type RS znegative_iff_zless_0,
                          not_zless_iff_zle,msize_zpositive])));
qed "msize_int_of_nat";

Goalw [multiset_def]
 "[| M~=0; multiset(M) |] ==> EX a:mset_of(M). 0 < mcount(M, a)";
by (etac not_emptyE 1);
by (rewrite_goal_tac [mset_of_def, mcount_def] 1);
by (auto_tac (claset(), simpset() addsimps [multiset_fun_iff]));
by (blast_tac (claset() addSDs [fun_is_rel]) 1);
qed "not_empty_multiset_imp_exist";

Goalw [msize_def] "multiset(M) ==> msize(M)=#0 <-> M=0";
by Auto_tac;
by (res_inst_tac [("Pa", "setsum(?u,?v) ~= #0")] swap 1);
by (Blast_tac 1);
by (dtac not_empty_multiset_imp_exist 1);
by (ALLGOALS(Clarify_tac));
by (subgoal_tac "Finite(mset_of(M) - {a})" 1);
by (asm_simp_tac (simpset() addsimps [Finite_Diff]) 2);
by (subgoal_tac "setsum(%x. $# mcount(M, x), cons(a, mset_of(M)-{a}))=#0" 1);
by (asm_simp_tac (simpset() addsimps [cons_Diff]) 2);
by (Asm_full_simp_tac 1);
by (subgoal_tac "#0 $<= setsum(%x. $# mcount(M, x), mset_of(M) - {a})" 1);
by (rtac g_zpos_imp_setsum_zpos 2);
by (auto_tac (claset(), simpset() 
              addsimps [Finite_Diff, not_zless_iff_zle RS iff_sym, 
                        znegative_iff_zless_0 RS iff_sym]));
by (dtac (rotate_prems 1 not_zneg_int_of) 1);
by (auto_tac (claset(), simpset() delsimps [int_of_0]
       addsimps [int_of_add RS sym, int_of_0 RS sym]));
qed "msize_eq_0_iff";

Goal 
"cons(x, A) Int B = (if x:B then cons(x, A Int B) else A Int B)";
by Auto_tac;
qed "cons_Int_right_cases";

Goal
"Finite(A) ==> setsum(%a. $# mcount(N, a), A Int mset_of(N)) \
\            = setsum(%a. $# mcount(N, a), A)";
by (etac Finite_induct 1);
by Auto_tac;
by (subgoal_tac "Finite(B Int mset_of(N))" 1);
by (blast_tac (claset() addIs [subset_Finite]) 2);
by (auto_tac (claset(), 
         simpset() addsimps [mcount_def, cons_Int_right_cases]));
qed "setsum_mcount_Int";

Goalw [msize_def]
"[| multiset(M); multiset(N) |] ==> msize(M +# N) = msize(M) $+ msize(N)";
by (asm_simp_tac (simpset() addsimps
        [setsum_Un , setsum_addf, int_of_add, setsum_mcount_Int]) 1);
by (stac Int_commute 1);
by (asm_simp_tac (simpset() addsimps [setsum_mcount_Int]) 1);
qed "msize_union"; 
Addsimps [msize_union];

Goalw [msize_def] "[|msize(M)= $# succ(n); n:nat|] ==> EX a. a:mset_of(M)";
by (blast_tac (claset() addDs [setsum_succD]) 1);
qed "msize_eq_succ_imp_elem";

(** Equality of multisets **)

Goalw [multiset_def] 
"[| multiset(M); multiset(N); ALL a. mcount(M, a)=mcount(N, a) |] \
\   ==> mset_of(M)=mset_of(N)";
by (rtac sym 1 THEN rtac equalityI 1);
by (rewrite_goals_tac [mcount_def, mset_of_def]);
by (auto_tac (claset(), simpset() addsimps [multiset_fun_iff]));
by (ALLGOALS(rotate_simp_tac "M:?u"));
by (ALLGOALS(rotate_simp_tac "N:?u"));
by (ALLGOALS(dres_inst_tac [("x", "x")] spec));
by (case_tac "x:Aa" 2 THEN case_tac "x:A" 1);
by Auto_tac;
qed "equality_lemma";

Goal  
"[| multiset(M); multiset(N) |]==> M=N<->(ALL a. mcount(M, a)=mcount(N, a))";
by Auto_tac;
by (subgoal_tac "mset_of(M) = mset_of(N)" 1);
by (blast_tac (claset() addIs [equality_lemma]) 2);
by (rewrite_goals_tac [multiset_def, mset_of_def]);
by (auto_tac (claset(), simpset() addsimps [multiset_fun_iff]));
by (rotate_simp_tac "M:?u" 1);
by (rotate_simp_tac "N:?u" 1);
by (rtac fun_extension 1);
by (Blast_tac 1 THEN Blast_tac 1);
by (dres_inst_tac [("x", "x")] spec 1);
by (auto_tac (claset(), simpset() addsimps [mcount_def, mset_of_def]));
qed "multiset_equality";

(** More algebraic properties of multisets **)

Goal "[|multiset(M); multiset(N)|]==>(M +# N =0) <-> (M=0 & N=0)";
by (auto_tac (claset(), simpset() addsimps [multiset_equality]));
qed "munion_eq_0_iff";
Addsimps [munion_eq_0_iff];

Goal "[|multiset(M); multiset(N)|]==>(0=M +# N) <-> (M=0 & N=0)";
by (rtac iffI 1 THEN dtac sym 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [multiset_equality])));
qed "empty_eq_munion_iff";
Addsimps [empty_eq_munion_iff];

Goal 
"[| multiset(M); multiset(N); multiset(K) |]==>(M +# K = N +# K)<->(M=N)";
by (auto_tac (claset(), simpset() addsimps [multiset_equality]));
qed "munion_right_cancel";
Addsimps [munion_right_cancel];

Goal 
"[|multiset(K); multiset(M); multiset(N)|] ==>(K +# M = K +# N) <-> (M = N)";
by (auto_tac (claset(), simpset() addsimps [multiset_equality]));
qed "munion_left_cancel";
Addsimps [munion_left_cancel];

Goal "[| m:nat; n:nat |] ==> (m #+ n = 1) <-> (m=1 & n=0) | (m=0 & n=1)";
by (induct_tac "n" 1 THEN Auto_tac);
qed "nat_add_eq_1_cases";

Goal "[|multiset(M); multiset(N)|]                                     \
\ ==> (M +# N = {#a#}) <->  (M={#a#} & N=0) | (M = 0 & N = {#a#})";
by (asm_simp_tac (simpset() addsimps [multiset_equality]) 1);
by Safe_tac;
by (ALLGOALS(Asm_full_simp_tac));
by (case_tac "aa=a" 1);
by (dres_inst_tac [("x", "aa")] spec 2);
by (dres_inst_tac [("x", "a")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [nat_add_eq_1_cases]) 1);
by (Asm_full_simp_tac 1);
by (case_tac "aaa=aa" 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x", "aa")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [nat_add_eq_1_cases]) 1);
by (case_tac "aaa=a" 1);
by (dres_inst_tac [("x", "aa")] spec 4);
by (dres_inst_tac [("x", "a")] spec 3);
by (dres_inst_tac [("x", "aaa")] spec 2);
by (dres_inst_tac [("x", "aa")] spec 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [nat_add_eq_1_cases])));
qed "munion_is_single";

Goal "[| multiset(M); multiset(N) |] \
\ ==> ({#a#} = M +# N) <-> ({#a#} = M  & N=0 | M = 0 & {#a#} = N)";
by (simp_tac (simpset() addsimps [sym]) 1);
by (subgoal_tac "({#a#} = M +# N) <-> (M +# N = {#a#})" 1);
by (asm_simp_tac (simpset() addsimps [munion_is_single]) 1);
by (REPEAT(blast_tac (claset() addDs [sym]) 1));
qed "msingle_is_union";

(** Towards induction over multisets **)

Goalw [multiset_def]  
"Finite(A) \
\ ==>  (ALL M. multiset(M) -->                                     \
\ (ALL a:mset_of(M). setsum(%x. $# mcount(M(a:=M`a #- 1), x), A) = \
\ (if a:A then setsum(%x. $# mcount(M, x), A) $- #1                \
\          else setsum(%x. $# mcount(M, x), A))))";
by (etac Finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [multiset_fun_iff]));
by (rewrite_goals_tac [mset_of_def, mcount_def]);
by (case_tac "x:A" 1);
by Auto_tac;
by (rotate_simp_tac "M:?u" 2);
by (subgoal_tac "$# M ` x $+ #-1 = $# M ` x $- $# 1" 1);
by (etac ssubst 1);
by (rtac int_of_diff 1);
by Auto_tac;
qed "setsum_decr";

(*FIXME: we should not have to rename x to x' below!  There's a bug in the
  interaction between simproc inteq_cancel_numerals and the simplifier.*)
Goalw [multiset_def]
     "Finite(A) \
\     ==> ALL M. multiset(M) --> (ALL a:mset_of(M).            \
\          setsum(%x'. $# mcount(funrestrict(M, mset_of(M)-{a}), x'), A) = \
\          (if a:A then setsum(%x'. $# mcount(M, x'), A) $- $# M`a     \
\           else setsum(%x'. $# mcount(M, x'), A)))";
by (etac Finite_induct 1);
by (auto_tac (claset(), 
              simpset() addsimps [multiset_fun_iff, 
                                  mcount_def, mset_of_def]));
qed "setsum_decr2";

Goal "[| Finite(A); multiset(M); a:mset_of(M) |] \
\     ==> setsum(%x. $# mcount(funrestrict(M, mset_of(M)-{a}), x), A - {a}) = \
\         (if a:A then setsum(%x. $# mcount(M, x), A) $- $# M`a\
\          else setsum(%x. $# mcount(M, x), A))";
by (subgoal_tac "setsum(%x. $# mcount(funrestrict(M, mset_of(M)-{a}),x),A-{a}) = \
\                setsum(%x. $# mcount(funrestrict(M, mset_of(M)-{a}),x),A)" 1);
by (rtac (setsum_Diff RS sym) 2);
by (REPEAT(asm_simp_tac (simpset() addsimps [mcount_def, mset_of_def]) 2));
by (rtac sym 1 THEN rtac ssubst 1);
by (Blast_tac 1);
by (rtac sym 1 THEN dtac setsum_decr2 1);
by Auto_tac;
qed "setsum_decr3";

Goal "n:nat ==> n le 1 <-> (n=0 | n=1)";
by (auto_tac (claset() addEs [natE], simpset()));
qed "nat_le_1_cases";

Goal "[| 0<n; n:nat |] ==> succ(n #- 1) = n";
by (subgoal_tac "1 le n" 1);
by (dtac add_diff_inverse2 1);
by Auto_tac;
qed "succ_pred_eq_self";

val major::prems = Goal
  "[| n:nat; P(0); \
\   (!!M a. [| multiset(M); a~:mset_of(M); P(M) |] ==> P(cons(<a, 1>, M))); \
\   (!!M b. [| multiset(M); b:mset_of(M); P(M) |] ==> P(M(b:= M`b #+ 1))) |] \
 \   ==> (ALL M. multiset(M)--> \
\ (setsum(%x. $# mcount(M, x), {x:mset_of(M). 0 < M`x}) = $# n) --> P(M))";
by (rtac (major RS nat_induct) 1);
by (ALLGOALS(Clarify_tac));
by (ftac msize_eq_0_iff 1);
by (auto_tac (claset(), 
              simpset() addsimps [mset_of_def, multiset_def,  
                                  multiset_fun_iff, msize_def]@prems));
by (rotate_simp_tac "M:?u" 1);
by (rotate_simp_tac "M:?u" 2);
by (rotate_simp_tac "ALL a:A. ?u(a)" 1);
by (subgoal_tac "setsum(%x. $# mcount(M, x), A)=$# succ(x)" 1);
by (dtac setsum_succD 1 THEN Auto_tac);
by (case_tac "1 <M`a" 1);
by (dtac not_lt_imp_le 2);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [nat_le_1_cases])));
by (subgoal_tac "M=(M(a:=M`a #- 1))(a:=(M(a:=M`a #- 1))`a #+ 1)" 1);
by (res_inst_tac [("A","A"),("B","%x. nat"),("D","%x. nat")] fun_extension 2);
by (REPEAT(rtac update_type 3));
by (ALLGOALS(Asm_simp_tac));
by (Clarify_tac 2);
by (rtac (succ_pred_eq_self RS sym) 2);
by (ALLGOALS(Asm_simp_tac));
by (rtac subst 1 THEN rtac sym 1 THEN Blast_tac 1 THEN resolve_tac prems 1);
by (simp_tac (simpset() addsimps [multiset_def, multiset_fun_iff]) 1);
by (res_inst_tac [("x", "A")] exI 1);
by (force_tac (claset() addIs [update_type], simpset()) 1);
by (asm_simp_tac (simpset() addsimps [mset_of_def, mcount_def]) 1);
by (dres_inst_tac [("x", "M(a := M ` a #- 1)")] spec 1);
by (dtac mp 1 THEN dtac mp 2);
by (ALLGOALS(Asm_full_simp_tac));
by (res_inst_tac [("x", "A")] exI 1);
by (auto_tac (claset() addIs [update_type], simpset()));
by (subgoal_tac "Finite({x:cons(a, A). x~=a-->0<M`x})" 1);
by (blast_tac(claset() addIs [Collect_subset RS subset_Finite,Finite_cons])2);
by (dres_inst_tac [("A", "{x:cons(a, A). x~=a-->0<M`x}")] setsum_decr 1);
by (dres_inst_tac [("x", "M")] spec 1);
by (subgoal_tac "multiset(M)" 1);
by (simp_tac (simpset() addsimps [multiset_def, multiset_fun_iff]) 2);
by (res_inst_tac [("x", "A")] exI 2);
by (Force_tac 2);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [mset_of_def])));
by (dres_inst_tac [("psi", "ALL x:A. ?u(x)")] asm_rl 1);
by (dres_inst_tac [("x", "a")] bspec 1);
by (Asm_simp_tac 1);
by (subgoal_tac "cons(a, A)= A" 1);
by (Blast_tac 2);
by (rotate_simp_tac "cons(a, A) = A" 1);
by (rotate_simp_tac "ALL x:A. ?u(x)" 1);
by (rotate_simp_tac "ALL x:A. ?u(x)" 2);
by (subgoal_tac "M=cons(<a, M`a>, funrestrict(M, A-{a}))" 1);
by (rtac  fun_cons_funrestrict_eq 2);
by (subgoal_tac "cons(a, A-{a}) = A" 2);
by (REPEAT(Force_tac 2));
by (res_inst_tac [("a", "cons(<a, 1>, funrestrict(M, A - {a}))")] ssubst 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "multiset(funrestrict(M, A - {a}))" 1);
by (simp_tac (simpset() addsimps [multiset_def, multiset_fun_iff]) 2);
by (res_inst_tac [("x", "A-{a}")] exI 2);
by Safe_tac;
by (res_inst_tac [("A", "A-{a}")] apply_type 3);
by (asm_simp_tac (simpset() addsimps [funrestrict]) 5);
by (REPEAT(blast_tac (claset() addIs [Finite_Diff, funrestrict_type]) 2));;
by (resolve_tac prems 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [mset_of_def]) 1);
by (dres_inst_tac [("x", "funrestrict(M, A-{a})")] spec 1);
by (dtac mp 1);
by (res_inst_tac [("x", "A-{a}")] exI 1);
by (auto_tac (claset() addIs [Finite_Diff, funrestrict_type], 
             simpset() addsimps [funrestrict]));
by (forw_inst_tac [("A", "A"), ("M", "M"), ("a", "a")] setsum_decr3 1);
by (asm_simp_tac  (simpset() addsimps [multiset_def, multiset_fun_iff]) 1);
by (Blast_tac 1);
by (asm_simp_tac (simpset() addsimps [mset_of_def]) 1);
by (dres_inst_tac [("b", "if ?u then ?v else ?w")] sym 1);
by (ALLGOALS(rotate_simp_tac "ALL x:A. ?u(x)"));
by (subgoal_tac "{x:A - {a} . 0 < funrestrict(M, A - {x}) ` x} = A - {a}" 1);
by (auto_tac (claset() addSIs [setsum_cong], 
              simpset() addsimps [zdiff_eq_iff, 
               zadd_commute, multiset_def, multiset_fun_iff,mset_of_def]));
qed "multiset_induct_aux";

val major::prems = Goal
  "[| multiset(M); P(0); \
\   (!!M a. [| multiset(M); a~:mset_of(M); P(M) |] ==> P(cons(<a, 1>, M)));  \
\   (!!M b. [| multiset(M); b:mset_of(M);  P(M) |] ==> P(M(b:= M`b #+ 1))) |] \
 \   ==> P(M)";
by (subgoal_tac "EX n:nat. setsum(\\<lambda>x. $# mcount(M, x), \
              \ {x : mset_of(M) . 0 < M ` x}) = $# n" 1);
by (rtac not_zneg_int_of 2);
by (ALLGOALS(asm_simp_tac (simpset() 
        addsimps [znegative_iff_zless_0, not_zless_iff_zle])));
by (rtac g_zpos_imp_setsum_zpos 2);
by (blast_tac (claset() addIs [major RS multiset_set_of_Finite, 
                              Collect_subset RS subset_Finite]) 2);
by (asm_full_simp_tac (simpset() addsimps [multiset_def, multiset_fun_iff]) 2);
by (Clarify_tac 1);
by (rtac (multiset_induct_aux RS spec RS mp RS mp) 1);
by (resolve_tac prems 4);
by (resolve_tac prems 3);
by (auto_tac (claset(), simpset() addsimps major::prems));
qed "multiset_induct2";

Goalw [multiset_def, msingle_def] 
 "[| multiset(M); a ~:mset_of(M) |] ==> M +# {#a#} = cons(<a, 1>, M)";
by (auto_tac (claset(), simpset() addsimps [munion_def]));
by (rewtac mset_of_def);
by (rotate_simp_tac "M:?u" 1);
by (rtac fun_extension 1 THEN rtac lam_type 1);
by (ALLGOALS(Asm_full_simp_tac));
by (auto_tac (claset(), simpset()  
        addsimps [multiset_fun_iff, fun_extend_apply]));
by (dres_inst_tac [("c", "a"), ("b", "1")] fun_extend3 1);
by (stac Un_commute 3);
by (auto_tac (claset(), simpset() addsimps [cons_eq]));
qed "munion_single_case1";

Goalw [multiset_def]
"[| multiset(M); a:mset_of(M) |] ==> M +# {#a#} = M(a:=M`a #+ 1)";
by (auto_tac (claset(),  simpset() 
     addsimps [munion_def, multiset_fun_iff, msingle_def]));
by (rewtac mset_of_def);
by (rotate_simp_tac "M:?u" 1);
by (subgoal_tac "A Un {a} = A" 1);
by (rtac fun_extension 1);
by (auto_tac (claset() addDs [domain_type] 
                       addIs [lam_type, update_type], simpset()));
qed "munion_single_case2";

(* Induction principle for multisets *)

val major::prems = Goal
  "[| multiset(M); P(0); \
\   (!!M a. [| multiset(M); P(M) |] ==> P(M +# {#a#})) |] \
 \   ==> P(M)";
by (rtac multiset_induct2 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps major::prems)));
by (forw_inst_tac [("a1", "b")] (munion_single_case2 RS sym) 2);
by (forw_inst_tac [("a1", "a")] (munion_single_case1 RS sym) 1);
by (ALLGOALS(Asm_full_simp_tac));
by (REPEAT(blast_tac (claset() addIs prems ) 1));
qed "multiset_induct";

(** MCollect **)

Goalw [MCollect_def, multiset_def, mset_of_def]
  "multiset(M) ==> multiset({# x:M. P(x)#})";
by (Clarify_tac 1);
by (res_inst_tac [("x", "{x:A. P(x)}")] exI 1);
by (auto_tac (claset()  addDs [CollectD1 RSN (2,apply_type)]
                        addIs [Collect_subset RS subset_Finite,
                               funrestrict_type],
              simpset()));
qed "MCollect_multiset";
Addsimps [MCollect_multiset];

Goalw [mset_of_def, MCollect_def]
 "multiset(M) ==> mset_of({# x:M. P(x) #}) <= mset_of(M)";
by (auto_tac (claset(), 
              simpset() addsimps [multiset_def, funrestrict_def]));
qed "mset_of_MCollect";
Addsimps [mset_of_MCollect];

Goalw [MCollect_def, mset_of_def]
 "x:mset_of({#x:M. P(x)#}) <->  x:mset_of(M) & P(x)";
by Auto_tac;
qed "MCollect_mem_iff";
AddIffs [MCollect_mem_iff];
 
Goalw [mcount_def, MCollect_def, mset_of_def]
 "mcount({# x:M. P(x) #}, a) = (if P(a) then mcount(M,a) else 0)";
by Auto_tac;
qed "mcount_MCollect";
Addsimps [mcount_MCollect];

Goal "multiset(M) ==> M = {# x:M. P(x) #} +# {# x:M. ~ P(x) #}";
by (asm_simp_tac (simpset() addsimps [multiset_equality]) 1);
qed "multiset_partition";

Goalw [multiset_def, mset_of_def]
 "[| multiset(M); a:mset_of(M) |] ==> natify(M`a) = M`a";
by (auto_tac (claset(), simpset() addsimps [multiset_fun_iff]));
by (rotate_simp_tac "M:?u" 1);
qed "natify_elem_is_self";
Addsimps [natify_elem_is_self];

(* and more algebraic laws on multisets *)

Goal "[| multiset(M); multiset(N) |] \
\ ==>  (M +# {#a#} = N +# {#b#}) <->  (M = N & a = b | \
\      M = N -# {#a#} +# {#b#} & N = M -# {#b#} +# {#a#})";
by (asm_full_simp_tac (simpset() delsimps [mcount_single]
                                 addsimps [multiset_equality]) 1);
by (rtac iffI 1 THEN etac disjE 2 THEN etac conjE 3);
by (case_tac "a=b" 1);
by Auto_tac;
by (dres_inst_tac [("x", "a")] spec 1);
by (dres_inst_tac [("x", "b")] spec 2);
by (dres_inst_tac [("x", "aa")] spec 3);
by (dres_inst_tac [("x", "a")] spec 4);
by Auto_tac;
by (ALLGOALS(subgoal_tac "mcount(N,a):nat"));
by (etac natE 3 THEN etac natE 1);
by Auto_tac;
qed "munion_eq_conv_diff";

Goal
"[| M:Mult(A); N:Mult(A) |] \
\ ==> (M +# {#a#} = N +# {#b#}) <-> \
\     (M=N & a=b | (EX K:Mult(A). M= K +# {#b#} & N=K +# {#a#}))";
by (auto_tac (claset(), 
              simpset() addsimps [Bex_def, Mult_iff_multiset,
                  melem_diff_single, munion_eq_conv_diff]));
qed "munion_eq_conv_exist";

(** multiset orderings **)

(* multiset on a domain A are finite functions from A to nat-{0} *)


(* multirel1 type *)

Goalw [multirel1_def]
"multirel1(A, r) <= Mult(A)*Mult(A)";
by Auto_tac;
qed "multirel1_type";

Goalw [multirel1_def] "multirel1(0, r) =0";
by Auto_tac;
qed "multirel1_0";
AddIffs [multirel1_0];

Goalw [multirel1_def]
" <N, M>:multirel1(A, r) <-> \
\ (EX a. a:A &                                       \
\ (EX M0. M0:Mult(A) & (EX K. K:Mult(A) &  \
\  M=M0 +# {#a#} & N=M0 +# K & (ALL b:mset_of(K). <b,a>:r))))";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset, Ball_def, Bex_def]));
qed "multirel1_iff";

(* Monotonicity of multirel1 *)

Goalw [multirel1_def]  "A<=B ==> multirel1(A, r)<=multirel1(B, r)";
by (auto_tac (claset(), simpset() addsimps []));
by (ALLGOALS(asm_full_simp_tac(simpset() 
    addsimps [Un_subset_iff, Mult_iff_multiset])));
by (res_inst_tac [("x", "a")] bexI 3);
by (res_inst_tac [("x", "M0")] bexI 3);
by (Asm_simp_tac 3);
by (res_inst_tac [("x", "K")] bexI 3);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [Mult_iff_multiset])));
by Auto_tac;
qed "multirel1_mono1";

Goalw [multirel1_def] "r<=s ==> multirel1(A,r)<=multirel1(A, s)";
by (auto_tac (claset(), simpset() addsimps []));
by (res_inst_tac [("x", "a")] bexI 1);
by (res_inst_tac [("x", "M0")] bexI 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [Mult_iff_multiset])));
by (res_inst_tac [("x", "K")] bexI 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [Mult_iff_multiset])));
by Auto_tac;
qed "multirel1_mono2";

Goal
 "[| A<=B; r<=s |] ==> multirel1(A, r) <= multirel1(B, s)";
by (rtac subset_trans 1);
by (rtac multirel1_mono1 1);
by (rtac multirel1_mono2 2);
by Auto_tac;
qed "multirel1_mono";

(* Towards the proof of well-foundedness of multirel1 *)

Goalw [multirel1_def]  "<M,0>~:multirel1(A, r)";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "not_less_0";
AddIffs [not_less_0];

Goal "[| <N, M0 +# {#a#}>:multirel1(A, r); M0:Mult(A) |] ==> \
\ (EX M. <M, M0>:multirel1(A, r) & N = M +# {#a#}) | \
\ (EX K. K:Mult(A) & (ALL b:mset_of(K). <b, a>:r) & N = M0 +# K)";
by (forward_tac [multirel1_type RS subsetD] 1);
by (asm_full_simp_tac (simpset() addsimps [multirel1_iff]) 1);
by (auto_tac (claset(), simpset() addsimps [munion_eq_conv_exist]));
by (ALLGOALS(res_inst_tac [("x", "Ka +# K")] exI));
by Auto_tac;
by (rewtac (Mult_iff_multiset RS iff_reflection));
by (asm_simp_tac (simpset() addsimps [munion_left_cancel, munion_assoc]) 1);
by (auto_tac (claset(), simpset() addsimps [munion_commute]));
qed "less_munion";

Goal "[| M:Mult(A); a:A |] ==> <M, M +# {#a#}>: multirel1(A, r)";
by (auto_tac (claset(), simpset() addsimps [multirel1_iff]));
by (rewrite_goals_tac [Mult_iff_multiset RS iff_reflection]);
by (res_inst_tac [("x", "a")] exI 1);
by (Clarify_tac 1);
by (res_inst_tac [("x", "M")] exI 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("x", "0")] exI 1);
by Auto_tac;
qed "multirel1_base";

Goal "acc(0)=0";
by (auto_tac (claset()  addSIs [equalityI]
    addDs  [thm "acc.dom_subset" RS subsetD], simpset()));
qed "acc_0";

Goal "[| ALL b:A. <b,a>:r --> \
\   (ALL M:acc(multirel1(A, r)). M +# {#b#}:acc(multirel1(A, r))); \
\   M0:acc(multirel1(A, r)); a:A; \
\   ALL M. <M,M0> : multirel1(A, r) --> M +# {#a#} : acc(multirel1(A, r)) |] \
\ ==> M0 +# {#a#} : acc(multirel1(A, r))";
by (subgoal_tac "M0:Mult(A)" 1);
by (etac (thm "acc.cases") 2);
by (etac fieldE 2);
by (REPEAT(blast_tac (claset() addDs [multirel1_type RS subsetD]) 2));
by (rtac (thm "accI") 1);
by (rename_tac "N" 1);
by (dtac less_munion 1);
by (Blast_tac 1);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
by (eres_inst_tac [("P", "ALL x:mset_of(K). <x, a>:r")] rev_mp 1);
by (eres_inst_tac [("P", "mset_of(K)<=A")] rev_mp 1);
by (eres_inst_tac [("M", "K")] multiset_induct 1);
(* three subgoals *)
(* subgoal 1: the induction base case *)
by (Asm_simp_tac 1);
(* subgoal 2: the induction general case *)
by (asm_full_simp_tac (simpset() addsimps [Ball_def, Un_subset_iff]) 1);
by (Clarify_tac 1);
by (dres_inst_tac [("x", "aa")] spec 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "aa:A" 1);
by (Blast_tac 2);
by (dres_inst_tac [("psi", "ALL x. x:acc(?u)-->?v(x)")] asm_rl 1);
by (rotate_tac ~1 1);
by (dres_inst_tac [("x", "M0 +# M")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [munion_assoc RS sym]) 1);
(* subgoal 3: additional conditions *)
by (auto_tac (claset() addSIs [multirel1_base RS fieldI2], 
              simpset() addsimps [Mult_iff_multiset]));
qed "lemma1";

Goal  "[| ALL b:A. <b,a>:r  \
\  --> (ALL M : acc(multirel1(A, r)). M +# {#b#} :acc(multirel1(A, r))); \
\       M:acc(multirel1(A, r)); a:A|] ==> M +# {#a#} : acc(multirel1(A, r))";
by (etac (thm "acc_induct") 1);
by (blast_tac (claset() addIs [lemma1]) 1);
qed "lemma2";

Goal "[| wf[A](r); a:A |] \
\     ==> ALL M:acc(multirel1(A, r)). M +# {#a#} : acc(multirel1(A, r))";
by (eres_inst_tac [("a","a")] wf_on_induct 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [lemma2]) 1);
qed "lemma3";

Goal "multiset(M) ==> mset_of(M)<=A --> \
\  wf[A](r) --> M:field(multirel1(A, r)) --> M:acc(multirel1(A, r))";
by (etac  multiset_induct 1);
by (ALLGOALS(Clarify_tac));
(* proving the base case *)
by (rtac (thm "accI") 1);
by (cut_inst_tac [("M", "b"), ("r", "r")] not_less_0 1);
by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [multirel1_def]) 1);
(* Proving the general case *)
by (Asm_full_simp_tac 1);
by (subgoal_tac "mset_of(M)<=A" 1);
by (Blast_tac 2);
by (Clarify_tac 1);
by (dres_inst_tac [("a", "a")] lemma3 1);
by (Blast_tac 1);
by (subgoal_tac "M:field(multirel1(A,r))" 1);
by (rtac (multirel1_base RS fieldI1) 2);
by (rewrite_goal_tac [Mult_iff_multiset RS iff_reflection] 2);
by (REPEAT(Blast_tac 1));
qed "lemma4";

Goal "[| wf[A](r); M:Mult(A); A ~= 0|] ==> M:acc(multirel1(A, r))";
by (etac not_emptyE 1);
by  (rtac (lemma4 RS mp RS mp RS mp) 1);
by (rtac (multirel1_base RS fieldI1) 4);
by  (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "all_accessible";

Goal "wf[A](r) ==> wf[A-||>nat-{0}](multirel1(A, r))";
by (case_tac "A=0" 1);
by (Asm_simp_tac 1);
by (rtac wf_imp_wf_on 1);
by (rtac wf_on_field_imp_wf 1);
by (asm_simp_tac (simpset() addsimps [wf_on_0]) 1);
by (res_inst_tac [("A", "acc(multirel1(A,r))")] wf_on_subset_A 1);
by (rtac (thm "wf_on_acc") 1);
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsimps []) 1);
by (blast_tac (claset() addIs [all_accessible]) 1);
qed "wf_on_multirel1";

Goal "wf(r) ==>wf(multirel1(field(r), r))";
by (full_simp_tac (simpset() addsimps [wf_iff_wf_on_field]) 1);
by (dtac wf_on_multirel1 1);
by (res_inst_tac [("A", "field(r) -||> nat - {0}")] wf_on_subset_A 1);
by (Asm_simp_tac 1);
by (rtac field_rel_subset 1);
by (rtac multirel1_type 1);
qed "wf_multirel1";

(** multirel **)

Goalw [multirel_def]
 "multirel(A, r) <= Mult(A)*Mult(A)";
by (rtac (trancl_type RS subset_trans) 1);
by (Clarify_tac 1);
by (auto_tac (claset() addDs [multirel1_type RS subsetD], 
              simpset() addsimps []));
qed "multirel_type";

(* Monotonicity of multirel *)
Goalw [multirel_def]
 "[| A<=B; r<=s |] ==> multirel(A, r)<=multirel(B,s)";
by (rtac trancl_mono 1);
by (rtac multirel1_mono 1);
by Auto_tac;
qed "multirel_mono";

(* Equivalence of multirel with the usual (closure-free) def *)

Goal "k:nat ==> 0 < k --> n #+ k #- 1 = n #+ (k #- 1)";
by (etac nat_induct 1 THEN Auto_tac);
qed "lemma";

Goal "[|a:mset_of(J); multiset(I); multiset(J) |] \
\  ==> I +# J -# {#a#} = I +# (J-# {#a#})";
by (asm_simp_tac (simpset() addsimps [multiset_equality]) 1);
by (case_tac "a ~: mset_of(I)" 1);
by (auto_tac (claset(), simpset() addsimps 
             [mcount_def, mset_of_def, multiset_def, multiset_fun_iff]));
by (rotate_simp_tac "I:?u" 1);
by (rotate_simp_tac "J:?u" 1);
by (auto_tac (claset() addDs [domain_type], simpset() addsimps [lemma]));
qed "mdiff_union_single_conv";

Goal "[| n le m;  m:nat; n:nat; k:nat |] ==> m #- n #+ k = m #+ k #- n";
by (auto_tac (claset(), simpset() addsimps 
         [le_iff, diff_self_eq_0, less_iff_succ_add]));
qed "diff_add_commute";

(* One direction *)

Goalw [multirel_def, Ball_def, Bex_def]
"<M,N>:multirel(A, r) ==> \
\    trans[A](r) --> \
\    (EX I J K. \
\        I:Mult(A) & J:Mult(A) &  K:Mult(A) & \
\        N = I +# J & M = I +# K & J ~= 0 & \
\       (ALL k:mset_of(K). EX j:mset_of(J). <k,j>:r))";
by (etac converse_trancl_induct 1);
by (ALLGOALS(asm_full_simp_tac (simpset() 
        addsimps [multirel1_iff, Mult_iff_multiset])));
by (ALLGOALS(Clarify_tac));
(* Two subgoals remain *)
(* Subgoal 1 *)
by (res_inst_tac [("x","M0")] exI 1);
by (Force_tac 1);
(* Subgoal 2 *)
by (case_tac "a:mset_of(Ka)" 1);
by (res_inst_tac [("x","I")] exI 1 THEN Asm_simp_tac 1);
by (res_inst_tac [("x", "J")] exI 1  THEN Asm_simp_tac 1);
by (res_inst_tac [("x","(Ka -# {#a#}) +# K")] exI 1 THEN Asm_simp_tac 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [Un_subset_iff])));
by (asm_simp_tac (simpset() addsimps [munion_assoc RS sym]) 1);
by (dres_inst_tac[("t","%M. M-#{#a#}")] subst_context 1);
by (asm_full_simp_tac (simpset() 
    addsimps [mdiff_union_single_conv, melem_diff_single]) 1);
by (Clarify_tac 1);
by (etac disjE 1);
by (Asm_full_simp_tac 1);
by (etac disjE 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("psi", "ALL x. x:#Ka -->?u(x)")] asm_rl 1);
by (rotate_tac ~1 1);
by (dres_inst_tac [("x", "a")] spec 1);
by (Clarify_tac 1);
by (res_inst_tac [("x", "xa")] exI 1);
by (Asm_simp_tac 1);
by (dres_inst_tac [("a", "x"), ("b", "a"), ("c", "xa")] trans_onD 1);
by (ALLGOALS(Asm_simp_tac));
by (Blast_tac 1);
by (Blast_tac 1);
(* new we know that  a~:mset_of(Ka) *)
by (subgoal_tac "a :# I" 1);
by (res_inst_tac [("x","I-#{#a#}")] exI 1 THEN Asm_simp_tac 1);
by (res_inst_tac [("x","J+#{#a#}")] exI 1);
by (asm_simp_tac (simpset() addsimps [Un_subset_iff]) 1);
by (res_inst_tac [("x","Ka +# K")] exI 1);
by (asm_simp_tac (simpset() addsimps [Un_subset_iff]) 1);
by (rtac conjI 1);
by (asm_simp_tac (simpset() addsimps
        [multiset_equality, mcount_elem RS succ_pred_eq_self]) 1);
by (rtac conjI 1);
by (dres_inst_tac[("t","%M. M-#{#a#}")] subst_context 1);
by (asm_full_simp_tac (simpset() addsimps [mdiff_union_inverse2]) 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [multiset_equality])));
by (rtac (diff_add_commute RS sym) 1);
by (auto_tac (claset() addIs [mcount_elem], simpset()));
by (subgoal_tac "a:mset_of(I +# Ka)" 1);
by (dtac sym 2 THEN Auto_tac);
qed "multirel_implies_one_step";

Goal "[| a:mset_of(M); multiset(M) |] ==> M -# {#a#} +# {#a#} = M";
by (asm_simp_tac (simpset() 
    addsimps [multiset_equality, mcount_elem RS succ_pred_eq_self]) 1);
qed "melem_imp_eq_diff_union";
Addsimps [melem_imp_eq_diff_union];
    
Goal "[| msize(M)=$# succ(n); M:Mult(A); n:nat |] \
\     ==> EX a N. M = N +# {#a#} & N:Mult(A) & a:A";
by (dtac msize_eq_succ_imp_elem 1);
by Auto_tac;
by (res_inst_tac [("x", "a")] exI 1);
by (res_inst_tac [("x", "M -# {#a#}")] exI 1);
by (ftac Mult_into_multiset 1);
by (Asm_simp_tac 1);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "msize_eq_succ_imp_eq_union";

(* The second direction *)

Goalw [Mult_iff_multiset RS iff_reflection] 
"n:nat ==> \
\  (ALL I J K.  \
\   I:Mult(A) & J:Mult(A) & K:Mult(A) & \
\  (msize(J) = $# n & J ~=0 &  (ALL k:mset_of(K).  EX j:mset_of(J). <k, j>:r)) \
\   --> <I +# K, I +# J>:multirel(A, r))";
by (etac nat_induct 1);
by (Clarify_tac 1);
by (dres_inst_tac [("M", "J")] msize_eq_0_iff 1);
by Auto_tac;
(* one subgoal remains *)
by (subgoal_tac "msize(J)=$# succ(x)" 1);
by (Asm_simp_tac 2);
by (forw_inst_tac [("A", "A")]  msize_eq_succ_imp_eq_union 1);
by (rewtac (Mult_iff_multiset RS iff_reflection));
by (Clarify_tac 3 THEN rotate_tac ~1 3);
by (ALLGOALS(Asm_full_simp_tac));
by (rename_tac  "J'" 1);
by (Asm_full_simp_tac 1); 
by (case_tac "J' = 0" 1);
by (asm_full_simp_tac (simpset() addsimps [multirel_def]) 1); 
by (rtac r_into_trancl 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [multirel1_iff, Mult_iff_multiset]) 1);
by (Force_tac 1);
(*Now we know J' ~=  0*)
by (rotate_simp_tac "multiset(J')" 1);
by (dtac sym 1 THEN rotate_tac ~1 1);
by (Asm_full_simp_tac 1);
by (thin_tac "$# x = msize(J')" 1);
by (forw_inst_tac [("M","K"),("P", "%x. <x,a>:r")] multiset_partition 1);
by (eres_inst_tac [("P", "ALL k:mset_of(K). ?P(k)")] rev_mp 1);
by (etac ssubst 1); 
by (asm_full_simp_tac (simpset() addsimps [Ball_def]) 1); 
by Auto_tac;
by (subgoal_tac "<(I +# {# x : K. <x, a> : r#}) +# {# x:K. <x, a> ~: r#}, \
               \  (I +# {# x : K. <x, a> : r#}) +# J'>:multirel(A, r)" 1);
by (dres_inst_tac [("x", "I +# {# x : K. <x, a>: r#}")] spec 2);
by (rotate_tac ~1 2);
by (dres_inst_tac [("x", "J'")] spec 2);
by (rotate_tac ~1 2);
by (dres_inst_tac [("x", "{# x : K. <x, a>~:r#}")] spec 2);
by (Clarify_tac 2);
by (Asm_full_simp_tac 2);
by (Blast_tac 2);
by (asm_full_simp_tac (simpset() addsimps [munion_assoc RS sym, multirel_def]) 1);
by (res_inst_tac [("b", "I +# {# x:K. <x, a>:r#} +# J'")] trancl_trans 1); 
by (Blast_tac 1);
by (rtac r_into_trancl 1); 
by (asm_full_simp_tac (simpset() addsimps [multirel1_iff, Mult_iff_multiset]) 1); 
by (res_inst_tac [("x", "a")] exI 1); 
by (Asm_simp_tac 1);
by (res_inst_tac [("x", "I +# J'")] exI 1); 
by (asm_simp_tac (simpset() addsimps munion_ac@[Un_subset_iff]) 1); 
by (rtac conjI 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (REPEAT(Blast_tac 1));
qed_spec_mp "one_step_implies_multirel_lemma";

Goal  "[| J ~= 0;  ALL k:mset_of(K). EX j:mset_of(J). <k,j>:r;\
\         I:Mult(A); J:Mult(A); K:Mult(A) |] \
\         ==> <I+#K, I+#J> : multirel(A, r)";
by (subgoal_tac "multiset(J)" 1);
by (asm_full_simp_tac (simpset() addsimps [Mult_iff_multiset]) 2);
by (forw_inst_tac [("M", "J")] msize_int_of_nat 1);
by (auto_tac (claset() addIs [one_step_implies_multirel_lemma], simpset()));
qed "one_step_implies_multirel";

(** Proving that multisets are partially ordered **)

(*irreflexivity*)

Goal "Finite(A) ==> \
\ part_ord(A, r) --> (ALL x:A. EX y:A. <x,y>:r) -->A=0";
by (etac Finite_induct 1);
by (auto_tac (claset() addDs 
           [subset_consI RSN (2, part_ord_subset)], simpset()));
by (auto_tac (claset(), simpset() addsimps [part_ord_def, irrefl_def]));
by (dres_inst_tac [("x", "xa")] bspec 1);
by (dres_inst_tac [("a", "xa"), ("b", "x")] trans_onD 2);
by Auto_tac;
qed "multirel_irrefl_lemma";

Goalw [irrefl_def] 
"part_ord(A, r) ==> irrefl(Mult(A), multirel(A, r))";
by (subgoal_tac "trans[A](r)" 1);
by (asm_full_simp_tac (simpset() addsimps [part_ord_def]) 2);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps []) 1);
by (dtac multirel_implies_one_step 1);
by (Clarify_tac 1);
by (rewrite_goal_tac [Mult_iff_multiset RS iff_reflection] 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "Finite(mset_of(K))" 1);
by (forw_inst_tac [("r", "r")] multirel_irrefl_lemma 1);
by (forw_inst_tac [("B", "mset_of(K)")] part_ord_subset 1);
by (ALLGOALS(Asm_full_simp_tac));
by (auto_tac (claset(), simpset() addsimps [multiset_def, mset_of_def]));
by (rotate_simp_tac "K:?u" 1);
qed "irrefl_on_multirel";

Goalw [multirel_def, trans_on_def] "trans[Mult(A)](multirel(A, r))";
by (blast_tac (claset() addIs [trancl_trans]) 1);
qed "trans_on_multirel";

Goalw [multirel_def]
 "[| <M, N>:multirel(A, r); <N, K>:multirel(A, r) |] ==>  <M, K>:multirel(A,r)";
by (blast_tac (claset() addIs [trancl_trans]) 1);
qed "multirel_trans";

Goalw [multirel_def]  "trans(multirel(A,r))";
by (rtac trans_trancl 1);
qed "trans_multirel";

Goal "part_ord(A,r) ==> part_ord(Mult(A), multirel(A, r))";
by (simp_tac (simpset() addsimps [part_ord_def]) 1);
by (blast_tac (claset() addIs [irrefl_on_multirel, trans_on_multirel]) 1);
qed "part_ord_multirel";

(** Monotonicity of multiset union **)

Goal
"[|<M,N>:multirel1(A, r); K:Mult(A) |] ==> <K +# M, K +# N>:multirel1(A, r)";
by (ftac (multirel1_type RS subsetD) 1);
by (auto_tac (claset(), simpset() addsimps [multirel1_iff, Mult_iff_multiset]));
by (res_inst_tac [("x", "a")] exI 1); 
by (Asm_simp_tac 1);
by (res_inst_tac [("x", "K+#M0")] exI 1); 
by (asm_simp_tac (simpset() addsimps [Un_subset_iff]) 1);
by (res_inst_tac [("x", "Ka")] exI 1); 
by (asm_simp_tac (simpset() addsimps [munion_assoc]) 1); 
qed "munion_multirel1_mono";

Goal
 "[| <M, N>:multirel(A, r); K:Mult(A) |]==><K +# M, K +# N>:multirel(A, r)";
by (ftac (multirel_type RS subsetD) 1);
by (full_simp_tac (simpset() addsimps [multirel_def]) 1);
by (Clarify_tac 1);
by (dres_inst_tac [("psi", "<M,N>:multirel1(A, r)^+")] asm_rl 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac trancl_induct 1); 
by (Clarify_tac 1);
by (blast_tac (claset() addIs [munion_multirel1_mono, r_into_trancl]) 1);
by (Clarify_tac 1);
by (subgoal_tac "y:Mult(A)" 1);
by (blast_tac (claset() addDs [rewrite_rule [multirel_def] multirel_type RS subsetD]) 2);
by (subgoal_tac "<K +# y, K +# z>:multirel1(A, r)" 1);
by (blast_tac (claset() addIs [munion_multirel1_mono]) 2);
by (blast_tac (claset() addIs [r_into_trancl, trancl_trans]) 1);
qed "munion_multirel_mono2";

Goal 
"[|<M, N>:multirel(A, r); K:Mult(A)|] ==> <M +# K, N +# K>:multirel(A, r)";
by (ftac (multirel_type RS subsetD) 1);
by (res_inst_tac [("P", "%x. <x,?u>:multirel(A, r)")] (munion_commute RS subst) 1);
by (stac (munion_commute RS sym) 3);
by (rtac munion_multirel_mono2 5);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "munion_multirel_mono1";

Goal 
"[|<M,K>:multirel(A, r); <N,L>:multirel(A, r)|]==><M +# N, K +# L>:multirel(A, r)";
by (subgoal_tac "M:Mult(A)& N:Mult(A) & K:Mult(A)& L:Mult(A)" 1);
by (blast_tac (claset() addDs [multirel_type RS subsetD]) 2);
by (blast_tac (claset() 
    addIs [munion_multirel_mono1, multirel_trans, munion_multirel_mono2]) 1);
qed "munion_multirel_mono";

(** Ordinal multisets **)

(* A <= B ==>  field(Memrel(A)) \\<subseteq> field(Memrel(B)) *)
bind_thm("field_Memrel_mono", Memrel_mono RS field_mono);

(* 
[| Aa <= Ba; A <= B |] ==>
multirel(field(Memrel(Aa)), Memrel(A))<= multirel(field(Memrel(Ba)), Memrel(B)) 
*) 
bind_thm ("multirel_Memrel_mono",
         [field_Memrel_mono, Memrel_mono]MRS multirel_mono);

Goalw [omultiset_def] "omultiset(M) ==> multiset(M)";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "omultiset_is_multiset";
Addsimps [omultiset_is_multiset];

Goalw [omultiset_def] "[| omultiset(M); omultiset(N) |] ==> omultiset(M +# N)";
by (Clarify_tac 1);
by (res_inst_tac [("x", "i Un ia")] exI 1);
by (asm_full_simp_tac (simpset() addsimps
            [Mult_iff_multiset, Ord_Un, Un_subset_iff]) 1);
by (blast_tac (claset() addIs [field_Memrel_mono]) 1);
qed "munion_omultiset";
Addsimps [munion_omultiset];

Goalw [omultiset_def] "omultiset(M) ==> omultiset(M -# N)";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
by (res_inst_tac [("x", "i")] exI 1);
by (Asm_simp_tac 1);
qed "mdiff_omultiset";
Addsimps [mdiff_omultiset];

(** Proving that Memrel is a partial order **)

Goal "Ord(i) ==> irrefl(field(Memrel(i)), Memrel(i))";
by (rtac irreflI 1);
by (Clarify_tac 1);
by (subgoal_tac "Ord(x)" 1);
by (blast_tac (claset() addIs [Ord_in_Ord]) 2);
by (dres_inst_tac [("i", "x")] (ltI RS lt_irrefl) 1);
by Auto_tac;
qed "irrefl_Memrel";

Goalw [trans_on_def, trans_def]
 "trans(r) <-> trans[field(r)](r)";
by Auto_tac;
qed "trans_iff_trans_on";

Goalw [part_ord_def]
 "Ord(i) ==>part_ord(field(Memrel(i)), Memrel(i))";
by (simp_tac (simpset() addsimps [trans_iff_trans_on RS iff_sym]) 1);
by (blast_tac (claset() addIs [trans_Memrel, irrefl_Memrel]) 1);
qed "part_ord_Memrel";

(*
  Ord(i) ==> 
  part_ord(field(Memrel(i))-||>nat-{0}, multirel(field(Memrel(i)), Memrel(i))) 
*)

bind_thm("part_ord_mless", part_ord_Memrel RS part_ord_multirel);

(*irreflexivity*)

Goalw [mless_def] "~(M <# M)";
by (Clarify_tac 1);
by (forward_tac [multirel_type RS subsetD] 1);
by (dtac part_ord_mless 1);
by (rewrite_goals_tac [part_ord_def, irrefl_def]);
by (Blast_tac 1);
qed "mless_not_refl";

(* N<N ==> R *)
bind_thm ("mless_irrefl", mless_not_refl RS notE);
AddSEs [mless_irrefl];

(*transitivity*)
Goalw [mless_def] "[| K <# M; M <# N |] ==> K <# N";
by (Clarify_tac 1);
by (res_inst_tac [("x", "i Un ia")] exI 1);
by (blast_tac (claset() addDs 
            [[Un_upper1, Un_upper1] MRS multirel_Memrel_mono RS subsetD,
            [Un_upper2, Un_upper2] MRS multirel_Memrel_mono RS subsetD]
            addIs [multirel_trans, Ord_Un]) 1);
qed "mless_trans";

(*asymmetry*)
Goal "M <# N ==> ~ N <# M";
by (Clarify_tac 1);
by (rtac (mless_not_refl RS notE) 1);
by (etac mless_trans 1);
by (assume_tac 1);
qed "mless_not_sym";

val major::prems =
Goal "[| M <# N; ~P ==> N <# M |] ==> P";
by (cut_facts_tac [major] 1);
by (dtac  mless_not_sym 1);
by (dres_inst_tac [("P", "P")] swap 1);
by (auto_tac (claset() addIs prems, simpset()));
qed "mless_asym";

Goalw [mle_def] "omultiset(M) ==> M <#= M";
by Auto_tac;
qed "mle_refl";
Addsimps [mle_refl];

(*anti-symmetry*)
Goalw [mle_def] 
"[| M <#= N;  N <#= M |] ==> M = N";
by (blast_tac (claset() addDs [mless_not_sym]) 1);
qed "mle_antisym";

(*transitivity*)
Goalw [mle_def]
     "[| K <#= M; M <#= N |] ==> K <#= N";
by (blast_tac (claset() addIs [mless_trans]) 1);
qed "mle_trans";

Goalw [mle_def] "M <# N <-> (M <#= N & M ~= N)";
by Auto_tac;
qed "mless_le_iff";

(** Monotonicity of mless **)

Goalw [mless_def, omultiset_def]
 "[| M <# N; omultiset(K) |] ==> K +# M <# K +# N";
by (Clarify_tac 1);
by (res_inst_tac [("x", "i Un ia")] exI 1);
by (asm_full_simp_tac (simpset() 
    addsimps [Mult_iff_multiset, Ord_Un, Un_subset_iff]) 1);
by (rtac munion_multirel_mono2 1);
by (asm_simp_tac (simpset() addsimps [Mult_iff_multiset]) 2);
by (blast_tac (claset() addIs [multirel_Memrel_mono RS subsetD]) 1);
by (blast_tac (claset() addIs [field_Memrel_mono RS subsetD]) 1);
qed "munion_less_mono2";

Goalw [mless_def, omultiset_def]
 "[| M <# N; omultiset(K) |] ==> M +# K <# N +# K";
by (Clarify_tac 1);
by (res_inst_tac [("x", "i Un ia")] exI 1);
by (asm_full_simp_tac (simpset() 
    addsimps [Mult_iff_multiset, Ord_Un, Un_subset_iff]) 1);
by (rtac munion_multirel_mono1 1);
by (asm_simp_tac (simpset() addsimps [Mult_iff_multiset]) 2);
by (blast_tac (claset() addIs [multirel_Memrel_mono RS subsetD]) 1);
by (blast_tac (claset() addIs [field_Memrel_mono RS subsetD]) 1);
qed "munion_less_mono1";

Goalw [mless_def, omultiset_def]
 "M <# N ==> omultiset(M) & omultiset(N)";
by (auto_tac (claset() addDs [multirel_type RS subsetD], simpset()));
qed "mless_imp_omultiset";

Goal "[| M <# K; N <# L |] ==> M +# N <# K +# L";
by (forw_inst_tac [("M", "M")] mless_imp_omultiset 1);
by (forw_inst_tac [("M", "N")] mless_imp_omultiset 1);
by (blast_tac (claset() addIs 
       [munion_less_mono1, munion_less_mono2, mless_trans]) 1); 
qed "munion_less_mono";

(* <#= *)

Goalw [mle_def] "M <#= N ==> omultiset(M) & omultiset(N)";
by (auto_tac (claset(), simpset() addsimps [mless_imp_omultiset]));
qed "mle_imp_omultiset";

Goal "[| M <#= K;  N <#= L |] ==> M +# N <#= K +# L";
by (forw_inst_tac [("M", "M")] mle_imp_omultiset 1);
by (forw_inst_tac [("M", "N")] mle_imp_omultiset 1);
by (rewtac mle_def);
by (ALLGOALS(Asm_full_simp_tac));
by (REPEAT(etac disjE 1));
by (etac disjE 3);
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS(rtac  disjI2));
by (auto_tac (claset() addIs [munion_less_mono1, munion_less_mono2, 
                              munion_less_mono], simpset()));
qed "mle_mono";

Goalw [omultiset_def]  "omultiset(0)";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "omultiset_0";
AddIffs [omultiset_0];

Goalw [mle_def, mless_def] "omultiset(M) ==> 0 <#= M";
by (subgoal_tac "EX i. Ord(i) & M:Mult(field(Memrel(i)))" 1);
by (asm_full_simp_tac (simpset() addsimps [omultiset_def]) 2);
by (case_tac "M=0" 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Clarify_tac 1);
by (subgoal_tac "<0 +# 0, 0 +# M>: multirel(field(Memrel(i)), Memrel(i))" 1);
by (rtac one_step_implies_multirel 2);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "empty_leI";
Addsimps [empty_leI];

Goal "[| omultiset(M); omultiset(N) |] ==> M <#= M +# N";
by (subgoal_tac "M +# 0 <#= M +# N" 1);
by (rtac mle_mono 2); 
by Auto_tac;
qed "munion_upper1";




