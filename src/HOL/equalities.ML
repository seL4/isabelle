(*  Title:      HOL/equalities
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Equalities involving union, intersection, inclusion, etc.
*)

writeln"File HOL/equalities";

AddSIs [equalityI];

section "{}";

(*supersedes Collect_False_empty*)
Goal "{s. P} = (if P then UNIV else {})";
by (Force_tac 1);
qed "Collect_const";
Addsimps [Collect_const];

Goal "(A <= {}) = (A = {})";
by (Blast_tac 1);
qed "subset_empty";
Addsimps [subset_empty];

Goalw [psubset_def] "~ (A < {})";
by (Blast_tac 1);
qed "not_psubset_empty";
AddIffs [not_psubset_empty];

Goal "(Collect P = {}) = (!x. ~ P x)";
by Auto_tac;
qed "Collect_empty_eq";
Addsimps[Collect_empty_eq];

Goal "{x. P x | Q x} = {x. P x} Un {x. Q x}";
by (Blast_tac 1);
qed "Collect_disj_eq";

Goal "{x. P x & Q x} = {x. P x} Int {x. Q x}";
by (Blast_tac 1);
qed "Collect_conj_eq";

Goal "{x. ALL y. P x y} = (INT y. {x. P x y})";
by (Blast_tac 1);
qed "Collect_all_eq";

Goal "{x. ALL y: A. P x y} = (INT y: A. {x. P x y})";
by (Blast_tac 1);
qed "Collect_ball_eq";

Goal "{x. EX y. P x y} = (UN y. {x. P x y})";
by (Blast_tac 1);
qed "Collect_ex_eq";

Goal "{x. EX y: A. P x y} = (UN y: A. {x. P x y})";
by (Blast_tac 1);
qed "Collect_bex_eq";


section "insert";

(*NOT SUITABLE FOR REWRITING since {a} == insert a {}*)
Goal "insert a A = {a} Un A";
by (Blast_tac 1);
qed "insert_is_Un";

Goal "insert a A ~= {}";
by (blast_tac (claset() addEs [equalityCE]) 1);
qed"insert_not_empty";
Addsimps[insert_not_empty];

bind_thm("empty_not_insert",insert_not_empty RS not_sym);
Addsimps[empty_not_insert];

Goal "a:A ==> insert a A = A";
by (Blast_tac 1);
qed "insert_absorb";
(* Addsimps [insert_absorb] causes recursive calls
   when there are nested inserts, with QUADRATIC running time
*)

Goal "insert x (insert x A) = insert x A";
by (Blast_tac 1);
qed "insert_absorb2";
Addsimps [insert_absorb2];

Goal "insert x (insert y A) = insert y (insert x A)";
by (Blast_tac 1);
qed "insert_commute";

Goal "(insert x A <= B) = (x:B & A <= B)";
by (Blast_tac 1);
qed "insert_subset";
Addsimps[insert_subset];

Goal "insert a A ~= insert a B ==> A ~= B";
by (Blast_tac 1);
qed "insert_lim";

(* use new B rather than (A-{a}) to avoid infinite unfolding *)
Goal "a:A ==> ? B. A = insert a B & a ~: B";
by (res_inst_tac [("x","A-{a}")] exI 1);
by (Blast_tac 1);
qed "mk_disjoint_insert";

bind_thm ("insert_Collect", prove_goal thy 
	  "insert a (Collect P) = {u. u ~= a --> P u}" (K [Auto_tac]));

Goal "u: A ==> (UN x:A. insert a (B x)) = insert a (UN x:A. B x)";
by (Blast_tac 1);
qed "UN_insert_distrib";

section "``";

Goal "f``{} = {}";
by (Blast_tac 1);
qed "image_empty";
Addsimps[image_empty];

Goal "f``insert a B = insert (f a) (f``B)";
by (Blast_tac 1);
qed "image_insert";
Addsimps[image_insert];

Goal "x:A ==> (%x. c) `` A = {c}";
by (Blast_tac 1);
qed "image_constant";

Goal "f``(g``A) = (%x. f (g x)) `` A";
by (Blast_tac 1);
qed "image_image";

Goal "x:A ==> insert (f x) (f``A) = f``A";
by (Blast_tac 1);
qed "insert_image";
Addsimps [insert_image];

Goal "(f``A = {}) = (A = {})";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "image_is_empty";
AddIffs [image_is_empty];

Goal "f `` {x. P x} = {f x | x. P x}";
by (Blast_tac 1);
qed "image_Collect";
Addsimps [image_Collect];

Goalw [image_def] "(%x. if P x then f x else g x) `` S   \
\                = (f `` (S Int {x. P x})) Un (g `` (S Int {x. ~(P x)}))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "if_image_distrib";
Addsimps[if_image_distrib];

val prems = Goal "[|M = N; !!x. x:N ==> f x = g x|] ==> f``M = g``N";
by (simp_tac (simpset() addsimps image_def::prems) 1);
qed "image_cong";


section "range";

Goal "{u. ? x. u = f x} = range f";
by Auto_tac;
qed "full_SetCompr_eq";
Addsimps[full_SetCompr_eq];


section "Int";

Goal "A Int A = A";
by (Blast_tac 1);
qed "Int_absorb";
Addsimps[Int_absorb];

Goal "A Int (A Int B) = A Int B";
by (Blast_tac 1);
qed "Int_left_absorb";

Goal "A Int B = B Int A";
by (Blast_tac 1);
qed "Int_commute";

Goal "A Int (B Int C) = B Int (A Int C)";
by (Blast_tac 1);
qed "Int_left_commute";

Goal "(A Int B) Int C = A Int (B Int C)";
by (Blast_tac 1);
qed "Int_assoc";

(*Intersection is an AC-operator*)
bind_thms ("Int_ac", [Int_assoc, Int_left_absorb, Int_commute, Int_left_commute]);

Goal "B<=A ==> A Int B = B";
by (Blast_tac 1);
qed "Int_absorb1";

Goal "A<=B ==> A Int B = A";
by (Blast_tac 1);
qed "Int_absorb2";

Goal "{} Int B = {}";
by (Blast_tac 1);
qed "Int_empty_left";
Addsimps[Int_empty_left];

Goal "A Int {} = {}";
by (Blast_tac 1);
qed "Int_empty_right";
Addsimps[Int_empty_right];

Goal "(A Int B = {}) = (A <= -B)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "disjoint_eq_subset_Compl";

Goal "(A Int B = {}) = (ALL x:A. ALL y:B. x ~= y)";
by  (Blast_tac 1);
qed "disjoint_iff_not_equal";

Goal "UNIV Int B = B";
by (Blast_tac 1);
qed "Int_UNIV_left";
Addsimps[Int_UNIV_left];

Goal "A Int UNIV = A";
by (Blast_tac 1);
qed "Int_UNIV_right";
Addsimps[Int_UNIV_right];

Goal "A Int B = Inter{A,B}";
by (Blast_tac 1);
qed "Int_eq_Inter";

Goal "A Int (B Un C) = (A Int B) Un (A Int C)";
by (Blast_tac 1);
qed "Int_Un_distrib";

Goal "(B Un C) Int A = (B Int A) Un (C Int A)";
by (Blast_tac 1);
qed "Int_Un_distrib2";

Goal "(A Int B = UNIV) = (A = UNIV & B = UNIV)";
by (blast_tac (claset() addEs [equalityCE]) 1);
qed "Int_UNIV";
Addsimps[Int_UNIV];

Goal "(C <= A Int B) = (C <= A & C <= B)";
by (Blast_tac 1);
qed "Int_subset_iff";

Goal "(x : A Int {x. P x}) = (x : A & P x)";
by (Blast_tac 1);
qed "Int_Collect";

section "Un";

Goal "A Un A = A";
by (Blast_tac 1);
qed "Un_absorb";
Addsimps[Un_absorb];

Goal " A Un (A Un B) = A Un B";
by (Blast_tac 1);
qed "Un_left_absorb";

Goal "A Un B = B Un A";
by (Blast_tac 1);
qed "Un_commute";

Goal "A Un (B Un C) = B Un (A Un C)";
by (Blast_tac 1);
qed "Un_left_commute";

Goal "(A Un B) Un C = A Un (B Un C)";
by (Blast_tac 1);
qed "Un_assoc";

(*Union is an AC-operator*)
bind_thms ("Un_ac", [Un_assoc, Un_left_absorb, Un_commute, Un_left_commute]);

Goal "A<=B ==> A Un B = B";
by (Blast_tac 1);
qed "Un_absorb1";

Goal "B<=A ==> A Un B = A";
by (Blast_tac 1);
qed "Un_absorb2";

Goal "{} Un B = B";
by (Blast_tac 1);
qed "Un_empty_left";
Addsimps[Un_empty_left];

Goal "A Un {} = A";
by (Blast_tac 1);
qed "Un_empty_right";
Addsimps[Un_empty_right];

Goal "UNIV Un B = UNIV";
by (Blast_tac 1);
qed "Un_UNIV_left";
Addsimps[Un_UNIV_left];

Goal "A Un UNIV = UNIV";
by (Blast_tac 1);
qed "Un_UNIV_right";
Addsimps[Un_UNIV_right];

Goal "A Un B = Union{A,B}";
by (Blast_tac 1);
qed "Un_eq_Union";

Goal "(insert a B) Un C = insert a (B Un C)";
by (Blast_tac 1);
qed "Un_insert_left";
Addsimps[Un_insert_left];

Goal "A Un (insert a B) = insert a (A Un B)";
by (Blast_tac 1);
qed "Un_insert_right";
Addsimps[Un_insert_right];

Goal "(insert a B) Int C = (if a:C then insert a (B Int C) \
\                                  else        B Int C)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "Int_insert_left";

Goal "A Int (insert a B) = (if a:A then insert a (A Int B) \
\                                  else        A Int B)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "Int_insert_right";

Goal "A Un (B Int C) = (A Un B) Int (A Un C)";
by (Blast_tac 1);
qed "Un_Int_distrib";

Goal "(B Int C) Un A = (B Un A) Int (C Un A)";
by (Blast_tac 1);
qed "Un_Int_distrib2";

Goal "(A Int B) Un (B Int C) Un (C Int A) = \
\     (A Un B) Int (B Un C) Int (C Un A)";
by (Blast_tac 1);
qed "Un_Int_crazy";

Goal "(A<=B) = (A Un B = B)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "subset_Un_eq";

Goal "(A <= insert b C) = (A <= C | b:A & A-{b} <= C)";
by (Blast_tac 1);
qed "subset_insert_iff";

Goal "(A Un B = {}) = (A = {} & B = {})";
by (blast_tac (claset() addEs [equalityCE]) 1);
qed "Un_empty";
Addsimps[Un_empty];

Goal "(A Un B <= C) = (A <= C & B <= C)";
by (Blast_tac 1);
qed "Un_subset_iff";

Goal "(A - B) Un (A Int B) = A";
by (Blast_tac 1);
qed "Un_Diff_Int";


section "Set complement";

Goal "A Int (-A) = {}";
by (Blast_tac 1);
qed "Compl_disjoint";
Addsimps[Compl_disjoint];

Goal "A Un (-A) = UNIV";
by (Blast_tac 1);
qed "Compl_partition";

Goal "- (-A) = (A:: 'a set)";
by (Blast_tac 1);
qed "double_complement";
Addsimps[double_complement];

Goal "-(A Un B) = (-A) Int (-B)";
by (Blast_tac 1);
qed "Compl_Un";

Goal "-(A Int B) = (-A) Un (-B)";
by (Blast_tac 1);
qed "Compl_Int";

Goal "-(UN x:A. B(x)) = (INT x:A. -B(x))";
by (Blast_tac 1);
qed "Compl_UN";

Goal "-(INT x:A. B(x)) = (UN x:A. -B(x))";
by (Blast_tac 1);
qed "Compl_INT";

Addsimps [Compl_Un, Compl_Int, Compl_UN, Compl_INT];

(*Halmos, Naive Set Theory, page 16.*)

Goal "((A Int B) Un C = A Int (B Un C)) = (C<=A)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "Un_Int_assoc_eq";


section "Union";

Goal "Union({}) = {}";
by (Blast_tac 1);
qed "Union_empty";
Addsimps[Union_empty];

Goal "Union(UNIV) = UNIV";
by (Blast_tac 1);
qed "Union_UNIV";
Addsimps[Union_UNIV];

Goal "Union(insert a B) = a Un Union(B)";
by (Blast_tac 1);
qed "Union_insert";
Addsimps[Union_insert];

Goal "Union(A Un B) = Union(A) Un Union(B)";
by (Blast_tac 1);
qed "Union_Un_distrib";
Addsimps[Union_Un_distrib];

Goal "Union(A Int B) <= Union(A) Int Union(B)";
by (Blast_tac 1);
qed "Union_Int_subset";

Goal "(Union M = {}) = (! A : M. A = {})"; 
by (blast_tac (claset() addEs [equalityCE]) 1);
qed "Union_empty_conv"; 
AddIffs [Union_empty_conv];

Goal "(Union(C) Int A = {}) = (! B:C. B Int A = {})";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "Union_disjoint";

section "Inter";

Goal "Inter({}) = UNIV";
by (Blast_tac 1);
qed "Inter_empty";
Addsimps[Inter_empty];

Goal "Inter(UNIV) = {}";
by (Blast_tac 1);
qed "Inter_UNIV";
Addsimps[Inter_UNIV];

Goal "Inter(insert a B) = a Int Inter(B)";
by (Blast_tac 1);
qed "Inter_insert";
Addsimps[Inter_insert];

Goal "Inter(A) Un Inter(B) <= Inter(A Int B)";
by (Blast_tac 1);
qed "Inter_Un_subset";

Goal "Inter(A Un B) = Inter(A) Int Inter(B)";
by (Blast_tac 1);
qed "Inter_Un_distrib";

section "UN and INT";

(*Basic identities*)

bind_thm ("not_empty", prove_goal Set.thy "(A ~= {}) = (? x. x:A)" (K [Blast_tac 1]));

Goal "(UN x:{}. B x) = {}";
by (Blast_tac 1);
qed "UN_empty";
Addsimps[UN_empty];

Goal "(UN x:A. {}) = {}";
by (Blast_tac 1);
qed "UN_empty2";
Addsimps[UN_empty2];

Goal "(UN x:A. {x}) = A";
by (Blast_tac 1);
qed "UN_singleton";
Addsimps [UN_singleton];

Goal "k:I ==> A k Un (UN i:I. A i) = (UN i:I. A i)";
by (Blast_tac 1);
qed "UN_absorb";

Goal "(INT x:{}. B x) = UNIV";
by (Blast_tac 1);
qed "INT_empty";
Addsimps[INT_empty];

Goal "k:I ==> A k Int (INT i:I. A i) = (INT i:I. A i)";
by (Blast_tac 1);
qed "INT_absorb";

Goal "(UN x:insert a A. B x) = B a Un UNION A B";
by (Blast_tac 1);
qed "UN_insert";
Addsimps[UN_insert];

Goal "(UN i: A Un B. M i) = (UN i: A. M i) Un (UN i:B. M i)";
by (Blast_tac 1);
qed "UN_Un";

Goal "(UN x : (UN y:A. B y). C x) = (UN y:A. UN x: B y. C x)";
by (Blast_tac 1);
qed "UN_UN_flatten";

Goal "((UN i:I. A i) <= B) = (ALL i:I. A i <= B)";
by (Blast_tac 1);
qed "UN_subset_iff";

Goal "(B <= (INT i:I. A i)) = (ALL i:I. B <= A i)";
by (Blast_tac 1);
qed "INT_subset_iff";

Goal "(INT x:insert a A. B x) = B a Int INTER A B";
by (Blast_tac 1);
qed "INT_insert";
Addsimps[INT_insert];

Goal "(INT i: A Un B. M i) = (INT i: A. M i) Int (INT i:B. M i)";
by (Blast_tac 1);
qed "INT_Un";

Goal "u: A ==> (INT x:A. insert a (B x)) = insert a (INT x:A. B x)";
by (Blast_tac 1);
qed "INT_insert_distrib";

Goal "Union(B``A) = (UN x:A. B(x))";
by (Blast_tac 1);
qed "Union_image_eq";
Addsimps [Union_image_eq];

Goal "f `` Union S = (UN x:S. f `` x)";
by (Blast_tac 1);
qed "image_Union_eq";

Goal "Inter(B``A) = (INT x:A. B(x))";
by (Blast_tac 1);
qed "Inter_image_eq";
Addsimps [Inter_image_eq];

Goal "u: A ==> (UN y:A. c) = c";
by (Blast_tac 1);
qed "UN_constant";
Addsimps[UN_constant];

Goal "u: A ==> (INT y:A. c) = c";
by (Blast_tac 1);
qed "INT_constant";
Addsimps[INT_constant];

Goal "(UN x:A. B(x)) = Union({Y. ? x:A. Y=B(x)})";
by (Blast_tac 1);
qed "UN_eq";

(*Look: it has an EXISTENTIAL quantifier*)
Goal "(INT x:A. B(x)) = Inter({Y. ? x:A. Y=B(x)})";
by (Blast_tac 1);
qed "INT_eq";


(*Distributive laws...*)

Goal "A Int Union(B) = (UN C:B. A Int C)";
by (Blast_tac 1);
qed "Int_Union";

Goal "Union(B) Int A = (UN C:B. C Int A)";
by (Blast_tac 1);
qed "Int_Union2";

(* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
   Union of a family of unions **)
Goal "(UN x:C. A(x) Un B(x)) = Union(A``C)  Un  Union(B``C)";
by (Blast_tac 1);
qed "Un_Union_image";

(*Equivalent version*)
Goal "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))";
by (Blast_tac 1);
qed "UN_Un_distrib";

Goal "A Un Inter(B) = (INT C:B. A Un C)";
by (Blast_tac 1);
qed "Un_Inter";

Goal "(INT x:C. A(x) Int B(x)) = Inter(A``C) Int Inter(B``C)";
by (Blast_tac 1);
qed "Int_Inter_image";

(*Equivalent version*)
Goal "(INT i:I. A(i) Int B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))";
by (Blast_tac 1);
qed "INT_Int_distrib";

(*Halmos, Naive Set Theory, page 35.*)
Goal "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (Blast_tac 1);
qed "Int_UN_distrib";

Goal "B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (Blast_tac 1);
qed "Un_INT_distrib";

Goal "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (Blast_tac 1);
qed "Int_UN_distrib2";

Goal "(INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (Blast_tac 1);
qed "Un_INT_distrib2";


section"Bounded quantifiers";

(** The following are not added to the default simpset because
    (a) they duplicate the body and (b) there are no similar rules for Int. **)

Goal "(ALL x:A Un B. P x) = ((ALL x:A. P x) & (ALL x:B. P x))";
by (Blast_tac 1);
qed "ball_Un";

Goal "(EX x:A Un B. P x) = ((EX x:A. P x) | (EX x:B. P x))";
by (Blast_tac 1);
qed "bex_Un";

Goal "(ALL z: UNION A B. P z) = (ALL x:A. ALL z:B x. P z)";
by (Blast_tac 1);
qed "ball_UN";

Goal "(EX z: UNION A B. P z) = (EX x:A. EX z:B x. P z)";
by (Blast_tac 1);
qed "bex_UN";


section "-";

Goal "A-B = A Int (-B)";
by (Blast_tac 1);
qed "Diff_eq";

Goal "(A-B = {}) = (A<=B)";
by (Blast_tac 1);
qed "Diff_eq_empty_iff";
Addsimps[Diff_eq_empty_iff];

Goal "A-A = {}";
by (Blast_tac 1);
qed "Diff_cancel";
Addsimps[Diff_cancel];

Goal "A Int B = {} ==> A-B = A";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "Diff_triv";

Goal "{}-A = {}";
by (Blast_tac 1);
qed "empty_Diff";
Addsimps[empty_Diff];

Goal "A-{} = A";
by (Blast_tac 1);
qed "Diff_empty";
Addsimps[Diff_empty];

Goal "A-UNIV = {}";
by (Blast_tac 1);
qed "Diff_UNIV";
Addsimps[Diff_UNIV];

Goal "x~:A ==> A - insert x B = A-B";
by (Blast_tac 1);
qed "Diff_insert0";
Addsimps [Diff_insert0];

(*NOT SUITABLE FOR REWRITING since {a} == insert a 0*)
Goal "A - insert a B = A - B - {a}";
by (Blast_tac 1);
qed "Diff_insert";

(*NOT SUITABLE FOR REWRITING since {a} == insert a 0*)
Goal "A - insert a B = A - {a} - B";
by (Blast_tac 1);
qed "Diff_insert2";

Goal "insert x A - B = (if x:B then A-B else insert x (A-B))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "insert_Diff_if";

Goal "x:B ==> insert x A - B = A-B";
by (Blast_tac 1);
qed "insert_Diff1";
Addsimps [insert_Diff1];

Goal "a:A ==> insert a (A-{a}) = A";
by (Blast_tac 1);
qed "insert_Diff";

Goal "x ~: A ==> (insert x A) - {x} = A";
by Auto_tac;
qed "Diff_insert_absorb";

Goal "A Int (B-A) = {}";
by (Blast_tac 1);
qed "Diff_disjoint";
Addsimps[Diff_disjoint];

Goal "A<=B ==> A Un (B-A) = B";
by (Blast_tac 1);
qed "Diff_partition";

Goal "[| A<=B; B<= C |] ==> (B - (C - A)) = (A :: 'a set)";
by (Blast_tac 1);
qed "double_diff";

Goal "A Un (B-A) = A Un B";
by (Blast_tac 1);
qed "Un_Diff_cancel";

Goal "(B-A) Un A = B Un A";
by (Blast_tac 1);
qed "Un_Diff_cancel2";

Addsimps [Un_Diff_cancel, Un_Diff_cancel2];

Goal "A - (B Un C) = (A-B) Int (A-C)";
by (Blast_tac 1);
qed "Diff_Un";

Goal "A - (B Int C) = (A-B) Un (A-C)";
by (Blast_tac 1);
qed "Diff_Int";

Goal "(A Un B) - C = (A - C) Un (B - C)";
by (Blast_tac 1);
qed "Un_Diff";

Goal "(A Int B) - C = A Int (B - C)";
by (Blast_tac 1);
qed "Int_Diff";

Goal "C Int (A-B) = (C Int A) - (C Int B)";
by (Blast_tac 1);
qed "Diff_Int_distrib";

Goal "(A-B) Int C = (A Int C) - (B Int C)";
by (Blast_tac 1);
qed "Diff_Int_distrib2";

Goal "A - (- B) = A Int B";
by Auto_tac;
qed "Diff_Compl";
Addsimps [Diff_Compl];


section "Quantification over type \"bool\"";

Goal "(ALL b::bool. P b) = (P True & P False)";
by Auto_tac;
by (case_tac "b" 1);
by Auto_tac;
qed "all_bool_eq";

bind_thm ("bool_induct", conjI RS (all_bool_eq RS iffD2) RS spec);

Goal "(EX b::bool. P b) = (P True | P False)";
by Auto_tac;
by (case_tac "b" 1);
by Auto_tac;
qed "ex_bool_eq";

Goal "A Un B = (UN b. if b then A else B)";
by (auto_tac(claset()delWrapper"bspec",simpset()addsimps [split_if_mem2]));
qed "Un_eq_UN";

Goal "(UN b::bool. A b) = (A True Un A False)";
by Auto_tac;
by (case_tac "b" 1);
by Auto_tac;
qed "UN_bool_eq";

Goal "(INT b::bool. A b) = (A True Int A False)";
by Auto_tac;
by (case_tac "b" 1);
by Auto_tac;
qed "INT_bool_eq";


section "Pow";

Goalw [Pow_def] "Pow {} = {{}}";
by Auto_tac;
qed "Pow_empty";
Addsimps [Pow_empty];

Goal "Pow (insert a A) = Pow A Un (insert a `` Pow A)";
by Safe_tac;
by (etac swap 1);
by (res_inst_tac [("x", "x-{a}")] image_eqI 1);
by (ALLGOALS Blast_tac);
qed "Pow_insert";

Goal "Pow (- A) = {-B |B. A: Pow B}";
by Safe_tac;
by (Blast_tac 2);
by (res_inst_tac [("x", "-x")] exI 1);
by (ALLGOALS Blast_tac);
qed "Pow_Compl";

Goal "Pow UNIV = UNIV";
by (Blast_tac 1);
qed "Pow_UNIV";
Addsimps [Pow_UNIV];

Goal "Pow(A) Un Pow(B) <= Pow(A Un B)";
by (Blast_tac 1);
qed "Un_Pow_subset";

Goal "(UN x:A. Pow(B(x))) <= Pow(UN x:A. B(x))";
by (Blast_tac 1);
qed "UN_Pow_subset";

Goal "A <= Pow(Union(A))";
by (Blast_tac 1);
qed "subset_Pow_Union";

Goal "Union(Pow(A)) = A";
by (Blast_tac 1);
qed "Union_Pow_eq";

Goal "Pow(A Int B) = Pow(A) Int Pow(B)";
by (Blast_tac 1);
qed "Pow_Int_eq";

Goal "Pow(INT x:A. B(x)) = (INT x:A. Pow(B(x)))";
by (Blast_tac 1);
qed "Pow_INT_eq";

Addsimps [Union_Pow_eq, Pow_Int_eq];


section "Miscellany";

Goal "(A = B) = ((A <= (B::'a set)) & (B<=A))";
by (Blast_tac 1);
qed "set_eq_subset";

Goal "A <= B =  (! t. t:A --> t:B)";
by (Blast_tac 1);
qed "subset_iff";

Goalw [psubset_def] "((A::'a set) <= B) = ((A < B) | (A=B))";
by (Blast_tac 1);
qed "subset_iff_psubset_eq";

Goal "(!x. x ~: A) = (A={})";
by (Blast_tac 1);
qed "all_not_in_conv";
AddIffs [all_not_in_conv];


(** for datatypes **)
Goal "f x ~= f y ==> x ~= y";
by (Fast_tac 1);
qed "distinct_lemma";


(** Miniscoping: pushing in big Unions and Intersections **)
local
  fun prover s = prove_goal thy s (fn _ => [Blast_tac 1])
in
val UN_simps = map prover 
    ["!!C. c: C ==> (UN x:C. insert a (B x)) = insert a (UN x:C. B x)",
     "!!C. c: C ==> (UN x:C. A x Un B)   = ((UN x:C. A x) Un B)",
     "!!C. c: C ==> (UN x:C. A Un B x)   = (A Un (UN x:C. B x))",
     "(UN x:C. A x Int B)  = ((UN x:C. A x) Int B)",
     "(UN x:C. A Int B x)  = (A Int (UN x:C. B x))",
     "(UN x:C. A x - B)    = ((UN x:C. A x) - B)",
     "(UN x:C. A - B x)    = (A - (INT x:C. B x))",
     "(UN x: Union A. B x) = (UN y:A. UN x:y. B x)",
     "(UN z: UNION A B. C z) = (UN  x:A. UN z: B(x). C z)",
     "(UN x:f``A. B x)     = (UN a:A. B(f a))"];

val INT_simps = map prover
    ["!!C. c: C ==> (INT x:C. A x Int B) = ((INT x:C. A x) Int B)",
     "!!C. c: C ==> (INT x:C. A Int B x) = (A Int (INT x:C. B x))",
     "!!C. c: C ==> (INT x:C. A x - B)   = ((INT x:C. A x) - B)",
     "!!C. c: C ==> (INT x:C. A - B x)   = (A - (UN x:C. B x))",
     "(INT x:C. insert a (B x)) = insert a (INT x:C. B x)",
     "(INT x:C. A x Un B)  = ((INT x:C. A x) Un B)",
     "(INT x:C. A Un B x)  = (A Un (INT x:C. B x))",
     "(INT x: Union A. B x) = (INT y:A. INT x:y. B x)",
     "(INT z: UNION A B. C z) = (INT x:A. INT z: B(x). C z)",
     "(INT x:f``A. B x)    = (INT a:A. B(f a))"];


val ball_simps = map prover
    ["(ALL x:A. P x | Q) = ((ALL x:A. P x) | Q)",
     "(ALL x:A. P | Q x) = (P | (ALL x:A. Q x))",
     "(ALL x:A. P --> Q x) = (P --> (ALL x:A. Q x))",
     "(ALL x:A. P x --> Q) = ((EX x:A. P x) --> Q)",
     "(ALL x:{}. P x) = True",
     "(ALL x:UNIV. P x) = (ALL x. P x)",
     "(ALL x:insert a B. P x) = (P(a) & (ALL x:B. P x))",
     "(ALL x:Union(A). P x) = (ALL y:A. ALL x:y. P x)",
     "(ALL x: UNION A B. P x) = (ALL a:A. ALL x: B a. P x)",
     "(ALL x:Collect Q. P x) = (ALL x. Q x --> P x)",
     "(ALL x:f``A. P x) = (ALL x:A. P(f x))",
     "(~(ALL x:A. P x)) = (EX x:A. ~P x)"];

val ball_conj_distrib = 
    prover "(ALL x:A. P x & Q x) = ((ALL x:A. P x) & (ALL x:A. Q x))";

val bex_simps = map prover
    ["(EX x:A. P x & Q) = ((EX x:A. P x) & Q)",
     "(EX x:A. P & Q x) = (P & (EX x:A. Q x))",
     "(EX x:{}. P x) = False",
     "(EX x:UNIV. P x) = (EX x. P x)",
     "(EX x:insert a B. P x) = (P(a) | (EX x:B. P x))",
     "(EX x:Union(A). P x) = (EX y:A. EX x:y.  P x)",
     "(EX x: UNION A B. P x) = (EX a:A. EX x: B a.  P x)",
     "(EX x:Collect Q. P x) = (EX x. Q x & P x)",
     "(EX x:f``A. P x) = (EX x:A. P(f x))",
     "(~(EX x:A. P x)) = (ALL x:A. ~P x)"];

val bex_disj_distrib = 
    prover "(EX x:A. P x | Q x) = ((EX x:A. P x) | (EX x:A. Q x))";

end;

bind_thms ("UN_simps", UN_simps);
bind_thms ("INT_simps", INT_simps);
bind_thms ("ball_simps", ball_simps);
bind_thms ("bex_simps", bex_simps);
bind_thm ("ball_conj_distrib", ball_conj_distrib);
bind_thm ("bex_disj_distrib", bex_disj_distrib);

Addsimps (UN_simps @ INT_simps @ ball_simps @ bex_simps);
