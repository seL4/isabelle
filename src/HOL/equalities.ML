(*  Title:      HOL/equalities
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Equalities involving union, intersection, inclusion, etc.
*)

writeln"File HOL/equalities";

AddSIs [equalityI];

section "{}";

goal thy "{x. False} = {}";
by (Blast_tac 1);
qed "Collect_False_empty";
Addsimps [Collect_False_empty];

goal thy "(A <= {}) = (A = {})";
by (Blast_tac 1);
qed "subset_empty";
Addsimps [subset_empty];

goalw thy [psubset_def] "~ (A < {})";
by (Blast_tac 1);
qed "not_psubset_empty";
AddIffs [not_psubset_empty];

section "insert";

(*NOT SUITABLE FOR REWRITING since {a} == insert a {}*)
goal thy "insert a A = {a} Un A";
by (Blast_tac 1);
qed "insert_is_Un";

goal thy "insert a A ~= {}";
by (blast_tac (claset() addEs [equalityCE]) 1);
qed"insert_not_empty";
Addsimps[insert_not_empty];

bind_thm("empty_not_insert",insert_not_empty RS not_sym);
Addsimps[empty_not_insert];

goal thy "!!a. a:A ==> insert a A = A";
by (Blast_tac 1);
qed "insert_absorb";
(* Addsimps [insert_absorb] causes recursive (ie quadtratic) calls
   in case of nested inserts!
*)

goal thy "insert x (insert x A) = insert x A";
by (Blast_tac 1);
qed "insert_absorb2";
Addsimps [insert_absorb2];

goal thy "insert x (insert y A) = insert y (insert x A)";
by (Blast_tac 1);
qed "insert_commute";

goal thy "(insert x A <= B) = (x:B & A <= B)";
by (Blast_tac 1);
qed "insert_subset";
Addsimps[insert_subset];

goal thy "!!a. insert a A ~= insert a B ==> A ~= B";
by (Blast_tac 1);
qed "insert_lim";

(* use new B rather than (A-{a}) to avoid infinite unfolding *)
goal thy "!!a. a:A ==> ? B. A = insert a B & a ~: B";
by (res_inst_tac [("x","A-{a}")] exI 1);
by (Blast_tac 1);
qed "mk_disjoint_insert";

goal thy
    "!!A. A~={} ==> (UN x:A. insert a (B x)) = insert a (UN x:A. B x)";
by (Blast_tac 1);
qed "UN_insert_distrib";

section "``";

goal thy "f``{} = {}";
by (Blast_tac 1);
qed "image_empty";
Addsimps[image_empty];

goal thy "f``insert a B = insert (f a) (f``B)";
by (Blast_tac 1);
qed "image_insert";
Addsimps[image_insert];

goal thy  "(f `` (UNION A B)) = (UN x:A.(f `` (B x)))";
by (Blast_tac 1);
qed "image_UNION";

goal thy "(%x. x) `` Y = Y";
by (Blast_tac 1);
qed "image_id";

goal thy "f``(g``A) = (%x. f (g x)) `` A";
by (Blast_tac 1);
qed "image_image";

goal thy "!!x. x:A ==> insert (f x) (f``A) = f``A";
by (Blast_tac 1);
qed "insert_image";
Addsimps [insert_image];

goal thy "(f``A = {}) = (A = {})";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "image_is_empty";
AddIffs [image_is_empty];

goalw thy [image_def]
"(%x. if P x then f x else g x) `` S                    \
\ = (f `` (S Int {x. P x})) Un (g `` (S Int {x. ~(P x)}))";
by (split_tac [expand_if] 1);
by (Blast_tac 1);
qed "if_image_distrib";
Addsimps[if_image_distrib];

val prems= goal thy "[|M = N; !!x. x:N ==> f x = g x|] ==> f``M = g``N";
by (rtac set_ext 1);
by (simp_tac (simpset() addsimps image_def::prems) 1);
qed "image_cong";


section "Int";

goal thy "A Int A = A";
by (Blast_tac 1);
qed "Int_absorb";
Addsimps[Int_absorb];

goal thy " A Int (A Int B) = A Int B";
by (Blast_tac 1);
qed "Int_left_absorb";

goal thy "A Int B  =  B Int A";
by (Blast_tac 1);
qed "Int_commute";

goal thy "A Int (B Int C) = B Int (A Int C)";
by (Blast_tac 1);
qed "Int_left_commute";

goal thy "(A Int B) Int C  =  A Int (B Int C)";
by (Blast_tac 1);
qed "Int_assoc";

(*Intersection is an AC-operator*)
val Int_ac = [Int_assoc, Int_left_absorb, Int_commute, Int_left_commute];

goal thy "{} Int B = {}";
by (Blast_tac 1);
qed "Int_empty_left";
Addsimps[Int_empty_left];

goal thy "A Int {} = {}";
by (Blast_tac 1);
qed "Int_empty_right";
Addsimps[Int_empty_right];

goal thy "(A Int B = {}) = (A <= Compl B)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "disjoint_eq_subset_Compl";

goal thy "UNIV Int B = B";
by (Blast_tac 1);
qed "Int_UNIV_left";
Addsimps[Int_UNIV_left];

goal thy "A Int UNIV = A";
by (Blast_tac 1);
qed "Int_UNIV_right";
Addsimps[Int_UNIV_right];

goal thy "A Int (B Un C)  =  (A Int B) Un (A Int C)";
by (Blast_tac 1);
qed "Int_Un_distrib";

goal thy "(B Un C) Int A =  (B Int A) Un (C Int A)";
by (Blast_tac 1);
qed "Int_Un_distrib2";

goal thy "(A<=B) = (A Int B = A)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "subset_Int_eq";

goal thy "(A Int B = UNIV) = (A = UNIV & B = UNIV)";
by (blast_tac (claset() addEs [equalityCE]) 1);
qed "Int_UNIV";
Addsimps[Int_UNIV];

section "Un";

goal thy "A Un A = A";
by (Blast_tac 1);
qed "Un_absorb";
Addsimps[Un_absorb];

goal thy " A Un (A Un B) = A Un B";
by (Blast_tac 1);
qed "Un_left_absorb";

goal thy "A Un B  =  B Un A";
by (Blast_tac 1);
qed "Un_commute";

goal thy "A Un (B Un C) = B Un (A Un C)";
by (Blast_tac 1);
qed "Un_left_commute";

goal thy "(A Un B) Un C  =  A Un (B Un C)";
by (Blast_tac 1);
qed "Un_assoc";

(*Union is an AC-operator*)
val Un_ac = [Un_assoc, Un_left_absorb, Un_commute, Un_left_commute];

goal thy "{} Un B = B";
by (Blast_tac 1);
qed "Un_empty_left";
Addsimps[Un_empty_left];

goal thy "A Un {} = A";
by (Blast_tac 1);
qed "Un_empty_right";
Addsimps[Un_empty_right];

goal thy "UNIV Un B = UNIV";
by (Blast_tac 1);
qed "Un_UNIV_left";
Addsimps[Un_UNIV_left];

goal thy "A Un UNIV = UNIV";
by (Blast_tac 1);
qed "Un_UNIV_right";
Addsimps[Un_UNIV_right];

goal thy "(insert a B) Un C = insert a (B Un C)";
by (Blast_tac 1);
qed "Un_insert_left";
Addsimps[Un_insert_left];

goal thy "A Un (insert a B) = insert a (A Un B)";
by (Blast_tac 1);
qed "Un_insert_right";
Addsimps[Un_insert_right];

goal thy "(insert a B) Int C = (if a:C then insert a (B Int C) \
\                                      else        B Int C)";
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Blast_tac 1);
qed "Int_insert_left";

goal thy "A Int (insert a B) = (if a:A then insert a (A Int B) \
\                                      else        A Int B)";
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Blast_tac 1);
qed "Int_insert_right";

goal thy "A Un (B Int C)  =  (A Un B) Int (A Un C)";
by (Blast_tac 1);
qed "Un_Int_distrib";

goal thy "(B Int C) Un A =  (B Un A) Int (C Un A)";
by (Blast_tac 1);
qed "Un_Int_distrib2";

goal thy
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (Blast_tac 1);
qed "Un_Int_crazy";

goal thy "(A<=B) = (A Un B = B)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "subset_Un_eq";

goal thy "(A <= insert b C) = (A <= C | b:A & A-{b} <= C)";
by (Blast_tac 1);
qed "subset_insert_iff";

goal thy "(A Un B = {}) = (A = {} & B = {})";
by (blast_tac (claset() addEs [equalityCE]) 1);
qed "Un_empty";
Addsimps[Un_empty];

section "Compl";

goal thy "A Int Compl(A) = {}";
by (Blast_tac 1);
qed "Compl_disjoint";
Addsimps[Compl_disjoint];

goal thy "A Un Compl(A) = UNIV";
by (Blast_tac 1);
qed "Compl_partition";

goal thy "Compl(Compl(A)) = A";
by (Blast_tac 1);
qed "double_complement";
Addsimps[double_complement];

goal thy "Compl(A Un B) = Compl(A) Int Compl(B)";
by (Blast_tac 1);
qed "Compl_Un";

goal thy "Compl(A Int B) = Compl(A) Un Compl(B)";
by (Blast_tac 1);
qed "Compl_Int";

goal thy "Compl(UN x:A. B(x)) = (INT x:A. Compl(B(x)))";
by (Blast_tac 1);
qed "Compl_UN";

goal thy "Compl(INT x:A. B(x)) = (UN x:A. Compl(B(x)))";
by (Blast_tac 1);
qed "Compl_INT";

Addsimps [Compl_Un, Compl_Int, Compl_UN, Compl_INT];

(*Halmos, Naive Set Theory, page 16.*)

goal thy "((A Int B) Un C = A Int (B Un C)) = (C<=A)";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "Un_Int_assoc_eq";


section "Union";

goal thy "Union({}) = {}";
by (Blast_tac 1);
qed "Union_empty";
Addsimps[Union_empty];

goal thy "Union(UNIV) = UNIV";
by (Blast_tac 1);
qed "Union_UNIV";
Addsimps[Union_UNIV];

goal thy "Union(insert a B) = a Un Union(B)";
by (Blast_tac 1);
qed "Union_insert";
Addsimps[Union_insert];

goal thy "Union(A Un B) = Union(A) Un Union(B)";
by (Blast_tac 1);
qed "Union_Un_distrib";
Addsimps[Union_Un_distrib];

goal thy "Union(A Int B) <= Union(A) Int Union(B)";
by (Blast_tac 1);
qed "Union_Int_subset";

goal thy "(Union M = {}) = (! A : M. A = {})"; 
by (blast_tac (claset() addEs [equalityCE]) 1);
qed "Union_empty_conv"; 
AddIffs [Union_empty_conv];

goal thy "(Union(C) Int A = {}) = (! B:C. B Int A = {})";
by (blast_tac (claset() addSEs [equalityCE]) 1);
qed "Union_disjoint";

section "Inter";

goal thy "Inter({}) = UNIV";
by (Blast_tac 1);
qed "Inter_empty";
Addsimps[Inter_empty];

goal thy "Inter(UNIV) = {}";
by (Blast_tac 1);
qed "Inter_UNIV";
Addsimps[Inter_UNIV];

goal thy "Inter(insert a B) = a Int Inter(B)";
by (Blast_tac 1);
qed "Inter_insert";
Addsimps[Inter_insert];

goal thy "Inter(A) Un Inter(B) <= Inter(A Int B)";
by (Blast_tac 1);
qed "Inter_Un_subset";

goal thy "Inter(A Un B) = Inter(A) Int Inter(B)";
by (Blast_tac 1);
qed "Inter_Un_distrib";

section "UN and INT";

(*Basic identities*)

val not_empty = prove_goal Set.thy "(A ~= {}) = (? x. x:A)" (K [Blast_tac 1]);
(*Addsimps[not_empty];*)

goal thy "(UN x:{}. B x) = {}";
by (Blast_tac 1);
qed "UN_empty";
Addsimps[UN_empty];

goal thy "(UN x:A. {}) = {}";
by (Blast_tac 1);
qed "UN_empty2";
Addsimps[UN_empty2];

goal thy "(INT x:{}. B x) = UNIV";
by (Blast_tac 1);
qed "INT_empty";
Addsimps[INT_empty];

goal thy "(UN x:insert a A. B x) = B a Un UNION A B";
by (Blast_tac 1);
qed "UN_insert";
Addsimps[UN_insert];

goal thy "(UN i: A Un B. M i) = ((UN i: A. M i) Un (UN i:B. M i))";
by (Blast_tac 1);
qed "UN_Un";

goal thy "(INT x:insert a A. B x) = B a Int INTER A B";
by (Blast_tac 1);
qed "INT_insert";
Addsimps[INT_insert];

goal thy
    "!!A. A~={} ==> (INT x:A. insert a (B x)) = insert a (INT x:A. B x)";
by (Blast_tac 1);
qed "INT_insert_distrib";

goal thy "Union(B``A) = (UN x:A. B(x))";
by (Blast_tac 1);
qed "Union_image_eq";

goal thy "Inter(B``A) = (INT x:A. B(x))";
by (Blast_tac 1);
qed "Inter_image_eq";

goal thy "!!A. A~={} ==> (UN y:A. c) = c";
by (Blast_tac 1);
qed "UN_constant";
Addsimps[UN_constant];

goal thy "!!A. A~={} ==> (INT y:A. c) = c";
by (Blast_tac 1);
qed "INT_constant";
Addsimps[INT_constant];

goal thy "(UN x:A. B(x)) = Union({Y. ? x:A. Y=B(x)})";
by (Blast_tac 1);
qed "UN_eq";

(*Look: it has an EXISTENTIAL quantifier*)
goal thy "(INT x:A. B(x)) = Inter({Y. ? x:A. Y=B(x)})";
by (Blast_tac 1);
qed "INT_eq";

goalw thy [o_def] "UNION A (g o f) = UNION (f``A) g";
by (Blast_tac 1);
qed "UNION_o";


(*Distributive laws...*)

goal thy "A Int Union(B) = (UN C:B. A Int C)";
by (Blast_tac 1);
qed "Int_Union";

(* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
   Union of a family of unions **)
goal thy "(UN x:C. A(x) Un B(x)) = Union(A``C)  Un  Union(B``C)";
by (Blast_tac 1);
qed "Un_Union_image";

(*Equivalent version*)
goal thy "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))";
by (Blast_tac 1);
qed "UN_Un_distrib";

goal thy "A Un Inter(B) = (INT C:B. A Un C)";
by (Blast_tac 1);
qed "Un_Inter";

goal thy "(INT x:C. A(x) Int B(x)) = Inter(A``C) Int Inter(B``C)";
by (Blast_tac 1);
qed "Int_Inter_image";

(*Equivalent version*)
goal thy "(INT i:I. A(i) Int B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))";
by (Blast_tac 1);
qed "INT_Int_distrib";

(*Halmos, Naive Set Theory, page 35.*)
goal thy "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (Blast_tac 1);
qed "Int_UN_distrib";

goal thy "B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (Blast_tac 1);
qed "Un_INT_distrib";

goal thy
    "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (Blast_tac 1);
qed "Int_UN_distrib2";

goal thy
    "(INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (Blast_tac 1);
qed "Un_INT_distrib2";


section"Bounded quantifiers";

(** The following are not added to the default simpset because
    (a) they duplicate the body and (b) there are no similar rules for Int. **)

goal thy "(ALL x:A Un B. P x) = ((ALL x:A. P x) & (ALL x:B. P x))";
by (Blast_tac 1);
qed "ball_Un";

goal thy "(EX x:A Un B. P x) = ((EX x:A. P x) | (EX x:B. P x))";
by (Blast_tac 1);
qed "bex_Un";


section "-";

goal thy "A-B = A Int Compl B";
by (Blast_tac 1);
qed "Diff_eq_Int_Compl";

goal thy "A-A = {}";
by (Blast_tac 1);
qed "Diff_cancel";
Addsimps[Diff_cancel];

goal thy "{}-A = {}";
by (Blast_tac 1);
qed "empty_Diff";
Addsimps[empty_Diff];

goal thy "A-{} = A";
by (Blast_tac 1);
qed "Diff_empty";
Addsimps[Diff_empty];

goal thy "A-UNIV = {}";
by (Blast_tac 1);
qed "Diff_UNIV";
Addsimps[Diff_UNIV];

goal thy "!!x. x~:A ==> A - insert x B = A-B";
by (Blast_tac 1);
qed "Diff_insert0";
Addsimps [Diff_insert0];

(*NOT SUITABLE FOR REWRITING since {a} == insert a 0*)
goal thy "A - insert a B = A - B - {a}";
by (Blast_tac 1);
qed "Diff_insert";

(*NOT SUITABLE FOR REWRITING since {a} == insert a 0*)
goal thy "A - insert a B = A - {a} - B";
by (Blast_tac 1);
qed "Diff_insert2";

goal thy "insert x A - B = (if x:B then A-B else insert x (A-B))";
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Blast_tac 1);
qed "insert_Diff_if";

goal thy "!!x. x:B ==> insert x A - B = A-B";
by (Blast_tac 1);
qed "insert_Diff1";
Addsimps [insert_Diff1];

goal thy "!!a. a:A ==> insert a (A-{a}) = A";
by (Blast_tac 1);
qed "insert_Diff";

goal thy "A Int (B-A) = {}";
by (Blast_tac 1);
qed "Diff_disjoint";
Addsimps[Diff_disjoint];

goal thy "!!A. A<=B ==> A Un (B-A) = B";
by (Blast_tac 1);
qed "Diff_partition";

goal thy "!!A. [| A<=B; B<= C |] ==> (B - (C - A)) = (A :: 'a set)";
by (Blast_tac 1);
qed "double_diff";

goal thy "A - (B Un C) = (A-B) Int (A-C)";
by (Blast_tac 1);
qed "Diff_Un";

goal thy "A - (B Int C) = (A-B) Un (A-C)";
by (Blast_tac 1);
qed "Diff_Int";

goal thy "(A Un B) - C = (A - C) Un (B - C)";
by (Blast_tac 1);
qed "Un_Diff";

goal thy "(A Int B) - C = (A - C) Int (B - C)";
by (Blast_tac 1);
qed "Int_Diff";


section "Miscellany";

goal thy "(A = B) = ((A <= (B::'a set)) & (B<=A))";
by (Blast_tac 1);
qed "set_eq_subset";

goal thy "A <= B =  (! t. t:A --> t:B)";
by (Blast_tac 1);
qed "subset_iff";

goalw thy [psubset_def] "((A::'a set) <= B) = ((A < B) | (A=B))";
by (Blast_tac 1);
qed "subset_iff_psubset_eq";

goal thy "(!x. x ~: A) = (A={})";
by (Blast_tac 1);
qed "all_not_in_conv";
AddIffs [all_not_in_conv];

goalw thy [Pow_def] "Pow {} = {{}}";
by Auto_tac;
qed "Pow_empty";
Addsimps [Pow_empty];

goal thy "Pow (insert a A) = Pow A Un (insert a `` Pow A)";
by Safe_tac;
by (etac swap 1);
by (res_inst_tac [("x", "x-{a}")] image_eqI 1);
by (ALLGOALS Blast_tac);
qed "Pow_insert";


(** Miniscoping: pushing in big Unions and Intersections **)
local
  fun prover s = prove_goal thy s (fn _ => [Blast_tac 1])
in
val UN_simps = map prover 
    ["!!C. C ~= {} ==> (UN x:C. insert a (B x)) = insert a (UN x:C. B x)",
     "!!C. C ~= {} ==> (UN x:C. A x Un B)   = ((UN x:C. A x) Un B)",
     "!!C. C ~= {} ==> (UN x:C. A Un B x)   = (A Un (UN x:C. B x))",
     "(UN x:C. A x Int B)  = ((UN x:C. A x) Int B)",
     "(UN x:C. A Int B x)  = (A Int (UN x:C. B x))",
     "(UN x:C. A x - B)    = ((UN x:C. A x) - B)",
     "(UN x:C. A - B x)    = (A - (INT x:C. B x))",
     "(UN x:f``A. B x)     = (UN a:A. B(f a))"];

val INT_simps = map prover
    ["!!C. C ~= {} ==> (INT x:C. A x Int B) = ((INT x:C. A x) Int B)",
     "!!C. C ~= {} ==> (INT x:C. A Int B x) = (A Int (INT x:C. B x))",
     "!!C. C ~= {} ==> (INT x:C. A x - B)   = ((INT x:C. A x) - B)",
     "!!C. C ~= {} ==> (INT x:C. A - B x)   = (A - (UN x:C. B x))",
     "(INT x:C. insert a (B x)) = insert a (INT x:C. B x)",
     "(INT x:C. A x Un B)  = ((INT x:C. A x) Un B)",
     "(INT x:C. A Un B x)  = (A Un (INT x:C. B x))",
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
     "(EX x:Collect Q. P x) = (EX x. Q x & P x)",
     "(EX x:f``A. P x) = (EX x:A. P(f x))",
     "(~(EX x:A. P x)) = (ALL x:A. ~P x)"];

val bex_disj_distrib = 
    prover "(EX x:A. P x | Q x) = ((EX x:A. P x) | (EX x:A. Q x))";

end;

Addsimps (UN_simps @ INT_simps @ ball_simps @ bex_simps);
