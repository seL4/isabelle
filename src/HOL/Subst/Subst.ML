(*  Title:      HOL/Subst/Subst.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Substitutions on uterms
*)

open Subst;


(**** Substitutions ****)

goal Subst.thy "t <| [] = t";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed "subst_Nil";

Addsimps [subst_Nil];

goal Subst.thy "t <: u --> t <| s <: u <| s";
by (induct_tac "u" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "subst_mono";

goal Subst.thy  "~ (Var(v) <: t) --> t <| (v,t <| s) # s = t <| s";
by (case_tac "t = Var(v)" 1);
by (etac rev_mp 2);
by (res_inst_tac [("P",
    "%x.~x=Var(v) --> ~(Var(v) <: x) --> x <| (v,t<|s)#s=x<|s")]
    uterm.induct 2);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed_spec_mp "Var_not_occs";

goal Subst.thy
    "(t <|r = t <|s) = (! v. v : vars_of(t) --> Var(v) <|r = Var(v) <|s)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_full_simp_tac);
by (ALLGOALS Blast_tac);
qed "agreement";

goal Subst.thy   "~ v: vars_of(t) --> t <| (v,u)#s = t <| s";
by (simp_tac (simpset() addsimps [agreement] addsplits [expand_if]) 1);
qed_spec_mp"repl_invariance";

val asms = goal Subst.thy 
     "v : vars_of(t) --> w : vars_of(t <| (v,Var(w))#s)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp"Var_in_subst";


(**** Equality between Substitutions ****)

goalw Subst.thy [subst_eq_def] "r =$= s = (! t. t <| r = t <| s)";
by (Simp_tac 1);
qed "subst_eq_iff";


local fun prove s = prove_goal Subst.thy s
                  (fn prems => [cut_facts_tac prems 1,
                                REPEAT (etac rev_mp 1),
                                simp_tac (simpset() addsimps [subst_eq_iff]) 1])
in 
  val subst_refl      = prove "r =$= r";
  val subst_sym       = prove "r =$= s ==> s =$= r";
  val subst_trans     = prove "[| q =$= r; r =$= s |] ==> q =$= s";
end;


AddIffs [subst_refl];


val eq::prems = goalw Subst.thy [subst_eq_def] 
    "[| r =$= s; P (t <| r) (u <| r) |] ==> P (t <| s) (u <| s)";
by (resolve_tac [eq RS spec RS subst] 1);
by (resolve_tac (prems RL [eq RS spec RS subst]) 1);
qed "subst_subst2";

val ssubst_subst2 = subst_sym RS subst_subst2;

(**** Composition of Substitutions ****)

let fun prove s = 
 prove_goalw Subst.thy [comp_def,sdom_def] s (fn _ => [Simp_tac 1])
in 
Addsimps
 (
   map prove 
   [ "[] <> bl = bl",
     "((a,b)#al) <> bl = (a,b <| bl) # (al <> bl)",
     "sdom([]) = {}",
     "sdom((a,b)#al) = (if Var(a)=b then (sdom al) - {a} else sdom al Un {a})"]
 )
end;


goal Subst.thy "s <> [] = s";
by (alist_ind_tac "s" 1);
by (ALLGOALS Asm_simp_tac);
qed "comp_Nil";

Addsimps [comp_Nil];

goal Subst.thy "s =$= s <> []";
by (Simp_tac 1);
qed "subst_comp_Nil";

goal Subst.thy "(t <| r <> s) = (t <| r <| s)";
by (induct_tac "t" 1);
by (ALLGOALS Asm_simp_tac);
by (alist_ind_tac "r" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "subst_comp";

Addsimps [subst_comp];

goal Subst.thy "(q <> r) <> s =$= q <> (r <> s)";
by (simp_tac (simpset() addsimps [subst_eq_iff]) 1);
qed "comp_assoc";

goal Subst.thy "!!s. [| theta =$= theta1; sigma =$= sigma1|] ==> \
             \       (theta <> sigma) =$= (theta1 <> sigma1)";
by (asm_full_simp_tac (simpset() addsimps [subst_eq_def]) 1);
qed "subst_cong";


goal Subst.thy "(w, Var(w) <| s) # s =$= s"; 
by (simp_tac (simpset() addsimps [subst_eq_iff]) 1);
by (rtac allI 1);
by (induct_tac "t" 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsplits [expand_if])));
qed "Cons_trivial";


goal Subst.thy "!!s. q <> r =$= s ==>  t <| q <| r = t <| s";
by (asm_full_simp_tac (simpset() addsimps [subst_eq_iff]) 1);
qed "comp_subst_subst";


(****  Domain and range of Substitutions ****)

goal Subst.thy  "(v : sdom(s)) = (Var(v) <| s ~= Var(v))";
by (alist_ind_tac "s" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
by (Blast_tac 1);
qed "sdom_iff";


goalw Subst.thy [srange_def]  
   "v : srange(s) = (? w. w : sdom(s) & v : vars_of(Var(w) <| s))";
by (Blast_tac 1);
qed "srange_iff";

goalw thy [empty_def] "(A = {}) = (ALL a.~ a:A)";
by (Blast_tac 1);
qed "empty_iff_all_not";

goal Subst.thy  "(t <| s = t) = (sdom(s) Int vars_of(t) = {})";
by (induct_tac "t" 1);
by (ALLGOALS
    (asm_full_simp_tac (simpset() addsimps [empty_iff_all_not, sdom_iff])));
by (ALLGOALS Blast_tac);
qed "invariance";

goal Subst.thy  "v : sdom(s) -->  v : vars_of(t <| s) --> v : srange(s)";
by (induct_tac "t" 1);
by (case_tac "a : sdom(s)" 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [sdom_iff, srange_iff])));
by (ALLGOALS Blast_tac);
qed_spec_mp "Var_in_srange";

goal Subst.thy 
     "!!v. [| v : sdom(s); v ~: srange(s) |] ==>  v ~: vars_of(t <| s)";
by (blast_tac (claset() addIs [Var_in_srange]) 1);
qed "Var_elim";

goal Subst.thy  "v : vars_of(t <| s) --> v : srange(s) | v : vars_of(t)";
by (induct_tac "t" 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [sdom_iff,srange_iff])));
by (Blast_tac 2);
by (safe_tac (claset() addSIs [exI, vars_var_iff RS iffD1 RS sym]));
by (Auto_tac());
qed_spec_mp "Var_intro";

goal Subst.thy
    "v : srange(s) --> (? w. w : sdom(s) & v : vars_of(Var(w) <| s))";
by (simp_tac (simpset() addsimps [srange_iff]) 1);
qed_spec_mp "srangeD";

goal Subst.thy
   "sdom(s) Int srange(s) = {} = (! t. sdom(s) Int vars_of(t <| s) = {})";
by (simp_tac (simpset() addsimps [empty_iff_all_not]) 1);
by (fast_tac (claset() addIs [Var_in_srange] addDs [srangeD]) 1);
qed "dom_range_disjoint";

goal Subst.thy "!!u. ~ u <| s = u ==> (? x. x : sdom(s))";
by (full_simp_tac (simpset() addsimps [empty_iff_all_not, invariance]) 1);
by (Blast_tac 1);
qed "subst_not_empty";


goal Subst.thy "(M <| [(x, Var x)]) = M";
by (induct_tac "M" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "id_subst_lemma";

Addsimps [id_subst_lemma];
