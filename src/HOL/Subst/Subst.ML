(*  Title: 	Substitutions/subst.ML
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For subst.thy.  
*)

open Subst;

(***********)

val subst_defs = [subst_def,comp_def,sdom_def];

val raw_subst_ss = utlemmas_ss addsimps al_rews;

local fun mk_thm s = prove_goalw Subst.thy subst_defs s 
                                 (fn _ => [simp_tac raw_subst_ss 1])
in val subst_rews = map mk_thm 
["Const(c) <| al = Const(c)",
 "Comb t u <| al = Comb (t <| al) (u <| al)",
 "[] <> bl = bl",
 "((a,b)#al) <> bl = (a,b <| bl) # (al <> bl)",
 "sdom([]) = {}",
 "sdom((a,b)#al) = (if Var(a)=b then (sdom al) Int Compl({a}) \
\                               else (sdom al) Un {a})"
];
   (* This rewrite isn't always desired *)
   val Var_subst = mk_thm "Var(x) <| al = assoc x (Var x) al";
end;

val subst_ss = raw_subst_ss addsimps subst_rews;

(**** Substitutions ****)

goal Subst.thy "t <| [] = t";
by (uterm_ind_tac "t" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [Var_subst])));
qed "subst_Nil";

goal Subst.thy "t <: u --> t <| s <: u <| s";
by (uterm_ind_tac "u" 1);
by (ALLGOALS (asm_simp_tac subst_ss));
val subst_mono  = store_thm("subst_mono", result() RS mp);

goal Subst.thy  "~ (Var(v) <: t) --> t <| (v,t <| s)#s = t <| s";
by (imp_excluded_middle_tac "t = Var(v)" 1);
by (res_inst_tac [("P",
    "%x.~x=Var(v) --> ~(Var(v) <: x) --> x <| (v,t<|s)#s=x<|s")]
    uterm_induct 2);
by (ALLGOALS (simp_tac (subst_ss addsimps [Var_subst])));
by (fast_tac HOL_cs 1);
val Var_not_occs  = store_thm("Var_not_occs", result() RS mp);

goal Subst.thy
    "(t <|r = t <|s) = (! v.v : vars_of(t) --> Var(v) <|r = Var(v) <|s)";
by (uterm_ind_tac "t" 1);
by (REPEAT (etac rev_mp 3));
by (ALLGOALS (asm_simp_tac subst_ss));
by (ALLGOALS (fast_tac HOL_cs));
qed "agreement";

goal Subst.thy   "~ v: vars_of(t) --> t <| (v,u)#s = t <| s";
by(simp_tac(subst_ss addsimps [agreement,Var_subst]
                     setloop (split_tac [expand_if])) 1);
val repl_invariance  = store_thm("repl_invariance", result() RS mp);

val asms = goal Subst.thy 
     "v : vars_of(t) --> w : vars_of(t <| (v,Var(w))#s)";
by (uterm_ind_tac "t" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [Var_subst])));
val Var_in_subst  = store_thm("Var_in_subst", result() RS mp);

(**** Equality between Substitutions ****)

goalw Subst.thy [subst_eq_def] "r =s= s = (! t.t <| r = t <| s)";
by (simp_tac subst_ss 1);
qed "subst_eq_iff";

local fun mk_thm s = prove_goal Subst.thy s
                  (fn prems => [cut_facts_tac prems 1,
                                REPEAT (etac rev_mp 1),
                                simp_tac (subst_ss addsimps [subst_eq_iff]) 1])
in 
  val subst_refl      = mk_thm "r = s ==> r =s= s";
  val subst_sym       = mk_thm "r =s= s ==> s =s= r";
  val subst_trans     = mk_thm "[| q =s= r; r =s= s |] ==> q =s= s";
end;

val eq::prems = goalw Subst.thy [subst_eq_def] 
    "[| r =s= s; P (t <| r) (u <| r) |] ==> P (t <| s) (u <| s)";
by (resolve_tac [eq RS spec RS subst] 1);
by (resolve_tac (prems RL [eq RS spec RS subst]) 1);
qed "subst_subst2";

val ssubst_subst2 = subst_sym RS subst_subst2;

(**** Composition of Substitutions ****)

goal Subst.thy "s <> [] = s";
by (alist_ind_tac "s" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [subst_Nil])));
qed "comp_Nil";

goal Subst.thy "(t <| r <> s) = (t <| r <| s)";
by (uterm_ind_tac "t" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [Var_subst])));
by (alist_ind_tac "r" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [Var_subst,subst_Nil]
                                     setloop (split_tac [expand_if]))));
qed "subst_comp";

goal Subst.thy "(q <> r) <> s =s= q <> (r <> s)";
by (simp_tac (subst_ss addsimps [subst_eq_iff,subst_comp]) 1);
qed "comp_assoc";

goal Subst.thy "(w,Var(w) <| s)#s =s= s"; 
by (rtac (allI RS (subst_eq_iff RS iffD2)) 1);
by (uterm_ind_tac "t" 1);
by (REPEAT (etac rev_mp 3));
by (ALLGOALS (simp_tac (subst_ss addsimps[Var_subst]
                                 setloop (split_tac [expand_if]))));
qed "Cons_trivial";

val [prem] = goal Subst.thy "q <> r =s= s ==>  t <| q <| r = t <| s";
by (simp_tac (subst_ss addsimps [prem RS (subst_eq_iff RS iffD1),
				subst_comp RS sym]) 1);
qed "comp_subst_subst";

(****  Domain and range of Substitutions ****)

goal Subst.thy  "(v : sdom(s)) = (~ Var(v) <| s = Var(v))";
by (alist_ind_tac "s" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [Var_subst]
                            setloop (split_tac[expand_if]))));
by (fast_tac HOL_cs 1);
qed "sdom_iff";

goalw Subst.thy [srange_def]  
   "v : srange(s) = (? w.w : sdom(s) & v : vars_of(Var(w) <| s))";
by (fast_tac set_cs 1);
qed "srange_iff";

goal Subst.thy  "(t <| s = t) = (sdom(s) Int vars_of(t) = {})";
by (uterm_ind_tac "t" 1);
by (REPEAT (etac rev_mp 3));
by (ALLGOALS (simp_tac (subst_ss addsimps [sdom_iff,Var_subst])));
by (ALLGOALS (fast_tac set_cs));
qed "invariance";

goal Subst.thy  "v : sdom(s) -->  ~v : srange(s) --> ~v : vars_of(t <| s)";
by (uterm_ind_tac "t" 1);
by (imp_excluded_middle_tac "x : sdom(s)" 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps [sdom_iff,srange_iff])));
by (ALLGOALS (fast_tac set_cs));
val Var_elim  = store_thm("Var_elim", result() RS mp RS mp);

val asms = goal Subst.thy 
     "[| v : sdom(s); v : vars_of(t <| s) |] ==>  v : srange(s)";
by (REPEAT (ares_tac (asms @ [Var_elim RS swap RS classical]) 1));
qed "Var_elim2";

goal Subst.thy  "v : vars_of(t <| s) --> v : srange(s) | v : vars_of(t)";
by (uterm_ind_tac "t" 1);
by (REPEAT_SOME (etac rev_mp ));
by (ALLGOALS (simp_tac (subst_ss addsimps [sdom_iff,srange_iff])));
by (REPEAT (step_tac (set_cs addIs [vars_var_iff RS iffD1 RS sym]) 1));
by (etac notE 1);
by (etac subst 1);
by (ALLGOALS (fast_tac set_cs));
val Var_intro  = store_thm("Var_intro", result() RS mp);

goal Subst.thy
    "v : srange(s) --> (? w.w : sdom(s) & v : vars_of(Var(w) <| s))";
by (simp_tac (subst_ss addsimps [srange_iff]) 1);
val srangeE  = store_thm("srangeE", make_elim (result() RS mp));

val asms = goal Subst.thy
   "sdom(s) Int srange(s) = {} = (! t.sdom(s) Int vars_of(t <| s) = {})";
by (simp_tac subst_ss 1);
by (fast_tac (set_cs addIs [Var_elim2] addEs [srangeE]) 1);
qed "dom_range_disjoint";

val asms = goal Subst.thy "~ u <| s = u --> (? x.x : sdom(s))";
by (simp_tac (subst_ss addsimps [invariance]) 1);
by (fast_tac set_cs 1);
val subst_not_empty  = store_thm("subst_not_empty", result() RS mp);
