(*  Title:      HOL/UNITY/GenPrefix.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Charpentier's Generalized Prefix Relation
   (xs,ys) : genPrefix r
     if ys = xs' @ zs where length xs = length xs'
     and corresponding elements of xs, xs' are pairwise related by r

Based on Lex/Prefix
*)

(*** preliminary lemmas ***)

Goal "([], xs) : genPrefix r";
by (cut_facts_tac [genPrefix.Nil RS genPrefix.append] 1);
by Auto_tac;
qed "Nil_genPrefix";
AddIffs[Nil_genPrefix];

Goal "(xs,ys) : genPrefix r ==> length xs <= length ys";
by (etac genPrefix.induct 1);
by Auto_tac;
qed "genPrefix_length_le";

Goal "[| (xs', ys'): genPrefix r |] \
\     ==> (ALL x xs. xs' = x#xs --> (EX y ys. ys' = y#ys & (x,y) : r & (xs, ys) : genPrefix r))";
by (etac genPrefix.induct 1);
by (Blast_tac 1);
by (Blast_tac 1);
by (force_tac (claset() addIs [genPrefix.append],
	       simpset()) 1);
val lemma = result();

(*As usual converting it to an elimination rule is tiresome*)
val major::prems = 
Goal "[| (x#xs, zs): genPrefix r;  \
\        !!y ys. [| zs = y#ys;  (x,y) : r;  (xs, ys) : genPrefix r |] ==> P \
\     |] ==> P";
by (cut_facts_tac [major RS lemma] 1);
by (Full_simp_tac 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (REPEAT (ares_tac prems 1));
qed "cons_genPrefixE";

AddSEs [cons_genPrefixE];

Goal "((x#xs,y#ys) : genPrefix r) = ((x,y) : r & (xs,ys) : genPrefix r)";
by (blast_tac (claset() addIs [genPrefix.prepend]) 1);
qed"Cons_genPrefix_Cons";
AddIffs [Cons_genPrefix_Cons];


(*** genPrefix is a partial order ***)

Goalw [refl_def] "reflexive r ==> reflexive (genPrefix r)";
by Auto_tac;
by (induct_tac "x" 1);
by (blast_tac (claset() addIs [genPrefix.prepend]) 2);
by (blast_tac (claset() addIs [genPrefix.Nil]) 1);
qed "refl_genPrefix";

Goal "reflexive r ==> (l,l) : genPrefix r";
by (etac ([refl_genPrefix,UNIV_I] MRS reflD) 1);
qed "genPrefix_refl";

Addsimps [genPrefix_refl];


(** Transitivity **)

(*Merely a lemma for proving transitivity*)
Goal "ALL zs. (xs @ ys, zs) : genPrefix r --> (xs, zs) : genPrefix r";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "append_genPrefix";

Goalw [trans_def]
     "[| (x, y) : genPrefix r; trans r |] \
\     ==> ALL z. (y, z) : genPrefix r --> (x, z) : genPrefix r";
by (etac genPrefix.induct 1);
by (blast_tac (claset() addDs [append_genPrefix]) 3);
by (blast_tac (claset() addIs [genPrefix.prepend]) 2);
by (Blast_tac 1);
qed_spec_mp "genPrefix_trans";

Goal "trans r ==> trans (genPrefix r)";
by (blast_tac (claset() addIs [transI, genPrefix_trans]) 1);
qed "trans_genPrefix";


(** Antisymmetry **)

Goal "[| (xs,ys) : genPrefix r;  antisym r |] \
\     ==> (ys,xs) : genPrefix r --> xs = ys";
by (etac genPrefix.induct 1);
by (full_simp_tac (simpset() addsimps [antisym_def]) 2);
by (Blast_tac 2);
by (Blast_tac 1);
(*append case is hardest*)
by (Clarify_tac 1);
by (subgoal_tac "length zs = 0" 1);
by (Force_tac 1);
by (REPEAT (dtac genPrefix_length_le 1));
by (full_simp_tac (simpset() delsimps [length_0_conv]) 1);
qed_spec_mp "genPrefix_antisym";

Goal "antisym r ==> antisym (genPrefix r)";
by (blast_tac (claset() addIs [antisymI, genPrefix_antisym]) 1);
qed "antisym_genPrefix";


(*** recursion equations ***)

Goal "((xs, []) : genPrefix r) = (xs = [])";
by (induct_tac "xs" 1);
by (Blast_tac 2);
by (Simp_tac 1);
qed "genPrefix_Nil";
Addsimps [genPrefix_Nil];

Goalw [refl_def]
    "reflexive r ==> ((xs@ys, xs@zs) : genPrefix r) = ((ys,zs) : genPrefix r)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "same_genPrefix_genPrefix";
Addsimps [same_genPrefix_genPrefix];

Goal "((xs, y#ys) : genPrefix r) = \
\     (xs=[] | (EX z zs. xs=z#zs & (z,y) : r & (zs,ys) : genPrefix r))";
by (exhaust_tac "xs" 1);
by Auto_tac;
qed "genPrefix_Cons";

Goal "[| reflexive r;  (xs,ys) : genPrefix r |] \
\     ==>  (xs@zs, take (length xs) ys @ zs) : genPrefix r";
by (etac genPrefix.induct 1);
by (forward_tac [genPrefix_length_le] 3);
by (ALLGOALS Asm_simp_tac);
qed "genPrefix_take_append";

Goal "[| reflexive r;  (xs,ys) : genPrefix r;  length xs = length ys |] \
\     ==>  (xs@zs, ys @ zs) : genPrefix r";
by (dtac genPrefix_take_append 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [take_all]) 1);
qed "genPrefix_append_both";


(*NOT suitable for rewriting since [y] has the form y#ys*)
Goal "xs @ y # ys = (xs @ [y]) @ ys";
by Auto_tac;
qed "append_cons_eq";

Goal "[| (xs,ys) : genPrefix r;  reflexive r |] \
\     ==> length xs < length ys --> (xs @ [ys ! length xs], ys) : genPrefix r";
by (etac genPrefix.induct 1);
by (Blast_tac 1);
by (Asm_simp_tac 1);
(*Append case is hardest*)
by (Asm_simp_tac 1);
by (forward_tac [genPrefix_length_le RS le_imp_less_or_eq] 1);
by (etac disjE 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [neq_Nil_conv, nth_append])));
by (blast_tac (claset() addIs [genPrefix.append]) 1);
by Auto_tac;
by (stac append_cons_eq 1);
by (blast_tac (claset() addIs [genPrefix_append_both, genPrefix.append]) 1);
val lemma = result() RS mp;

Goal "[| (xs,ys) : genPrefix r;  length xs < length ys;  reflexive r |] \
\     ==> (xs @ [ys ! length xs], ys) : genPrefix r";
by (blast_tac (claset() addIs [lemma]) 1);
qed "append_one_genPrefix";




(** Proving the equivalence with Charpentier's definition **)

Goal "ALL i ys. i < length xs \
\               --> (xs, ys) : genPrefix r --> (xs ! i, ys ! i) : r";
by (induct_tac "xs" 1);
by Auto_tac;
by (exhaust_tac "i" 1);
by Auto_tac;
qed_spec_mp "genPrefix_imp_nth";

Goal "ALL ys. length xs <= length ys  \
\     --> (ALL i. i < length xs --> (xs ! i, ys ! i) : r)  \
\     --> (xs, ys) : genPrefix r";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [less_Suc_eq_0_disj, 
						all_conj_distrib])));
by (Clarify_tac 1);
by (exhaust_tac "ys" 1);
by (ALLGOALS Force_tac);
qed_spec_mp "nth_imp_genPrefix";

Goal "((xs,ys) : genPrefix r) = \
\     (length xs <= length ys & (ALL i. i < length xs --> (xs!i, ys!i) : r))";
by (blast_tac (claset() addIs [genPrefix_length_le, genPrefix_imp_nth,
			       nth_imp_genPrefix]) 1);
qed "genPrefix_iff_nth";


(** <= is a partial order: **)

AddIffs [reflexive_Id, antisym_Id, trans_Id];

Goalw [prefix_def] "xs <= (xs::'a list)";
by (Simp_tac 1);
qed "prefix_refl";
AddIffs[prefix_refl];

Goalw [prefix_def] "!!xs::'a list. [| xs <= ys; ys <= zs |] ==> xs <= zs";
by (blast_tac (claset() addIs [genPrefix_trans]) 1);
qed "prefix_trans";

Goalw [prefix_def] "!!xs::'a list. [| xs <= ys; ys <= xs |] ==> xs = ys";
by (blast_tac (claset() addIs [genPrefix_antisym]) 1);
qed "prefix_antisym";

Goalw [strict_prefix_def] "!!xs::'a list. (xs < zs) = (xs <= zs & xs ~= zs)";
by Auto_tac;
qed "prefix_less_le";


(** recursion equations **)

Goalw [prefix_def] "[] <= xs";
by (simp_tac (simpset() addsimps [Nil_genPrefix]) 1);
qed "Nil_prefix";
AddIffs[Nil_prefix];

Goalw [prefix_def] "(xs <= []) = (xs = [])";
by (simp_tac (simpset() addsimps [genPrefix_Nil]) 1);
qed "prefix_Nil";
Addsimps [prefix_Nil];

Goalw [prefix_def] "(x#xs <= y#ys) = (x=y & xs<=ys)";
by (Simp_tac 1);
qed"Cons_prefix_Cons";
Addsimps [Cons_prefix_Cons];

Goalw [prefix_def] "(xs@ys <= xs@zs) = (ys <= zs)";
by (Simp_tac 1);
qed "same_prefix_prefix";
Addsimps [same_prefix_prefix];

AddIffs   (* (xs@ys <= xs) = (ys <= []) *)
 [simplify (simpset()) (read_instantiate [("zs","[]")] same_prefix_prefix)];

Goalw [prefix_def] "xs <= ys ==> xs <= ys@zs";
by (etac genPrefix.append 1);
qed "prefix_appendI";
Addsimps [prefix_appendI];

Goalw [prefix_def]
   "(xs <= y#ys) = (xs=[] | (? zs. xs=y#zs & zs <= ys))";
by (simp_tac (simpset() addsimps [genPrefix_Cons]) 1);
by Auto_tac;
qed "prefix_Cons";

Goalw [prefix_def]
  "[| xs <= ys; length xs < length ys |] ==> xs @ [ys ! length xs] <= ys";
by (asm_simp_tac (simpset() addsimps [append_one_genPrefix]) 1);
qed "append_one_prefix";

Goalw [prefix_def] "xs <= ys ==> length xs <= length ys";
by (etac genPrefix_length_le 1);
qed "prefix_length_le";

Goal "mono length";
by (blast_tac (claset() addIs [monoI, prefix_length_le]) 1);
qed "mono_length";

(*Equivalence to the definition used in Lex/Prefix.thy*)
Goalw [prefix_def] "(xs <= zs) = (EX ys. zs = xs@ys)";
by (auto_tac (claset(),
	      simpset() addsimps [genPrefix_iff_nth, nth_append]));
by (res_inst_tac [("x", "drop (length xs) zs")] exI 1);
br nth_equalityI 1;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [nth_append])));
qed "prefix_iff";

Goal "(xs <= ys@[y]) = (xs = ys@[y] | xs <= ys)";
by (simp_tac (simpset() addsimps [prefix_iff]) 1);
by (rtac iffI 1);
 by (etac exE 1);
 by (rename_tac "zs" 1);
 by (res_inst_tac [("xs","zs")] rev_exhaust 1);
  by (Asm_full_simp_tac 1);
 by (hyp_subst_tac 1);
 by (asm_full_simp_tac (simpset() delsimps [append_assoc]
                                  addsimps [append_assoc RS sym])1);
by (Force_tac 1);
qed "prefix_snoc";
Addsimps [prefix_snoc];

Goal "(xs <= ys@zs) = (xs <= ys | (? us. xs = ys@us & us <= zs))";
by (res_inst_tac [("xs","zs")] rev_induct 1);
 by (Force_tac 1);
by (asm_full_simp_tac (simpset() delsimps [append_assoc]
                                 addsimps [append_assoc RS sym])1);
by (Force_tac 1);
qed "prefix_append_iff";


(*** pfix_le: partial ordering, etc. ***)

Goalw [refl_def, Le_def] "reflexive Le";
auto();
qed "reflexive_Le";

Goalw [antisym_def, Le_def] "antisym Le";
auto();
qed "antisym_Le";

Goalw [trans_def, Le_def] "trans Le";
auto();
qed "trans_Le";

AddIffs [reflexive_Le, antisym_Le, trans_Le];

Goal "xs pfix_le xs";
by (Simp_tac 1);
qed "pfix_le_refl";
AddIffs[pfix_le_refl];

Goal "[| xs pfix_le ys; ys pfix_le zs |] ==> xs pfix_le zs";
by (blast_tac (claset() addIs [genPrefix_trans]) 1);
qed "pfix_le_trans";

Goal "[| xs pfix_le ys; ys pfix_le xs |] ==> xs = ys";
by (blast_tac (claset() addIs [genPrefix_antisym]) 1);
qed "pfix_le_antisym";

Goal "(xs@ys pfix_le xs@zs) = (ys pfix_le zs)";
by (Simp_tac 1);
qed "same_pfix_le_pfix_le";
Addsimps [same_pfix_le_pfix_le];

Goal "[| xs pfix_le ys; length xs < length ys |] \
\     ==> xs @ [ys ! length xs] pfix_le ys";
by (asm_simp_tac (simpset() addsimps [append_one_genPrefix]) 1);
qed "append_one_pfix_le";


(*** pfix_ge: partial ordering, etc. ***)

Goalw [refl_def, Ge_def] "reflexive Ge";
auto();
qed "reflexive_Ge";

Goalw [antisym_def, Ge_def] "antisym Ge";
auto();
qed "antisym_Ge";

Goalw [trans_def, Ge_def] "trans Ge";
auto();
qed "trans_Ge";

AddIffs [reflexive_Ge, antisym_Ge, trans_Ge];

Goal "xs pfix_ge xs";
by (Simp_tac 1);
qed "pfix_ge_refl";
AddIffs[pfix_ge_refl];

Goal "[| xs pfix_ge ys; ys pfix_ge zs |] ==> xs pfix_ge zs";
by (blast_tac (claset() addIs [genPrefix_trans]) 1);
qed "pfix_ge_trans";

Goal "[| xs pfix_ge ys; ys pfix_ge xs |] ==> xs = ys";
by (blast_tac (claset() addIs [genPrefix_antisym]) 1);
qed "pfix_ge_antisym";

Goal "(xs@ys pfix_ge xs@zs) = (ys pfix_ge zs)";
by (Simp_tac 1);
qed "same_pfix_ge_pfix_ge";
Addsimps [same_pfix_ge_pfix_ge];

Goal "[| xs pfix_ge ys; length xs < length ys |] \
\     ==> xs @ [ys ! length xs] pfix_ge ys";
by (asm_simp_tac (simpset() addsimps [append_one_genPrefix]) 1);
qed "append_one_pfix_ge";
