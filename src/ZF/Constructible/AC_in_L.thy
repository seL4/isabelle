(*  Title:      ZF/Constructible/AC_in_L.thy
    ID: $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

header {* The Axiom of Choice Holds in L! *}

theory AC_in_L = Formula:

subsection{*Extending a Wellordering over a List -- Lexicographic Power*}

text{*This could be moved into a library.*}

consts
  rlist   :: "[i,i]=>i"

inductive
  domains "rlist(A,r)" \<subseteq> "list(A) * list(A)"
  intros
    shorterI:
      "[| length(l') < length(l); l' \<in> list(A); l \<in> list(A) |] 
       ==> <l', l> \<in> rlist(A,r)"

    sameI:
      "[| <l',l> \<in> rlist(A,r); a \<in> A |] 
       ==> <Cons(a,l'), Cons(a,l)> \<in> rlist(A,r)"

    diffI:
      "[| length(l') = length(l); <a',a> \<in> r; 
          l' \<in> list(A); l \<in> list(A); a' \<in> A; a \<in> A |] 
       ==> <Cons(a',l'), Cons(a,l)> \<in> rlist(A,r)"
  type_intros list.intros


subsubsection{*Type checking*}

lemmas rlist_type = rlist.dom_subset

lemmas field_rlist = rlist_type [THEN field_rel_subset]

subsubsection{*Linearity*}

lemma rlist_Nil_Cons [intro]:
    "[|a \<in> A; l \<in> list(A)|] ==> <[], Cons(a,l)> \<in> rlist(A, r)"
by (simp add: shorterI) 

lemma linear_rlist:
    "linear(A,r) ==> linear(list(A),rlist(A,r))"
apply (simp (no_asm_simp) add: linear_def)
apply (rule ballI)  
apply (induct_tac x) 
 apply (rule ballI)  
 apply (induct_tac y)  
  apply (simp_all add: shorterI) 
apply (rule ballI)  
apply (erule_tac a=y in list.cases) 
 apply (rename_tac [2] a2 l2) 
 apply (rule_tac [2] i = "length(l)" and j = "length(l2)" in Ord_linear_lt)
     apply (simp_all add: shorterI) 
apply (erule_tac x=a and y=a2 in linearE) 
    apply (simp_all add: diffI) 
apply (blast intro: sameI) 
done


subsubsection{*Well-foundedness*}

text{*Nothing preceeds Nil in this ordering.*}
inductive_cases rlist_NilE: " <l,[]> \<in> rlist(A,r)"

inductive_cases rlist_ConsE: " <l', Cons(x,l)> \<in> rlist(A,r)"

lemma not_rlist_Nil [simp]: " <l,[]> \<notin> rlist(A,r)"
by (blast intro: elim: rlist_NilE)

lemma rlist_imp_length_le: "<l',l> \<in> rlist(A,r) ==> length(l') \<le> length(l)"
apply (erule rlist.induct)
apply (simp_all add: leI)  
done

lemma wf_on_rlist_n:
  "[| n \<in> nat; wf[A](r) |] ==> wf[{l \<in> list(A). length(l) = n}](rlist(A,r))"
apply (induct_tac n) 
 apply (rule wf_onI2, simp) 
apply (rule wf_onI2, clarify) 
apply (erule_tac a=y in list.cases, clarify) 
 apply (simp (no_asm_use))
apply clarify 
apply (simp (no_asm_use))
apply (subgoal_tac "\<forall>l2 \<in> list(A). length(l2) = x --> Cons(a,l2) \<in> B", blast)
apply (erule_tac a=a in wf_on_induct, assumption)
apply (rule ballI)
apply (rule impI) 
apply (erule_tac a=l2 in wf_on_induct, blast, clarify)
apply (rename_tac a' l2 l') 
apply (drule_tac x="Cons(a',l')" in bspec, typecheck) 
apply simp 
apply (erule mp, clarify) 
apply (erule rlist_ConsE, auto)
done

lemma list_eq_UN_length: "list(A) = (\<Union>n\<in>nat. {l \<in> list(A). length(l) = n})"
by (blast intro: length_type)


lemma wf_on_rlist: "wf[A](r) ==> wf[list(A)](rlist(A,r))"
apply (subst list_eq_UN_length) 
apply (rule wf_on_Union) 
  apply (rule wf_imp_wf_on [OF wf_Memrel [of nat]])
 apply (simp add: wf_on_rlist_n)
apply (frule rlist_type [THEN subsetD]) 
apply (simp add: length_type)   
apply (drule rlist_imp_length_le)
apply (erule leE) 
apply (simp_all add: lt_def) 
done


lemma wf_rlist: "wf(r) ==> wf(rlist(field(r),r))"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A [OF _ field_rlist])
apply (blast intro: wf_on_rlist) 
done

lemma well_ord_rlist:
     "well_ord(A,r) ==> well_ord(list(A), rlist(A,r))"
apply (rule well_ordI)
apply (simp add: well_ord_def wf_on_rlist)
apply (simp add: well_ord_def tot_ord_def linear_rlist)
done


subsection{*An Injection from Formulas into the Natural Numbers*}

text{*There is a well-known bijection between @{term "nat*nat"} and @{term
nat} given by the expression f(m,n) = triangle(m+n) + m, where triangle(k)
enumerates the triangular numbers and can be defined by triangle(0)=0,
triangle(succ(k)) = succ(k + triangle(k)).  Some small amount of effort is
needed to show that f is a bijection.  We already know (by the theorem @{text
InfCard_square_eqpoll}) that such a bijection exists, but as we have no direct
way to refer to it, we must use a locale.*}

text{*Locale for any arbitrary injection between @{term "nat*nat"} 
      and @{term nat}*}
locale Nat_Times_Nat =
  fixes fn
  assumes fn_inj: "fn \<in> inj(nat*nat, nat)"


consts   enum :: "[i,i]=>i"
primrec
  "enum(f, Member(x,y)) = f ` <0, f ` <x,y>>"
  "enum(f, Equal(x,y)) = f ` <1, f ` <x,y>>"
  "enum(f, Nand(p,q)) = f ` <2, f ` <enum(f,p), enum(f,q)>>"
  "enum(f, Forall(p)) = f ` <succ(2), enum(f,p)>"

lemma (in Nat_Times_Nat) fn_type [TC,simp]:
    "[|x \<in> nat; y \<in> nat|] ==> fn`<x,y> \<in> nat"
by (blast intro: inj_is_fun [OF fn_inj] apply_funtype) 

lemma (in Nat_Times_Nat) fn_iff:
    "[|x \<in> nat; y \<in> nat; u \<in> nat; v \<in> nat|] 
     ==> (fn`<x,y> = fn`<u,v>) <-> (x=u & y=v)"
by (blast dest: inj_apply_equality [OF fn_inj]) 

lemma (in Nat_Times_Nat) enum_type [TC,simp]:
    "p \<in> formula ==> enum(fn,p) \<in> nat"
by (induct_tac p, simp_all) 

lemma (in Nat_Times_Nat) enum_inject [rule_format]:
    "p \<in> formula ==> \<forall>q\<in>formula. enum(fn,p) = enum(fn,q) --> p=q"
apply (induct_tac p, simp_all) 
   apply (rule ballI) 
   apply (erule formula.cases) 
   apply (simp_all add: fn_iff) 
  apply (rule ballI) 
  apply (erule formula.cases) 
  apply (simp_all add: fn_iff) 
 apply (rule ballI) 
 apply (erule_tac a=qa in formula.cases) 
 apply (simp_all add: fn_iff) 
 apply blast 
apply (rule ballI) 
apply (erule_tac a=q in formula.cases) 
apply (simp_all add: fn_iff, blast) 
done

lemma (in Nat_Times_Nat) inj_formula_nat:
    "(\<lambda>p \<in> formula. enum(fn,p)) \<in> inj(formula, nat)"
apply (simp add: inj_def lam_type) 
apply (blast intro: enum_inject) 
done

lemma (in Nat_Times_Nat) well_ord_formula:
    "well_ord(formula, measure(formula, enum(fn)))"
apply (rule well_ord_measure, simp)
apply (blast intro: enum_inject)   
done

lemmas nat_times_nat_lepoll_nat =
    InfCard_nat [THEN InfCard_square_eqpoll, THEN eqpoll_imp_lepoll]


text{*Not needed--but interesting?*}
theorem formula_lepoll_nat: "formula \<lesssim> nat"
apply (insert nat_times_nat_lepoll_nat)
apply (unfold lepoll_def)
apply (blast intro: exI Nat_Times_Nat.inj_formula_nat Nat_Times_Nat.intro)
done


subsection{*Limit Construction for Well-Orderings*}

text{*Now we work towards the transfinite definition of wellorderings for
@{term "Lset(i)"}.  We assume as an inductive hypothesis that there is a family
of wellorderings for smaller ordinals.*}

text{*This constant denotes the set of elements introduced at level
@{term "succ(i)"}*}
constdefs
  Lset_new :: "i=>i"
    "Lset_new(i) == {x \<in> Lset(succ(i)). lrank(x) = i}"

lemma Lset_new_iff_lrank_eq:
     "Ord(i) ==> x \<in> Lset_new(i) <-> L(x) & lrank(x) = i"
by (auto simp add: Lset_new_def Lset_iff_lrank_lt) 

lemma Lset_new_eq:
     "Ord(i) ==> Lset_new(i) = Lset(succ(i)) - Lset(i)"
apply (rule equality_iffI)
apply (simp add: Lset_new_iff_lrank_eq Lset_iff_lrank_lt, auto) 
apply (blast elim: leE) 
done

lemma Limit_Lset_eq2:
    "Limit(i) ==> Lset(i) = (\<Union>j\<in>i. Lset_new(j))"
apply (simp add: Limit_Lset_eq) 
apply (rule equalityI)
 apply safe
 apply (subgoal_tac "Ord(y)")
  prefer 2 apply (blast intro: Ord_in_Ord Limit_is_Ord)
 apply (rotate_tac -1) 
 apply (simp_all add: Limit_is_Ord Lset_iff_lrank_lt Lset_new_def 
                      Ord_mem_iff_lt) 
 apply (blast intro: lt_trans) 
apply (rule_tac x = "succ(lrank(x))" in bexI)
 apply (simp add: Lset_succ_lrank_iff) 
apply (blast intro: Limit_has_succ ltD) 
done

text{*This constant expresses the wellordering at limit ordinals.*}
constdefs
  rlimit :: "[i,i=>i]=>i"
    "rlimit(i,r) == 
       {z: Lset(i) * Lset(i).
        \<exists>x' x. z = <x',x> &         
               (lrank(x') < lrank(x) | 
                (lrank(x') = lrank(x) & <x',x> \<in> r(succ(lrank(x)))))}"

lemma rlimit_eqI:
     "[|Limit(i); \<forall>j<i. r'(j) = r(j)|] ==> rlimit(i,r) = rlimit(i,r')"
apply (simp add: rlimit_def) 
apply (rule refl iff_refl Collect_cong ex_cong conj_cong)+
apply (simp add: Limit_is_Ord Lset_lrank_lt)  
done

lemma wf_on_Lset:
    "wf[Lset(succ(j))](r(succ(j))) ==> wf[Lset_new(j)](rlimit(i,r))"
apply (simp add: wf_on_def Lset_new_def) 
apply (erule wf_subset) 
apply (force simp add: rlimit_def) 
done

lemma wf_on_rlimit:
    "[|Limit(i); \<forall>j<i. wf[Lset(j)](r(j)) |] ==> wf[Lset(i)](rlimit(i,r))"
apply (simp add: Limit_Lset_eq2)
apply (rule wf_on_Union)
  apply (rule wf_imp_wf_on [OF wf_Memrel [of i]]) 
 apply (blast intro: wf_on_Lset Limit_has_succ Limit_is_Ord ltI) 
apply (force simp add: rlimit_def Limit_is_Ord Lset_iff_lrank_lt Lset_new_def
                       Ord_mem_iff_lt)

done

lemma linear_rlimit:
    "[|Limit(i); \<forall>j<i. linear(Lset(j), r(j)) |]
     ==> linear(Lset(i), rlimit(i,r))"
apply (frule Limit_is_Ord) 
apply (simp add: Limit_Lset_eq2)
apply (simp add: linear_def Lset_new_def rlimit_def Ball_def) 
apply (simp add: lt_Ord Lset_iff_lrank_lt) 
apply (simp add: ltI, clarify) 
apply (rename_tac u v) 
apply (rule_tac i="lrank(u)" and j="lrank(v)" in Ord_linear_lt) 
apply simp_all
apply (drule_tac x="succ(lrank(u) Un lrank(v))" in ospec) 
apply (simp add: ltI)
apply (drule_tac x=u in spec, simp) 
apply (drule_tac x=v in spec, simp) 
done


lemma well_ord_rlimit:
    "[|Limit(i); \<forall>j<i. well_ord(Lset(j), r(j)) |]
     ==> well_ord(Lset(i), rlimit(i,r))"
by (blast intro: well_ordI wf_on_rlimit well_ord_is_wf 
                           linear_rlimit well_ord_is_linear) 


subsection{*Defining the Wellordering on @{term "Lset(succ(i))"}*}

text{*We introduce wellorderings for environments, which are lists built over
@{term "Lset(succ(i))"}.  We combine it with the enumeration of formulas.  The
order type of the resulting wellordering gives us a map from (environment,
formula) pairs into the ordinals.  For each member of @{term "DPow(Lset(i))"},
we take the minimum such ordinal.  This yields a wellordering of
@{term "DPow(Lset(i))"}, which we then extend to @{term "Lset(succ(i))"}*}

constdefs
  env_form_r :: "[i,i,i]=>i"
    --{*wellordering on (environment, formula) pairs*}
   "env_form_r(f,r,i) ==
      rmult(list(Lset(i)), rlist(Lset(i), r),
	    formula, measure(formula, enum(f)))"

  env_form_map :: "[i,i,i,i]=>i"
    --{*map from (environment, formula) pairs to ordinals*}
   "env_form_map(f,r,i,z) 
      == ordermap(list(Lset(i)) * formula, env_form_r(f,r,i)) ` z"

  L_new_ord :: "[i,i,i,i,i]=>o"
    --{*predicate that holds if @{term k} is a valid index for @{term X}*}
   "L_new_ord(f,r,i,X,k) ==  
           \<exists>env \<in> list(Lset(i)). \<exists>p \<in> formula. 
             arity(p) \<le> succ(length(env)) & 
             X = {x\<in>Lset(i). sats(Lset(i), p, Cons(x,env))} &
             env_form_map(f,r,i,<env,p>) = k"

  L_new_least :: "[i,i,i,i]=>i"
    --{*function yielding the smallest index for @{term X}*}
   "L_new_least(f,r,i,X) == \<mu>k. L_new_ord(f,r,i,X,k)"

  L_new_r :: "[i,i,i]=>i"
    --{*a wellordering on @{term "DPow(Lset(i))"}*}
   "L_new_r(f,r,i) == measure(Lset_new(i), L_new_least(f,r,i))"

  L_succ_r :: "[i,i,i]=>i"
    --{*a wellordering on @{term "Lset(succ(i))"}*}
   "L_succ_r(f,r,i) == (L_new_r(f,r,i) Un (Lset(i) * Lset_new(i))) Un r"


lemma (in Nat_Times_Nat) well_ord_env_form_r:
    "well_ord(Lset(i), r) 
     ==> well_ord(list(Lset(i)) * formula, env_form_r(fn,r,i))"
by (simp add: env_form_r_def well_ord_rmult well_ord_rlist well_ord_formula) 

lemma (in Nat_Times_Nat) Ord_env_form_map:
    "[|well_ord(Lset(i), r); z \<in> list(Lset(i)) * formula|]
     ==> Ord(env_form_map(fn,r,i,z))"
by (simp add: env_form_map_def Ord_ordermap well_ord_env_form_r) 


lemma DPow_imp_ex_L_new_ord:
    "X \<in> DPow(Lset(i)) ==> \<exists>k. L_new_ord(fn,r,i,X,k)"
apply (simp add: L_new_ord_def) 
apply (blast dest!: DPowD) 
done

lemma (in Nat_Times_Nat) L_new_ord_imp_Ord:
     "[|L_new_ord(fn,r,i,X,k); well_ord(Lset(i), r)|] ==> Ord(k)"
apply (simp add: L_new_ord_def, clarify)
apply (simp add: Ord_env_form_map)  
done

lemma (in Nat_Times_Nat) DPow_imp_L_new_least:
    "[|X \<in> DPow(Lset(i)); well_ord(Lset(i), r)|] 
     ==> L_new_ord(fn, r, i, X, L_new_least(fn,r,i,X))"
apply (simp add: L_new_least_def)
apply (blast dest!: DPow_imp_ex_L_new_ord intro: L_new_ord_imp_Ord LeastI)  
done

lemma (in Nat_Times_Nat) env_form_map_inject:
    "[|env_form_map(fn,r,i,u) = env_form_map(fn,r,i,v); well_ord(Lset(i), r);  
       u \<in> list(Lset(i)) * formula;  v \<in> list(Lset(i)) * formula|] 
     ==> u=v"
apply (simp add: env_form_map_def) 
apply (rule inj_apply_equality [OF bij_is_inj, OF ordermap_bij, 
                                OF well_ord_env_form_r], assumption+)
done


lemma (in Nat_Times_Nat) L_new_ord_unique:
    "[|L_new_ord(fn,r,i,X,k); L_new_ord(fn,r,i,Y,k); well_ord(Lset(i), r)|] 
     ==> X=Y"
apply (simp add: L_new_ord_def, clarify)
apply (drule env_form_map_inject, auto) 
done

lemma (in Nat_Times_Nat) well_ord_L_new_r:
    "[|Ord(i); well_ord(Lset(i), r)|]
     ==> well_ord(Lset_new(i), L_new_r(fn,r,i))"
apply (simp add: L_new_r_def) 
apply (rule well_ord_measure) 
 apply (simp add: L_new_least_def Ord_Least)
apply (simp add: Lset_new_eq Lset_succ, clarify) 
apply (drule DPow_imp_L_new_least, assumption)+
apply simp 
apply (blast intro: L_new_ord_unique) 
done

lemma L_new_r_subset: "L_new_r(f,r,i) <= Lset_new(i) * Lset_new(i)"
by (simp add: L_new_r_def measure_type)

lemma Lset_Lset_new_disjoint: "Ord(i) ==> Lset(i) \<inter> Lset_new(i) = 0"
by (simp add: Lset_new_eq, blast)

lemma (in Nat_Times_Nat) linear_L_succ_r:
    "[|Ord(i); well_ord(Lset(i), r)|]
     ==> linear(Lset(succ(i)), L_succ_r(fn, r, i))"
apply (frule well_ord_L_new_r, assumption) 
apply (drule well_ord_is_linear)+
apply (simp add: linear_def L_succ_r_def Lset_new_eq, auto) 
done


lemma (in Nat_Times_Nat) wf_L_new_r:
    "[|Ord(i); well_ord(Lset(i), r)|] ==> wf(L_new_r(fn,r,i))"
apply (rule well_ord_L_new_r [THEN well_ord_is_wf, THEN wf_on_imp_wf], 
       assumption+)
apply (rule L_new_r_subset)
done


lemma (in Nat_Times_Nat) well_ord_L_new_r:
    "[|Ord(i); well_ord(Lset(i), r); r \<subseteq> Lset(i) * Lset(i)|]
     ==> well_ord(Lset(succ(i)), L_succ_r(fn,r,i))"
apply (rule well_ordI [OF wf_imp_wf_on])
 prefer 2 apply (blast intro: linear_L_succ_r) 
apply (simp add: L_succ_r_def)
apply (rule wf_Un)
  apply (cut_tac L_new_r_subset [of fn r i], simp add: Lset_new_eq, blast)
 apply (rule wf_Un)  
   apply (cut_tac L_new_r_subset [of fn r i], simp add: Lset_new_eq, blast)
  apply (blast intro: wf_L_new_r) 
 apply (simp add: wf_times Lset_Lset_new_disjoint)
apply (blast intro: well_ord_is_wf wf_on_imp_wf)
done


lemma (in Nat_Times_Nat) L_succ_r_type:
    "[|Ord(i); r \<subseteq> Lset(i) * Lset(i)|]
     ==> L_succ_r(fn,r,i) \<subseteq> Lset(succ(i)) * Lset(succ(i))"
apply (simp add: L_succ_r_def L_new_r_def measure_def Lset_new_eq) 
apply (blast intro: Lset_mono_mem [OF succI1, THEN subsetD] ) 
done				   


subsection{*Transfinite Definition of the Wellordering on @{term "L"}*}

constdefs
 L_r :: "[i, i] => i"
  "L_r(f,i) == 
      transrec(i, \<lambda>x r. 
         if x=0 then 0
         else if Limit(x) then rlimit(x, \<lambda>y. r`y)
         else L_succ_r(f, r ` Arith.pred(x), Arith.pred(x)))"

subsubsection{*The Corresponding Recursion Equations*}
lemma [simp]: "L_r(f,0) = 0"
by (simp add: def_transrec [OF L_r_def])

lemma [simp]: "Ord(i) ==> L_r(f, succ(i)) = L_succ_r(f, L_r(f,i), i)"
by (simp add: def_transrec [OF L_r_def])

text{*Needed to handle the limit case*}
lemma L_r_eq:
     "Ord(i) ==> 
      L_r(f, i) =
      (if i = 0 then 0
       else if Limit(i) then rlimit(i, op `(Lambda(i, L_r(f))))
       else L_succ_r (f, Lambda(i, L_r(f)) ` Arith.pred(i), Arith.pred(i)))"
apply (induct i rule: trans_induct3_rule)
apply (simp_all add: def_transrec [OF L_r_def])
done

text{*I don't know why the limit case is so complicated.*}
lemma [simp]: "Limit(i) ==> L_r(f,i) = rlimit(i, L_r(f))"
apply (simp add: Limit_nonzero def_transrec [OF L_r_def])
apply (rule rlimit_eqI, assumption)
apply (rule oallI)
apply (frule lt_Ord) 
apply (simp only: beta ltD L_r_eq [symmetric])  
done

lemma (in Nat_Times_Nat) L_r_type:
    "Ord(i) ==> L_r(fn,i) \<subseteq> Lset(i) * Lset(i)"
apply (induct i rule: trans_induct3_rule)
  apply (simp_all add: L_succ_r_type well_ord_L_new_r rlimit_def, blast) 
done

lemma (in Nat_Times_Nat) well_ord_L_r:
    "Ord(i) ==> well_ord(Lset(i), L_r(fn,i))"
apply (induct i rule: trans_induct3_rule)
apply (simp_all add: well_ord0 L_r_type well_ord_L_new_r well_ord_rlimit ltD)
done

lemma well_ord_L_r:
    "Ord(i) ==> \<exists>r. well_ord(Lset(i), r)"
apply (insert nat_times_nat_lepoll_nat)
apply (unfold lepoll_def)
apply (blast intro: exI Nat_Times_Nat.well_ord_L_r Nat_Times_Nat.intro)
done


text{*Locale for proving results under the assumption @{text "V=L"}*}
locale V_equals_L =
  assumes VL: "L(x)"

text{*The Axiom of Choice holds in @{term L}!  Or, to be precise, the
Wellordering Theorem.*}
theorem (in V_equals_L) AC: "\<exists>r. well_ord(x,r)"
apply (insert Transset_Lset VL [of x]) 
apply (simp add: Transset_def L_def)
apply (blast dest!: well_ord_L_r intro: well_ord_subset) 
done

end
