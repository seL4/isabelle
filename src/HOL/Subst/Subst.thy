(*  Title:      Subst/Subst.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header{*Substitutions on uterms*}

theory Subst
imports AList UTerm
begin

consts

  "=$="  ::  "[('a*('a uterm)) list,('a*('a uterm)) list] => bool" (infixr 52)
  "<|"   ::  "'a uterm => ('a * 'a uterm) list => 'a uterm"        (infixl 55)
  "<>"   ::  "[('a*('a uterm)) list, ('a*('a uterm)) list] 
                 => ('a*('a uterm)) list"                          (infixl 56)
  sdom   ::  "('a*('a uterm)) list => 'a set"
  srange ::  "('a*('a uterm)) list => 'a set"


syntax (xsymbols)
  "op =$=" :: "[('a*('a uterm)) list,('a*('a uterm)) list] => bool" 
              (infixr "\<doteq>" 52)
  "op <|" :: "'a uterm => ('a * 'a uterm) list => 'a uterm" (infixl "\<lhd>" 55)
  "op <>" :: "[('a*('a uterm)) list, ('a*('a uterm)) list] 
                 => ('a*('a uterm)) list"                   (infixl "\<lozenge>" 56)


primrec
  subst_Var:      "(Var v \<lhd> s) = assoc v (Var v) s"
  subst_Const:  "(Const c \<lhd> s) = Const c"
  subst_Comb:  "(Comb M N \<lhd> s) = Comb (M \<lhd> s) (N \<lhd> s)"


defs 

  subst_eq_def:  "r =$= s == ALL t. t \<lhd> r = t \<lhd> s"

  comp_def:    "al \<lozenge> bl == alist_rec al bl (%x y xs g. (x,y \<lhd> bl)#g)"

  sdom_def:
  "sdom(al) == alist_rec al {}  
                (%x y xs g. if Var(x)=y then g - {x} else g Un {x})"

  srange_def:
   "srange(al) == Union({y. \<exists>x \<in> sdom(al). y = vars_of(Var(x) \<lhd> al)})"



subsection{*Basic Laws*}

lemma subst_Nil [simp]: "t \<lhd> [] = t"
by (induct_tac "t", auto)

lemma subst_mono [rule_format]: "t \<prec> u --> t \<lhd> s \<prec> u \<lhd> s"
by (induct_tac "u", auto)

lemma Var_not_occs [rule_format]:
     "~ (Var(v) \<prec> t) --> t \<lhd> (v,t \<lhd> s) # s = t \<lhd> s"
apply (case_tac "t = Var v")
apply (erule_tac [2] rev_mp)
apply (rule_tac [2] P = 
         "%x. x \<noteq> Var v --> ~(Var v \<prec> x) --> x \<lhd> (v,t\<lhd>s) #s = x\<lhd>s" 
       in uterm.induct)
apply auto 
done

lemma agreement: "(t\<lhd>r = t\<lhd>s) = (\<forall>v \<in> vars_of t. Var v \<lhd> r = Var v \<lhd> s)"
by (induct_tac "t", auto)

lemma repl_invariance: "~ v: vars_of(t) ==> t \<lhd> (v,u)#s = t \<lhd> s"
by (simp add: agreement)

lemma Var_in_subst [rule_format]:
     "v \<in> vars_of(t) --> w \<in> vars_of(t \<lhd> (v,Var(w))#s)"
by (induct_tac "t", auto)


subsection{*Equality between Substitutions*}

lemma subst_eq_iff: "r \<doteq> s = (\<forall>t. t \<lhd> r = t \<lhd> s)"
by (simp add: subst_eq_def)

lemma subst_refl [iff]: "r \<doteq> r"
by (simp add: subst_eq_iff)

lemma subst_sym: "r \<doteq> s ==> s \<doteq> r"
by (simp add: subst_eq_iff)

lemma subst_trans: "[| q \<doteq> r; r \<doteq> s |] ==> q \<doteq> s"
by (simp add: subst_eq_iff)

lemma subst_subst2:
    "[| r \<doteq> s; P (t \<lhd> r) (u \<lhd> r) |] ==> P (t \<lhd> s) (u \<lhd> s)"
by (simp add: subst_eq_def)

lemmas ssubst_subst2 = subst_sym [THEN subst_subst2]


subsection{*Composition of Substitutions*}

lemma [simp]: 
     "[] \<lozenge> bl = bl"
     "((a,b)#al) \<lozenge> bl = (a,b \<lhd> bl) # (al \<lozenge> bl)"
     "sdom([]) = {}"
     "sdom((a,b)#al) = (if Var(a)=b then (sdom al) - {a} else sdom al Un {a})"
by (simp_all add: comp_def sdom_def) 

lemma comp_Nil [simp]: "s \<lozenge> [] = s"
by (induct "s", auto)

lemma subst_comp_Nil: "s \<doteq> s \<lozenge> []"
by simp

lemma subst_comp [simp]: "(t \<lhd> r \<lozenge> s) = (t \<lhd> r \<lhd> s)"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
apply (induct "r", auto)
done

lemma comp_assoc: "(q \<lozenge> r) \<lozenge> s \<doteq> q \<lozenge> (r \<lozenge> s)"
by (simp add: subst_eq_iff)

lemma subst_cong:
     "[| theta \<doteq> theta1; sigma \<doteq> sigma1|] 
      ==> (theta \<lozenge> sigma) \<doteq> (theta1 \<lozenge> sigma1)"
by (simp add: subst_eq_def)


lemma Cons_trivial: "(w, Var(w) \<lhd> s) # s \<doteq> s"
apply (simp add: subst_eq_iff)
apply (rule allI)
apply (induct_tac "t", simp_all)
done


lemma comp_subst_subst: "q \<lozenge> r \<doteq> s ==>  t \<lhd> q \<lhd> r = t \<lhd> s"
by (simp add: subst_eq_iff)


subsection{*Domain and range of Substitutions*}

lemma sdom_iff: "(v \<in> sdom(s)) = (Var(v) \<lhd> s ~= Var(v))"
apply (induct "s")
apply (case_tac [2] a, auto)  
done


lemma srange_iff: 
   "v \<in> srange(s) = (\<exists>w. w \<in> sdom(s) & v \<in> vars_of(Var(w) \<lhd> s))"
by (auto simp add: srange_def)

lemma empty_iff_all_not: "(A = {}) = (ALL a.~ a:A)"
by (unfold empty_def, blast)

lemma invariance: "(t \<lhd> s = t) = (sdom(s) Int vars_of(t) = {})"
apply (induct_tac "t")
apply (auto simp add: empty_iff_all_not sdom_iff)
done

lemma Var_in_srange [rule_format]:
     "v \<in> sdom(s) -->  v \<in> vars_of(t \<lhd> s) --> v \<in> srange(s)"
apply (induct_tac "t")
apply (case_tac "a \<in> sdom s")
apply (auto simp add: sdom_iff srange_iff)
done

lemma Var_elim: "[| v \<in> sdom(s); v \<notin> srange(s) |] ==>  v \<notin> vars_of(t \<lhd> s)"
by (blast intro: Var_in_srange)

lemma Var_intro [rule_format]:
     "v \<in> vars_of(t \<lhd> s) --> v \<in> srange(s) | v \<in> vars_of(t)"
apply (induct_tac "t")
apply (auto simp add: sdom_iff srange_iff)
apply (rule_tac x=a in exI, auto) 
done

lemma srangeD: "v \<in> srange(s) ==> \<exists>w. w \<in> sdom(s) & v \<in> vars_of(Var(w) \<lhd> s)"
by (simp add: srange_iff)

lemma dom_range_disjoint:
     "sdom(s) Int srange(s) = {} = (\<forall>t. sdom(s) Int vars_of(t \<lhd> s) = {})"
apply (simp add: empty_iff_all_not)
apply (force intro: Var_in_srange dest: srangeD)
done

lemma subst_not_empty: "~ u \<lhd> s = u ==> (\<exists>x. x \<in> sdom(s))"
by (auto simp add: empty_iff_all_not invariance)


lemma id_subst_lemma [simp]: "(M \<lhd> [(x, Var x)]) = M"
by (induct_tac "M", auto)


end
