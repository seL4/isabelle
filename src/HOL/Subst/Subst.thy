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


primrec
  subst_Var:      "(Var v <| s) = assoc v (Var v) s"
  subst_Const:  "(Const c <| s) = Const c"
  subst_Comb:  "(Comb M N <| s) = Comb (M <| s) (N <| s)"


defs 

  subst_eq_def:  "r =$= s == ALL t. t <| r = t <| s"

  comp_def:    "al <> bl == alist_rec al bl (%x y xs g. (x,y <| bl)#g)"

  sdom_def:
  "sdom(al) == alist_rec al {}  
                (%x y xs g. if Var(x)=y then g - {x} else g Un {x})"

  srange_def:
   "srange(al) == Union({y. EX x:sdom(al). y=vars_of(Var(x) <| al)})"



subsection{*Basic Laws*}

lemma subst_Nil [simp]: "t <| [] = t"
by (induct_tac "t", auto)

lemma subst_mono [rule_format]: "t <: u --> t <| s <: u <| s"
by (induct_tac "u", auto)

lemma Var_not_occs [rule_format]:
     "~ (Var(v) <: t) --> t <| (v,t <| s) # s = t <| s"
apply (case_tac "t = Var v")
apply (erule_tac [2] rev_mp)
apply (rule_tac [2] P = "%x.~x=Var (v) --> ~ (Var (v) <: x) --> x <| (v,t<|s) #s=x<|s" in uterm.induct)
apply auto 
done

lemma agreement: "(t <|r = t <|s) = (\<forall>v. v : vars_of(t) --> Var(v) <|r = Var(v) <|s)"
by (induct_tac "t", auto)

lemma repl_invariance: "~ v: vars_of(t) ==> t <| (v,u)#s = t <| s"
by (simp add: agreement)

lemma Var_in_subst [rule_format]:
     "v : vars_of(t) --> w : vars_of(t <| (v,Var(w))#s)"
by (induct_tac "t", auto)


subsection{*Equality between Substitutions*}

lemma subst_eq_iff: "r =$= s = (\<forall>t. t <| r = t <| s)"
by (simp add: subst_eq_def)

lemma subst_refl [iff]: "r =$= r"
by (simp add: subst_eq_iff)

lemma subst_sym: "r =$= s ==> s =$= r"
by (simp add: subst_eq_iff)

lemma subst_trans: "[| q =$= r; r =$= s |] ==> q =$= s"
by (simp add: subst_eq_iff)

lemma subst_subst2:
    "[| r =$= s; P (t <| r) (u <| r) |] ==> P (t <| s) (u <| s)"
by (simp add: subst_eq_def)

lemmas ssubst_subst2 = subst_sym [THEN subst_subst2]


subsection{*Composition of Substitutions*}

lemma [simp]: 
     "[] <> bl = bl"
     "((a,b)#al) <> bl = (a,b <| bl) # (al <> bl)"
     "sdom([]) = {}"
     "sdom((a,b)#al) = (if Var(a)=b then (sdom al) - {a} else sdom al Un {a})"
by (simp_all add: comp_def sdom_def) 

lemma comp_Nil [simp]: "s <> [] = s"
by (induct "s", auto)

lemma subst_comp_Nil: "s =$= s <> []"
by simp

lemma subst_comp [simp]: "(t <| r <> s) = (t <| r <| s)"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
apply (induct "r", auto)
done

lemma comp_assoc: "(q <> r) <> s =$= q <> (r <> s)"
apply (simp (no_asm) add: subst_eq_iff)
done

lemma subst_cong:
     "[| theta =$= theta1; sigma =$= sigma1|] 
      ==> (theta <> sigma) =$= (theta1 <> sigma1)"
by (simp add: subst_eq_def)


lemma Cons_trivial: "(w, Var(w) <| s) # s =$= s"
apply (simp add: subst_eq_iff)
apply (rule allI)
apply (induct_tac "t", simp_all)
done


lemma comp_subst_subst: "q <> r =$= s ==>  t <| q <| r = t <| s"
by (simp add: subst_eq_iff)


subsection{*Domain and range of Substitutions*}

lemma sdom_iff: "(v : sdom(s)) = (Var(v) <| s ~= Var(v))"
apply (induct "s")
apply (case_tac [2] a, auto)  
done


lemma srange_iff: 
   "v : srange(s) = (\<exists>w. w : sdom(s) & v : vars_of(Var(w) <| s))"
by (auto simp add: srange_def)

lemma empty_iff_all_not: "(A = {}) = (ALL a.~ a:A)"
by (unfold empty_def, blast)

lemma invariance: "(t <| s = t) = (sdom(s) Int vars_of(t) = {})"
apply (induct_tac "t")
apply (auto simp add: empty_iff_all_not sdom_iff)
done

lemma Var_in_srange [rule_format]:
     "v : sdom(s) -->  v : vars_of(t <| s) --> v : srange(s)"
apply (induct_tac "t")
apply (case_tac "a : sdom (s) ")
apply (auto simp add: sdom_iff srange_iff)
done

lemma Var_elim: "[| v : sdom(s); v ~: srange(s) |] ==>  v ~: vars_of(t <| s)"
by (blast intro: Var_in_srange)

lemma Var_intro [rule_format]:
     "v : vars_of(t <| s) --> v : srange(s) | v : vars_of(t)"
apply (induct_tac "t")
apply (auto simp add: sdom_iff srange_iff)
apply (rule_tac x=a in exI, auto) 
done

lemma srangeD [rule_format]:
     "v : srange(s) --> (\<exists>w. w : sdom(s) & v : vars_of(Var(w) <| s))"
apply (simp (no_asm) add: srange_iff)
done

lemma dom_range_disjoint:
     "sdom(s) Int srange(s) = {} = (\<forall>t. sdom(s) Int vars_of(t <| s) = {})"
apply (simp (no_asm) add: empty_iff_all_not)
apply (force intro: Var_in_srange dest: srangeD)
done

lemma subst_not_empty: "~ u <| s = u ==> (\<exists>x. x : sdom(s))"
by (auto simp add: empty_iff_all_not invariance)


lemma id_subst_lemma [simp]: "(M <| [(x, Var x)]) = M"
by (induct_tac "M", auto)


end
