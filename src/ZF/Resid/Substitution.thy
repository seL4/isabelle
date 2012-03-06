(*  Title:      ZF/Resid/Substitution.thy
    Author:     Ole Rasmussen, University of Cambridge
*)

theory Substitution imports Redex begin

(** The clumsy _aux functions are required because other arguments vary
    in the recursive calls ***)

consts
  lift_aux      :: "i=>i"
primrec
  "lift_aux(Var(i)) = (\<lambda>k \<in> nat. if i<k then Var(i) else Var(succ(i)))"

  "lift_aux(Fun(t)) = (\<lambda>k \<in> nat. Fun(lift_aux(t) ` succ(k)))"

  "lift_aux(App(b,f,a)) = (\<lambda>k \<in> nat. App(b, lift_aux(f)`k, lift_aux(a)`k))"

definition
  lift_rec      :: "[i,i]=> i"  where
    "lift_rec(r,k) == lift_aux(r)`k"

abbreviation
  lift :: "i=>i" where
  "lift(r) == lift_rec(r,0)"


consts
  subst_aux     :: "i=>i"
primrec
  "subst_aux(Var(i)) =
     (\<lambda>r \<in> redexes. \<lambda>k \<in> nat. if k<i then Var(i #- 1)
                                else if k=i then r else Var(i))"
  "subst_aux(Fun(t)) =
     (\<lambda>r \<in> redexes. \<lambda>k \<in> nat. Fun(subst_aux(t) ` lift(r) ` succ(k)))"

  "subst_aux(App(b,f,a)) =
     (\<lambda>r \<in> redexes. \<lambda>k \<in> nat. App(b, subst_aux(f)`r`k, subst_aux(a)`r`k))"

definition
  subst_rec     :: "[i,i,i]=> i"        (**NOTE THE ARGUMENT ORDER BELOW**)  where
    "subst_rec(u,r,k) == subst_aux(r)`u`k"

abbreviation
  subst :: "[i,i]=>i"  (infixl "'/" 70)  where
  "u/v == subst_rec(u,v,0)"



(* ------------------------------------------------------------------------- *)
(*   Arithmetic extensions                                                   *)
(* ------------------------------------------------------------------------- *)

lemma gt_not_eq: "p < n ==> n\<noteq>p"
by blast

lemma succ_pred [rule_format, simp]: "j \<in> nat ==> i < j \<longrightarrow> succ(j #- 1) = j"
by (induct_tac "j", auto)

lemma lt_pred: "[|succ(x)<n; n \<in> nat|] ==> x < n #- 1 "
apply (rule succ_leE)
apply (simp add: succ_pred)
done

lemma gt_pred: "[|n < succ(x); p<n; n \<in> nat|] ==> n #- 1 < x "
apply (rule succ_leE)
apply (simp add: succ_pred)
done


declare not_lt_iff_le [simp] if_P [simp] if_not_P [simp]


(* ------------------------------------------------------------------------- *)
(*     lift_rec equality rules                                               *)
(* ------------------------------------------------------------------------- *)
lemma lift_rec_Var:
     "n \<in> nat ==> lift_rec(Var(i),n) = (if i<n then Var(i) else Var(succ(i)))"
by (simp add: lift_rec_def)

lemma lift_rec_le [simp]:
     "[|i \<in> nat; k\<le>i|] ==> lift_rec(Var(i),k) = Var(succ(i))"
by (simp add: lift_rec_def le_in_nat)

lemma lift_rec_gt [simp]: "[| k \<in> nat; i<k |] ==> lift_rec(Var(i),k) = Var(i)"
by (simp add: lift_rec_def)

lemma lift_rec_Fun [simp]:
     "k \<in> nat ==> lift_rec(Fun(t),k) = Fun(lift_rec(t,succ(k)))"
by (simp add: lift_rec_def)

lemma lift_rec_App [simp]:
     "k \<in> nat ==> lift_rec(App(b,f,a),k) = App(b,lift_rec(f,k),lift_rec(a,k))"
by (simp add: lift_rec_def)


(* ------------------------------------------------------------------------- *)
(*    substitution quality rules                                             *)
(* ------------------------------------------------------------------------- *)

lemma subst_Var:
     "[|k \<in> nat; u \<in> redexes|]
      ==> subst_rec(u,Var(i),k) =
          (if k<i then Var(i #- 1) else if k=i then u else Var(i))"
by (simp add: subst_rec_def gt_not_eq leI)


lemma subst_eq [simp]:
     "[|n \<in> nat; u \<in> redexes|] ==> subst_rec(u,Var(n),n) = u"
by (simp add: subst_rec_def)

lemma subst_gt [simp]:
     "[|u \<in> redexes; p \<in> nat; p<n|] ==> subst_rec(u,Var(n),p) = Var(n #- 1)"
by (simp add: subst_rec_def)

lemma subst_lt [simp]:
     "[|u \<in> redexes; p \<in> nat; n<p|] ==> subst_rec(u,Var(n),p) = Var(n)"
by (simp add: subst_rec_def gt_not_eq leI lt_nat_in_nat)

lemma subst_Fun [simp]:
     "[|p \<in> nat; u \<in> redexes|]
      ==> subst_rec(u,Fun(t),p) = Fun(subst_rec(lift(u),t,succ(p))) "
by (simp add: subst_rec_def)

lemma subst_App [simp]:
     "[|p \<in> nat; u \<in> redexes|]
      ==> subst_rec(u,App(b,f,a),p) = App(b,subst_rec(u,f,p),subst_rec(u,a,p))"
by (simp add: subst_rec_def)


lemma lift_rec_type [rule_format, simp]:
     "u \<in> redexes ==> \<forall>k \<in> nat. lift_rec(u,k) \<in> redexes"
apply (erule redexes.induct)
apply (simp_all add: lift_rec_Var lift_rec_Fun lift_rec_App)
done

lemma subst_type [rule_format, simp]:
     "v \<in> redexes ==>  \<forall>n \<in> nat. \<forall>u \<in> redexes. subst_rec(u,v,n) \<in> redexes"
apply (erule redexes.induct)
apply (simp_all add: subst_Var lift_rec_type)
done


(* ------------------------------------------------------------------------- *)
(*    lift and  substitution proofs                                          *)
(* ------------------------------------------------------------------------- *)

(*The i\<in>nat is redundant*)
lemma lift_lift_rec [rule_format]:
     "u \<in> redexes
      ==> \<forall>n \<in> nat. \<forall>i \<in> nat. i\<le>n \<longrightarrow>
           (lift_rec(lift_rec(u,i),succ(n)) = lift_rec(lift_rec(u,n),i))"
apply (erule redexes.induct, auto)
apply (case_tac "n < i")
apply (frule lt_trans2, assumption)
apply (simp_all add: lift_rec_Var leI)
done

lemma lift_lift:
     "[|u \<in> redexes; n \<in> nat|]
      ==> lift_rec(lift(u),succ(n)) = lift(lift_rec(u,n))"
by (simp add: lift_lift_rec)

lemma lt_not_m1_lt: "\<lbrakk>m < n; n \<in> nat; m \<in> nat\<rbrakk>\<Longrightarrow> ~ n #- 1 < m"
by (erule natE, auto)

lemma lift_rec_subst_rec [rule_format]:
     "v \<in> redexes ==>
       \<forall>n \<in> nat. \<forall>m \<in> nat. \<forall>u \<in> redexes. n\<le>m\<longrightarrow>
          lift_rec(subst_rec(u,v,n),m) =
               subst_rec(lift_rec(u,m),lift_rec(v,succ(m)),n)"
apply (erule redexes.induct, simp_all (no_asm_simp) add: lift_lift)
apply safe
apply (rename_tac n n' m u)
apply (case_tac "n < n'")
 apply (frule_tac j = n' in lt_trans2, assumption)
 apply (simp add: leI, simp)
apply (erule_tac j=n in leE)
apply (auto simp add: lift_rec_Var subst_Var leI lt_not_m1_lt)
done


lemma lift_subst:
     "[|v \<in> redexes; u \<in> redexes; n \<in> nat|]
      ==> lift_rec(u/v,n) = lift_rec(u,n)/lift_rec(v,succ(n))"
by (simp add: lift_rec_subst_rec)


lemma lift_rec_subst_rec_lt [rule_format]:
     "v \<in> redexes ==>
       \<forall>n \<in> nat. \<forall>m \<in> nat. \<forall>u \<in> redexes. m\<le>n\<longrightarrow>
          lift_rec(subst_rec(u,v,n),m) =
               subst_rec(lift_rec(u,m),lift_rec(v,m),succ(n))"
apply (erule redexes.induct, simp_all (no_asm_simp) add: lift_lift)
apply safe
apply (rename_tac n n' m u)
apply (case_tac "n < n'")
apply (case_tac "n < m")
apply (simp_all add: leI)
apply (erule_tac i=n' in leE)
apply (frule lt_trans1, assumption)
apply (simp_all add: succ_pred leI gt_pred)
done


lemma subst_rec_lift_rec [rule_format]:
     "u \<in> redexes ==>
        \<forall>n \<in> nat. \<forall>v \<in> redexes. subst_rec(v,lift_rec(u,n),n) = u"
apply (erule redexes.induct, auto)
apply (case_tac "n < na", auto)
done

lemma subst_rec_subst_rec [rule_format]:
     "v \<in> redexes ==>
        \<forall>m \<in> nat. \<forall>n \<in> nat. \<forall>u \<in> redexes. \<forall>w \<in> redexes. m\<le>n \<longrightarrow>
          subst_rec(subst_rec(w,u,n),subst_rec(lift_rec(w,m),v,succ(n)),m) =
          subst_rec(w,subst_rec(u,v,m),n)"
apply (erule redexes.induct)
apply (simp_all add: lift_lift [symmetric] lift_rec_subst_rec_lt, safe)
apply (rename_tac n' u w)
apply (case_tac "n \<le> succ(n') ")
 apply (erule_tac i = n in leE)
 apply (simp_all add: succ_pred subst_rec_lift_rec leI)
 apply (case_tac "n < m")
  apply (frule lt_trans2, assumption, simp add: gt_pred)
 apply simp
 apply (erule_tac j = n in leE, simp add: gt_pred)
 apply (simp add: subst_rec_lift_rec)
(*final case*)
apply (frule nat_into_Ord [THEN le_refl, THEN lt_trans], assumption)
apply (erule leE)
 apply (frule succ_leI [THEN lt_trans], assumption)
 apply (frule_tac i = m in nat_into_Ord [THEN le_refl, THEN lt_trans],
        assumption)
 apply (simp_all add: succ_pred lt_pred)
done


lemma substitution:
     "[|v \<in> redexes; u \<in> redexes; w \<in> redexes; n \<in> nat|]
      ==> subst_rec(w,u,n)/subst_rec(lift(w),v,succ(n)) = subst_rec(w,u/v,n)"
by (simp add: subst_rec_subst_rec)


(* ------------------------------------------------------------------------- *)
(*          Preservation lemmas                                              *)
(*          Substitution preserves comp and regular                          *)
(* ------------------------------------------------------------------------- *)


lemma lift_rec_preserve_comp [rule_format, simp]:
     "u ~ v ==> \<forall>m \<in> nat. lift_rec(u,m) ~ lift_rec(v,m)"
by (erule Scomp.induct, simp_all add: comp_refl)

lemma subst_rec_preserve_comp [rule_format, simp]:
     "u2 ~ v2 ==> \<forall>m \<in> nat. \<forall>u1 \<in> redexes. \<forall>v1 \<in> redexes.
                  u1 ~ v1\<longrightarrow> subst_rec(u1,u2,m) ~ subst_rec(v1,v2,m)"
by (erule Scomp.induct,
    simp_all add: subst_Var lift_rec_preserve_comp comp_refl)

lemma lift_rec_preserve_reg [simp]:
     "regular(u) ==> \<forall>m \<in> nat. regular(lift_rec(u,m))"
by (erule Sreg.induct, simp_all add: lift_rec_Var)

lemma subst_rec_preserve_reg [simp]:
     "regular(v) ==>
        \<forall>m \<in> nat. \<forall>u \<in> redexes. regular(u)\<longrightarrow>regular(subst_rec(u,v,m))"
by (erule Sreg.induct, simp_all add: subst_Var lift_rec_preserve_reg)

end
