(*  Title:      CCL/Trancl.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Transitive closure of a relation *}

theory Trancl
imports CCL
begin

consts
  trans   :: "i set => o"                   (*transitivity predicate*)
  id      :: "i set"
  rtrancl :: "i set => i set"               ("(_^*)" [100] 100)
  trancl  :: "i set => i set"               ("(_^+)" [100] 100)
  relcomp :: "[i set,i set] => i set"       (infixr "O" 60)

axioms
  trans_def:       "trans(r) == (ALL x y z. <x,y>:r --> <y,z>:r --> <x,z>:r)"
  relcomp_def:     (*composition of relations*)
                   "r O s == {xz. EX x y z. xz = <x,z> & <x,y>:s & <y,z>:r}"
  id_def:          (*the identity relation*)
                   "id == {p. EX x. p = <x,x>}"
  rtrancl_def:     "r^* == lfp(%s. id Un (r O s))"
  trancl_def:      "r^+ == r O rtrancl(r)"


subsection {* Natural deduction for @{text "trans(r)"} *}

lemma transI:
  "(!! x y z. [| <x,y>:r;  <y,z>:r |] ==> <x,z>:r) ==> trans(r)"
  unfolding trans_def by blast

lemma transD: "[| trans(r);  <a,b>:r;  <b,c>:r |] ==> <a,c>:r"
  unfolding trans_def by blast


subsection {* Identity relation *}

lemma idI: "<a,a> : id"
  apply (unfold id_def)
  apply (rule CollectI)
  apply (rule exI)
  apply (rule refl)
  done

lemma idE:
    "[| p: id;  !!x.[| p = <x,x> |] ==> P |] ==>  P"
  apply (unfold id_def)
  apply (erule CollectE)
  apply blast
  done


subsection {* Composition of two relations *}

lemma compI: "[| <a,b>:s; <b,c>:r |] ==> <a,c> : r O s"
  unfolding relcomp_def by blast

(*proof requires higher-level assumptions or a delaying of hyp_subst_tac*)
lemma compE:
    "[| xz : r O s;
        !!x y z. [| xz = <x,z>;  <x,y>:s;  <y,z>:r |] ==> P
     |] ==> P"
  unfolding relcomp_def by blast

lemma compEpair:
  "[| <a,c> : r O s;
      !!y. [| <a,y>:s;  <y,c>:r |] ==> P
   |] ==> P"
  apply (erule compE)
  apply (simp add: pair_inject)
  done

lemmas [intro] = compI idI
  and [elim] = compE idE
  and [elim!] = pair_inject

lemma comp_mono: "[| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)"
  by blast


subsection {* The relation rtrancl *}

lemma rtrancl_fun_mono: "mono(%s. id Un (r O s))"
  apply (rule monoI)
  apply (rule monoI subset_refl comp_mono Un_mono)+
  apply assumption
  done

lemma rtrancl_unfold: "r^* = id Un (r O r^*)"
  by (rule rtrancl_fun_mono [THEN rtrancl_def [THEN def_lfp_Tarski]])

(*Reflexivity of rtrancl*)
lemma rtrancl_refl: "<a,a> : r^*"
  apply (subst rtrancl_unfold)
  apply blast
  done

(*Closure under composition with r*)
lemma rtrancl_into_rtrancl: "[| <a,b> : r^*;  <b,c> : r |] ==> <a,c> : r^*"
  apply (subst rtrancl_unfold)
  apply blast
  done

(*rtrancl of r contains r*)
lemma r_into_rtrancl: "[| <a,b> : r |] ==> <a,b> : r^*"
  apply (rule rtrancl_refl [THEN rtrancl_into_rtrancl])
  apply assumption
  done


subsection {* standard induction rule *}

lemma rtrancl_full_induct:
  "[| <a,b> : r^*;
      !!x. P(<x,x>);
      !!x y z.[| P(<x,y>); <x,y>: r^*; <y,z>: r |]  ==>  P(<x,z>) |]
   ==>  P(<a,b>)"
  apply (erule def_induct [OF rtrancl_def])
   apply (rule rtrancl_fun_mono)
  apply blast
  done

(*nice induction rule*)
lemma rtrancl_induct:
  "[| <a,b> : r^*;
      P(a);
      !!y z.[| <a,y> : r^*;  <y,z> : r;  P(y) |] ==> P(z) |]
    ==> P(b)"
(*by induction on this formula*)
  apply (subgoal_tac "ALL y. <a,b> = <a,y> --> P(y)")
(*now solve first subgoal: this formula is sufficient*)
  apply blast
(*now do the induction*)
  apply (erule rtrancl_full_induct)
   apply blast
  apply blast
  done

(*transitivity of transitive closure!! -- by induction.*)
lemma trans_rtrancl: "trans(r^*)"
  apply (rule transI)
  apply (rule_tac b = z in rtrancl_induct)
    apply (fast elim: rtrancl_into_rtrancl)+
  done

(*elimination of rtrancl -- by induction on a special formula*)
lemma rtranclE:
  "[| <a,b> : r^*;  (a = b) ==> P;
      !!y.[| <a,y> : r^*; <y,b> : r |] ==> P |]
   ==> P"
  apply (subgoal_tac "a = b | (EX y. <a,y> : r^* & <y,b> : r)")
   prefer 2
   apply (erule rtrancl_induct)
    apply blast
   apply blast
  apply blast
  done


subsection {* The relation trancl *}

subsubsection {* Conversions between trancl and rtrancl *}

lemma trancl_into_rtrancl: "[| <a,b> : r^+ |] ==> <a,b> : r^*"
  apply (unfold trancl_def)
  apply (erule compEpair)
  apply (erule rtrancl_into_rtrancl)
  apply assumption
  done

(*r^+ contains r*)
lemma r_into_trancl: "[| <a,b> : r |] ==> <a,b> : r^+"
  unfolding trancl_def by (blast intro: rtrancl_refl)

(*intro rule by definition: from rtrancl and r*)
lemma rtrancl_into_trancl1: "[| <a,b> : r^*;  <b,c> : r |]   ==>  <a,c> : r^+"
  unfolding trancl_def by blast

(*intro rule from r and rtrancl*)
lemma rtrancl_into_trancl2: "[| <a,b> : r;  <b,c> : r^* |]   ==>  <a,c> : r^+"
  apply (erule rtranclE)
   apply (erule subst)
   apply (erule r_into_trancl)
  apply (rule trans_rtrancl [THEN transD, THEN rtrancl_into_trancl1])
    apply (assumption | rule r_into_rtrancl)+
  done

(*elimination of r^+ -- NOT an induction rule*)
lemma tranclE:
  "[| <a,b> : r^+;
      <a,b> : r ==> P;
      !!y.[| <a,y> : r^+;  <y,b> : r |] ==> P
   |] ==> P"
  apply (subgoal_tac "<a,b> : r | (EX y. <a,y> : r^+ & <y,b> : r)")
   apply blast
  apply (unfold trancl_def)
  apply (erule compEpair)
  apply (erule rtranclE)
   apply blast
  apply (blast intro!: rtrancl_into_trancl1)
  done

(*Transitivity of r^+.
  Proved by unfolding since it uses transitivity of rtrancl. *)
lemma trans_trancl: "trans(r^+)"
  apply (unfold trancl_def)
  apply (rule transI)
  apply (erule compEpair)+
  apply (erule rtrancl_into_rtrancl [THEN trans_rtrancl [THEN transD, THEN compI]])
    apply assumption+
  done

lemma trancl_into_trancl2: "[| <a,b> : r;  <b,c> : r^+ |]   ==>  <a,c> : r^+"
  apply (rule r_into_trancl [THEN trans_trancl [THEN transD]])
   apply assumption+
  done

end
