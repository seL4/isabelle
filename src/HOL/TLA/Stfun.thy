(*  Title:      HOL/TLA/Stfun.thy
    Author:     Stephan Merz
    Copyright:  1998 University of Munich
*)

section \<open>States and state functions for TLA as an "intensional" logic\<close>

theory Stfun
imports Intensional
begin

typedecl state
instance state :: world ..

type_synonym 'a stfun = "state \<Rightarrow> 'a"
type_synonym stpred  = "bool stfun"


consts
  (* Formalizing type "state" would require formulas to be tagged with
     their underlying state space and would result in a system that is
     much harder to use. (Unlike Hoare logic or Unity, TLA has quantification
     over state variables, and therefore one usually works with different
     state spaces within a single specification.) Instead, "state" is just
     an anonymous type whose only purpose is to provide "Skolem" constants.
     Moreover, we do not define a type of state variables separate from that
     of arbitrary state functions, again in order to simplify the definition
     of flexible quantification later on. Nevertheless, we need to distinguish
     state variables, mainly to define the enabledness of actions. The user
     identifies (tuples of) "base" state variables in a specification via the
     "meta predicate" basevars, which is defined here.
  *)
  stvars    :: "'a stfun \<Rightarrow> bool"

syntax
  "_PRED"   :: "lift \<Rightarrow> 'a"                          (\<open>PRED _\<close>)
  "_stvars" :: "lift \<Rightarrow> bool"                        (\<open>basevars _\<close>)

translations
  "PRED P"   =>  "(P::state \<Rightarrow> _)"
  "_stvars"  ==  "CONST stvars"

(* Base variables may be assigned arbitrary (type-correct) values.
   Note that vs may be a tuple of variables. The correct identification
   of base variables is up to the user who must take care not to
   introduce an inconsistency. For example, "basevars (x,x)" would
   definitely be inconsistent.
*)
overloading stvars \<equiv> stvars
begin
  definition stvars :: "(state \<Rightarrow> 'a) \<Rightarrow> bool"
    where basevars_def: "stvars vs == range vs = UNIV"
end

lemma basevars: "\<And>vs. basevars vs \<Longrightarrow> \<exists>u. vs u = c"
  apply (unfold basevars_def)
  apply (rule_tac b = c and f = vs in rangeE)
   apply auto
  done

lemma base_pair1: "\<And>x y. basevars (x,y) \<Longrightarrow> basevars x"
  apply (simp (no_asm) add: basevars_def)
  apply (rule equalityI)
   apply (rule subset_UNIV)
  apply (rule subsetI)
  apply (drule_tac c = "(xa, _) " in basevars)
  apply auto
  done

lemma base_pair2: "\<And>x y. basevars (x,y) \<Longrightarrow> basevars y"
  apply (simp (no_asm) add: basevars_def)
  apply (rule equalityI)
   apply (rule subset_UNIV)
  apply (rule subsetI)
  apply (drule_tac c = "(_, xa) " in basevars)
  apply auto
  done

lemma base_pair: "\<And>x y. basevars (x,y) \<Longrightarrow> basevars x & basevars y"
  apply (rule conjI)
  apply (erule base_pair1)
  apply (erule base_pair2)
  done

(* Since the unit type has just one value, any state function can be
   regarded as "base". The following axiom can sometimes be useful
   because it gives a trivial solution for "basevars" premises.
*)
lemma unit_base: "basevars (v::unit stfun)"
  apply (unfold basevars_def)
  apply auto
  done

lemma baseE: "\<lbrakk> basevars v; \<And>x. v x = c \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (erule basevars [THEN exE])
  apply blast
  done


(* -------------------------------------------------------------------------------
   The following shows that there should not be duplicates in a "stvars" tuple:
*)

lemma "\<And>v. basevars (v::bool stfun, v) \<Longrightarrow> False"
  apply (erule baseE)
  apply (subgoal_tac "(LIFT (v,v)) x = (True, False)")
   prefer 2
   apply assumption
  apply simp
  done

end
