(* ID:         $Id$ *)
theory Advanced = Even:


datatype 'f gterm = Apply 'f "'f gterm list"

datatype integer_op = Number int | UnaryMinus | Plus;

consts gterms :: "'f set \<Rightarrow> 'f gterm set"
inductive "gterms F"
intros
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> gterms F;  f \<in> F\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> gterms F"

lemma gterms_mono: "F\<subseteq>G \<Longrightarrow> gterms F \<subseteq> gterms G"
apply clarify
apply (erule gterms.induct)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply blast
done


text{*
@{thm[display] even.cases[no_vars]}
\rulename{even.cases}

Just as a demo I include
the two forms that Markus has made available. First the one for binding the
result to a name 

*}

inductive_cases Suc_Suc_cases [elim!]:
  "Suc(Suc n) \<in> even"

thm Suc_Suc_cases;

text{*
@{thm[display] Suc_Suc_cases[no_vars]}
\rulename{Suc_Suc_cases}

and now the one for local usage:
*}

lemma "Suc(Suc n) \<in> even \<Longrightarrow> P n";
apply (ind_cases "Suc(Suc n) \<in> even");
oops

inductive_cases gterm_Apply_elim [elim!]: "Apply f args \<in> gterms F"

text{*this is what we get:

@{thm[display] gterm_Apply_elim[no_vars]}
\rulename{gterm_Apply_elim}
*}

lemma gterms_IntI [rule_format, intro!]:
     "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
apply (erule gterms.induct)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply blast
done


text{*
@{thm[display] mono_Int[no_vars]}
\rulename{mono_Int}
*}

lemma gterms_Int_eq [simp]:
     "gterms (F\<inter>G) = gterms F \<inter> gterms G"
by (blast intro!: mono_Int monoI gterms_mono)


consts integer_arity :: "integer_op \<Rightarrow> nat"
primrec
"integer_arity (Number n)        = #0"
"integer_arity UnaryMinus        = #1"
"integer_arity Plus              = #2"

consts well_formed_gterm :: "('f \<Rightarrow> nat) \<Rightarrow> 'f gterm set"
inductive "well_formed_gterm arity"
intros
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> well_formed_gterm arity;  
                length args = arity f\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> well_formed_gterm arity"


consts well_formed_gterm' :: "('f \<Rightarrow> nat) \<Rightarrow> 'f gterm set"
inductive "well_formed_gterm' arity"
intros
step[intro!]: "\<lbrakk>args \<in> lists (well_formed_gterm' arity);  
                length args = arity f\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> well_formed_gterm' arity"
monos lists_mono

lemma "well_formed_gterm arity \<subseteq> well_formed_gterm' arity"
apply clarify
txt{*
The situation after clarify
@{subgoals[display,indent=0,margin=65]}
*};
apply (erule well_formed_gterm.induct)
txt{*
note the induction hypothesis!
@{subgoals[display,indent=0,margin=65]}
*};
apply auto
done



lemma "well_formed_gterm' arity \<subseteq> well_formed_gterm arity"
apply clarify
txt{*
The situation after clarify
@{subgoals[display,indent=0,margin=65]}
*};
apply (erule well_formed_gterm'.induct)
txt{*
note the induction hypothesis!
@{subgoals[display,indent=0,margin=65]}
*};
apply auto
done


text{*
@{thm[display] lists_Int_eq[no_vars]}
*}

text{* the rest isn't used: too complicated.  OK for an exercise though.*}

consts integer_signature :: "(integer_op * (unit list * unit)) set"
inductive "integer_signature"
intros
Number:     "(Number n,   ([], ())) \<in> integer_signature"
UnaryMinus: "(UnaryMinus, ([()], ())) \<in> integer_signature"
Plus:       "(Plus,       ([(),()], ())) \<in> integer_signature"


consts well_typed_gterm :: "('f \<Rightarrow> 't list * 't) \<Rightarrow> ('f gterm * 't)set"
inductive "well_typed_gterm sig"
intros
step[intro!]: 
    "\<lbrakk>\<forall>pair \<in> set args. pair \<in> well_typed_gterm sig; 
      sig f = (map snd args, rtype)\<rbrakk>
     \<Longrightarrow> (Apply f (map fst args), rtype) 
         \<in> well_typed_gterm sig"

consts well_typed_gterm' :: "('f \<Rightarrow> 't list * 't) \<Rightarrow> ('f gterm * 't)set"
inductive "well_typed_gterm' sig"
intros
step[intro!]: 
    "\<lbrakk>args \<in> lists(well_typed_gterm' sig); 
      sig f = (map snd args, rtype)\<rbrakk>
     \<Longrightarrow> (Apply f (map fst args), rtype) 
         \<in> well_typed_gterm' sig"
monos lists_mono


lemma "well_typed_gterm sig \<subseteq> well_typed_gterm' sig"
apply clarify
apply (erule well_typed_gterm.induct)
apply auto
done

lemma "well_typed_gterm' sig \<subseteq> well_typed_gterm sig"
apply clarify
apply (erule well_typed_gterm'.induct)
apply auto
done


end

