header{*Examples of Intuitionistic Reasoning*}

theory IFOL_examples = IFOL:

text{*Quantifier example from the book Logic and Computation*}
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule impI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule allI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule exI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule exE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule allE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
txt{*Now @{text "apply assumption"} fails*}
oops

text{*Trying again, with the same first two steps*}
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule impI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule allI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule exE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule exI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule allE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption
  --{* @{subgoals[display,indent=0,margin=65]} *}
done

lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
by (tactic {*IntPr.fast_tac 1*})

text{*Example of Dyckhoff's method*}
lemma "~ ~ ((P-->Q) | (Q-->P))"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (unfold not_def)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule impI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule disj_impE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule imp_impE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
 apply (erule imp_impE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
apply (erule FalseE)+
done

end
