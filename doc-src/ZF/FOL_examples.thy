header{*Examples of Classical Reasoning*}

theory FOL_examples imports "~~/src/FOL/FOL" begin

lemma "EX y. ALL x. P(y)-->P(x)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule exCI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule allI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule impI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule allE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
txt{*see below for @{text allI} combined with @{text swap}*}
apply (erule allI [THEN [2] swap])
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule impI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule notE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption
done

text {*
@{thm[display] allI [THEN [2] swap]}
*}

lemma "EX y. ALL x. P(y)-->P(x)"
by blast

end


