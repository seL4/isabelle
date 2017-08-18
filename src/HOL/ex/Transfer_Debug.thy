(*  Title:      HOL/ex/Transfer_Debug.thy
    Author:     Ondřej Kunčar, TU München
*)
theory Transfer_Debug 
imports Main "HOL-Library.FSet"
begin                              

(*
  This file demonstrates some of the typical scenarios 
  when transfer or transfer_prover does not produce expected results
  and how the user might handle such cases.
*)

(* As an example, we use finite sets. The following command recreates the environment in which
   the type of finite sets was created and allows us to do transferring on this type. *)
context
includes fset.lifting
begin

subsection \<open>1. A missing transfer rule\<close>

(* We will simulate the situation in which there is not any transfer rules for fmember. *)
declare fmember.transfer[transfer_rule del] fmember_transfer[transfer_rule del]

(* We want to prove the following theorem about |\<subseteq>| by transfer *)
lemma "(A |\<subseteq>| B) = fBall A (\<lambda>x. x |\<in>| B)"
apply transfer
(* 
   Transfer complains that it could not find a transfer rule for |\<subseteq>| with a matching transfer
   relation. An experienced user could notice that |\<in>| was transferred to |\<in>| by a 
   a default reflexivity transfer rule (because there was not any genuine transfer rule for |\<in>|)
   and fBall was transferred to Ball using the transfer relation pcr_fset. Therefore transfer
   is looking for a transfer rule for |\<subseteq>| with a transfer relation that mixes op= and pcr_fset.
   This situation might be confusing because the real problem (a missing transfer rule) propagates
   during the transferring algorithm and manifests later in an obfuscated way. Fortunately,
   we could inspect the behavior of transfer in a more interactive way to pin down the real problem.
*)
oops

lemma "(A |\<subseteq>| B) = fBall A (\<lambda>x. x |\<in>| B)"
apply transfer_start 
(* Setups 6 goals for 6 transfer rules that have to be found and the result as the 7. goal, which
   gets synthesized to the final result of transferring when we find the 6 transfer rules. *)
apply transfer_step
(* We can see that the default reflexivity transfer rule was applied and |\<in>| 
  was transferred to |\<in>| \<Longrightarrow> there is no genuine transfer rule for |\<in>|. *)
oops

(* We provide a transfer rule for |\<in>|. *)
lemma [transfer_rule]: "bi_unique A \<Longrightarrow> rel_fun A (rel_fun (pcr_fset A) op =) op \<in> op |\<in>|"
by (rule fmember.transfer)

lemma "(A |\<subseteq>| B) = fBall A (\<lambda>x. x |\<in>| B)"
apply transfer_start
apply transfer_step (* The new transfer rule was selected and |\<in>| was transferred to \<in>. *)
apply transfer_step+
apply transfer_end
by blast

(* Of course in the real life, we would use transfer instead of transfer_start, transfer_step+ and 
   transfer_end. *) 
lemma "(A |\<subseteq>| B) = fBall A (\<lambda>x. x |\<in>| B)"
by transfer blast

subsection \<open>2. Unwanted instantiation of a transfer relation variable\<close>

(* We want to prove the following fact. *)
lemma "finite (UNIV :: 'a::finite fset set)"
apply transfer
(* Transfer does not do anything here. *)
oops

(* Let us inspect interactively what happened. *)
lemma "finite (UNIV :: 'a::finite fset set)"
apply transfer_start
apply transfer_step 
(* 
   Here we can realize that not an expected transfer rule was chosen. 
   We stumbled upon a limitation of Transfer: the tool used the rule Lifting_Set.UNIV_transfer,
   which transfers UNIV to UNIV and assumes that the transfer relation has to be bi-total.
   The problem is that at this point the transfer relation is not known (it is represented by
   a schematic variable ?R) and therefore in order to discharge the assumption "bi_total ?R", ?R is
   instantiated to op=. If the relation had been known (we wish pcr_fset op=, which is not bi-total),
   the assumption bi_total pcr_fset op= could not have been discharged and the tool would have 
   backtracked and chosen Lifting.right_total_UNIV_transfer, which assumes only right-totalness 
   (and pcr_fset is right-total).
*)
back back (* We can force the tool to backtrack and choose the desired transfer rule. *)
apply transfer_step
apply transfer_end
by auto

(* Of course, to use "back" in proofs is not a desired style. But we can prioritize
   the rule Lifting.right_total_UNIV_transfer by redeclaring it LOCALLY as a transfer rule.
 *)
lemma "finite (UNIV :: 'a::finite fset set)"
proof -
  note right_total_UNIV_transfer[transfer_rule]
  show ?thesis by transfer auto
qed

end

(* Let us close the environment of fset transferring and add the rule that we deleted. *)
lifting_forget fset.lifting (* deletes the extra added transfer rule for |\<in>| *)
declare fmember_transfer[transfer_rule] (* we want to keep parametricity of |\<in>| *)

end
