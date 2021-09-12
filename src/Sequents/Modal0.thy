(*  Title:      Sequents/Modal0.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory Modal0
imports LK0
begin

ML_file \<open>modal.ML\<close>

consts
  box           :: "o\<Rightarrow>o"       ("[]_" [50] 50)
  dia           :: "o\<Rightarrow>o"       ("<>_" [50] 50)
  Lstar         :: "two_seqi"
  Rstar         :: "two_seqi"

syntax
  "_Lstar"      :: "two_seqe"   ("(_)|L>(_)" [6,6] 5)
  "_Rstar"      :: "two_seqe"   ("(_)|R>(_)" [6,6] 5)

ML \<open>
  fun star_tr c [s1, s2] = Syntax.const c $ seq_tr s1 $ seq_tr s2;
  fun star_tr' c [s1, s2] = Syntax.const c $ seq_tr' s1 $ seq_tr' s2;
\<close>

parse_translation \<open>
 [(\<^syntax_const>\<open>_Lstar\<close>, K (star_tr \<^const_syntax>\<open>Lstar\<close>)),
  (\<^syntax_const>\<open>_Rstar\<close>, K (star_tr \<^const_syntax>\<open>Rstar\<close>))]
\<close>

print_translation \<open>
 [(\<^const_syntax>\<open>Lstar\<close>, K (star_tr' \<^syntax_const>\<open>_Lstar\<close>)),
  (\<^const_syntax>\<open>Rstar\<close>, K (star_tr' \<^syntax_const>\<open>_Rstar\<close>))]
\<close>

definition strimp :: "[o,o]\<Rightarrow>o"   (infixr "--<" 25)
  where "P --< Q == [](P \<longrightarrow> Q)"

definition streqv :: "[o,o]\<Rightarrow>o"   (infixr ">-<" 25)
  where "P >-< Q == (P --< Q) \<and> (Q --< P)"


lemmas rewrite_rls = strimp_def streqv_def

lemma iffR: "\<lbrakk>$H,P \<turnstile> $E,Q,$F;  $H,Q \<turnstile> $E,P,$F\<rbrakk> \<Longrightarrow> $H \<turnstile> $E, P \<longleftrightarrow> Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL: "\<lbrakk>$H,$G \<turnstile> $E,P,Q;  $H,Q,P,$G \<turnstile> $E \<rbrakk> \<Longrightarrow> $H, P \<longleftrightarrow> Q, $G \<turnstile> $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemmas safe_rls = basic conjL conjR disjL disjR impL impR notL notR iffL iffR
  and unsafe_rls = allR exL
  and bound_rls = allL exR

end
