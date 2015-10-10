(*  Title:      Sequents/Modal0.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory Modal0
imports LK0
begin

ML_file "modal.ML"

consts
  box           :: "o\<Rightarrow>o"       ("[]_" [50] 50)
  dia           :: "o\<Rightarrow>o"       ("<>_" [50] 50)
  strimp        :: "[o,o]\<Rightarrow>o"   (infixr "--<" 25)
  streqv        :: "[o,o]\<Rightarrow>o"   (infixr ">-<" 25)
  Lstar         :: "two_seqi"
  Rstar         :: "two_seqi"

syntax
  "_Lstar"      :: "two_seqe"   ("(_)|L>(_)" [6,6] 5)
  "_Rstar"      :: "two_seqe"   ("(_)|R>(_)" [6,6] 5)

ML \<open>
  fun star_tr c [s1, s2] = Const(c, dummyT) $ seq_tr s1 $ seq_tr s2;
  fun star_tr' c [s1, s2] = Const(c, dummyT) $ seq_tr' s1 $ seq_tr' s2;
\<close>

parse_translation \<open>
 [(@{syntax_const "_Lstar"}, K (star_tr @{const_syntax Lstar})),
  (@{syntax_const "_Rstar"}, K (star_tr @{const_syntax Rstar}))]
\<close>

print_translation \<open>
 [(@{const_syntax Lstar}, K (star_tr' @{syntax_const "_Lstar"})),
  (@{const_syntax Rstar}, K (star_tr' @{syntax_const "_Rstar"}))]
\<close>

defs
  strimp_def:    "P --< Q == [](P \<longrightarrow> Q)"
  streqv_def:    "P >-< Q == (P --< Q) \<and> (Q --< P)"


lemmas rewrite_rls = strimp_def streqv_def

lemma iffR: "\<lbrakk>$H,P |- $E,Q,$F;  $H,Q |- $E,P,$F\<rbrakk> \<Longrightarrow> $H |- $E, P \<longleftrightarrow> Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL: "\<lbrakk>$H,$G |- $E,P,Q;  $H,Q,P,$G |- $E \<rbrakk> \<Longrightarrow> $H, P \<longleftrightarrow> Q, $G |- $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemmas safe_rls = basic conjL conjR disjL disjR impL impR notL notR iffL iffR
  and unsafe_rls = allR exL
  and bound_rls = allL exR

end
