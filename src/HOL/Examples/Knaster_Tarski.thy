(*  Title:      HOL/Examples/Knaster_Tarski.thy
    Author:     Makarius

Typical textbook proof example.
*)

section \<open>Textbook-style reasoning: the Knaster-Tarski Theorem\<close>

theory Knaster_Tarski
  imports Main
begin

unbundle lattice_syntax


subsection \<open>Prose version\<close>

text \<open>
  According to the textbook @{cite \<open>pages 93--94\<close> "davey-priestley"}, the
  Knaster-Tarski fixpoint theorem is as follows.\<^footnote>\<open>We have dualized the
  argument, and tuned the notation a little bit.\<close>

  \<^bold>\<open>The Knaster-Tarski Fixpoint Theorem.\<close> Let \<open>L\<close> be a complete lattice and
  \<open>f: L \<rightarrow> L\<close> an order-preserving map. Then \<open>\<Sqinter>{x \<in> L | f(x) \<le> x}\<close> is a fixpoint
  of \<open>f\<close>.

  \<^bold>\<open>Proof.\<close> Let \<open>H = {x \<in> L | f(x) \<le> x}\<close> and \<open>a = \<Sqinter>H\<close>. For all \<open>x \<in> H\<close> we have
  \<open>a \<le> x\<close>, so \<open>f(a) \<le> f(x) \<le> x\<close>. Thus \<open>f(a)\<close> is a lower bound of \<open>H\<close>, whence
  \<open>f(a) \<le> a\<close>. We now use this inequality to prove the reverse one (!) and
  thereby complete the proof that \<open>a\<close> is a fixpoint. Since \<open>f\<close> is
  order-preserving, \<open>f(f(a)) \<le> f(a)\<close>. This says \<open>f(a) \<in> H\<close>, so \<open>a \<le> f(a)\<close>.\<close>


subsection \<open>Formal versions\<close>

text \<open>
  The Isar proof below closely follows the original presentation. Virtually
  all of the prose narration has been rephrased in terms of formal Isar
  language elements. Just as many textbook-style proofs, there is a strong
  bias towards forward proof, and several bends in the course of reasoning.
\<close>

theorem Knaster_Tarski:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "\<exists>a. f a = a"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a = ?a"
  proof -
    {
      fix x
      assume "x \<in> ?H"
      then have "?a \<le> x" by (rule Inf_lower)
      with \<open>mono f\<close> have "f ?a \<le> f x" ..
      also from \<open>x \<in> ?H\<close> have "\<dots> \<le> x" ..
      finally have "f ?a \<le> x" .
    }
    then have "f ?a \<le> ?a" by (rule Inf_greatest)
    {
      also presume "\<dots> \<le> f ?a"
      finally (order_antisym) show ?thesis .
    }
    from \<open>mono f\<close> and \<open>f ?a \<le> ?a\<close> have "f (f ?a) \<le> f ?a" ..
    then have "f ?a \<in> ?H" ..
    then show "?a \<le> f ?a" by (rule Inf_lower)
  qed
qed

text \<open>
  Above we have used several advanced Isar language elements, such as explicit
  block structure and weak assumptions. Thus we have mimicked the particular
  way of reasoning of the original text.

  In the subsequent version the order of reasoning is changed to achieve
  structured top-down decomposition of the problem at the outer level, while
  only the inner steps of reasoning are done in a forward manner. We are
  certainly more at ease here, requiring only the most basic features of the
  Isar language.
\<close>

theorem Knaster_Tarski':
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "\<exists>a. f a = a"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a = ?a"
  proof (rule order_antisym)
    show "f ?a \<le> ?a"
    proof (rule Inf_greatest)
      fix x
      assume "x \<in> ?H"
      then have "?a \<le> x" by (rule Inf_lower)
      with \<open>mono f\<close> have "f ?a \<le> f x" ..
      also from \<open>x \<in> ?H\<close> have "\<dots> \<le> x" ..
      finally show "f ?a \<le> x" .
    qed
    show "?a \<le> f ?a"
    proof (rule Inf_lower)
      from \<open>mono f\<close> and \<open>f ?a \<le> ?a\<close> have "f (f ?a) \<le> f ?a" ..
      then show "f ?a \<in> ?H" ..
    qed
  qed
qed

end
