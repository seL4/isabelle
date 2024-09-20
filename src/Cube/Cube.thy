(*  Title:      Cube/Cube.thy
    Author:     Tobias Nipkow
*)

section \<open>Barendregt's Lambda-Cube\<close>

theory Cube
imports Pure
begin

setup Pure_Thy.old_appl_syntax_setup

named_theorems rules "Cube inference rules"

typedecl "term"
typedecl "context"
typedecl typing

axiomatization
  Abs :: "[term, term \<Rightarrow> term] \<Rightarrow> term" and
  Prod :: "[term, term \<Rightarrow> term] \<Rightarrow> term" and
  Trueprop :: "[context, typing] \<Rightarrow> prop" and
  MT_context :: "context" and
  Context :: "[typing, context] \<Rightarrow> context" and
  star :: "term"  (\<open>*\<close>) and
  box :: "term"  (\<open>\<box>\<close>) and
  app :: "[term, term] \<Rightarrow> term"  (infixl \<open>\<cdot>\<close> 20) and
  Has_type :: "[term, term] \<Rightarrow> typing"

nonterminal context' and typing'
syntax
  "_Trueprop" :: "[context', typing'] \<Rightarrow> prop"  (\<open>(_/ \<turnstile> _)\<close>)
  "_Trueprop1" :: "typing' \<Rightarrow> prop"  (\<open>(_)\<close>)
  "" :: "id \<Rightarrow> context'"  (\<open>_\<close>)
  "" :: "var \<Rightarrow> context'"  (\<open>_\<close>)
  "_MT_context" :: "context'"  (\<open>\<close>)
  "_Context" :: "[typing', context'] \<Rightarrow> context'"  (\<open>_ _\<close>)
  "_Has_type" :: "[term, term] \<Rightarrow> typing'"  (\<open>(_:/ _)\<close> [0, 0] 5)
  "_Lam" :: "[idt, term, term] \<Rightarrow> term"  (\<open>(3\<^bold>\<lambda>_:_./ _)\<close> [0, 0, 0] 10)
  "_Pi" :: "[idt, term, term] \<Rightarrow> term"  (\<open>(3\<Prod>_:_./ _)\<close> [0, 0] 10)
  "_arrow" :: "[term, term] \<Rightarrow> term"  (infixr \<open>\<rightarrow>\<close> 10)
syntax_consts
  "_Trueprop" \<rightleftharpoons> Trueprop and
  "_MT_context" \<rightleftharpoons> MT_context and
  "_Context" \<rightleftharpoons> Context and
  "_Has_type" \<rightleftharpoons> Has_type and
  "_Lam" \<rightleftharpoons> Abs and
  "_Pi" "_arrow" \<rightleftharpoons> Prod
translations
  "_Trueprop(G, t)" \<rightleftharpoons> "CONST Trueprop(G, t)"
  ("prop") "x:X" \<rightleftharpoons> ("prop") "\<turnstile> x:X"
  "_MT_context" \<rightleftharpoons> "CONST MT_context"
  "_Context" \<rightleftharpoons> "CONST Context"
  "_Has_type" \<rightleftharpoons> "CONST Has_type"
  "\<^bold>\<lambda>x:A. B" \<rightleftharpoons> "CONST Abs(A, \<lambda>x. B)"
  "\<Prod>x:A. B" \<rightharpoonup> "CONST Prod(A, \<lambda>x. B)"
  "A \<rightarrow> B" \<rightharpoonup> "CONST Prod(A, \<lambda>_. B)"
print_translation \<open>
  [(\<^const_syntax>\<open>Prod\<close>,
    fn _ => Syntax_Trans.dependent_tr' (\<^syntax_const>\<open>_Pi\<close>, \<^syntax_const>\<open>_arrow\<close>))]
\<close>

axiomatization where
  s_b: "*: \<box>"  and

  strip_s: "\<lbrakk>A:*; a:A \<Longrightarrow> G \<turnstile> x:X\<rbrakk> \<Longrightarrow> a:A G \<turnstile> x:X" and
  strip_b: "\<lbrakk>A:\<box>; a:A \<Longrightarrow> G \<turnstile> x:X\<rbrakk> \<Longrightarrow> a:A G \<turnstile> x:X" and

  app: "\<lbrakk>F:Prod(A, B); C:A\<rbrakk> \<Longrightarrow> F\<cdot>C: B(C)" and

  pi_ss: "\<lbrakk>A:*; \<And>x. x:A \<Longrightarrow> B(x):*\<rbrakk> \<Longrightarrow> Prod(A, B):*" and

  lam_ss: "\<lbrakk>A:*; \<And>x. x:A \<Longrightarrow> f(x):B(x); \<And>x. x:A \<Longrightarrow> B(x):* \<rbrakk>
            \<Longrightarrow> Abs(A, f) : Prod(A, B)" and

  beta: "Abs(A, f)\<cdot>a \<equiv> f(a)"

lemmas [rules] = s_b strip_s strip_b app lam_ss pi_ss

lemma imp_elim:
  assumes "f:A\<rightarrow>B" and "a:A" and "f\<cdot>a:B \<Longrightarrow> PROP P"
  shows "PROP P" by (rule app assms)+

lemma pi_elim:
  assumes "F:Prod(A,B)" and "a:A" and "F\<cdot>a:B(a) \<Longrightarrow> PROP P"
  shows "PROP P" by (rule app assms)+


locale L2 =
  assumes pi_bs: "\<lbrakk>A:\<box>; \<And>x. x:A \<Longrightarrow> B(x):*\<rbrakk> \<Longrightarrow> Prod(A,B):*"
    and lam_bs: "\<lbrakk>A:\<box>; \<And>x. x:A \<Longrightarrow> f(x):B(x); \<And>x. x:A \<Longrightarrow> B(x):*\<rbrakk>
                   \<Longrightarrow> Abs(A,f) : Prod(A,B)"
begin

lemmas [rules] = lam_bs pi_bs

end


locale Lomega =
  assumes
    pi_bb: "\<lbrakk>A:\<box>; \<And>x. x:A \<Longrightarrow> B(x):\<box>\<rbrakk> \<Longrightarrow> Prod(A,B):\<box>"
    and lam_bb: "\<lbrakk>A:\<box>; \<And>x. x:A \<Longrightarrow> f(x):B(x); \<And>x. x:A \<Longrightarrow> B(x):\<box>\<rbrakk>
                   \<Longrightarrow> Abs(A,f) : Prod(A,B)"
begin

lemmas [rules] = lam_bb pi_bb

end


locale LP =
  assumes pi_sb: "\<lbrakk>A:*; \<And>x. x:A \<Longrightarrow> B(x):\<box>\<rbrakk> \<Longrightarrow> Prod(A,B):\<box>"
    and lam_sb: "\<lbrakk>A:*; \<And>x. x:A \<Longrightarrow> f(x):B(x); \<And>x. x:A \<Longrightarrow> B(x):\<box>\<rbrakk>
                   \<Longrightarrow> Abs(A,f) : Prod(A,B)"
begin

lemmas [rules] = lam_sb pi_sb

end


locale LP2 = LP + L2
begin

lemmas [rules] = lam_bs pi_bs lam_sb pi_sb

end


locale Lomega2 = L2 + Lomega
begin

lemmas [rules] = lam_bs pi_bs lam_bb pi_bb

end


locale LPomega = LP + Lomega
begin

lemmas [rules] = lam_bb pi_bb lam_sb pi_sb

end


locale CC = L2 + LP + Lomega
begin

lemmas [rules] = lam_bs pi_bs lam_bb pi_bb lam_sb pi_sb

end

end
