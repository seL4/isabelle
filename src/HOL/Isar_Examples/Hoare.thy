(*  Title:      HOL/Isar_Examples/Hoare.thy
    Author:     Makarius

A formulation of Hoare logic suitable for Isar.
*)

section \<open>Hoare Logic\<close>

theory Hoare
  imports "HOL-Hoare.Hoare_Tac"
begin

subsection \<open>Abstract syntax and semantics\<close>

text \<open>
  The following abstract syntax and semantics of Hoare Logic over \<^verbatim>\<open>WHILE\<close>
  programs closely follows the existing tradition in Isabelle/HOL of
  formalizing the presentation given in @{cite \<open>\S6\<close> "Winskel:1993"}. See also
  \<^dir>\<open>~~/src/HOL/Hoare\<close> and @{cite "Nipkow:1998:Winskel"}.
\<close>

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"
type_synonym 'a var = "'a \<Rightarrow> nat"

datatype 'a com =
    Basic "'a \<Rightarrow> 'a"
  | Seq "'a com" "'a com"    ("(_;/ _)" [60, 61] 60)
  | Cond "'a bexp" "'a com" "'a com"
  | While "'a bexp" "'a assn" "'a var" "'a com"

abbreviation Skip  ("SKIP")
  where "SKIP \<equiv> Basic id"

type_synonym 'a sem = "'a \<Rightarrow> 'a \<Rightarrow> bool"

primrec iter :: "nat \<Rightarrow> 'a bexp \<Rightarrow> 'a sem \<Rightarrow> 'a sem"
  where
    "iter 0 b S s s' \<longleftrightarrow> s \<notin> b \<and> s = s'"
  | "iter (Suc n) b S s s' \<longleftrightarrow> s \<in> b \<and> (\<exists>s''. S s s'' \<and> iter n b S s'' s')"

primrec Sem :: "'a com \<Rightarrow> 'a sem"
  where
    "Sem (Basic f) s s' \<longleftrightarrow> s' = f s"
  | "Sem (c1; c2) s s' \<longleftrightarrow> (\<exists>s''. Sem c1 s s'' \<and> Sem c2 s'' s')"
  | "Sem (Cond b c1 c2) s s' \<longleftrightarrow> (if s \<in> b then Sem c1 s s' else Sem c2 s s')"
  | "Sem (While b x y c) s s' \<longleftrightarrow> (\<exists>n. iter n b (Sem c) s s')"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"  ("(3\<turnstile> _/ (2_)/ _)" [100, 55, 100] 50)
  where "\<turnstile> P c Q \<longleftrightarrow> (\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> P \<longrightarrow> s' \<in> Q)"

lemma ValidI [intro?]: "(\<And>s s'. Sem c s s' \<Longrightarrow> s \<in> P \<Longrightarrow> s' \<in> Q) \<Longrightarrow> \<turnstile> P c Q"
  by (simp add: Valid_def)

lemma ValidD [dest?]: "\<turnstile> P c Q \<Longrightarrow> Sem c s s' \<Longrightarrow> s \<in> P \<Longrightarrow> s' \<in> Q"
  by (simp add: Valid_def)


subsection \<open>Primitive Hoare rules\<close>

text \<open>
  From the semantics defined above, we derive the standard set of primitive
  Hoare rules; e.g.\ see @{cite \<open>\S6\<close> "Winskel:1993"}. Usually, variant forms
  of these rules are applied in actual proof, see also \S\ref{sec:hoare-isar}
  and \S\ref{sec:hoare-vcg}.

  \<^medskip>
  The \<open>basic\<close> rule represents any kind of atomic access to the state space.
  This subsumes the common rules of \<open>skip\<close> and \<open>assign\<close>, as formulated in
  \S\ref{sec:hoare-isar}.
\<close>

theorem basic: "\<turnstile> {s. f s \<in> P} (Basic f) P"
proof
  fix s s'
  assume s: "s \<in> {s. f s \<in> P}"
  assume "Sem (Basic f) s s'"
  then have "s' = f s" by simp
  with s show "s' \<in> P" by simp
qed

text \<open>
  The rules for sequential commands and semantic consequences are established
  in a straight forward manner as follows.
\<close>

theorem seq: "\<turnstile> P c1 Q \<Longrightarrow> \<turnstile> Q c2 R \<Longrightarrow> \<turnstile> P (c1; c2) R"
proof
  assume cmd1: "\<turnstile> P c1 Q" and cmd2: "\<turnstile> Q c2 R"
  fix s s'
  assume s: "s \<in> P"
  assume "Sem (c1; c2) s s'"
  then obtain s'' where sem1: "Sem c1 s s''" and sem2: "Sem c2 s'' s'"
    by auto
  from cmd1 sem1 s have "s'' \<in> Q" ..
  with cmd2 sem2 show "s' \<in> R" ..
qed

theorem conseq: "P' \<subseteq> P \<Longrightarrow> \<turnstile> P c Q \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> \<turnstile> P' c Q'"
proof
  assume P'P: "P' \<subseteq> P" and QQ': "Q \<subseteq> Q'"
  assume cmd: "\<turnstile> P c Q"
  fix s s' :: 'a
  assume sem: "Sem c s s'"
  assume "s \<in> P'" with P'P have "s \<in> P" ..
  with cmd sem have "s' \<in> Q" ..
  with QQ' show "s' \<in> Q'" ..
qed

text \<open>
  The rule for conditional commands is directly reflected by the corresponding
  semantics; in the proof we just have to look closely which cases apply.
\<close>

theorem cond:
  assumes case_b: "\<turnstile> (P \<inter> b) c1 Q"
    and case_nb: "\<turnstile> (P \<inter> -b) c2 Q"
  shows "\<turnstile> P (Cond b c1 c2) Q"
proof
  fix s s'
  assume s: "s \<in> P"
  assume sem: "Sem (Cond b c1 c2) s s'"
  show "s' \<in> Q"
  proof cases
    assume b: "s \<in> b"
    from case_b show ?thesis
    proof
      from sem b show "Sem c1 s s'" by simp
      from s b show "s \<in> P \<inter> b" by simp
    qed
  next
    assume nb: "s \<notin> b"
    from case_nb show ?thesis
    proof
      from sem nb show "Sem c2 s s'" by simp
      from s nb show "s \<in> P \<inter> -b" by simp
    qed
  qed
qed

text \<open>
  The \<open>while\<close> rule is slightly less trivial --- it is the only one based on
  recursion, which is expressed in the semantics by a Kleene-style least
  fixed-point construction. The auxiliary statement below, which is by
  induction on the number of iterations is the main point to be proven; the
  rest is by routine application of the semantics of \<^verbatim>\<open>WHILE\<close>.
\<close>

theorem while:
  assumes body: "\<turnstile> (P \<inter> b) c P"
  shows "\<turnstile> P (While b X Y c) (P \<inter> -b)"
proof
  fix s s' assume s: "s \<in> P"
  assume "Sem (While b X Y c) s s'"
  then obtain n where "iter n b (Sem c) s s'" by auto
  from this and s show "s' \<in> P \<inter> -b"
  proof (induct n arbitrary: s)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then obtain s'' where b: "s \<in> b" and sem: "Sem c s s''"
      and iter: "iter n b (Sem c) s'' s'" by auto
    from Suc and b have "s \<in> P \<inter> b" by simp
    with body sem have "s'' \<in> P" ..
    with iter show ?case by (rule Suc)
  qed
qed


subsection \<open>Concrete syntax for assertions\<close>

text \<open>
  We now introduce concrete syntax for describing commands (with embedded
  expressions) and assertions. The basic technique is that of semantic
  ``quote-antiquote''. A \<^emph>\<open>quotation\<close> is a syntactic entity delimited by an
  implicit abstraction, say over the state space. An \<^emph>\<open>antiquotation\<close> is a
  marked expression within a quotation that refers the implicit argument; a
  typical antiquotation would select (or even update) components from the
  state.

  We will see some examples later in the concrete rules and applications.

  \<^medskip>
  The following specification of syntax and translations is for Isabelle
  experts only; feel free to ignore it.

  While the first part is still a somewhat intelligible specification of the
  concrete syntactic representation of our Hoare language, the actual ``ML
  drivers'' is quite involved. Just note that the we re-use the basic
  quote/antiquote translations as already defined in Isabelle/Pure (see \<^ML>\<open>Syntax_Trans.quote_tr\<close>, and \<^ML>\<open>Syntax_Trans.quote_tr'\<close>,).
\<close>

syntax
  "_quote" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"  ("\<acute>_" [1000] 1000)
  "_Subst" :: "'a bexp \<Rightarrow> 'b \<Rightarrow> idt \<Rightarrow> 'a bexp"  ("_[_'/\<acute>_]" [1000] 999)
  "_Assert" :: "'a \<Rightarrow> 'a set"  ("(\<lbrace>_\<rbrace>)" [0] 1000)
  "_Assign" :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"  ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_Cond" :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"
    ("(0IF _/ THEN _/ ELSE _/ FI)" [0, 0, 0] 61)
  "_While_inv" :: "'a bexp \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com"
    ("(0WHILE _/ INV _ //DO _ /OD)"  [0, 0, 0] 61)
  "_While" :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("(0WHILE _ //DO _ /OD)"  [0, 0] 61)

translations
  "\<lbrace>b\<rbrace>" \<rightharpoonup> "CONST Collect (_quote b)"
  "B [a/\<acute>x]" \<rightharpoonup> "\<lbrace>\<acute>(_update_name x (\<lambda>_. a)) \<in> B\<rbrace>"
  "\<acute>x := a" \<rightharpoonup> "CONST Basic (_quote (\<acute>(_update_name x (\<lambda>_. a))))"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cond \<lbrace>b\<rbrace> c1 c2"
  "WHILE b INV i DO c OD" \<rightharpoonup> "CONST While \<lbrace>b\<rbrace> i (\<lambda>_. 0) c"
  "WHILE b DO c OD" \<rightleftharpoons> "WHILE b INV CONST undefined DO c OD"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr \<^syntax_const>\<open>_antiquote\<close> t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

text \<open>
  As usual in Isabelle syntax translations, the part for printing is more
  complicated --- we cannot express parts as macro rules as above. Don't look
  here, unless you have to do similar things for yourself.
\<close>

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' \<^syntax_const>\<open>_antiquote\<close> t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const \<^syntax_const>\<open>_Assert\<close>);

    fun bexp_tr' name ((Const (\<^const_syntax>\<open>Collect\<close>, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const \<^syntax_const>\<open>_Assign\<close> $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(\<^const_syntax>\<open>Collect\<close>, K assert_tr'),
    (\<^const_syntax>\<open>Basic\<close>, K assign_tr'),
    (\<^const_syntax>\<open>Cond\<close>, K (bexp_tr' \<^syntax_const>\<open>_Cond\<close>)),
    (\<^const_syntax>\<open>While\<close>, K (bexp_tr' \<^syntax_const>\<open>_While_inv\<close>))]
  end
\<close>


subsection \<open>Rules for single-step proof \label{sec:hoare-isar}\<close>

text \<open>
  We are now ready to introduce a set of Hoare rules to be used in single-step
  structured proofs in Isabelle/Isar. We refer to the concrete syntax
  introduce above.

  \<^medskip>
  Assertions of Hoare Logic may be manipulated in calculational proofs, with
  the inclusion expressed in terms of sets or predicates. Reversed order is
  supported as well.
\<close>

lemma [trans]: "\<turnstile> P c Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> \<turnstile> P' c Q"
  by (unfold Valid_def) blast
lemma [trans] : "P' \<subseteq> P \<Longrightarrow> \<turnstile> P c Q \<Longrightarrow> \<turnstile> P' c Q"
  by (unfold Valid_def) blast

lemma [trans]: "Q \<subseteq> Q' \<Longrightarrow> \<turnstile> P c Q \<Longrightarrow> \<turnstile> P c Q'"
  by (unfold Valid_def) blast
lemma [trans]: "\<turnstile> P c Q \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> \<turnstile> P c Q'"
  by (unfold Valid_def) blast

lemma [trans]:
    "\<turnstile> \<lbrace>\<acute>P\<rbrace> c Q \<Longrightarrow> (\<And>s. P' s \<longrightarrow> P s) \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P'\<rbrace> c Q"
  by (simp add: Valid_def)
lemma [trans]:
    "(\<And>s. P' s \<longrightarrow> P s) \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P\<rbrace> c Q \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P'\<rbrace> c Q"
  by (simp add: Valid_def)

lemma [trans]:
    "\<turnstile> P c \<lbrace>\<acute>Q\<rbrace> \<Longrightarrow> (\<And>s. Q s \<longrightarrow> Q' s) \<Longrightarrow> \<turnstile> P c \<lbrace>\<acute>Q'\<rbrace>"
  by (simp add: Valid_def)
lemma [trans]:
    "(\<And>s. Q s \<longrightarrow> Q' s) \<Longrightarrow> \<turnstile> P c \<lbrace>\<acute>Q\<rbrace> \<Longrightarrow> \<turnstile> P c \<lbrace>\<acute>Q'\<rbrace>"
  by (simp add: Valid_def)


text \<open>
  Identity and basic assignments.\<^footnote>\<open>The \<open>hoare\<close> method introduced in
  \S\ref{sec:hoare-vcg} is able to provide proper instances for any number of
  basic assignments, without producing additional verification conditions.\<close>
\<close>

lemma skip [intro?]: "\<turnstile> P SKIP P"
proof -
  have "\<turnstile> {s. id s \<in> P} SKIP P" by (rule basic)
  then show ?thesis by simp
qed

lemma assign: "\<turnstile> P [\<acute>a/\<acute>x::'a] \<acute>x := \<acute>a P"
  by (rule basic)

text \<open>
  Note that above formulation of assignment corresponds to our preferred way
  to model state spaces, using (extensible) record types in HOL @{cite
  "Naraschewski-Wenzel:1998:HOOL"}. For any record field \<open>x\<close>, Isabelle/HOL
  provides a functions \<open>x\<close> (selector) and \<open>x_update\<close> (update). Above, there is
  only a place-holder appearing for the latter kind of function: due to
  concrete syntax \<open>\<acute>x := \<acute>a\<close> also contains \<open>x_update\<close>.\<^footnote>\<open>Note that due to the
  external nature of HOL record fields, we could not even state a general
  theorem relating selector and update functions (if this were required here);
  this would only work for any particular instance of record fields introduced
  so far.\<close>

  \<^medskip>
  Sequential composition --- normalizing with associativity achieves proper of
  chunks of code verified separately.
\<close>

lemmas [trans, intro?] = seq

lemma seq_assoc [simp]: "\<turnstile> P c1;(c2;c3) Q \<longleftrightarrow> \<turnstile> P (c1;c2);c3 Q"
  by (auto simp add: Valid_def)

text \<open>Conditional statements.\<close>

lemmas [trans, intro?] = cond

lemma [trans, intro?]:
  "\<turnstile> \<lbrace>\<acute>P \<and> \<acute>b\<rbrace> c1 Q
      \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P \<and> \<not> \<acute>b\<rbrace> c2 Q
      \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P\<rbrace> IF \<acute>b THEN c1 ELSE c2 FI Q"
    by (rule cond) (simp_all add: Valid_def)

text \<open>While statements --- with optional invariant.\<close>

lemma [intro?]: "\<turnstile> (P \<inter> b) c P \<Longrightarrow> \<turnstile> P (While b P V c) (P \<inter> -b)"
  by (rule while)

lemma [intro?]: "\<turnstile> (P \<inter> b) c P \<Longrightarrow> \<turnstile> P (While b undefined V c) (P \<inter> -b)"
  by (rule while)


lemma [intro?]:
  "\<turnstile> \<lbrace>\<acute>P \<and> \<acute>b\<rbrace> c \<lbrace>\<acute>P\<rbrace>
    \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P\<rbrace> WHILE \<acute>b INV \<lbrace>\<acute>P\<rbrace> DO c OD \<lbrace>\<acute>P \<and> \<not> \<acute>b\<rbrace>"
  by (simp add: while Collect_conj_eq Collect_neg_eq)

lemma [intro?]:
  "\<turnstile> \<lbrace>\<acute>P \<and> \<acute>b\<rbrace> c \<lbrace>\<acute>P\<rbrace>
    \<Longrightarrow> \<turnstile> \<lbrace>\<acute>P\<rbrace> WHILE \<acute>b DO c OD \<lbrace>\<acute>P \<and> \<not> \<acute>b\<rbrace>"
  by (simp add: while Collect_conj_eq Collect_neg_eq)


subsection \<open>Verification conditions \label{sec:hoare-vcg}\<close>

text \<open>
  We now load the \<^emph>\<open>original\<close> ML file for proof scripts and tactic definition
  for the Hoare Verification Condition Generator (see \<^dir>\<open>~~/src/HOL/Hoare\<close>).
  As far as we are concerned here, the result is a proof method \<open>hoare\<close>, which
  may be applied to a Hoare Logic assertion to extract purely logical
  verification conditions. It is important to note that the method requires
  \<^verbatim>\<open>WHILE\<close> loops to be fully annotated with invariants beforehand.
  Furthermore, only \<^emph>\<open>concrete\<close> pieces of code are handled --- the underlying
  tactic fails ungracefully if supplied with meta-variables or parameters, for
  example.
\<close>

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
  by (auto simp add: Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
  by (auto simp: Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1;c2) R"
  by (auto simp: Valid_def)

lemma CondRule:
  "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
    \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
  by (auto simp: Valid_def)

lemma iter_aux:
  "\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> I \<and> s \<in> b \<longrightarrow> s' \<in> I \<Longrightarrow>
       (\<And>s s'. s \<in> I \<Longrightarrow> iter n b (Sem c) s s' \<Longrightarrow> s' \<in> I \<and> s' \<notin> b)"
  by (induct n) auto

lemma WhileRule:
    "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i v c) q"
  apply (clarsimp simp: Valid_def)
  apply (drule iter_aux)
    prefer 2
    apply assumption
   apply blast
  apply blast
  done

declare BasicRule [Hoare_Tac.BasicRule]
  and SkipRule [Hoare_Tac.SkipRule]
  and SeqRule [Hoare_Tac.SeqRule]
  and CondRule [Hoare_Tac.CondRule]
  and WhileRule [Hoare_Tac.WhileRule]

method_setup hoare =
  \<open>Scan.succeed (fn ctxt =>
    (SIMPLE_METHOD'
      (Hoare_Tac.hoare_tac ctxt
        (simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm "Record.K_record_comp"}] )))))\<close>
  "verification condition generator for Hoare logic"

end
