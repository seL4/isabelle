(*  Title:      HOL/Isar_Examples/Hoare.thy
    Author:     Markus Wenzel, TU Muenchen

A formulation of Hoare logic suitable for Isar.
*)

header {* Hoare Logic *}

theory Hoare
imports Main
begin

subsection {* Abstract syntax and semantics *}

text {* The following abstract syntax and semantics of Hoare Logic
  over \texttt{WHILE} programs closely follows the existing tradition
  in Isabelle/HOL of formalizing the presentation given in
  \cite[\S6]{Winskel:1993}.  See also @{file "~~/src/HOL/Hoare"} and
  \cite{Nipkow:1998:Winskel}. *}

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"

datatype 'a com =
    Basic "'a => 'a"
  | Seq "'a com" "'a com"    ("(_;/ _)" [60, 61] 60)
  | Cond "'a bexp" "'a com" "'a com"
  | While "'a bexp" "'a assn" "'a com"

abbreviation Skip  ("SKIP")
  where "SKIP == Basic id"

type_synonym 'a sem = "'a => 'a => bool"

primrec iter :: "nat => 'a bexp => 'a sem => 'a sem"
where
  "iter 0 b S s s' = (s ~: b & s = s')"
| "iter (Suc n) b S s s' = (s : b & (EX s''. S s s'' & iter n b S s'' s'))"

primrec Sem :: "'a com => 'a sem"
where
  "Sem (Basic f) s s' = (s' = f s)"
| "Sem (c1; c2) s s' = (EX s''. Sem c1 s s'' & Sem c2 s'' s')"
| "Sem (Cond b c1 c2) s s' =
    (if s : b then Sem c1 s s' else Sem c2 s s')"
| "Sem (While b x c) s s' = (EX n. iter n b (Sem c) s s')"

definition Valid :: "'a bexp => 'a com => 'a bexp => bool"
    ("(3|- _/ (2_)/ _)" [100, 55, 100] 50)
  where "|- P c Q \<longleftrightarrow> (\<forall>s s'. Sem c s s' --> s : P --> s' : Q)"

notation (xsymbols) Valid  ("(3\<turnstile> _/ (2_)/ _)" [100, 55, 100] 50)

lemma ValidI [intro?]:
    "(!!s s'. Sem c s s' ==> s : P ==> s' : Q) ==> |- P c Q"
  by (simp add: Valid_def)

lemma ValidD [dest?]:
    "|- P c Q ==> Sem c s s' ==> s : P ==> s' : Q"
  by (simp add: Valid_def)


subsection {* Primitive Hoare rules *}

text {* From the semantics defined above, we derive the standard set
  of primitive Hoare rules; e.g.\ see \cite[\S6]{Winskel:1993}.
  Usually, variant forms of these rules are applied in actual proof,
  see also \S\ref{sec:hoare-isar} and \S\ref{sec:hoare-vcg}.

  \medskip The \name{basic} rule represents any kind of atomic access
  to the state space.  This subsumes the common rules of \name{skip}
  and \name{assign}, as formulated in \S\ref{sec:hoare-isar}. *}

theorem basic: "|- {s. f s : P} (Basic f) P"
proof
  fix s s' assume s: "s : {s. f s : P}"
  assume "Sem (Basic f) s s'"
  then have "s' = f s" by simp
  with s show "s' : P" by simp
qed

text {*
 The rules for sequential commands and semantic consequences are
 established in a straight forward manner as follows.
*}

theorem seq: "|- P c1 Q ==> |- Q c2 R ==> |- P (c1; c2) R"
proof
  assume cmd1: "|- P c1 Q" and cmd2: "|- Q c2 R"
  fix s s' assume s: "s : P"
  assume "Sem (c1; c2) s s'"
  then obtain s'' where sem1: "Sem c1 s s''" and sem2: "Sem c2 s'' s'"
    by auto
  from cmd1 sem1 s have "s'' : Q" ..
  with cmd2 sem2 show "s' : R" ..
qed

theorem conseq: "P' <= P ==> |- P c Q ==> Q <= Q' ==> |- P' c Q'"
proof
  assume P'P: "P' <= P" and QQ': "Q <= Q'"
  assume cmd: "|- P c Q"
  fix s s' :: 'a
  assume sem: "Sem c s s'"
  assume "s : P'" with P'P have "s : P" ..
  with cmd sem have "s' : Q" ..
  with QQ' show "s' : Q'" ..
qed

text {* The rule for conditional commands is directly reflected by the
  corresponding semantics; in the proof we just have to look closely
  which cases apply. *}

theorem cond:
  assumes case_b: "|- (P Int b) c1 Q"
    and case_nb: "|- (P Int -b) c2 Q"
  shows "|- P (Cond b c1 c2) Q"
proof
  fix s s' assume s: "s : P"
  assume sem: "Sem (Cond b c1 c2) s s'"
  show "s' : Q"
  proof cases
    assume b: "s : b"
    from case_b show ?thesis
    proof
      from sem b show "Sem c1 s s'" by simp
      from s b show "s : P Int b" by simp
    qed
  next
    assume nb: "s ~: b"
    from case_nb show ?thesis
    proof
      from sem nb show "Sem c2 s s'" by simp
      from s nb show "s : P Int -b" by simp
    qed
  qed
qed

text {* The @{text while} rule is slightly less trivial --- it is the
  only one based on recursion, which is expressed in the semantics by
  a Kleene-style least fixed-point construction.  The auxiliary
  statement below, which is by induction on the number of iterations
  is the main point to be proven; the rest is by routine application
  of the semantics of \texttt{WHILE}. *}

theorem while:
  assumes body: "|- (P Int b) c P"
  shows "|- P (While b X c) (P Int -b)"
proof
  fix s s' assume s: "s : P"
  assume "Sem (While b X c) s s'"
  then obtain n where "iter n b (Sem c) s s'" by auto
  from this and s show "s' : P Int -b"
  proof (induct n arbitrary: s)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then obtain s'' where b: "s : b" and sem: "Sem c s s''"
      and iter: "iter n b (Sem c) s'' s'" by auto
    from Suc and b have "s : P Int b" by simp
    with body sem have "s'' : P" ..
    with iter show ?case by (rule Suc)
  qed
qed


subsection {* Concrete syntax for assertions *}

text {* We now introduce concrete syntax for describing commands (with
  embedded expressions) and assertions. The basic technique is that of
  semantic ``quote-antiquote''.  A \emph{quotation} is a syntactic
  entity delimited by an implicit abstraction, say over the state
  space.  An \emph{antiquotation} is a marked expression within a
  quotation that refers the implicit argument; a typical antiquotation
  would select (or even update) components from the state.

  We will see some examples later in the concrete rules and
  applications. *}

text {* The following specification of syntax and translations is for
  Isabelle experts only; feel free to ignore it.

  While the first part is still a somewhat intelligible specification
  of the concrete syntactic representation of our Hoare language, the
  actual ``ML drivers'' is quite involved.  Just note that the we
  re-use the basic quote/antiquote translations as already defined in
  Isabelle/Pure (see @{ML Syntax_Trans.quote_tr}, and
  @{ML Syntax_Trans.quote_tr'},). *}

syntax
  "_quote"       :: "'b => ('a => 'b)"       ("(.'(_').)" [0] 1000)
  "_antiquote"   :: "('a => 'b) => 'b"       ("\<acute>_" [1000] 1000)
  "_Subst"       :: "'a bexp \<Rightarrow> 'b \<Rightarrow> idt \<Rightarrow> 'a bexp"
        ("_[_'/\<acute>_]" [1000] 999)
  "_Assert"      :: "'a => 'a set"           ("(.{_}.)" [0] 1000)
  "_Assign"      :: "idt => 'b => 'a com"    ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_Cond"        :: "'a bexp => 'a com => 'a com => 'a com"
        ("(0IF _/ THEN _/ ELSE _/ FI)" [0, 0, 0] 61)
  "_While_inv"   :: "'a bexp => 'a assn => 'a com => 'a com"
        ("(0WHILE _/ INV _ //DO _ /OD)"  [0, 0, 0] 61)
  "_While"       :: "'a bexp => 'a com => 'a com"
        ("(0WHILE _ //DO _ /OD)"  [0, 0] 61)

syntax (xsymbols)
  "_Assert"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)

translations
  ".{b}."                   => "CONST Collect .(b)."
  "B [a/\<acute>x]"                => ".{\<acute>(_update_name x (\<lambda>_. a)) \<in> B}."
  "\<acute>x := a"                 => "CONST Basic .(\<acute>(_update_name x (\<lambda>_. a)))."
  "IF b THEN c1 ELSE c2 FI" => "CONST Cond .{b}. c1 c2"
  "WHILE b INV i DO c OD"   => "CONST While .{b}. i c"
  "WHILE b DO c OD"         == "WHILE b INV CONST undefined DO c OD"

parse_translation {*
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, quote_tr)] end
*}

text {* As usual in Isabelle syntax translations, the part for
  printing is more complicated --- we cannot express parts as macro
  rules as above.  Don't look here, unless you have to do similar
  things for yourself. *}

print_translation {*
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

    fun bexp_tr' name ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(@{const_syntax Collect}, assert_tr'),
    (@{const_syntax Basic}, assign_tr'),
    (@{const_syntax Cond}, bexp_tr' @{syntax_const "_Cond"}),
    (@{const_syntax While}, bexp_tr' @{syntax_const "_While_inv"})]
  end
*}


subsection {* Rules for single-step proof \label{sec:hoare-isar} *}

text {* We are now ready to introduce a set of Hoare rules to be used
  in single-step structured proofs in Isabelle/Isar.  We refer to the
  concrete syntax introduce above.

  \medskip Assertions of Hoare Logic may be manipulated in
  calculational proofs, with the inclusion expressed in terms of sets
  or predicates.  Reversed order is supported as well. *}

lemma [trans]: "|- P c Q ==> P' <= P ==> |- P' c Q"
  by (unfold Valid_def) blast
lemma [trans] : "P' <= P ==> |- P c Q ==> |- P' c Q"
  by (unfold Valid_def) blast

lemma [trans]: "Q <= Q' ==> |- P c Q ==> |- P c Q'"
  by (unfold Valid_def) blast
lemma [trans]: "|- P c Q ==> Q <= Q' ==> |- P c Q'"
  by (unfold Valid_def) blast

lemma [trans]:
    "|- .{\<acute>P}. c Q ==> (!!s. P' s --> P s) ==> |- .{\<acute>P'}. c Q"
  by (simp add: Valid_def)
lemma [trans]:
    "(!!s. P' s --> P s) ==> |- .{\<acute>P}. c Q ==> |- .{\<acute>P'}. c Q"
  by (simp add: Valid_def)

lemma [trans]:
    "|- P c .{\<acute>Q}. ==> (!!s. Q s --> Q' s) ==> |- P c .{\<acute>Q'}."
  by (simp add: Valid_def)
lemma [trans]:
    "(!!s. Q s --> Q' s) ==> |- P c .{\<acute>Q}. ==> |- P c .{\<acute>Q'}."
  by (simp add: Valid_def)


text {* Identity and basic assignments.\footnote{The $\idt{hoare}$
  method introduced in \S\ref{sec:hoare-vcg} is able to provide proper
  instances for any number of basic assignments, without producing
  additional verification conditions.} *}

lemma skip [intro?]: "|- P SKIP P"
proof -
  have "|- {s. id s : P} SKIP P" by (rule basic)
  then show ?thesis by simp
qed

lemma assign: "|- P [\<acute>a/\<acute>x::'a] \<acute>x := \<acute>a P"
  by (rule basic)

text {* Note that above formulation of assignment corresponds to our
  preferred way to model state spaces, using (extensible) record types
  in HOL \cite{Naraschewski-Wenzel:1998:HOOL}.  For any record field
  $x$, Isabelle/HOL provides a functions $x$ (selector) and
  $\idt{x{\dsh}update}$ (update).  Above, there is only a place-holder
  appearing for the latter kind of function: due to concrete syntax
  \isa{\'x := \'a} also contains \isa{x\_update}.\footnote{Note that
  due to the external nature of HOL record fields, we could not even
  state a general theorem relating selector and update functions (if
  this were required here); this would only work for any particular
  instance of record fields introduced so far.} *}

text {* Sequential composition --- normalizing with associativity
  achieves proper of chunks of code verified separately. *}

lemmas [trans, intro?] = seq

lemma seq_assoc [simp]: "( |- P c1;(c2;c3) Q) = ( |- P (c1;c2);c3 Q)"
  by (auto simp add: Valid_def)

text {* Conditional statements. *}

lemmas [trans, intro?] = cond

lemma [trans, intro?]:
  "|- .{\<acute>P & \<acute>b}. c1 Q
      ==> |- .{\<acute>P & ~ \<acute>b}. c2 Q
      ==> |- .{\<acute>P}. IF \<acute>b THEN c1 ELSE c2 FI Q"
    by (rule cond) (simp_all add: Valid_def)

text {* While statements --- with optional invariant. *}

lemma [intro?]:
    "|- (P Int b) c P ==> |- P (While b P c) (P Int -b)"
  by (rule while)

lemma [intro?]:
    "|- (P Int b) c P ==> |- P (While b undefined c) (P Int -b)"
  by (rule while)


lemma [intro?]:
  "|- .{\<acute>P & \<acute>b}. c .{\<acute>P}.
    ==> |- .{\<acute>P}. WHILE \<acute>b INV .{\<acute>P}. DO c OD .{\<acute>P & ~ \<acute>b}."
  by (simp add: while Collect_conj_eq Collect_neg_eq)

lemma [intro?]:
  "|- .{\<acute>P & \<acute>b}. c .{\<acute>P}.
    ==> |- .{\<acute>P}. WHILE \<acute>b DO c OD .{\<acute>P & ~ \<acute>b}."
  by (simp add: while Collect_conj_eq Collect_neg_eq)


subsection {* Verification conditions \label{sec:hoare-vcg} *}

text {* We now load the \emph{original} ML file for proof scripts and
  tactic definition for the Hoare Verification Condition Generator
  (see @{file "~~/src/HOL/Hoare/"}).  As far as we
  are concerned here, the result is a proof method \name{hoare}, which
  may be applied to a Hoare Logic assertion to extract purely logical
  verification conditions.  It is important to note that the method
  requires \texttt{WHILE} loops to be fully annotated with invariants
  beforehand.  Furthermore, only \emph{concrete} pieces of code are
  handled --- the underlying tactic fails ungracefully if supplied
  with meta-variables or parameters, for example. *}

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
  "\<forall>s s'. Sem c s s' --> s : I & s : b --> s' : I ==>
       (\<And>s s'. s : I \<Longrightarrow> iter n b (Sem c) s s' \<Longrightarrow> s' : I & s' ~: b)"
  apply(induct n)
   apply clarsimp
   apply (simp (no_asm_use))
   apply blast
  done

lemma WhileRule:
    "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i c) q"
  apply (clarsimp simp: Valid_def)
  apply (drule iter_aux)
    prefer 2
    apply assumption
   apply blast
  apply blast
  done

lemma Compl_Collect: "- Collect b = {x. \<not> b x}"
  by blast

lemmas AbortRule = SkipRule  -- "dummy version"

ML_file "~~/src/HOL/Hoare/hoare_tac.ML"

method_setup hoare = {*
  Scan.succeed (fn ctxt =>
    (SIMPLE_METHOD'
       (hoare_tac ctxt (simp_tac (HOL_basic_ss addsimps [@{thm "Record.K_record_comp"}] ))))) *}
  "verification condition generator for Hoare logic"

end
