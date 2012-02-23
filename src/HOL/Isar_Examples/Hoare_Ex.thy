header {* Using Hoare Logic *}

theory Hoare_Ex
imports Hoare
begin

subsection {* State spaces *}

text {* First of all we provide a store of program variables that
  occur in any of the programs considered later.  Slightly unexpected
  things may happen when attempting to work with undeclared variables. *}

record vars =
  I :: nat
  M :: nat
  N :: nat
  S :: nat

text {* While all of our variables happen to have the same type,
  nothing would prevent us from working with many-sorted programs as
  well, or even polymorphic ones.  Also note that Isabelle/HOL's
  extensible record types even provides simple means to extend the
  state space later. *}


subsection {* Basic examples *}

text {* We look at few trivialities involving assignment and
  sequential composition, in order to get an idea of how to work with
  our formulation of Hoare Logic. *}

text {* Using the basic @{text assign} rule directly is a bit
  cumbersome. *}

lemma "|- .{\<acute>(N_update (\<lambda>_. (2 * \<acute>N))) : .{\<acute>N = 10}.}. \<acute>N := 2 * \<acute>N .{\<acute>N = 10}."
  by (rule assign)

text {* Certainly we want the state modification already done, e.g.\
  by simplification.  The \name{hoare} method performs the basic state
  update for us; we may apply the Simplifier afterwards to achieve
  ``obvious'' consequences as well. *}

lemma "|- .{True}. \<acute>N := 10 .{\<acute>N = 10}."
  by hoare

lemma "|- .{2 * \<acute>N = 10}. \<acute>N := 2 * \<acute>N .{\<acute>N = 10}."
  by hoare

lemma "|- .{\<acute>N = 5}. \<acute>N := 2 * \<acute>N .{\<acute>N = 10}."
  by hoare simp

lemma "|- .{\<acute>N + 1 = a + 1}. \<acute>N := \<acute>N + 1 .{\<acute>N = a + 1}."
  by hoare

lemma "|- .{\<acute>N = a}. \<acute>N := \<acute>N + 1 .{\<acute>N = a + 1}."
  by hoare simp

lemma "|- .{a = a & b = b}. \<acute>M := a; \<acute>N := b .{\<acute>M = a & \<acute>N = b}."
  by hoare

lemma "|- .{True}. \<acute>M := a; \<acute>N := b .{\<acute>M = a & \<acute>N = b}."
  by hoare simp

lemma
  "|- .{\<acute>M = a & \<acute>N = b}.
      \<acute>I := \<acute>M; \<acute>M := \<acute>N; \<acute>N := \<acute>I
      .{\<acute>M = b & \<acute>N = a}."
  by hoare simp

text {* It is important to note that statements like the following one
  can only be proven for each individual program variable.  Due to the
  extra-logical nature of record fields, we cannot formulate a theorem
  relating record selectors and updates schematically. *}

lemma "|- .{\<acute>N = a}. \<acute>N := \<acute>N .{\<acute>N = a}."
  by hoare

lemma "|- .{\<acute>x = a}. \<acute>x := \<acute>x .{\<acute>x = a}."
  oops

lemma
  "Valid {s. x s = a} (Basic (\<lambda>s. x_update (x s) s)) {s. x s = n}"
  -- {* same statement without concrete syntax *}
  oops


text {* In the following assignments we make use of the consequence
  rule in order to achieve the intended precondition.  Certainly, the
  \name{hoare} method is able to handle this case, too. *}

lemma "|- .{\<acute>M = \<acute>N}. \<acute>M := \<acute>M + 1 .{\<acute>M ~= \<acute>N}."
proof -
  have ".{\<acute>M = \<acute>N}. <= .{\<acute>M + 1 ~= \<acute>N}."
    by auto
  also have "|- ... \<acute>M := \<acute>M + 1 .{\<acute>M ~= \<acute>N}."
    by hoare
  finally show ?thesis .
qed

lemma "|- .{\<acute>M = \<acute>N}. \<acute>M := \<acute>M + 1 .{\<acute>M ~= \<acute>N}."
proof -
  have "!!m n::nat. m = n --> m + 1 ~= n"
      -- {* inclusion of assertions expressed in ``pure'' logic, *}
      -- {* without mentioning the state space *}
    by simp
  also have "|- .{\<acute>M + 1 ~= \<acute>N}. \<acute>M := \<acute>M + 1 .{\<acute>M ~= \<acute>N}."
    by hoare
  finally show ?thesis .
qed

lemma "|- .{\<acute>M = \<acute>N}. \<acute>M := \<acute>M + 1 .{\<acute>M ~= \<acute>N}."
  by hoare simp


subsection {* Multiplication by addition *}

text {* We now do some basic examples of actual \texttt{WHILE}
  programs.  This one is a loop for calculating the product of two
  natural numbers, by iterated addition.  We first give detailed
  structured proof based on single-step Hoare rules. *}

lemma
  "|- .{\<acute>M = 0 & \<acute>S = 0}.
      WHILE \<acute>M ~= a
      DO \<acute>S := \<acute>S + b; \<acute>M := \<acute>M + 1 OD
      .{\<acute>S = a * b}."
proof -
  let "|- _ ?while _" = ?thesis
  let ".{\<acute>?inv}." = ".{\<acute>S = \<acute>M * b}."

  have ".{\<acute>M = 0 & \<acute>S = 0}. <= .{\<acute>?inv}." by auto
  also have "|- ... ?while .{\<acute>?inv & ~ (\<acute>M ~= a)}."
  proof
    let ?c = "\<acute>S := \<acute>S + b; \<acute>M := \<acute>M + 1"
    have ".{\<acute>?inv & \<acute>M ~= a}. <= .{\<acute>S + b = (\<acute>M + 1) * b}."
      by auto
    also have "|- ... ?c .{\<acute>?inv}." by hoare
    finally show "|- .{\<acute>?inv & \<acute>M ~= a}. ?c .{\<acute>?inv}." .
  qed
  also have "... <= .{\<acute>S = a * b}." by auto
  finally show ?thesis .
qed

text {* The subsequent version of the proof applies the @{text hoare}
  method to reduce the Hoare statement to a purely logical problem
  that can be solved fully automatically.  Note that we have to
  specify the \texttt{WHILE} loop invariant in the original statement. *}

lemma
  "|- .{\<acute>M = 0 & \<acute>S = 0}.
      WHILE \<acute>M ~= a
      INV .{\<acute>S = \<acute>M * b}.
      DO \<acute>S := \<acute>S + b; \<acute>M := \<acute>M + 1 OD
      .{\<acute>S = a * b}."
  by hoare auto


subsection {* Summing natural numbers *}

text {* We verify an imperative program to sum natural numbers up to a
  given limit.  First some functional definition for proper
  specification of the problem. *}

text {* The following proof is quite explicit in the individual steps
  taken, with the \name{hoare} method only applied locally to take
  care of assignment and sequential composition.  Note that we express
  intermediate proof obligation in pure logic, without referring to
  the state space. *}

theorem
  "|- .{True}.
      \<acute>S := 0; \<acute>I := 1;
      WHILE \<acute>I ~= n
      DO
        \<acute>S := \<acute>S + \<acute>I;
        \<acute>I := \<acute>I + 1
      OD
      .{\<acute>S = (SUM j<n. j)}."
  (is "|- _ (_; ?while) _")
proof -
  let ?sum = "\<lambda>k::nat. SUM j<k. j"
  let ?inv = "\<lambda>s i::nat. s = ?sum i"

  have "|- .{True}. \<acute>S := 0; \<acute>I := 1 .{?inv \<acute>S \<acute>I}."
  proof -
    have "True --> 0 = ?sum 1"
      by simp
    also have "|- .{...}. \<acute>S := 0; \<acute>I := 1 .{?inv \<acute>S \<acute>I}."
      by hoare
    finally show ?thesis .
  qed
  also have "|- ... ?while .{?inv \<acute>S \<acute>I & ~ \<acute>I ~= n}."
  proof
    let ?body = "\<acute>S := \<acute>S + \<acute>I; \<acute>I := \<acute>I + 1"
    have "!!s i. ?inv s i & i ~= n -->  ?inv (s + i) (i + 1)"
      by simp
    also have "|- .{\<acute>S + \<acute>I = ?sum (\<acute>I + 1)}. ?body .{?inv \<acute>S \<acute>I}."
      by hoare
    finally show "|- .{?inv \<acute>S \<acute>I & \<acute>I ~= n}. ?body .{?inv \<acute>S \<acute>I}." .
  qed
  also have "!!s i. s = ?sum i & ~ i ~= n --> s = ?sum n"
    by simp
  finally show ?thesis .
qed

text {* The next version uses the @{text hoare} method, while still
  explaining the resulting proof obligations in an abstract,
  structured manner. *}

theorem
  "|- .{True}.
      \<acute>S := 0; \<acute>I := 1;
      WHILE \<acute>I ~= n
      INV .{\<acute>S = (SUM j<\<acute>I. j)}.
      DO
        \<acute>S := \<acute>S + \<acute>I;
        \<acute>I := \<acute>I + 1
      OD
      .{\<acute>S = (SUM j<n. j)}."
proof -
  let ?sum = "\<lambda>k::nat. SUM j<k. j"
  let ?inv = "\<lambda>s i::nat. s = ?sum i"

  show ?thesis
  proof hoare
    show "?inv 0 1" by simp
  next
    fix s i assume "?inv s i & i ~= n"
    then show "?inv (s + i) (i + 1)" by simp
  next
    fix s i assume "?inv s i & ~ i ~= n"
    then show "s = ?sum n" by simp
  qed
qed

text {* Certainly, this proof may be done fully automatic as well,
  provided that the invariant is given beforehand. *}

theorem
  "|- .{True}.
      \<acute>S := 0; \<acute>I := 1;
      WHILE \<acute>I ~= n
      INV .{\<acute>S = (SUM j<\<acute>I. j)}.
      DO
        \<acute>S := \<acute>S + \<acute>I;
        \<acute>I := \<acute>I + 1
      OD
      .{\<acute>S = (SUM j<n. j)}."
  by hoare auto


subsection {* Time *}

text {* A simple embedding of time in Hoare logic: function @{text
  timeit} inserts an extra variable to keep track of the elapsed time. *}

record tstate = time :: nat

type_synonym 'a time = "\<lparr>time :: nat, \<dots> :: 'a\<rparr>"

primrec timeit :: "'a time com \<Rightarrow> 'a time com"
where
  "timeit (Basic f) = (Basic f; Basic(\<lambda>s. s\<lparr>time := Suc (time s)\<rparr>))"
| "timeit (c1; c2) = (timeit c1; timeit c2)"
| "timeit (Cond b c1 c2) = Cond b (timeit c1) (timeit c2)"
| "timeit (While b iv c) = While b iv (timeit c)"

record tvars = tstate +
  I :: nat
  J :: nat

lemma lem: "(0::nat) < n \<Longrightarrow> n + n \<le> Suc (n * n)"
  by (induct n) simp_all

lemma
  "|- .{i = \<acute>I & \<acute>time = 0}.
    timeit (
    WHILE \<acute>I \<noteq> 0
    INV .{2 *\<acute> time + \<acute>I * \<acute>I + 5 * \<acute>I = i * i + 5 * i}.
    DO
      \<acute>J := \<acute>I;
      WHILE \<acute>J \<noteq> 0
      INV .{0 < \<acute>I & 2 * \<acute>time + \<acute>I * \<acute>I + 3 * \<acute>I + 2 * \<acute>J - 2 = i * i + 5 * i}.
      DO \<acute>J := \<acute>J - 1 OD;
        \<acute>I := \<acute>I - 1
    OD
    ) .{2*\<acute>time = i*i + 5*i}."
  apply simp
  apply hoare
      apply simp
     apply clarsimp
    apply clarsimp
   apply arith
   prefer 2
   apply clarsimp
  apply (clarsimp simp: nat_distrib)
  apply (frule lem)
  apply arith
  done

end
