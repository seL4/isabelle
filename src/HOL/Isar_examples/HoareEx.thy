
header {* Using Hoare Logic *}

theory HoareEx = Hoare:

subsection {* State spaces *}

text {*
 First of all we provide a store of program variables that
 occur in any of the programs considered later.  Slightly unexpected
 things may happen when attempting to work with undeclared variables.
*}

record vars =
  I :: nat
  M :: nat
  N :: nat
  S :: nat

text {*
 While all of our variables happen to have the same type, nothing
 would prevent us from working with many-sorted programs as well, or
 even polymorphic ones.  Also note that Isabelle/HOL's extensible
 record types even provides simple means to extend the state space
 later.
*}


subsection {* Basic examples *}

text {*
 We look at few trivialities involving assignment and sequential
 composition, in order to get an idea of how to work with our
 formulation of Hoare Logic.
*}

text {*
 Using the basic \name{assign} rule directly is a bit cumbersome.
*}

lemma
  "|- .{`(N_update (2 * `N)) : .{`N = #10}.}. `N := 2 * `N .{`N = #10}."
  by (rule assign)

text {*
 Certainly we want the state modification already done, e.g.\ by
 simplification.  The \name{hoare} method performs the basic state
 update for us; we may apply the Simplifier afterwards to achieve
 ``obvious'' consequences as well.
*}

lemma "|- .{True}. `N := #10 .{`N = #10}."
  by hoare

lemma "|- .{2 * `N = #10}. `N := 2 * `N .{`N = #10}."
  by hoare

lemma "|- .{`N = #5}. `N := 2 * `N .{`N = #10}."
  by hoare simp

lemma "|- .{`N + 1 = a + 1}. `N := `N + 1 .{`N = a + 1}."
  by hoare

lemma "|- .{`N = a}. `N := `N + 1 .{`N = a + 1}."
  by hoare simp

lemma "|- .{a = a & b = b}. `M := a; `N := b .{`M = a & `N = b}."
  by hoare

lemma "|- .{True}. `M := a; `N := b .{`M = a & `N = b}."
  by hoare simp

lemma
"|- .{`M = a & `N = b}.
    `I := `M; `M := `N; `N := `I
    .{`M = b & `N = a}."
  by hoare simp

text {*
 It is important to note that statements like the following one can
 only be proven for each individual program variable.  Due to the
 extra-logical nature of record fields, we cannot formulate a theorem
 relating record selectors and updates schematically.
*}

lemma "|- .{`N = a}. `N := `N .{`N = a}."
  by hoare

lemma "|- .{`x = a}. `x := `x .{`x = a}."
  oops

lemma
  "Valid {s. x s = a} (Basic (\<lambda>s. x_update (x s) s)) {s. x s = n}"
  -- {* same statement without concrete syntax *}
  oops


text {*
 In the following assignments we make use of the consequence rule in
 order to achieve the intended precondition.  Certainly, the
 \name{hoare} method is able to handle this case, too.
*}

lemma "|- .{`M = `N}. `M := `M + 1 .{`M ~= `N}."
proof -
  have ".{`M = `N}. <= .{`M + 1 ~= `N}."
    by auto
  also have "|- ... `M := `M + 1 .{`M ~= `N}."
    by hoare
  finally show ?thesis .
qed

lemma "|- .{`M = `N}. `M := `M + 1 .{`M ~= `N}."
proof -
  have "!!m n. m = n --> m + 1 ~= n"
      -- {* inclusion of assertions expressed in ``pure'' logic, *}
      -- {* without mentioning the state space *}
    by simp
  also have "|- .{`M + 1 ~= `N}. `M := `M + 1 .{`M ~= `N}."
    by hoare
  finally show ?thesis .
qed

lemma "|- .{`M = `N}. `M := `M + 1 .{`M ~= `N}."
  by hoare simp


subsection {* Multiplication by addition *}

text {*
 We now do some basic examples of actual \texttt{WHILE} programs.
 This one is a loop for calculating the product of two natural
 numbers, by iterated addition.  We first give detailed structured
 proof based on single-step Hoare rules.
*}

lemma
  "|- .{`M = 0 & `S = 0}.
      WHILE `M ~= a
      DO `S := `S + b; `M := `M + 1 OD
      .{`S = a * b}."
proof -
  let "|- _ ?while _" = ?thesis
  let ".{`?inv}." = ".{`S = `M * b}."

  have ".{`M = 0 & `S = 0}. <= .{`?inv}." by auto
  also have "|- ... ?while .{`?inv & ~ (`M ~= a)}."
  proof
    let ?c = "`S := `S + b; `M := `M + 1"
    have ".{`?inv & `M ~= a}. <= .{`S + b = (`M + 1) * b}."
      by auto
    also have "|- ... ?c .{`?inv}." by hoare
    finally show "|- .{`?inv & `M ~= a}. ?c .{`?inv}." .
  qed
  also have "... <= .{`S = a * b}." by auto
  finally show ?thesis .
qed

text {*
 The subsequent version of the proof applies the \name{hoare} method
 to reduce the Hoare statement to a purely logical problem that can be
 solved fully automatically.  Note that we have to specify the
 \texttt{WHILE} loop invariant in the original statement.
*}

lemma
  "|- .{`M = 0 & `S = 0}.
      WHILE `M ~= a
      INV .{`S = `M * b}.
      DO `S := `S + b; `M := `M + 1 OD
      .{`S = a * b}."
  by hoare auto


subsection {* Summing natural numbers *}

text {*
 We verify an imperative program to sum natural numbers up to a given
 limit.  First some functional definition for proper specification of
 the problem.
*}

consts
  sum :: "(nat => nat) => nat => nat"
primrec
  "sum f 0 = 0"
  "sum f (Suc n) = f n + sum f n"

syntax
  "_sum" :: "idt => nat => nat => nat"
    ("SUM _<_. _" [0, 0, 10] 10)
translations
  "SUM j<k. b" == "sum (\<lambda>j. b) k"

text {*
 The following proof is quite explicit in the individual steps taken,
 with the \name{hoare} method only applied locally to take care of
 assignment and sequential composition.  Note that we express
 intermediate proof obligation in pure logic, without referring to the
 state space.
*}

theorem
  "|- .{True}.
      `S := 0; `I := 1;
      WHILE `I ~= n
      DO
        `S := `S + `I;
        `I := `I + 1
      OD
      .{`S = (SUM j<n. j)}."
  (is "|- _ (_; ?while) _")
proof -
  let ?sum = "\<lambda>k. SUM j<k. j"
  let ?inv = "\<lambda>s i. s = ?sum i"

  have "|- .{True}. `S := 0; `I := 1 .{?inv `S `I}."
  proof -
    have "True --> 0 = ?sum 1"
      by simp
    also have "|- .{...}. `S := 0; `I := 1 .{?inv `S `I}."
      by hoare
    finally show ?thesis .
  qed
  also have "|- ... ?while .{?inv `S `I & ~ `I ~= n}."
  proof
    let ?body = "`S := `S + `I; `I := `I + 1"
    have "!!s i. ?inv s i & i ~= n -->  ?inv (s + i) (i + 1)"
      by simp
    also have "|- .{`S + `I = ?sum (`I + 1)}. ?body .{?inv `S `I}."
      by hoare
    finally show "|- .{?inv `S `I & `I ~= n}. ?body .{?inv `S `I}." .
  qed
  also have "!!s i. s = ?sum i & ~ i ~= n --> s = ?sum n"
    by simp
  finally show ?thesis .
qed

text {*
 The next version uses the \name{hoare} method, while still explaining
 the resulting proof obligations in an abstract, structured manner.
*}

theorem
  "|- .{True}.
      `S := 0; `I := 1;
      WHILE `I ~= n
      INV .{`S = (SUM j<`I. j)}.
      DO
        `S := `S + `I;
        `I := `I + 1
      OD
      .{`S = (SUM j<n. j)}."
proof -
  let ?sum = "\<lambda>k. SUM j<k. j"
  let ?inv = "\<lambda>s i. s = ?sum i"

  show ?thesis
  proof hoare
    show "?inv 0 1" by simp
  next
    fix s i assume "?inv s i & i ~= n"
    thus "?inv (s + i) (i + 1)" by simp
  next
    fix s i assume "?inv s i & ~ i ~= n"
    thus "s = ?sum n" by simp
  qed
qed

text {*
 Certainly, this proof may be done fully automatic as well, provided
 that the invariant is given beforehand.
*}

theorem
  "|- .{True}.
      `S := 0; `I := 1;
      WHILE `I ~= n
      INV .{`S = (SUM j<`I. j)}.
      DO
        `S := `S + `I;
        `I := `I + 1
      OD
      .{`S = (SUM j<n. j)}."
  by hoare auto

end