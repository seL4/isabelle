theory Synopsis
imports Base Main
begin

chapter {* Synopsis *}

section {* Notepad *}

text {*
  An Isar proof body serves as mathematical notepad to compose logical
  content, consisting of types, terms, facts.
*}


subsection {* Types and terms *}

notepad
begin
  txt {* Locally fixed entities: *}
  fix x   -- {* local constant, without any type information yet *}
  fix x :: 'a  -- {* variant with explicit type-constraint for subsequent use*}

  fix a b
  assume "a = b"  -- {* type assignment at first occurrence in concrete term *}

  txt {* Definitions (non-polymorphic): *}
  def x \<equiv> "t::'a"

  txt {* Abbreviations (polymorphic): *}
  let ?f = "\<lambda>x. x"
  term "?f ?f"

  txt {* Notation: *}
  write x  ("***")
end


subsection {* Facts *}

text {*
  A fact is a simultaneous list of theorems.
*}


subsubsection {* Producing facts *}

notepad
begin

  txt {* Via assumption (``lambda''): *}
  assume a: A

  txt {* Via proof (``let''): *}
  have b: B sorry

  txt {* Via abbreviation (``let''): *}
  note c = a b

end


subsubsection {* Referencing facts *}

notepad
begin
  txt {* Via explicit name: *}
  assume a: A
  note a

  txt {* Via implicit name: *}
  assume A
  note this

  txt {* Via literal proposition (unification with results from the proof text): *}
  assume A
  note `A`

  assume "\<And>x. B x"
  note `B a`
  note `B b`
end


subsubsection {* Manipulating facts *}

notepad
begin
  txt {* Instantiation: *}
  assume a: "\<And>x. B x"
  note a
  note a [of b]
  note a [where x = b]

  txt {* Backchaining: *}
  assume 1: A
  assume 2: "A \<Longrightarrow> C"
  note 2 [OF 1]
  note 1 [THEN 2]

  txt {* Symmetric results: *}
  assume "x = y"
  note this [symmetric]

  assume "x \<noteq> y"
  note this [symmetric]

  txt {* Adhoc-simplication (take care!): *}
  assume "P ([] @ xs)"
  note this [simplified]
end


subsubsection {* Projections *}

text {*
  Isar facts consist of multiple theorems.  There is notation to project
  interval ranges.
*}

notepad
begin
  assume stuff: A B C D
  note stuff(1)
  note stuff(2-3)
  note stuff(2-)
end


subsubsection {* Naming conventions *}

text {*
  \begin{itemize}

  \item Lower-case identifiers are usually preferred.

  \item Facts can be named after the main term within the proposition.

  \item Facts should \emph{not} be named after the command that
  introduced them (@{command "assume"}, @{command "have"}).  This is
  misleading and hard to maintain.

  \item Natural numbers can be used as ``meaningless'' names (more
  appropriate than @{text "a1"}, @{text "a2"} etc.)

  \item Symbolic identifiers are supported (e.g. @{text "*"}, @{text
  "**"}, @{text "***"}).

  \end{itemize}
*}


subsection {* Block structure *}

text {*
  The formal notepad is block structured.  The fact produced by the last
  entry of a block is exported into the outer context.
*}

notepad
begin
  {
    have a: A sorry
    have b: B sorry
    note a b
  }
  note this
  note `A`
  note `B`
end

text {* Explicit blocks as well as implicit blocks of nested goal
  statements (e.g.\ @{command have}) automatically introduce one extra
  pair of parentheses in reserve.  The @{command next} command allows
  to ``jump'' between these sub-blocks. *}

notepad
begin

  {
    have a: A sorry
  next
    have b: B
    proof -
      show B sorry
    next
      have c: C sorry
    next
      have d: D sorry
    qed
  }

  txt {* Alternative version with explicit parentheses everywhere: *}

  {
    {
      have a: A sorry
    }
    {
      have b: B
      proof -
        {
          show B sorry
        }
        {
          have c: C sorry
        }
        {
          have d: D sorry
        }
      qed
    }
  }

end

end