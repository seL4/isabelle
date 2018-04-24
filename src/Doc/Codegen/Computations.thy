theory Computations
  imports Codegen_Basics.Setup
    "HOL-Library.Code_Target_Int"
begin

section \<open>Computations \label{sec:computations}\<close>

subsection \<open>Prelude -- The @{text code} antiquotation \label{sec:code_antiq}\<close>

text \<open>
  The @{ML_antiquotation_def code} antiquotation allows to include constants
  from
  generated code directly into ML system code, as in the following toy
  example:
\<close>

datatype %quote form = T | F | And form form | Or form form (*<*)

(*>*) ML %quotetypewriter \<open>
  fun eval_form @{code T} = true
    | eval_form @{code F} = false
    | eval_form (@{code And} (p, q)) =
        eval_form p andalso eval_form q
    | eval_form (@{code Or} (p, q)) =
        eval_form p orelse eval_form q;
\<close>

text \<open>
  \noindent The antiquotation @{ML_antiquotation code} takes
  the name of a constant as argument;
  the required code is generated
  transparently and the corresponding constant names are inserted
  for the given antiquotations.  This technique allows to use pattern
  matching on constructors stemming from compiled datatypes.
  Note that the @{ML_antiquotation code}
  antiquotation may not refer to constants which carry adaptations;
  here you have to refer to the corresponding adapted code directly.
\<close>

  
subsection \<open>The concept of computations\<close>

text \<open>
  Computations embody the simple idea that for each
  monomorphic Isabelle/HOL term of type @{text \<tau>} by virtue of
  code generation there exists an corresponding ML type @{text T} and
  a morphism @{text "\<Phi> :: \<tau> \<rightarrow> T"} satisfying
  @{text "\<Phi> (t\<^sub>1 \<cdot> t\<^sub>2) = \<Phi> t\<^sub>1 \<cdot> \<Phi> t\<^sub>2"}, with @{text \<cdot>} denoting
  term application.

  For a given Isabelle/HOL type @{text \<tau>}, parts of @{text \<Phi>} can be
  implemented by a corresponding ML function @{text "\<phi>\<^sub>\<tau> :: term \<rightarrow> T"}.
  How?

    \<^descr> \<open>Let input be a constant C :: \<tau>.\<close> \\
      Then @{text "\<phi>\<^sub>\<tau> C = f\<^sub>C"} with @{text "f\<^sub>C"} being
      the image of @{text C} under code generation.

    \<^descr> \<open>Let input be an application (t\<^sub>1 \<cdot> t\<^sub>2) :: \<tau>.\<close> \\
      Then @{text "\<phi>\<^sub>\<tau> (t\<^sub>1 \<cdot> t\<^sub>2) = \<phi>\<^sub>\<tau> t\<^sub>1 (\<phi>\<^sub>\<tau> t\<^sub>2)"}.

  \noindent Using these trivial properties, each monomorphic constant
  @{text "C : \<^vec>\<tau>\<^sub>n \<rightarrow> \<tau>"} yields the following
  equations:
\<close>

text %quote \<open>
  @{text "\<phi>\<^bsub>(\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<rightarrow> \<dots> \<rightarrow> \<tau>\<^sub>n \<rightarrow> \<tau>)\<^esub> C = f\<^sub>C"} \\
  @{text "\<phi>\<^bsub>(\<tau>\<^sub>2 \<rightarrow> \<dots> \<rightarrow> \<tau>\<^sub>n \<rightarrow> \<tau>)\<^esub> (C \<cdot> t\<^sub>1) = f\<^sub>C (\<phi>\<^bsub>\<tau>\<^sub>1\<^esub> t\<^sub>1)"} \\
  @{text "\<dots>"} \\
  @{text "\<phi>\<^bsub>\<tau>\<^esub> (C \<cdot> t\<^sub>1 \<cdot> \<dots> \<cdot> t\<^sub>n) = f\<^sub>C (\<phi>\<^bsub>\<tau>\<^sub>1\<^esub> t\<^sub>1) \<dots> (\<phi>\<^bsub>\<tau>\<^sub>n\<^esub> t\<^sub>n)"}
\<close>
  
text \<open>
  \noindent Hence a computation is characterized as follows:

    \<^item> Let @{text "input constants"} denote a set of monomorphic constants.

    \<^item> Let @{text \<tau>} denote a monomorphic type and @{text "'ml"} be a schematic
      placeholder for its corresponding type in ML under code generation.

    \<^item> Then the corresponding computation is an ML function of type
      @{ML_type "Proof.context -> term -> 'ml"}
      partially implementing the morphism @{text "\<Phi> :: \<tau> \<rightarrow> T"} for all
      \<^emph>\<open>input terms\<close> consisting only of input constants and applications.

  \noindent The charming idea is that all required code is automatically generated
  by the code generator for givens input constants and types;
  that code is directly inserted into the Isabelle/ML runtime system
  by means of antiquotations.
\<close>


subsection \<open>The @{text computation} antiquotation\<close>

text \<open>
  The following example illustrates its basic usage:
\<close>

ML %quotetypewriter \<open>
  local

  fun int_of_nat @{code "0 :: nat"} = 0
    | int_of_nat (@{code Suc} n) = int_of_nat n + 1;

  in

  val comp_nat = @{computation nat terms:
    "plus :: nat \<Rightarrow> nat \<Rightarrow> nat" "times :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "sum_list :: nat list \<Rightarrow> nat" "prod_list :: nat list \<Rightarrow> nat"
    datatypes: nat "nat list"}
    (fn post => post o HOLogic.mk_nat o int_of_nat o the);

  end
\<close>

text \<open>
    \<^item> Antiquotations occurring in the
      same ML block always refer to the same transparently generated code;
      particularly, they share the same transparently generated datatype
      declarations.

    \<^item> The type of a computation is specified as first argument.

    \<^item> Input constants are specified the following ways:

        \<^item> Each term following @{text "terms:"} specifies all constants
          it contains as input constants.

        \<^item> Each type following @{text "datatypes:"} specifies all constructors
          of the corresponding code datatype as input constants.  Note that
          this does not increase expressiveness but succinctness for datatypes
          with many constructors.  Abstract type constructors are skipped
          silently.

    \<^item> The code generated by a @{text computation} antiquotation takes a functional argument
      which describes how to conclude the computation.  What's the rationale
      behind this?

        \<^item> There is no automated way to generate a reconstruction function
          from the resulting ML type to a Isabelle term -- this is in the
          responsibility of the implementor.  One possible approach
          for robust term reconstruction is the @{text code} antiquotation.

        \<^item> Both statically specified input constants and dynamically provided input
          terms are subject to preprocessing.  Likewise the result
          is supposed to be subject to postprocessing; the implementor
          is expected to take care for this explicitly.

        \<^item> Computations follow the partiality principle (cf.~\secref{sec:partiality_principle}):
          failures due to pattern matching or unspecified functions
          are interpreted as partiality; therefore resulting ML values
          are optional. 

      Hence the functional argument accepts the following parameters

        \<^item> A postprocessor function @{ML_type "term -> term"}.

        \<^item> The resulting value as optional argument.

      The functional argument is supposed to compose the final result
      from these in a suitable manner.

  \noindent A simple application:
\<close>

ML_val %quotetypewriter \<open>
  comp_nat @{context} @{term "sum_list [Suc 0, Suc (Suc 0)] * Suc (Suc 0)"}
\<close>

text \<open>
  \noindent A single ML block may contain an arbitrary number of computation
  antiquotations.  These share the \<^emph>\<open>same\<close> set of possible
  input constants.  In other words, it does not matter in which
  antiquotation constants are specified;  in the following example,
  \<^emph>\<open>all\<close> constants are specified by the first antiquotation once
  and for all:
\<close>

ML %quotetypewriter \<open>
  local

  fun int_of_nat @{code "0 :: nat"} = 0
    | int_of_nat (@{code Suc} n) = int_of_nat n + 1;

  in

  val comp_nat = @{computation nat terms:
    "plus :: nat \<Rightarrow> nat \<Rightarrow> nat" "times :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "sum_list :: nat list \<Rightarrow> nat" "prod_list :: nat list \<Rightarrow> nat"
    "replicate :: nat \<Rightarrow> nat \<Rightarrow> nat list"
    datatypes: nat "nat list"}
    (fn post => post o HOLogic.mk_nat o int_of_nat o the);

  val comp_nat_list = @{computation "nat list"}
    (fn post => post o HOLogic.mk_list @{typ nat} o
      map (HOLogic.mk_nat o int_of_nat) o the);

  end
\<close>

  
subsection \<open>Pitfalls when specifying input constants \label{sec:input_constants_pitfalls}\<close>

text \<open>
    \<^descr> \<open>Complete type coverage.\<close> Specified input constants must
      be \<^emph>\<open>complete\<close> in the sense that for each
      required type @{text \<tau>} there is at least one corresponding
      input constant which can actually \<^emph>\<open>construct\<close> a concrete
      value of type @{text \<tau>}, potentially requiring more types recursively;
      otherwise the system of equations cannot be generated properly.
      Hence such incomplete input constants sets are rejected immediately.

    \<^descr> \<open>Unsuitful right hand sides.\<close> The generated code for a computation
      must compile in the strict ML runtime environment.  This imposes
      the technical restriction that each compiled input constant
      @{text f\<^sub>C} on the right hand side of a generated equations
      must compile without throwing an exception.  That rules
      out pathological examples like @{term [source] "undefined :: nat"}
      as input constants, as well as abstract constructors (cf. \secref{sec:invariant}).

    \<^descr> \<open>Preprocessing.\<close> For consistency, input constants are subject
      to preprocessing;  however, the overall approach requires
      to operate on constants @{text C} and their respective compiled images
      @{text f\<^sub>C}.\footnote{Technical restrictions of the implementation
      enforce this, although those could be lifted in the future.}
      This is a problem whenever preprocessing maps an input constant
      to a non-constant.

      To circumvent these situations, the computation machinery
      has a dedicated preprocessor which is applied \<^emph>\<open>before\<close>
      the regular preprocessing, both to input constants as well as
      input terms.  This can be used to map problematic constants
      to other ones that are not subject to regular preprocessing. 
      Rewrite rules are added using attribute @{attribute code_computation_unfold}.
      There should rarely be a need to use this beyond the few default
      setups in HOL, which deal with literals (see also \secref{sec:literal_input}).
\<close>

  
subsection \<open>Pitfalls concerning input terms\<close>

text \<open>
    \<^descr> \<open>No polymorphims.\<close> Input terms must be monomorphic: compilation
      to ML requires dedicated choice of monomorphic types.

    \<^descr> \<open>No abstractions.\<close> Only constants and applications are admissible
      as input; abstractions are not possible.  In theory, the
      compilation schema could be extended to cover abstractions also,
      but this would increase the trusted code base.  If abstractions
      are required, they can always be eliminated by a dedicated preprocessing
      step, e.g.~using combinatorial logic.

    \<^descr> \<open>Potential interfering of the preprocessor.\<close> As described in \secref{sec:input_constants_pitfalls}
      regular preprocessing can have a disruptive effect for input constants.
      The same also applies to input terms; however the same measures 
      to circumvent that problem for input constants apply to input terms also.
\<close>

  
subsection \<open>Computations using the @{text computation_conv} antiquotation\<close>

text \<open>
  Computations are a device to implement fast proof procedures.
  Then results of a computation are often assumed to be trustable
  and thus wrapped in oracles (see @{cite "isabelle-isar-ref"}),
  as in the following example:\footnote{
  The technical details how numerals are dealt with are given later in
  \secref{sec:literal_input}.}
\<close>

ML %quotetypewriter \<open>
  local

  fun raw_dvd (b, ct) = Thm.mk_binop @{cterm "Pure.eq :: bool \<Rightarrow> bool \<Rightarrow> prop"}
    ct (if b then @{cterm True} else @{cterm False});

  val (_, dvd_oracle) = Context.>>> (Context.map_theory_result
    (Thm.add_oracle (@{binding dvd}, raw_dvd)));

  in

  val conv_dvd = @{computation_conv bool terms:
    "Rings.dvd :: int \<Rightarrow> int \<Rightarrow> bool"
    "plus :: int \<Rightarrow> int \<Rightarrow> int"
    "minus :: int \<Rightarrow> int \<Rightarrow> int"
    "times :: int \<Rightarrow> int \<Rightarrow> int"
    "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
  } (K (curry dvd_oracle))

  end
\<close>

text \<open>
    \<^item> Antiquotation @{ML_antiquotation computation_conv} basically yields
      a conversion of type @{ML_type "Proof.context -> cterm -> thm"}
      (see further @{cite "isabelle-implementation"}).

    \<^item> The antiquotation expects one functional argument to bridge the
      \qt{untrusted gap};  this can be done e.g.~using an oracle.  Since that oracle
      will only yield \qt{valid} results in the context of that particular
      computation, the implementor must make sure that it does not leave
      the local ML scope;  in this example, this is achieved using
      an explicit @{text local} ML block.  The very presence of the oracle
      in the code acknowledges that each computation requires explicit thinking
      before it can be considered trustworthy!

    \<^item> Postprocessing just operates as further conversion after normalization.

    \<^item> Partiality makes the whole conversion fall back to reflexivity.
\<close> (*<*)

(*>*) ML_val %quotetypewriter \<open>
  conv_dvd @{context} @{cterm "7 dvd ( 62437867527846782 :: int)"};
  conv_dvd @{context} @{cterm "7 dvd (-62437867527846783 :: int)"};
\<close>

text \<open>
  \noindent An oracle is not the only way to construct a valid theorem.
  A computation result can be used to construct an appropriate certificate:
\<close>

lemma %quote conv_div_cert:
  "(Code_Target_Int.positive r * Code_Target_Int.positive s)
     div Code_Target_Int.positive s \<equiv> (numeral r :: int)" (is "?lhs \<equiv> ?rhs")
proof (rule eq_reflection)
  have "?lhs = numeral r * numeral s div numeral s"
    by simp
  also have "numeral r * numeral s div numeral s = ?rhs"
    by (rule nonzero_mult_div_cancel_right) simp
  finally show "?lhs = ?rhs" .
qed

lemma %quote positive_mult:
  "Code_Target_Int.positive r * Code_Target_Int.positive s = 
    Code_Target_Int.positive (r * s)"
  by simp
  
ML %quotetypewriter \<open>
  local

  fun integer_of_int (@{code int_of_integer} k) = k

  val cterm_of_int = Thm.cterm_of @{context} o HOLogic.mk_numeral o integer_of_int;

  val divisor = Thm.dest_arg o Thm.dest_arg;

  val evaluate_simps = map mk_eq @{thms arith_simps positive_mult};

  fun evaluate ctxt = 
    Simplifier.rewrite_rule ctxt evaluate_simps;

  fun revaluate ctxt k ct =
    @{thm conv_div_cert}
    |> Thm.instantiate' [] [SOME (cterm_of_int k), SOME (divisor ct)]
    |> evaluate ctxt;

  in

  val conv_div = @{computation_conv int terms:
    "divide :: int \<Rightarrow> int \<Rightarrow> int"
    "0 :: int" "1 :: int" "2 :: int" "3 :: int"
  } revaluate

  end
\<close>

ML_val %quotetypewriter \<open>
  conv_div @{context}
    @{cterm "46782454343499999992777742432342242323423425 div (7 :: int)"}
\<close>

text \<open>
  \noindent The example is intentionally kept simple: only positive
  integers are covered, only remainder-free divisions are feasible,
  and the input term is expected to have a particular shape.
  This exhibits the idea more clearly:
  the result of the computation is used as a mere
  hint how to instantiate @{fact conv_div_cert}, from which the required
  theorem is obtained by performing multiplication using the
  simplifier;  hence that theorem is built of proper inferences,
  with no oracles involved.
\<close>


subsection \<open>Computations using the @{text computation_check} antiquotation\<close>

text \<open>
  The @{text computation_check} antiquotation is convenient if
  only a positive checking of propositions is desired, because then
  the result type is fixed (@{typ prop}) and all the technical
  matter concerning postprocessing and oracles is done in the framework
  once and for all:
\<close>

ML %quotetypewriter \<open>
  val check_nat = @{computation_check terms:
    Trueprop "less :: nat \<Rightarrow> nat \<Rightarrow> bool" "plus :: nat \<Rightarrow> nat \<Rightarrow> nat" 
    "times :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "0 :: nat" Suc
  }
\<close>

text \<open>
  \noindent The HOL judgement @{term Trueprop} embeds an expression
  of type @{typ bool} into @{typ prop}.
\<close>

ML_val %quotetypewriter \<open>
  check_nat @{context} @{cprop "less (Suc (Suc 0)) (Suc (Suc (Suc 0)))"}
\<close>

text \<open>
  \noindent Note that such computations can only \<^emph>\<open>check\<close>
  for @{typ prop}s to hold but not \<^emph>\<open>decide\<close>.
\<close>


subsection \<open>Some practical hints\<close>  

subsubsection \<open>Inspecting generated code\<close>

text \<open>
  The antiquotations for computations attempt to produce meaningful error
  messages.  If these are not sufficient, it might by useful to
  inspect the generated code, which can be achieved using
\<close>
  
declare %quote [[ML_source_trace]] (*<*) declare %quote [[ML_source_trace = false]] (*>*)


subsubsection \<open>Literals as input constants \label{sec:literal_input}\<close>

text \<open>
  Literals (characters, numerals) in computations cannot be processed
  naively: the compilation pattern for computations fails whenever
  target-language literals are involved; since various
  common code generator setups (see \secref{sec:common_adaptation})
  implement @{typ nat} and @{typ int} by target-language literals,
  this problem manifests whenever numeric types are involved.
  In practice, this is circumvented with a dedicated preprocessor
  setup for literals (see also \secref{sec:input_constants_pitfalls}).

  The following examples illustrate the pattern
  how to specify input constants when literals are involved, without going into
  too much detail:
\<close>

paragraph \<open>An example for @{typ nat}\<close>

ML %quotetypewriter \<open>
  val check_nat = @{computation_check terms:
    Trueprop "even :: nat \<Rightarrow> bool" "plus :: nat \<Rightarrow> nat \<Rightarrow> nat" 
    "0 :: nat" Suc "1 :: nat" "2 :: nat" "3 :: nat"
  }
\<close>

ML_val %quotetypewriter \<open>
  check_nat @{context} @{cprop "even (Suc 0 + 1 + 2 + 3 + 4 + 5)"}
\<close>
  
paragraph \<open>An example for @{typ int}\<close>

ML %quotetypewriter \<open>
  val check_int = @{computation_check terms:
    Trueprop "even :: int \<Rightarrow> bool" "plus :: int \<Rightarrow> int \<Rightarrow> int" 
    "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
  }
\<close>

ML_val %quotetypewriter \<open>
  check_int @{context} @{cprop "even ((0::int) + 1 + 2 + 3 + -1 + -2 + -3)"}
\<close>
  
paragraph \<open>An example for @{typ String.literal}\<close>

definition %quote is_cap_letter :: "String.literal \<Rightarrow> bool"
  where "is_cap_letter s \<longleftrightarrow> (case String.asciis_of_literal s
    of [] \<Rightarrow> False | k # _ \<Rightarrow> 65 \<le> k \<and> k \<le> 90)" (*<*)

(*>*) ML %quotetypewriter \<open>
  val check_literal = @{computation_check terms:
    Trueprop is_cap_letter datatypes: bool String.literal
  }
\<close>

ML_val %quotetypewriter \<open>
  check_literal @{context} @{cprop "is_cap_letter (STR ''Q'')"}
\<close>

  
subsubsection \<open>Preprocessing HOL terms into evaluable shape\<close>

text \<open>
  When integrating decision procedures developed inside HOL into HOL itself,
  a common approach is to use a deep embedding where operators etc.
  are represented by datatypes in Isabelle/HOL.  Then it is necessary
  to turn generic shallowly embedded statements into that particular
  deep embedding (\qt{reification}).

  One option is to hardcode using code antiquotations (see \secref{sec:code_antiq}).
  Another option is to use pre-existing infrastructure in HOL:
  @{ML "Reification.conv"} and @{ML "Reification.tac"}.

  A simplistic example:
\<close>

datatype %quote form_ord = T | F | Less nat nat
  | And form_ord form_ord | Or form_ord form_ord | Neg form_ord

primrec %quote interp :: "form_ord \<Rightarrow> 'a::order list \<Rightarrow> bool"
where
  "interp T vs \<longleftrightarrow> True"
| "interp F vs \<longleftrightarrow> False"
| "interp (Less i j) vs \<longleftrightarrow> vs ! i < vs ! j"
| "interp (And f1 f2) vs \<longleftrightarrow> interp f1 vs \<and> interp f2 vs"
| "interp (Or f1 f2) vs \<longleftrightarrow> interp f1 vs \<or> interp f2 vs"
| "interp (Neg f) vs \<longleftrightarrow> \<not> interp f vs"

text \<open>
  \noindent The datatype @{type form_ord} represents formulae whose semantics is given by
  @{const interp}.  Note that values are represented by variable indices (@{typ nat})
  whose concrete values are given in list @{term vs}.
\<close>

ML %quotetypewriter (*<*) \<open>\<close>
lemma "thm": fixes x y z :: "'a::order" shows "x < y \<and> x < z \<equiv> interp (And (Less (Suc 0) (Suc (Suc 0))) (Less (Suc 0) 0)) [z, x, y]"
ML_prf %quotetypewriter
(*>*) \<open>val thm =
  Reification.conv @{context} @{thms interp.simps} @{cterm "x < y \<and> x < z"}\<close> (*<*)
by (tactic \<open>ALLGOALS (resolve_tac @{context} [thm])\<close>)
(*>*) 

text \<open>
  \noindent By virtue of @{fact interp.simps}, @{ML "Reification.conv"} provides a conversion
  which, for this concrete example, yields @{thm thm [no_vars]}.  Note that the argument
  to @{const interp} does not contain any free variables and can thus be evaluated
  using evaluation.

  A less meager example can be found in the AFP, session @{text "Regular-Sets"},
  theory @{text Regexp_Method}.
\<close>

end
