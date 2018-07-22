(*<*)
theory Real_Asymp_Doc
  imports "HOL-Real_Asymp.Real_Asymp"
begin

ML_file "~~/src/Doc/antiquote_setup.ML"
(*>*)

section \<open>Introduction\<close>

text \<open>
  This document describes the \<^verbatim>\<open>real_asymp\<close> package that provides a number of tools
  related to the asymptotics of real-valued functions. These tools are:

    \<^item> The @{method real_asymp} method to prove limits, statements involving Landau symbols
      (`Big-O' etc.), and asymptotic equivalence (\<open>\<sim>\<close>)

    \<^item> The @{command real_limit} command to compute the limit of a real-valued function at a
      certain point

    \<^item> The @{command real_expansion} command to compute the asymptotic expansion of a
      real-valued function at a certain point

  These three tools will be described in the following sections.
\<close>

section \<open>Supported Operations\<close>

text \<open>
  The \<^verbatim>\<open>real_asymp\<close> package fully supports the following operations:

    \<^item> Basic arithmetic (addition, subtraction, multiplication, division)

    \<^item> Powers with constant natural exponent

    \<^item> @{term exp}, @{term ln}, @{term log}, @{term sqrt}, @{term "root k"} (for a constant k)
  
    \<^item> @{term sin}, @{term cos}, @{term tan} at finite points

    \<^item> @{term sinh}, @{term cosh}, @{term tanh}

    \<^item> @{term min}, @{term max}, @{term abs}

  Additionally, the following operations are supported in a `best effort' fashion using asymptotic
  upper/lower bounds:

    \<^item> Powers with variable natural exponent

    \<^item> @{term sin} and @{term cos} at \<open>\<plusminus>\<infinity>\<close>

    \<^item> @{term floor}, @{term ceiling}, @{term frac}, and \<open>mod\<close>

  Additionally, the @{term arctan} function is partially supported. The method may fail when
  the argument to @{term arctan} contains functions of different order of growth.
\<close>


section \<open>Proving Limits and Asymptotic Properties\<close>

text \<open>
  \[
    @{method_def (HOL) real_asymp} : \<open>method\<close>
  \]

  @{rail \<open>
    @@{method (HOL) real_asymp} opt? (@{syntax simpmod} * )
    ;
    opt: '(' ('verbose' | 'fallback' ) ')'
    ;
    @{syntax_def simpmod}: ('add' | 'del' | 'only' | 'split' (() | '!' | 'del') |
      'cong' (() | 'add' | 'del')) ':' @{syntax thms}
  \<close>}
\<close>

text \<open>
  The @{method real_asymp} method is a semi-automatic proof method for proving certain statements
  related to the asymptotic behaviour of real-valued functions. In the following, let \<open>f\<close> and \<open>g\<close>
  be functions of type @{typ "real \<Rightarrow> real"} and \<open>F\<close> and \<open>G\<close> real filters.

  The functions \<open>f\<close> and \<open>g\<close> can be built from the operations mentioned before and may contain free 
  variables. The filters \<open>F\<close> and \<open>G\<close> can be either \<open>\<plusminus>\<infinity>\<close> or a finite point in \<open>\<real>\<close>, possibly
  with approach from the left or from the right.

  The class of statements that is supported by @{method real_asymp} then consists of:

    \<^item> Limits, i.\,e.\ @{prop "filterlim f F G"}

    \<^item> Landau symbols, i.\,e.\ @{prop "f \<in> O[F](g)"} and analogously for \<^emph>\<open>o\<close>, \<open>\<Omega>\<close>, \<open>\<omega>\<close>, \<open>\<Theta>\<close>

    \<^item> Asymptotic equivalence, i.\,e.\ @{prop "f \<sim>[F] g"}

    \<^item> Asymptotic inequalities, i.\,e.\ @{prop "eventually (\<lambda>x. f x \<le> g x) F"}

  For typical problems arising in practice that do not contain free variables, @{method real_asymp}
  tends to succeed fully automatically within fractions of seconds, e.\,g.:
\<close>

lemma \<open>filterlim (\<lambda>x::real. (1 + 1 / x) powr x) (nhds (exp 1)) at_top\<close>
  by real_asymp

text \<open>
  What makes the method \<^emph>\<open>semi-automatic\<close> is the fact that it has to internally determine the 
  sign of real-valued constants and identical zeroness of real-valued functions, and while the
  internal heuristics for this work very well most of the time, there are situations where the 
  method fails to determine the sign of a constant, in which case the user needs to go back and
  supply more information about the sign of that constant in order to get a result.

  A simple example is the following:
\<close>
(*<*)
experiment
  fixes a :: real
begin
(*>*)
lemma \<open>filterlim (\<lambda>x::real. exp (a * x)) at_top at_top\<close>
oops

text \<open>
  Here, @{method real_asymp} outputs an error message stating that it could not determine the
  sign of the free variable @{term "a :: real"}. In this case, the user must add the assumption
  \<open>a > 0\<close> and give it to @{method real_asymp}.
\<close>
lemma
  assumes \<open>a > 0\<close>
  shows   \<open>filterlim (\<lambda>x::real. exp (a * x)) at_top at_top\<close>
  using assms by real_asymp
(*<*)
end
(*>*)
text \<open>
  Additional modifications to the simpset that is used for determining signs can also be made
  with \<open>simp add:\<close> modifiers etc.\ in the same way as when using the @{method simp} method directly.

  The same situation can also occur without free variables if the constant in question is a
  complicated expression that the simplifier does not know enough ebout,
  e.\,g.\ @{term "pi - exp 1"}.

  In order to trace problems with sign determination, the \<open>(verbose)\<close> option can be passed to
  @{method real_asymp}. It will then print a detailed error message whenever it encounters
  a sign determination problem that it cannot solve.

  The \<open>(fallback)\<close> flag causes the method not to use asymptotic interval arithmetic, but only
  the much simpler core mechanism of computing a single Multiseries expansion for the input
  function. There should normally be no need to use this flag; however, the core part of the 
  code has been tested much more rigorously than the asymptotic interval part. In case there 
  is some implementation problem with it for a problem that can be solved without it, the 
  \<open>(fallback)\<close> option can be used until that problem is resolved.
\<close>



section \<open>Diagnostic Commands\<close>

text \<open>
  \[\begin{array}{rcl}
    @{command_def (HOL) real_limit} & : & \<open>context \<rightarrow>\<close> \\
    @{command_def (HOL) real_expansion} & : & \<open>context \<rightarrow>\<close>
  \end{array}\]

  @{rail \<open>
    @@{command (HOL) real_limit} (limitopt*)
    ;
    @@{command (HOL) real_expansion} (expansionopt*)
    ;
    limitopt : ('limit' ':' @{syntax term}) | ('facts' ':' @{syntax thms})
    ;
    expansionopt : 
        ('limit' ':' @{syntax term}) |
        ('terms' ':' @{syntax nat} ('(' 'strict' ')') ?) |
        ('facts' ':' @{syntax thms})
  \<close>}

    \<^descr>@{command real_limit} computes the limit of the given function \<open>f(x)\<close> for as \<open>x\<close> tends
    to the specified limit point. Additional facts can be provided with the \<open>facts\<close> option, 
    similarly to the @{command using} command with @{method real_asymp}. The limit point given
    by the \<open>limit\<close> option must be one of the filters @{term "at_top"}, @{term "at_bot"}, 
    @{term "at_left"}, or @{term "at_right"}. If no limit point is given, @{term "at_top"} is used
    by default.
  
    \<^medskip>
    The output of @{command real_limit} can be \<open>\<infinity>\<close>, \<open>-\<infinity>\<close>, \<open>\<plusminus>\<infinity>\<close>, \<open>c\<close> (for some real constant \<open>c\<close>),
    \<open>0\<^sup>+\<close>, or \<open>0\<^sup>-\<close>. The \<open>+\<close> and \<open>-\<close> in the last case indicate whether the approach is from above
    or from below (corresponding to @{term "at_right (0::real)"} and @{term "at_left (0::real)"}); 
    for technical reasons, this information is currently not displayed if the limit is not 0.
  
    \<^medskip>
    If the given function does not tend to a definite limit (e.\,g.\ @{term "sin x"} for \<open>x \<rightarrow> \<infinity>\<close>),
    the command might nevertheless succeed to compute an asymptotic upper and/or lower bound and
    display the limits of these bounds instead.

    \<^descr>@{command real_expansion} works similarly to @{command real_limit}, but displays the first few
    terms of the asymptotic multiseries expansion of the given function at the given limit point 
    and the order of growth of the remainder term.
  
    In addition to the options already explained for the @{command real_limit} command, it takes
    an additional option \<open>terms\<close> that controls how many of the leading terms of the expansion are
    printed. If the \<open>(strict)\<close> modifier is passed to the \<open>terms option\<close>, terms whose coefficient is
    0 are dropped from the output and do not count to the number of terms to be output.
  
    \<^medskip>
    By default, the first three terms are output and the \<open>strict\<close> option is disabled.

  Note that these two commands are intended for diagnostic use only. While the central part
  of their implementation -- finding a multiseries expansion and reading off the limit -- are the
  same as in the @{method real_asymp} method and therefore trustworthy, there is a small amount
  of unverified code involved in pre-processing and printing (e.\,g.\ for reducing all the
  different options for the \<open>limit\<close> option to the @{term at_top} case).
\<close>


section \<open>Extensibility\<close>

subsection \<open>Basic fact collections\<close>

text \<open>
  The easiest way to add support for additional operations is to add corresponding facts
  to one of the following fact collections. However, this only works for particularly simple cases.

    \<^descr>@{thm [source] real_asymp_reify_simps} specifies a list of (unconditional) equations that are 
     unfolded as a first step of @{method real_asymp} and the related commands. This can be used to 
     add support for operations that can be represented easily by other operations that are already
     supported, such as @{term sinh}, which is equal to @{term "\<lambda>x. (exp x - exp (-x)) / 2"}.

    \<^descr>@{thm [source] real_asymp_nat_reify} and @{thm [source] real_asymp_int_reify} is used to
     convert operations on natural numbers or integers to operations on real numbers. This enables
     @{method real_asymp} to also work on functions that return a natural number or an integer.
\<close>

subsection \<open>Expanding Custom Operations\<close>

text \<open>
  Support for some non-trivial new operation \<open>f(x\<^sub>1, \<dots>, x\<^sub>n)\<close> can be added dynamically at any
  time, but it involves writing ML code and involves a significant amount of effort, especially
  when the function has essential singularities.

  The first step is to write an ML function that takes as arguments
    \<^item> the expansion context
    \<^item> the term \<open>t\<close> to expand (which will be of the form \<open>f(g\<^sub>1(x), \<dots>, g\<^sub>n(x))\<close>)
    \<^item> a list of \<open>n\<close> theorems of the form @{prop "(g\<^sub>i expands_to G\<^sub>i) bs"}
    \<^item> the current basis \<open>bs\<close>
  and returns a theorem of the form @{prop "(t expands_to F) bs'"} and a new basis \<open>bs'\<close> which 
  must be a superset of the original basis.

  This function must then be registered as a handler for the operation by proving a vacuous lemma
  of the form @{prop "REAL_ASYMP_CUSTOM f"} (which is only used for tagging) and passing that
  lemma and the expansion function to @{ML [source] Exp_Log_Expression.register_custom_from_thm}
  in a @{command local_setup} invocation.

  If the expansion produced by the handler function contains new definitions, corresponding 
  evaluation equations must be added to the fact collection @{thm [source] real_asymp_eval_eqs}.
  These equations must have the form \<open>h p\<^sub>1 \<dots> p\<^sub>m = rhs\<close> where \<open>h\<close> must be a constant of arity \<open>m\<close>
  (i.\,e.\ the function on the left-hand side must be fully applied) and the \<open>p\<^sub>i\<close> can be patterns
  involving \<open>constructors\<close>.

  New constructors for this pattern matching can be registered by adding a theorem of the form
  @{prop "REAL_ASYMP_EVAL_CONSTRUCTOR c"} to the fact collection
  @{thm [source] exp_log_eval_constructor}, but this should be quite rare in practice.

  \<^medskip>
  Note that there is currently no way to add support for custom operations in connection with
  `oscillating' terms. The above mechanism only works if all arguments of the new operation have
  an exact multiseries expansion.
\<close>


subsection \<open>Extending the Sign Oracle\<close>

text \<open>
  By default, the \<^verbatim>\<open>real_asymp\<close> package uses the simplifier with the given simpset and facts
  in order to determine the sign of real constants. This is done by invoking the simplifier
  on goals like \<open>c = 0\<close>, \<open>c \<noteq> 0\<close>, \<open>c > 0\<close>, or \<open>c < 0\<close> or some subset thereof, depending on the
  context.

  If the simplifier cannot prove any of them, the entire method (or command) invocation will fail.
  It is, however, possible to dynamically add additional sign oracles that will be tried; the 
  most obvious candidate for an oracle that one may want to add or remove dynamically are 
  approximation-based tactics.

  Adding such a tactic can be done by calling
  @{ML [source] Multiseries_Expansion.register_sign_oracle}. Note that if the tactic cannot prove
  a goal, it should fail as fast as possible.
\<close>

(*<*)
end
(*>*)
