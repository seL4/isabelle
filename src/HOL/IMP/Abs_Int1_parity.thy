(* Author: Tobias Nipkow *)

subsection "Parity Analysis"

theory Abs_Int1_parity
imports Abs_Int1
begin

datatype parity = Even | Odd | Either

text\<open>Instantiation of class \<^class>\<open>order\<close> with type \<^typ>\<open>parity\<close>:\<close>

instantiation parity :: order
begin

text\<open>First the definition of the interface function \<open>\<le>\<close>. Note that
the header of the definition must refer to the ascii name \<^const>\<open>less_eq\<close> of the
constants as \<open>less_eq_parity\<close> and the definition is named \<open>less_eq_parity_def\<close>.  Inside the definition the symbolic names can be used.\<close>

definition less_eq_parity where
"x \<le> y = (y = Either \<or> x=y)"

text\<open>We also need \<open><\<close>, which is defined canonically:\<close>

definition less_parity where
"x < y = (x \<le> y \<and> \<not> y \<le> (x::parity))"

text\<open>\noindent(The type annotation is necessary to fix the type of the polymorphic predicates.)

Now the instance proof, i.e.\ the proof that the definition fulfills
the axioms (assumptions) of the class. The initial proof-step generates the
necessary proof obligations.\<close>

instance
proof
  fix x::parity show "x \<le> x" by(auto simp: less_eq_parity_def)
next
  fix x y z :: parity assume "x \<le> y" "y \<le> z" thus "x \<le> z"
    by(auto simp: less_eq_parity_def)
next
  fix x y :: parity assume "x \<le> y" "y \<le> x" thus "x = y"
    by(auto simp: less_eq_parity_def)
next
  fix x y :: parity show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by(rule less_parity_def)
qed

end

text\<open>Instantiation of class \<^class>\<open>semilattice_sup_top\<close> with type \<^typ>\<open>parity\<close>:\<close>

instantiation parity :: semilattice_sup_top
begin

definition sup_parity where
"x \<squnion> y = (if x = y then x else Either)"

definition top_parity where
"\<top> = Either"

text\<open>Now the instance proof. This time we take a shortcut with the help of
proof method \<open>goal_cases\<close>: it creates cases 1 ... n for the subgoals
1 ... n; in case i, i is also the name of the assumptions of subgoal i and
\<open>case?\<close> refers to the conclusion of subgoal i.
The class axioms are presented in the same order as in the class definition.\<close>

instance
proof (standard, goal_cases)
  case 1 (*sup1*) show ?case by(auto simp: less_eq_parity_def sup_parity_def)
next
  case 2 (*sup2*) show ?case by(auto simp: less_eq_parity_def sup_parity_def)
next
  case 3 (*sup least*) thus ?case by(auto simp: less_eq_parity_def sup_parity_def)
next
  case 4 (*top*) show ?case by(auto simp: less_eq_parity_def top_parity_def)
qed

end


text\<open>Now we define the functions used for instantiating the abstract
interpretation locales. Note that the Isabelle terminology is
\emph{interpretation}, not \emph{instantiation} of locales, but we use
instantiation to avoid confusion with abstract interpretation.\<close>

fun \<gamma>_parity :: "parity \<Rightarrow> val set" where
"\<gamma>_parity Even = {i. i mod 2 = 0}" |
"\<gamma>_parity Odd  = {i. i mod 2 = 1}" |
"\<gamma>_parity Either = UNIV"

fun num_parity :: "val \<Rightarrow> parity" where
"num_parity i = (if i mod 2 = 0 then Even else Odd)"

fun plus_parity :: "parity \<Rightarrow> parity \<Rightarrow> parity" where
"plus_parity Even Even = Even" |
"plus_parity Odd  Odd  = Even" |
"plus_parity Even Odd  = Odd" |
"plus_parity Odd  Even = Odd" |
"plus_parity Either y  = Either" |
"plus_parity x Either  = Either"

text\<open>First we instantiate the abstract value interface and prove that the
functions on type \<^typ>\<open>parity\<close> have all the necessary properties:\<close>

global_interpretation Val_semilattice
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof (standard, goal_cases) txt\<open>subgoals are the locale axioms\<close>
  case 1 thus ?case by(auto simp: less_eq_parity_def)
next
  case 2 show ?case by(auto simp: top_parity_def)
next
  case 3 show ?case by auto
next
  case (4 _ a1 _ a2) thus ?case
    by (induction a1 a2 rule: plus_parity.induct)
      (auto simp add: mod_add_eq [symmetric])
qed

text\<open>In case 4 we needed to refer to particular variables.
Writing (i x y z) fixes the names of the variables in case i to be x, y and z
in the left-to-right order in which the variables occur in the subgoal.
Underscores are anonymous placeholders for variable names we don't care to fix.\<close>

text\<open>Instantiating the abstract interpretation locale requires no more
proofs (they happened in the instatiation above) but delivers the
instantiated abstract interpreter which we call \<open>AI_parity\<close>:\<close>

global_interpretation Abs_Int
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
defines aval_parity = aval' and step_parity = step' and AI_parity = AI
..


subsubsection "Tests"

definition "test1_parity =
  ''x'' ::= N 1;;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 2)"
value "show_acom (the(AI_parity test1_parity))"

definition "test2_parity =
  ''x'' ::= N 1;;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 3)"

definition "steps c i = ((step_parity \<top>) ^^ i) (bot c)"

value "show_acom (steps test2_parity 0)"
value "show_acom (steps test2_parity 1)"
value "show_acom (steps test2_parity 2)"
value "show_acom (steps test2_parity 3)"
value "show_acom (steps test2_parity 4)"
value "show_acom (steps test2_parity 5)"
value "show_acom (steps test2_parity 6)"
value "show_acom (the(AI_parity test2_parity))"


subsubsection "Termination"

global_interpretation Abs_Int_mono
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof (standard, goal_cases)
  case (1 _ a1 _ a2) thus ?case
    by(induction a1 a2 rule: plus_parity.induct)
      (auto simp add:less_eq_parity_def)
qed

definition m_parity :: "parity \<Rightarrow> nat" where
"m_parity x = (if x = Either then 0 else 1)"

global_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
and m = m_parity and h = "1"
proof (standard, goal_cases)
  case 1 thus ?case by(auto simp add: m_parity_def less_eq_parity_def)
next
  case 2 thus ?case by(auto simp add: m_parity_def less_eq_parity_def less_parity_def)
qed

thm AI_Some_measure

end
