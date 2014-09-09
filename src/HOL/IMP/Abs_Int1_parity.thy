(* Author: Tobias Nipkow *)

theory Abs_Int1_parity
imports Abs_Int1
begin

subsection "Parity Analysis"

datatype_new parity = Even | Odd | Either

text{* Instantiation of class @{class order} with type @{typ parity}: *}

instantiation parity :: order
begin

text{* First the definition of the interface function @{text"\<le>"}. Note that
the header of the definition must refer to the ascii name @{const less_eq} of the
constants as @{text less_eq_parity} and the definition is named @{text
less_eq_parity_def}.  Inside the definition the symbolic names can be used. *}

definition less_eq_parity where
"x \<le> y = (y = Either \<or> x=y)"

text{* We also need @{text"<"}, which is defined canonically: *}

definition less_parity where
"x < y = (x \<le> y \<and> \<not> y \<le> (x::parity))"

text{*\noindent(The type annotation is necessary to fix the type of the polymorphic predicates.)

Now the instance proof, i.e.\ the proof that the definition fulfills
the axioms (assumptions) of the class. The initial proof-step generates the
necessary proof obligations. *}

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

text{* Instantiation of class @{class semilattice_sup_top} with type @{typ parity}: *}

instantiation parity :: semilattice_sup_top
begin

definition sup_parity where
"x \<squnion> y = (if x = y then x else Either)"

definition top_parity where
"\<top> = Either"

text{* Now the instance proof. This time we take a lazy shortcut: we do not
write out the proof obligations but use the @{text goali} primitive to refer
to the assumptions of subgoal i and @{text "case?"} to refer to the
conclusion of subgoal i. The class axioms are presented in the same order as
in the class definition. Warning: this is brittle! *}

instance
proof
  case goal1 (*sup1*) show ?case by(auto simp: less_eq_parity_def sup_parity_def)
next
  case goal2 (*sup2*) show ?case by(auto simp: less_eq_parity_def sup_parity_def)
next
  case goal3 (*sup least*) thus ?case by(auto simp: less_eq_parity_def sup_parity_def)
next
  case goal4 (*top*) show ?case by(auto simp: less_eq_parity_def top_parity_def)
qed

end


text{* Now we define the functions used for instantiating the abstract
interpretation locales. Note that the Isabelle terminology is
\emph{interpretation}, not \emph{instantiation} of locales, but we use
instantiation to avoid confusion with abstract interpretation.  *}

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

text{* First we instantiate the abstract value interface and prove that the
functions on type @{typ parity} have all the necessary properties: *}

permanent_interpretation Val_semilattice
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof txt{* of the locale axioms *}
  fix a b :: parity
  assume "a \<le> b" thus "\<gamma>_parity a \<subseteq> \<gamma>_parity b"
    by(auto simp: less_eq_parity_def)
next txt{* The rest in the lazy, implicit way *}
  case goal2 show ?case by(auto simp: top_parity_def)
next
  case goal3 show ?case by auto
next
  txt{* Warning: this subproof refers to the names @{text a1} and @{text a2}
  from the statement of the axiom. *}
  case goal4 thus ?case
    by (induction a1 a2 rule: plus_parity.induct) (auto simp add:mod_add_eq)
qed

text{* Instantiating the abstract interpretation locale requires no more
proofs (they happened in the instatiation above) but delivers the
instantiated abstract interpreter which we call @{text AI_parity}: *}

permanent_interpretation Abs_Int
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
defining aval_parity = aval' and step_parity = step' and AI_parity = AI
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

permanent_interpretation Abs_Int_mono
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof
  case goal1 thus ?case
    by(induction a1 a2 rule: plus_parity.induct)
      (auto simp add:less_eq_parity_def)
qed

definition m_parity :: "parity \<Rightarrow> nat" where
"m_parity x = (if x = Either then 0 else 1)"

permanent_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
and m = m_parity and h = "1"
proof
  case goal1 thus ?case by(auto simp add: m_parity_def less_eq_parity_def)
next
  case goal2 thus ?case by(auto simp add: m_parity_def less_eq_parity_def less_parity_def)
qed

thm AI_Some_measure

end
