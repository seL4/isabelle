theory Abs_Int1_parity
imports Abs_Int1
begin

subsection "Parity Analysis"

datatype parity = Even | Odd | Either

text{* Instantiation of class @{class preord} with type @{typ parity}: *}

instantiation parity :: preord
begin

text{* First the definition of the interface function @{text"\<sqsubseteq>"}. Note that
the header of the definition must refer to the ascii name @{const le} of the
constants as @{text le_parity} and the definition is named @{text
le_parity_def}.  Inside the definition the symbolic names can be used. *}

definition le_parity where
"x \<sqsubseteq> y = (y = Either \<or> x=y)"

text{* Now the instance proof, i.e.\ the proof that the definition fulfills
the axioms (assumptions) of the class. The initial proof-step generates the
necessary proof obligations. *}

instance
proof
  fix x::parity show "x \<sqsubseteq> x" by(auto simp: le_parity_def)
next
  fix x y z :: parity assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    by(auto simp: le_parity_def)
qed

end

text{* Instantiation of class @{class SL_top} with type @{typ parity}: *}

instantiation parity :: SL_top
begin

definition join_parity where
"x \<squnion> y = (if x \<sqsubseteq> y then y else if y \<sqsubseteq> x then x else Either)"

definition Top_parity where
"\<top> = Either"

text{* Now the instance proof. This time we take a lazy shortcut: we do not
write out the proof obligations but use the @{text goali} primitive to refer
to the assumptions of subgoal i and @{text "case?"} to refer to the
conclusion of subgoal i. The class axioms are presented in the same order as
in the class definition. *}

instance
proof
  case goal1 (*join1*) show ?case by(auto simp: le_parity_def join_parity_def)
next
  case goal2 (*join2*) show ?case by(auto simp: le_parity_def join_parity_def)
next
  case goal3 (*join least*) thus ?case by(auto simp: le_parity_def join_parity_def)
next
  case goal4 (*Top*) show ?case by(auto simp: le_parity_def Top_parity_def)
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

interpretation Val_abs
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof txt{* of the locale axioms *}
  fix a b :: parity
  assume "a \<sqsubseteq> b" thus "\<gamma>_parity a \<subseteq> \<gamma>_parity b"
    by(auto simp: le_parity_def)
next txt{* The rest in the lazy, implicit way *}
  case goal2 show ?case by(auto simp: Top_parity_def)
next
  case goal3 show ?case by auto
next
  txt{* Warning: this subproof refers to the names @{text a1} and @{text a2}
  from the statement of the axiom. *}
  case goal4 thus ?case
  proof(cases a1 a2 rule: parity.exhaust[case_product parity.exhaust])
  qed (auto simp add:mod_add_eq)
qed

text{* Instantiating the abstract interpretation locale requires no more
proofs (they happened in the instatiation above) but delivers the
instantiated abstract interpreter which we call AI: *}

interpretation Abs_Int
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
defines aval_parity is aval' and step_parity is step' and AI_parity is AI
..


subsubsection "Tests"

definition "test1_parity =
  ''x'' ::= N 1;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 2)"

value "show_acom_opt (AI_parity test1_parity)"

definition "test2_parity =
  ''x'' ::= N 1;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 3)"

definition "steps c i = (step_parity(top c) ^^ i) (bot c)"

value "show_acom (steps test2_parity 0)"
value "show_acom (steps test2_parity 1)"
value "show_acom (steps test2_parity 2)"
value "show_acom (steps test2_parity 3)"
value "show_acom (steps test2_parity 4)"
value "show_acom (steps test2_parity 5)"
value "show_acom_opt (AI_parity test2_parity)"


subsubsection "Termination"

interpretation Abs_Int_mono
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof
  case goal1 thus ?case
  proof(cases a1 a2 b1 b2
   rule: parity.exhaust[case_product parity.exhaust[case_product parity.exhaust[case_product parity.exhaust]]]) (* FIXME - UGLY! *)
  qed (auto simp add:le_parity_def)
qed

definition m_parity :: "parity \<Rightarrow> nat" where
"m_parity x = (if x=Either then 0 else 1)"

interpretation Abs_Int_measure
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
and m = m_parity and h = "2"
proof
  case goal1 thus ?case by(auto simp add: m_parity_def le_parity_def)
next
  case goal2 thus ?case by(auto simp add: m_parity_def le_parity_def)
next
  case goal3 thus ?case by(auto simp add: m_parity_def le_parity_def)
qed

thm AI_Some_measure

end
