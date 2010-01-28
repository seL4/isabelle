(*  Title:      HOL/Algebras.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Generic algebraic structures and operations *}

theory Algebras
imports HOL
begin

subsection {* Generic algebraic structures *}

locale semigroup =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
  assumes assoc: "a * b * c = a * (b * c)"

locale abel_semigroup = semigroup +
  assumes commute: "a * b = b * a"
begin

lemma left_commute:
  "b * (a * c) = a * (b * c)"
proof -
  have "(b * a) * c = (a * b) * c"
    by (simp only: commute)
  then show ?thesis
    by (simp only: assoc)
qed

end

locale semilattice = abel_semigroup +
  assumes idem [simp]: "a * a = a"
begin

lemma left_idem [simp]:
  "a * (a * b) = a * b"
  by (simp add: assoc [symmetric])

end

locale lattice = inf!: abel_semigroup inf + sup!: abel_semigroup sup
  for inf (infixl "\<sqinter>" 70) and sup (infixl "\<squnion>" 70) +
  assumes sup_inf_absorb: "a \<squnion> (a \<sqinter> b) = a"
  and inf_sup_absorb: "a \<sqinter> (a \<squnion> b) = a"

sublocale lattice < inf!: semilattice inf
proof
  fix a
  have "a \<sqinter> (a \<squnion> (a \<sqinter> a)) = a" by (fact inf_sup_absorb)
  then show "a \<sqinter> a = a" by (simp add: sup_inf_absorb)
qed

sublocale lattice < sup!: semilattice sup
proof
  fix a
  have "a \<squnion> (a \<sqinter> (a \<squnion> a)) = a" by (fact sup_inf_absorb)
  then show "a \<squnion> a = a" by (simp add: inf_sup_absorb)
qed


subsection {* Generic algebraic operations *}

class zero = 
  fixes zero :: 'a  ("0")

class one =
  fixes one  :: 'a  ("1")

lemma Let_0 [simp]: "Let 0 f = f 0"
  unfolding Let_def ..

lemma Let_1 [simp]: "Let 1 f = f 1"
  unfolding Let_def ..

setup {*
  Reorient_Proc.add
    (fn Const(@{const_name Algebras.zero}, _) => true
      | Const(@{const_name Algebras.one}, _) => true
      | _ => false)
*}

simproc_setup reorient_zero ("0 = x") = Reorient_Proc.proc
simproc_setup reorient_one ("1 = x") = Reorient_Proc.proc

typed_print_translation {*
let
  fun tr' c = (c, fn show_sorts => fn T => fn ts =>
    if (not o null) ts orelse T = dummyT
      orelse not (! show_types) andalso can Term.dest_Type T
    then raise Match
    else Syntax.const Syntax.constrainC $ Syntax.const c $ Syntax.term_of_typ show_sorts T);
in map tr' [@{const_syntax Algebras.one}, @{const_syntax Algebras.zero}] end;
*} -- {* show types that are presumably too general *}

hide (open) const zero one

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "+" 65)

class minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "-" 65)

class uminus =
  fixes uminus :: "'a \<Rightarrow> 'a"  ("- _" [81] 80)

class times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "*" 70)

class inverse =
  fixes inverse :: "'a \<Rightarrow> 'a"
    and divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)

class abs =
  fixes abs :: "'a \<Rightarrow> 'a"
begin

notation (xsymbols)
  abs  ("\<bar>_\<bar>")

notation (HTML output)
  abs  ("\<bar>_\<bar>")

end

class sgn =
  fixes sgn :: "'a \<Rightarrow> 'a"

class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

abbreviation (input)
  greater_eq  (infix ">=" 50) where
  "x >= y \<equiv> y <= x"

notation (input)
  greater_eq  (infix "\<ge>" 50)

abbreviation (input)
  greater  (infix ">" 50) where
  "x > y \<equiv> y < x"

end

syntax
  "_index1"  :: index    ("\<^sub>1")
translations
  (index) "\<^sub>1" => (index) "\<^bsub>\<struct>\<^esub>"

end