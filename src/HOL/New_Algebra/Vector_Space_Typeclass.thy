section \<open>Linking the locale-based vector-space theory to Isabelle's type classes\<close>

theory Vector_Space_Typeclass
  imports Vector_Space Field_Typeclass
begin

text \<open>Following the @{text field_TC} pattern of \<open>Field_Typeclass\<close>, we bridge
  the locale-based @{locale Vector_Space} to Isabelle's type-class arithmetic.  A type-class field
  @{typ "'a :: field"} plays the scalar role, and a type-class abelian additive group
  @{typ "'b :: ab_group_add"} plays the vector role; a scale operation
  @{term "scale :: 'a \<Rightarrow> 'b \<Rightarrow> 'b"} satisfying the four vector-space axioms then witnesses
  @{locale Vector_Space} on the whole types as carriers.

  The constraints match the locale exactly: @{class field} corresponds to the @{text field}
  extension in the locale, and @{class ab_group_add} corresponds to the vector-side
  \<open>abelian_group\<close> assumption of the locale.\<close>

lemma vector_space_TC:
  fixes scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
  assumes scale_add_right: "\<And>a x y. scale a (x + y) = scale a x + scale a y"
    and scale_add_left:    "\<And>a b x. scale (a + b) x = scale a x + scale b x"
    and scale_scale:       "\<And>a b x. scale a (scale b x) = scale (a * b) x"
    and scale_one:         "\<And>x. scale 1 x = x"
  shows "Vector_Space (UNIV :: 'a set) (+) (*) 0 1 (+) 0 (UNIV :: 'b set) scale"
proof -
  interpret F: Field "UNIV :: 'a set" "(+)" "(*)" 0 1 by (rule field_TC.Field_axioms)
  show ?thesis
  proof (intro Vector_Space.intro Vector_Space_axioms.intro)
    show "Field (UNIV :: 'a set) (+) (*) 0 1" by (rule field_TC.Field_axioms)
    show "Abelian_Group (UNIV :: 'b set) (+) 0" by (rule add_abelian_TC)
  qed (simp_all add: scale_add_right scale_add_left scale_scale scale_one)
qed

text \<open>Concrete specialisations to Isabelle's built-in \<open>real_vector\<close> and \<open>complex_vector\<close> classes
  (which live in \<open>Complex_Main\<close>, not in the ancestor closure of this file) can be added by any
  consumer that also imports the relevant HOL theory: apply @{thm [source] vector_space_TC} and
  discharge the four axioms from the class's \<open>scaleR\<close> / \<open>scaleC\<close> simp facts.\<close>

end
