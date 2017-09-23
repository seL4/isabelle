theory Base_FDS
imports "HOL-Library.Pattern_Aliases"
begin

declare Let_def [simp]

text \<open>Lemma \<open>size_prod_measure\<close>, when declared with the \<open>measure_function\<close> attribute,
enables \<open>fun\<close> to prove termination of a larger class of functions automatically.
By default, \<open>fun\<close> only tries lexicographic combinations of the sizes of the parameters.
With \<open>size_prod_measure\<close> enabled it also tries measures based on the sum of the sizes
of different parameters.

To alert the reader whenever such a more subtle termination proof is taking place
the lemma is not enabled all the time but only when it is needed.
\<close>

lemma size_prod_measure: 
  "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (size_prod f g)"
by (rule is_measure_trivial)

end