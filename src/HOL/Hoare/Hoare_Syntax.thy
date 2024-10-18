(*  Title:      HOL/Hoare/Hoare_Syntax.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Author:     Walter Guttmann (extension to total-correctness proofs)
*)

section \<open>Concrete syntax for Hoare logic, with translations for variables\<close>

theory Hoare_Syntax
  imports Main
begin

syntax
  "_assign" :: "idt \<Rightarrow> 'b \<Rightarrow> 'com"
    (\<open>(\<open>indent notation=\<open>infix Hoare assignment\<close>\<close>_ :=/ _)\<close> [70, 65] 61)
  "_Seq" :: "'com \<Rightarrow> 'com \<Rightarrow> 'com"
    (\<open>(\<open>notation=\<open>infix Hoare sequential composition\<close>\<close>_;/ _)\<close> [61, 60] 60)
  "_Cond" :: "'bexp \<Rightarrow> 'com \<Rightarrow> 'com \<Rightarrow> 'com"
    (\<open>(\<open>notation=\<open>mixfix Hoare if expression\<close>\<close>IF _/ THEN _ / ELSE _/ FI)\<close> [0, 0, 0] 61)
  "_While" :: "'bexp \<Rightarrow> 'assn \<Rightarrow> 'var \<Rightarrow> 'com \<Rightarrow> 'com"
    (\<open>(\<open>notation=\<open>mixfix Hoare while expression\<close>\<close>WHILE _/ INV {(_)} / VAR {(_)} //DO _ /OD)\<close> [0, 0, 0, 0] 61)

text \<open>The \<open>VAR {_}\<close> syntax supports two variants:
\<^item> \<open>VAR {x = t}\<close> where \<open>t::nat\<close> is the decreasing expression,
  the variant, and \<open>x\<close> a variable that can be referred to from inner annotations.
  The \<open>x\<close> can be necessary for nested loops, e.g. to prove that the inner loops do not mess with \<open>t\<close>.
\<^item> \<open>VAR {t}\<close> where the variable is omitted because it is not needed.
\<close>

syntax
  "_While0" :: "'bexp \<Rightarrow> 'assn \<Rightarrow> 'com \<Rightarrow> 'com"
    (\<open>(\<open>indent=1 notation=\<open>mixfix Hoare while expression\<close>\<close>WHILE _/ INV (\<open>open_block notation=\<open>mixfix Hoare invariant\<close>\<close>{_}) //DO _ /OD)\<close> [0, 0, 0] 61)
text \<open>The \<open>_While0\<close> syntax is translated into the \<open>_While\<close> syntax with the trivial variant 0.
This is ok because partial correctness proofs do not make use of the variant.\<close>

syntax
  "_hoare_vars" :: "[idts, 'assn,'com, 'assn] \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>mixfix Hoare triple\<close>\<close>VARS _// (\<open>open_block notation=\<open>mixfix Hoare precondition\<close>\<close>{_}) // _ // (\<open>open_block notation=\<open>mixfix Hoare postcondition\<close>\<close>{_}))\<close> [0, 0, 55, 0] 50)
  "_hoare_vars_tc" :: "[idts, 'assn, 'com, 'assn] \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>mixfix Hoare triple\<close>\<close>VARS _// (\<open>open_block notation=\<open>mixfix Hoare precondition\<close>\<close>[_]) // _ // (\<open>open_block notation=\<open>mixfix Hoare postcondition\<close>\<close>[_]))\<close> [0, 0, 55, 0] 50)
syntax (output)
  "_hoare" :: "['assn, 'com, 'assn] \<Rightarrow> bool"
    (\<open>(\<open>notation=\<open>mixfix Hoare triple\<close>\<close>(\<open>open_block notation=\<open>mixfix Hoare precondition\<close>\<close>{_})//_//(\<open>open_block notation=\<open>mixfix Hoare postcondition\<close>\<close>{_}))\<close> [0, 55, 0] 50)
  "_hoare_tc" :: "['assn, 'com, 'assn] \<Rightarrow> bool"
    (\<open>(\<open>notation=\<open>mixfix Hoare triple\<close>\<close>(\<open>open_block notation=\<open>mixfix Hoare precondition\<close>\<close>[_])//_//(\<open>open_block notation=\<open>mixfix Hoare postcondition\<close>\<close>[_]))\<close> [0, 55, 0] 50)

text \<open>Completeness requires(?) the ability to refer to an outer variant in an inner invariant.
Thus we need to abstract over a variable equated with the variant, the \<open>x\<close> in \<open>VAR {x = t}\<close>.
But the \<open>x\<close> should only occur in invariants. To enforce this, syntax translations in \<^file>\<open>hoare_syntax.ML\<close>
separate the program from its annotations and only the latter are abstracted over over \<open>x\<close>.
(Thus \<open>x\<close> can also occur in inner variants, but that neither helps nor hurts.)\<close>

datatype 'a anno =
  Abasic |
  Aseq "'a anno"  "'a anno" |
  Acond "'a anno" "'a anno" |
  Awhile "'a set" "'a \<Rightarrow> nat" "nat \<Rightarrow> 'a anno"

ML_file \<open>hoare_syntax.ML\<close>

end
