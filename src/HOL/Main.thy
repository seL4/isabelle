section \<open>Main HOL\<close>

text \<open>
  Classical Higher-order Logic -- only ``Main'', excluding real and
  complex numbers etc.
\<close>

theory Main
  imports
    Predicate_Compile
    Quickcheck_Narrowing 
    Extraction
    Nunchaku
    BNF_Greatest_Fixpoint
    Filter
    Conditionally_Complete_Lattices
    Binomial
    GCD
begin

text \<open>Legacy\<close>

context Inf
begin

abbreviation (input) INFIMUM :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "INFIMUM A f \<equiv> \<Sqinter>(f ` A)"

end

context Sup
begin

abbreviation (input) SUPREMUM :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "SUPREMUM A f \<equiv> \<Squnion>(f ` A)"

end

abbreviation (input) INTER :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "INTER \<equiv> INFIMUM"

abbreviation (input) UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "UNION \<equiv> SUPREMUM"


text \<open>Namespace cleanup\<close>

hide_const (open)
  czero cinfinite cfinite csum cone ctwo Csum cprod cexp image2 image2p vimage2p Gr Grp collect
  fsts snds setl setr convol pick_middlep fstOp sndOp csquare relImage relInvImage Succ Shift
  shift proj id_bnf

hide_fact (open) id_bnf_def type_definition_id_bnf_UNIV


text \<open>Syntax cleanup\<close>

no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter> _" [900] 900) and
  Sup ("\<Squnion> _" [900] 900) and
  ordLeq2 (infix "<=o" 50) and
  ordLeq3 (infix "\<le>o" 50) and
  ordLess2 (infix "<o" 50) and
  ordIso2 (infix "=o" 50) and
  card_of ("|_|") and
  BNF_Cardinal_Arithmetic.csum (infixr "+c" 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90) and
  BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end
