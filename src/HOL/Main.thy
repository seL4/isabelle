section \<open>Main HOL\<close>

text \<open>
  Classical Higher-order Logic -- only ``Main'', excluding real and
  complex numbers etc.
\<close>

theory Main
  imports
    Predicate_Compile
    Quickcheck_Narrowing
    Mirabelle
    Extraction
    Nunchaku
    BNF_Greatest_Fixpoint
    Filter
    Conditionally_Complete_Lattices
    Binomial
    GCD
begin

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
  Inf ("\<Sqinter>") and
  Sup ("\<Squnion>") and
  ordLeq2 (infix "<=o" 50) and
  ordLeq3 (infix "\<le>o" 50) and
  ordLess2 (infix "<o" 50) and
  ordIso2 (infix "=o" 50) and
  card_of ("|_|") and
  BNF_Cardinal_Arithmetic.csum (infixr "+c" 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90) and
  BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

bundle cardinal_syntax begin
notation
  ordLeq2 (infix "<=o" 50) and
  ordLeq3 (infix "\<le>o" 50) and
  ordLess2 (infix "<o" 50) and
  ordIso2 (infix "=o" 50) and
  card_of ("|_|") and
  BNF_Cardinal_Arithmetic.csum (infixr "+c" 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)

alias cinfinite = BNF_Cardinal_Arithmetic.cinfinite
alias czero = BNF_Cardinal_Arithmetic.czero
alias cone = BNF_Cardinal_Arithmetic.cone
alias ctwo = BNF_Cardinal_Arithmetic.ctwo
end

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

thy_deps

end
