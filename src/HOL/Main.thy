header {* Main HOL *}

theory Main
imports Predicate_Compile Nitpick Extraction Lifting_Sum List_Prefix Coinduction BNF_LFP BNF_GFP
begin

text {*
  Classical Higher-order Logic -- only ``Main'', excluding real and
  complex numbers etc.
*}

text {* See further \cite{Nipkow-et-al:2002:tutorial} *}

no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900) and
  ordLeq2 ("<=o") and
  ordLeq3 ("\<le>o") and
  ordLess2 ("<o") and
  ordIso2 ("=o") and
  csum (infixr "+c" 65) and
  cprod (infixr "*c" 80) and
  cexp (infixr "^c" 90)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end
