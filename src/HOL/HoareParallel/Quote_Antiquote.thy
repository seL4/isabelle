
header {* \section{Concrete Syntax} *}

theory Quote_Antiquote = Main:

syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    ("(.{_}.)" [0] 1000)

syntax (xsymbols)
  "_Assert"    :: "'a \<Rightarrow> 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)

translations
  ".{b}." \<rightharpoonup> "Collect \<guillemotleft>b\<guillemotright>"

parse_translation {*
  let
    fun quote_tr [t] = Syntax.quote_tr "_antiquote" t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [("_quote", quote_tr)] end
*}

end