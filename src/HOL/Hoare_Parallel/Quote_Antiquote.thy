section \<open>Concrete Syntax\<close>

theory Quote_Antiquote imports Main begin

syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                (\<open>(\<guillemotleft>_\<guillemotright>)\<close> [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                (\<open>\<acute>_\<close> [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    (\<open>(\<lbrace>_\<rbrace>)\<close> [0] 1000)

translations
  "\<lbrace>b\<rbrace>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr \<^syntax_const>\<open>_antiquote\<close> t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

end
