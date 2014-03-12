theory Setup
imports Main
begin

ML_file "../antiquote_setup.ML"
ML_file "../more_antiquote.ML"

setup {*
  Code_Target.set_default_code_width 74
*}

syntax
  "_alpha" :: "type"  ("\<alpha>")
  "_alpha_ofsort" :: "sort \<Rightarrow> type"  ("\<alpha>()\<Colon>_" [0] 1000)
  "_beta" :: "type"  ("\<beta>")
  "_beta_ofsort" :: "sort \<Rightarrow> type"  ("\<beta>()\<Colon>_" [0] 1000)

parse_ast_translation {*
  let
    fun alpha_ast_tr [] = Ast.Variable "'a"
      | alpha_ast_tr asts = raise Ast.AST ("alpha_ast_tr", asts);
    fun alpha_ofsort_ast_tr [ast] =
          Ast.Appl [Ast.Constant @{syntax_const "_ofsort"}, Ast.Variable "'a", ast]
      | alpha_ofsort_ast_tr asts = raise Ast.AST ("alpha_ast_tr", asts);
    fun beta_ast_tr [] = Ast.Variable "'b"
      | beta_ast_tr asts = raise Ast.AST ("beta_ast_tr", asts);
    fun beta_ofsort_ast_tr [ast] =
          Ast.Appl [Ast.Constant @{syntax_const "_ofsort"}, Ast.Variable "'b", ast]
      | beta_ofsort_ast_tr asts = raise Ast.AST ("beta_ast_tr", asts);
  in
   [(@{syntax_const "_alpha"}, K alpha_ast_tr),
    (@{syntax_const "_alpha_ofsort"}, K alpha_ofsort_ast_tr),
    (@{syntax_const "_beta"}, K beta_ast_tr),
    (@{syntax_const "_beta_ofsort"}, K beta_ofsort_ast_tr)]
  end
*}

end
