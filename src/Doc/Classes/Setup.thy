theory Setup
imports Main
begin

ML_file \<open>../antiquote_setup.ML\<close>
ML_file \<open>../more_antiquote.ML\<close>

declare [[default_code_width = 74]]

syntax
  "_alpha" :: "type"  (\<open>\<alpha>\<close>)
  "_alpha_ofsort" :: "sort \<Rightarrow> type"  (\<open>\<alpha>' ::_\<close> [0] 1000)
  "_beta" :: "type"  (\<open>\<beta>\<close>)
  "_beta_ofsort" :: "sort \<Rightarrow> type"  (\<open>\<beta>' ::_\<close> [0] 1000)

parse_ast_translation \<open>
  let
    fun alpha_ast_tr [] = Ast.Variable "'a"
      | alpha_ast_tr asts = raise Ast.AST ("alpha_ast_tr", asts);
    fun alpha_ofsort_ast_tr [ast] =
          Ast.Appl [Ast.Constant \<^syntax_const>\<open>_ofsort\<close>, Ast.Variable "'a", ast]
      | alpha_ofsort_ast_tr asts = raise Ast.AST ("alpha_ast_tr", asts);
    fun beta_ast_tr [] = Ast.Variable "'b"
      | beta_ast_tr asts = raise Ast.AST ("beta_ast_tr", asts);
    fun beta_ofsort_ast_tr [ast] =
          Ast.Appl [Ast.Constant \<^syntax_const>\<open>_ofsort\<close>, Ast.Variable "'b", ast]
      | beta_ofsort_ast_tr asts = raise Ast.AST ("beta_ast_tr", asts);
  in
   [(\<^syntax_const>\<open>_alpha\<close>, K alpha_ast_tr),
    (\<^syntax_const>\<open>_alpha_ofsort\<close>, K alpha_ofsort_ast_tr),
    (\<^syntax_const>\<open>_beta\<close>, K beta_ast_tr),
    (\<^syntax_const>\<open>_beta_ofsort\<close>, K beta_ofsort_ast_tr)]
  end
\<close>

end
