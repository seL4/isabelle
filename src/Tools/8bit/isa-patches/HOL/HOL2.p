local open Ast;
fun Gbigimpl_ast_tr (*"Gbigimpl"*) [asms, concl] =
      fold_ast_p "кл" (unfold_ast "_asms" asms, concl)
  | Gbigimpl_ast_tr (*"Gbigimpl"*) asts = raise_ast "bigimpl_ast_tr" asts;
fun Glam_ast_tr (*"Glam"*) [idts, body] =
      fold_ast_p "_abs" (unfold_ast "_idts" idts, body)
  | Glam_ast_tr (*"Glam"*) asts = raise_ast "lambda_ast_tr" asts;

fun Gimpl_ast_tr' (*"Gbigimpl"*) asts =
  (case unfold_ast_p "кл" (Appl (Constant "кл" :: asts)) of
    (asms as _ :: _ :: _, concl)
      => Appl [Constant "Gbigimpl", fold_ast "_asms" asms, concl]
  | _ => raise Match);
in
    val parse_ast_translation = ("Gbigimpl", Gbigimpl_ast_tr)::
				("Glam", Glam_ast_tr)::
				parse_ast_translation;

    val print_ast_translation = ("кл", Gimpl_ast_tr')::
				("_lambda", fn asts => 
					Appl (Constant "Glam" :: asts)) ::	
				print_ast_translation;

end;

local open Syntax in
val thy = thy 
|> add_trrules_i 
[mk_appl (Constant "Ъ" ) [Variable "P", Variable "Q"] <-> 
 mk_appl (Constant "==") [Variable "P", Variable "Q"],
 mk_appl (Constant "кл" ) [Variable "P", Variable "Q"] <-> 
 mk_appl (Constant "==>") [Variable "P", Variable "Q"],
 (Constant "Д" ) <->  (Constant "!!")]
end;
