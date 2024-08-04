(*:maxLineLen=78:*)

section \<open>Basic setup that is not included in the document\<close>

theory Base
imports Main
begin

ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>

ML\<open>
fun get_split_rule ctxt target =
  let
    val (head, args) = strip_comb (Envir.eta_contract target);
    val const_name = dest_Const_name head;
    val const_name_components = Long_Name.explode const_name;

    val _ =
      if String.isPrefix "case_" (List.last const_name_components) then ()
      else raise TERM ("Not a case statement", [target]);

    val type_name = Long_Name.implode (rev (tl (rev const_name_components)));
    val split = Proof_Context.get_thm ctxt (type_name ^ ".split");
    val vars = Term.add_vars (Thm.prop_of split) [];

    val datatype_name = nth (rev const_name_components) 1;

    fun is_datatype (Type (a, _)) = Long_Name.base_name a = Long_Name.base_name datatype_name
      | is_datatype _ = false;

    val datatype_var =
      (case find_first (fn (_, T') => is_datatype T') vars of
        SOME (xi, _) => xi
      | NONE => error ("Couldn't find datatype in thm: " ^ datatype_name));
  in
    SOME (infer_instantiate ctxt [(datatype_var, Thm.cterm_of ctxt (List.last args))] split)
  end
  handle TERM _ => NONE;
\<close>

end
