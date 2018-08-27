(*  Title:      Pure/ML_Bootstrap.thy
    Author:     Makarius

ML bootstrap environment -- with access to low-level structures!
*)

theory ML_Bootstrap
imports Pure
begin

external_file "$POLYML_EXE"


subsection \<open>ML environment for virtual bootstrap\<close>

ML \<open>
  #allStruct ML_Name_Space.global () |> List.app (fn (name, _) =>
    if member (op =) ML_Name_Space.hidden_structures name then
      ML (Input.string ("structure " ^ name ^ " = " ^ name))
    else ());
  structure Output_Primitives = Output_Primitives_Virtual;
  structure Thread_Data = Thread_Data_Virtual;
  structure PolyML = PolyML;
  fun ML_system_pp (_: FixedInt.int -> 'a -> 'b -> PolyML_Pretty.pretty) = ();
\<close>


subsection \<open>Global ML environment for Isabelle/Pure\<close>

ML \<open>Proofterm.proofs := 0\<close>

ML \<open>
  Context.setmp_generic_context NONE
    ML \<open>
      List.app ML_Name_Space.forget_structure ML_Name_Space.hidden_structures;
      structure PolyML =
      struct
        val pointerEq = pointer_eq;
        structure IntInf = PolyML.IntInf;
      end;
    \<close>
\<close>

setup \<open>Context.theory_map ML_Env.bootstrap_name_space\<close>
declare [[ML_read_global = false]]

end
