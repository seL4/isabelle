(*  Title:      Pure/ML_Bootstrap.thy
    Author:     Makarius

ML bootstrap environment -- with access to low-level structures!
*)

theory ML_Bootstrap
imports Pure
  options [condition = true]
begin

ML \<open>
  structure Output_Primitives = Output_Primitives_Virtual;
  structure Thread_Data = Thread_Data_Virtual;
  structure PolyML = PolyML;
  structure RunCall = RunCall;
  structure Foreign = Foreign;
  fun ML_system_pp (_: FixedInt.int -> 'a -> 'b -> PolyML.pretty) = ();

  Proofterm.proofs := 0;

  Context.setmp_generic_context NONE
    ML \<open>
      structure PolyML =
      struct
        val pointerEq = pointer_eq;
        val exit = PolyML.exit;
        structure IntInf = PolyML.IntInf;
        datatype context = datatype PolyML.context;
        datatype pretty = datatype PolyML.pretty;
      end;
      structure RunCall = struct end;
      structure Foreign = Foreign;
    \<close>
\<close>

setup \<open>Context.theory_map ML_Env.bootstrap_name_space\<close>

declare [[ML_read_global = false, ML_check_strings = false, ML_catch_all = true]]

end
