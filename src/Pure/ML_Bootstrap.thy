(*  Title:      Pure/ML_Bootstrap.thy
    Author:     Makarius

ML bootstrap environment -- with access to low-level structures!
*)

theory ML_Bootstrap
imports Pure
begin

setup \<open>Context.theory_map ML_Env.init_bootstrap\<close>

SML_import \<open>
structure Output_Primitives = Output_Primitives_Virtual;
structure Thread_Data = Thread_Data_Virtual;
\<close>

setup \<open>Config.put_global ML_Env.SML_environment true\<close>

end
