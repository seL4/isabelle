theory SMT_CVC \<comment> \<open>More Setup for CVC that should be in HOL eventually\<close>
  imports HOL.SMT "HOL.Alethe_Rare_Interface"
begin

(*Term rewrites*)

ML \<open>

 fun power _ _ [t1] =
    let
      val mk = Term.list_comb o pair @{term "pow_2"}
    in SOME ("int.pow2", 1, [t1], mk) end
 | power _ _ _ = NONE

val setup_builtins =
  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (("int.pow2", Term.dest_Const (\<^Const>\<open>SMT.pow_2\<close>) |> snd), power)

val _ = Theory.setup (Context.theory_map (
  setup_builtins 
))
\<close>

(*check that int.pow2 is properly registered*)
ML \<open>
if is_none (SMT_Builtin.dest_builtin_fun @{context}
  ("int.pow2", @{typ "int \<Rightarrow> int"})
   [@{term "2::int"}])
then error "fail to recognize int.pow2" else ()\<close>

end
