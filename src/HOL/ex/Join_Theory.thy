(*  Title:      HOL/ex/Join_Theory.thy
    Author:     Makarius
*)

section \<open>Join theory content from independent (parallel) specifications\<close>

theory Join_Theory
  imports Main
begin

subsection \<open>Example template\<close>

definition "test = True"
lemma test: "test" by (simp add: test_def)


subsection \<open>Specification as Isabelle/ML function\<close>

ML \<open>
  fun spec i lthy =
    let
      val b = Binding.name ("test" ^ string_of_int i)
      val ((t, (_, def)), lthy') = lthy
        |> Local_Theory.define ((b, NoSyn), ((Binding.empty, []), \<^term>\<open>True\<close>));
      val th =
        Goal.prove lthy' [] [] (HOLogic.mk_Trueprop t)
          (fn {context = goal_ctxt, ...} => asm_full_simp_tac (goal_ctxt addsimps [def]) 1);
      val (_, lthy'') = lthy' |> Local_Theory.note ((b, []), [th]);
    in lthy'' end;
\<close>


subsection \<open>Example application\<close>

setup \<open>
  fn thy =>
    let val forked_thys = Par_List.map (fn i => Named_Target.theory_map (spec i) thy) (1 upto 10)
    in Theory.join_theory forked_thys end
\<close>

term test1
thm test1

term test10
thm test10

end
