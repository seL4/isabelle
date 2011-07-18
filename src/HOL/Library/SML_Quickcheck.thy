
header {* Install quickcheck of SML code generator *}

theory SML_Quickcheck
imports Main
begin

ML {*
signature SML_QUICKCHECK =
sig
  val active : bool Config.T
  val setup : theory -> theory  
end;

structure SML_Quickcheck : SML_QUICKCHECK =
struct

val active = Attrib.setup_config_bool @{binding quickcheck_SML_active} (K true);

fun compile_generator_expr ctxt [(t, eval_terms)] [_, size] =
  let
    val prop = list_abs_free (Term.add_frees t [], t)
    val test_fun = Codegen.test_term ctxt prop
    val iterations = Config.get ctxt Quickcheck.iterations
    fun iterate size 0 = NONE
      | iterate size j =
          let
            val result = test_fun size handle Match =>
              (if Config.get ctxt Quickcheck.quiet then ()
               else warning "Exception Match raised during quickcheck"; NONE)
          in
            case result of NONE => iterate size (j - 1) | SOME q => SOME q
          end
  in (iterate size iterations, NONE) end

val test_goals = Quickcheck.generator_test_goal_terms compile_generator_expr

val setup =
  Inductive_Codegen.quickcheck_setup
  #> Context.theory_map (Quickcheck.add_tester ("SML", (active, test_goals)))

end;
*}

setup {* SML_Quickcheck.setup *}

end
