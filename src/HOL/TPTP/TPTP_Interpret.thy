(*  Title:      HOL/TPTP/TPTP_Interpret.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Importing TPTP files into Isabelle/HOL: parsing TPTP formulas and
interpreting them as HOL terms (i.e. importing types and type-checking the terms)
*)

theory TPTP_Interpret
imports Complex_Main TPTP_Parser
keywords "import_tptp" :: thy_decl
begin

typedecl ind

ML_file "TPTP_Parser/tptp_interpret.ML"


ML {*
open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open ATP_Systems

fun exploded_absolute_path file_name =
  Path.explode file_name
  |> (fn path => path |> not (Path.is_absolute path) ? Path.append (Path.explode "$PWD"))

fun read_tptp_file thy postproc file_name =
  let
    fun has_role role (_, role', _, _) = (role' = role)
    fun get_prop f (name, _, P, _) =
      let val P' = P |> f |> close_form in
        (name, P') |> postproc
      end
    val path = exploded_absolute_path file_name
    val ((_, _, problem), thy) =
      TPTP_Interpret.interpret_file true [Path.dir path, Path.explode "$TPTP"]
                                    path [] [] thy
    val (conjs, defs_and_nondefs) =
      problem |> List.partition (has_role TPTP_Syntax.Role_Conjecture)
              ||> List.partition (has_role TPTP_Syntax.Role_Definition)
  in
    (map (get_prop I) conjs,
     pairself (map (get_prop Logic.varify_global)) defs_and_nondefs,
     Proof_Context.init_global thy)
  end
*}

declare [[ML_exception_trace]]

setup {*
snd o Theory.specify_const ((@{binding c}, @{typ "'b * 'a"}), NoSyn)
*}

ML {* Sign.the_const_type @{theory} @{const_name c} *}

declare [[ML_print_depth = 1000]]

ML {*
let
  val (conjs, (defs, nondefs), _) = read_tptp_file @{theory} snd (* "/Users/blanchet/tmp/e.tptp" *)
    "/Users/blanchet/.isabelle/prob_alt_ergo_1"
  val ts = conjs @ defs @ nondefs
    |> map (map_aterms (fn Const (s, T) =>
        if String.isPrefix "TPTP" s then
          Const (s |> Long_Name.base_name |> perhaps (try (unprefix "bnd_")), T)
        else
          Const (s, T)
      | t => t))
in
  tracing (cat_lines (map (Syntax.string_of_term_global @{theory}) ts));
  tracing (cat_lines (map @{make_string} ts))
end
*}

end