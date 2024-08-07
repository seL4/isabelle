(*  Title:      ZF/Tools/ind_cases.ML
    Author:     Markus Wenzel, LMU Muenchen

Generic inductive cases facility for (co)inductive definitions.
*)

signature IND_CASES =
sig
  val declare: string -> (Proof.context -> conv) -> theory -> theory
  val inductive_cases: (Attrib.binding * string list) list -> theory -> theory
end;

structure IndCases: IND_CASES =
struct


(* theory data *)

structure IndCasesData = Theory_Data
(
  type T = (Proof.context -> conv) Symtab.table;
  val empty = Symtab.empty;
  fun merge data = Symtab.merge (K true) data;
);


fun declare name f = IndCasesData.map (Symtab.update (name, f));

fun smart_cases ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun err msg = cat_error msg ("Malformed set membership statement: " ^ s);
    val A = Syntax.read_prop ctxt s handle ERROR msg => err msg;
    val c = dest_Const_name (Term.head_of (#2 (Ind_Syntax.dest_mem (\<^dest_judgment>
      (Logic.strip_imp_concl A))))) handle TERM _ => err "";
  in
    (case Symtab.lookup (IndCasesData.get thy) c of
      NONE => error ("Unknown inductive cases rule for set " ^ quote c)
    | SOME f => f ctxt (Thm.cterm_of ctxt A))
  end;


(* inductive_cases command *)

fun inductive_cases args thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val facts = args |> map (fn ((name, srcs), props) =>
      ((name, map (Attrib.attribute_cmd ctxt) srcs),
        map (Thm.no_attributes o single o smart_cases ctxt) props));
  in thy |> Global_Theory.note_thmss "" facts |> snd end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>inductive_cases\<close>
    "create simplified instances of elimination rules (improper)"
    (Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.prop)
      >> (Toplevel.theory o inductive_cases));


(* ind_cases method *)

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>ind_cases\<close>
      (Scan.lift (Scan.repeat1 Parse.embedded_inner_syntax) >>
        (fn props => fn ctxt => Method.erule ctxt 0 (map (smart_cases ctxt) props)))
      "dynamic case analysis on sets");

end;

