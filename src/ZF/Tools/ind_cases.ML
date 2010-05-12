(*  Title:      ZF/Tools/ind_cases.ML
    Author:     Markus Wenzel, LMU Muenchen

Generic inductive cases facility for (co)inductive definitions.
*)

signature IND_CASES =
sig
  val declare: string -> (Proof.context -> conv) -> theory -> theory
  val inductive_cases: (Attrib.binding * string list) list -> theory -> theory
  val setup: theory -> theory
end;

structure IndCases: IND_CASES =
struct


(* theory data *)

structure IndCasesData = Theory_Data
(
  type T = (Proof.context -> conv) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);


fun declare name f = IndCasesData.map (Symtab.update (name, f));

fun smart_cases ctxt s =
  let
    val thy = ProofContext.theory_of ctxt;
    fun err msg = cat_error msg ("Malformed set membership statement: " ^ s);
    val A = Syntax.read_prop ctxt s handle ERROR msg => err msg;
    val c = #1 (Term.dest_Const (Term.head_of (#2 (Ind_Syntax.dest_mem (FOLogic.dest_Trueprop
      (Logic.strip_imp_concl A)))))) handle TERM _ => err "";
  in
    (case Symtab.lookup (IndCasesData.get thy) c of
      NONE => error ("Unknown inductive cases rule for set " ^ quote c)
    | SOME f => f ctxt (Thm.cterm_of thy A))
  end;


(* inductive_cases command *)

fun inductive_cases args thy =
  let
    val ctxt = ProofContext.init_global thy;
    val facts = args |> map (fn ((name, srcs), props) =>
      ((name, map (Attrib.attribute thy) srcs),
        map (Thm.no_attributes o single o smart_cases ctxt) props));
  in thy |> PureThy.note_thmss "" facts |> snd end;


(* ind_cases method *)

val setup =
  Method.setup @{binding "ind_cases"}
    (Scan.lift (Scan.repeat1 Args.name_source) >>
      (fn props => fn ctxt => Method.erule 0 (map (smart_cases ctxt) props)))
    "dynamic case analysis on sets";


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val _ =
  OuterSyntax.command "inductive_cases"
    "create simplified instances of elimination rules (improper)" K.thy_script
    (P.and_list1 (SpecParse.opt_thm_name ":" -- Scan.repeat1 P.prop)
      >> (Toplevel.theory o inductive_cases));

end;

end;

