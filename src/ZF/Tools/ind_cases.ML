(*  Title:      ZF/Tools/ind_cases.ML
    ID:         $Id$
    Author:     Markus Wenzel, LMU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Generic inductive cases facility for (co)inductive definitions.
*)

signature IND_CASES =
sig
  val declare: string -> (simpset -> cterm -> thm) -> theory -> theory
  val inductive_cases: ((bstring * Args.src list) * string list) list -> theory -> theory
  val setup: (theory -> theory) list
end;

structure IndCases: IND_CASES =
struct


(* theory data *)

structure IndCasesArgs =
struct
  val name = "ZF/ind_cases";
  type T = (simpset -> cterm -> thm) Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val prep_ext = I;
  fun merge (tab1, tab2) = Symtab.merge (K true) (tab1, tab2);
  fun print _ _ = ();
end;

structure IndCasesData = TheoryDataFun(IndCasesArgs);

fun declare name f = IndCasesData.map (fn tab => Symtab.update ((name, f), tab));

fun smart_cases thy ss read_prop s =
  let
    fun err () = error ("Malformed set membership statement: " ^ s);
    val A = read_prop s handle ERROR => err ();
    val c = #1 (Term.dest_Const (Term.head_of (#2 (Ind_Syntax.dest_mem (FOLogic.dest_Trueprop
      (Logic.strip_imp_concl A)))))) handle TERM _ => err ();
  in
    (case Symtab.lookup (IndCasesData.get thy, c) of
      None => error ("Unknown inductive cases rule for set " ^ quote c)
    | Some f => f ss (Thm.cterm_of (Theory.sign_of thy) A))
  end;


(* inductive_cases command *)

fun inductive_cases args thy =
  let
    val read_prop = ProofContext.read_prop (ProofContext.init thy);
    val mk_cases = smart_cases thy (Simplifier.simpset_of thy) read_prop;
    val facts = args |> map (fn ((name, srcs), props) =>
      ((name, map (Attrib.global_attribute thy) srcs),
        map (Thm.no_attributes o single o mk_cases) props));
  in thy |> IsarThy.theorems_i Drule.lemmaK facts |> #1 end;


(* ind_cases method *)

fun mk_cases_meth (ctxt, props) =
  props
  |> map (smart_cases (ProofContext.theory_of ctxt) (Simplifier.get_local_simpset ctxt)
    (ProofContext.read_prop ctxt))
  |> Method.erule 0;

val mk_cases_args = Method.syntax (Scan.lift (Scan.repeat1 Args.name));


(* package setup *)

val setup =
 [IndCasesData.init,
  Method.add_methods [("ind_cases", mk_cases_meth oo mk_cases_args,
    "dynamic case analysis on sets")]];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val ind_cases =
  P.and_list1 (P.opt_thm_name ":" -- Scan.repeat1 P.prop)
  >> (Toplevel.theory o inductive_cases);

val inductive_casesP =
  OuterSyntax.command "inductive_cases"
    "create simplified instances of elimination rules (improper)" K.thy_script ind_cases;

val _ = OuterSyntax.add_parsers [inductive_casesP];

end;

end;
