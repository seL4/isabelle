(*  Title:      Pure/Isar/term_style.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Styles for terms, to use with the "term_style" and "thm_style" antiquotations
*)

(* style data *)
signature TERM_STYLE =
sig
  val lookup_style: theory -> string -> (Proof.context -> term -> term)
  val update_style: string -> (Proof.context -> term -> term) -> theory -> theory
end;

structure TermStyle: TERM_STYLE =
struct

structure StyleArgs =
struct
  val name = "Isar/style";
  type T = (Proof.context -> term -> term) Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val prep_ext = I;
  val merge = Symtab.merge (K true);
  fun print _ table =
    Pretty.strs ("defined styles:" :: (Symtab.keys table))
    |> Pretty.writeln;
end;

structure StyleData = TheoryDataFun(StyleArgs);

(* accessors *)
fun lookup_style thy name =
  case Symtab.lookup ((StyleData.get thy), name)
    of NONE => raise (ERROR_MESSAGE ("no style named " ^ name))
     | SOME style => style

fun update_style name style thy =
  thy
  |> StyleData.put (Symtab.update ((name, style), StyleData.get thy));

(* predefined styles *)
fun style_binargs ctxt t =
  let val concl = ObjectLogic.drop_judgment (ProofContext.sign_of ctxt) (Logic.strip_imp_concl t) in
    case concl of (_ $ l $ r) => (l, r)
        | _ => error ("Binary operator expected in term: " ^ ProofContext.string_of_term ctxt concl)
  end;

(* initialization *)
val _ = Context.add_setup [StyleData.init,
  update_style "lhs" (fst oo style_binargs),
  update_style "rhs" (snd oo style_binargs),
  update_style "conclusion" (K Logic.strip_imp_concl)
];

end;
