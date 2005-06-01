(*  Title:      Pure/Isar/term_style.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Styles for terms, to use with the "term_style" and "thm_style" antiquotations.
*)

signature TERM_STYLE =
sig
  val the_style: theory -> string -> (Proof.context -> term -> term)
  val add_style: string -> (Proof.context -> term -> term) -> theory -> theory
  val print_styles: theory -> unit
end;

structure TermStyle: TERM_STYLE =
struct

(* style data *)

fun err_dup_styles names =
  error ("Duplicate declaration of antiquote style(s): " ^ commas_quote names);

structure StyleArgs =
struct
  val name = "Isar/style";
  type T = ((Proof.context -> term -> term) * stamp) Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val prep_ext = I;
  fun merge tabs = Symtab.merge eq_snd tabs
    handle Symtab.DUPS dups => err_dup_styles dups;
  fun print _ tab = Pretty.writeln (Pretty.strs ("antiquote styles:" :: Symtab.keys tab));
end;

structure StyleData = TheoryDataFun(StyleArgs);
val _ = Context.add_setup [StyleData.init];
val print_styles = StyleData.print;


(* accessors *)

fun the_style thy name =
  (case Symtab.lookup (StyleData.get thy, name) of
    NONE => error ("Unknown antiquote style: " ^ quote name)
  | SOME (style, _) => style);

fun add_style name style thy =
  StyleData.map (curry Symtab.update_new (name, (style, stamp ()))) thy
    handle Symtab.DUP _ => err_dup_styles [name];


(* predefined styles *)

fun style_binargs ctxt t =
  let val concl = ObjectLogic.drop_judgment (ProofContext.sign_of ctxt) (Logic.strip_imp_concl t) in
    case concl of (_ $ l $ r) => (l, r)
    | _ => error ("Binary operator expected in term: " ^ ProofContext.string_of_term ctxt concl)
  end;

fun premise i _ t =
  let val prems = Logic.strip_imp_prems t
  in if i <= length prems then List.nth(prems,i-1)
     else error ("Not enough premises: premise" ^ string_of_int i)
  end;
 
val _ = Context.add_setup
 [add_style "lhs" (fst oo style_binargs),
  add_style "rhs" (snd oo style_binargs),
  add_style "premise1" (premise 1),
  add_style "premise2" (premise 2),
  add_style "premise3" (premise 3),
  add_style "premise4" (premise 4),
  add_style "premise5" (premise 5),
  add_style "premise6" (premise 6),
  add_style "premise7" (premise 7),
  add_style "premise8" (premise 8),
  add_style "premise9" (premise 9),
  add_style "conclusion" (K Logic.strip_imp_concl)];

end;
