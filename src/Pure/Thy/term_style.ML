(*  Title:      Pure/Thy/term_style.ML
    Author:     Florian Haftmann, TU Muenchen

Styles for term printing.
*)

signature TERM_STYLE =
sig
  val setup: string -> (Proof.context -> term -> term) parser -> theory -> theory
  val parse: (term -> term) context_parser
  val parse_bare: (term -> term) context_parser
end;

structure Term_Style: TERM_STYLE =
struct

(* style data *)

fun err_dup_style name =
  error ("Duplicate declaration of antiquote style: " ^ quote name);

structure StyleData = TheoryDataFun
(
  type T = ((Proof.context -> term -> term) parser * stamp) Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ tabs : T = Symtab.merge (eq_snd (op =)) tabs
    handle Symtab.DUP dup => err_dup_style dup;
);


(* accessors *)

fun the_style thy name =
  (case Symtab.lookup (StyleData.get thy) name of
    NONE => error ("Unknown antiquote style: " ^ quote name)
  | SOME (style, _) => style);

fun setup name style thy =
  StyleData.map (Symtab.update_new (name, (style, stamp ()))) thy
    handle Symtab.DUP _ => err_dup_style name;


(* style parsing *)

fun parse_single ctxt = OuterParse.position (OuterParse.xname -- Args.parse)
  >> (fn x as ((name, _), _) => fst (Args.context_syntax "style"
       (Scan.lift (the_style (ProofContext.theory_of ctxt) name))
         (Args.src x) ctxt |>> (fn f => f ctxt)));

val parse = Args.context :|-- (fn ctxt => Scan.lift 
  (Args.parens (parse_single ctxt ::: Scan.repeat (Args.$$$ "," |-- parse_single ctxt))
      >> fold I
  || Scan.succeed I));

val parse_bare = Args.context :|-- (fn ctxt => Scan.lift Args.liberal_name
  >> (fn name => fst (Args.context_syntax "style"
       (Scan.lift (the_style (ProofContext.theory_of ctxt) name))
          (Args.src (("style", []), Position.none)) ctxt |>> (fn f => f ctxt))));


(* predefined styles *)

fun style_lhs_rhs proj = Scan.succeed (fn ctxt => fn t =>
  let
    val concl = ObjectLogic.drop_judgment (ProofContext.theory_of ctxt)
      (Logic.strip_imp_concl t)
  in
    case concl of (_ $ l $ r) => proj (l, r)
    | _ => error ("Binary operator expected in term: " ^ Syntax.string_of_term ctxt concl)
  end);

val style_prem = Args.name >> (fn raw_i => fn ctxt => fn t =>
  let
    val i = (the o Int.fromString) raw_i;
    val prems = Logic.strip_imp_prems t;
  in
    if i <= length prems then nth prems (i - 1)
    else error ("Not enough premises for prem " ^ string_of_int i ^
      " in propositon: " ^ Syntax.string_of_term ctxt t)
  end);

fun style_parm_premise i = Scan.succeed (fn ctxt => fn t =>
  let
    val i_str = string_of_int i;
    val prems = Logic.strip_imp_prems t;
  in
    if i <= length prems then nth prems (i - 1)
    else error ("Not enough premises for prem" ^ string_of_int i ^
      " in propositon: " ^ Syntax.string_of_term ctxt t)
  end);

val _ = Context.>> (Context.map_theory
 (setup "lhs" (style_lhs_rhs fst) #>
  setup "rhs" (style_lhs_rhs snd) #>
  setup "prem" style_prem #>
  setup "concl" (Scan.succeed (K Logic.strip_imp_concl)) #>
  setup "prem1" (style_parm_premise 1) #>
  setup "prem2" (style_parm_premise 2) #>
  setup "prem3" (style_parm_premise 3) #>
  setup "prem4" (style_parm_premise 4) #>
  setup "prem5" (style_parm_premise 5) #>
  setup "prem6" (style_parm_premise 6) #>
  setup "prem7" (style_parm_premise 7) #>
  setup "prem8" (style_parm_premise 8) #>
  setup "prem9" (style_parm_premise 9) #>
  setup "prem10" (style_parm_premise 10) #>
  setup "prem11" (style_parm_premise 11) #>
  setup "prem12" (style_parm_premise 12) #>
  setup "prem13" (style_parm_premise 13) #>
  setup "prem14" (style_parm_premise 14) #>
  setup "prem15" (style_parm_premise 15) #>
  setup "prem16" (style_parm_premise 16) #>
  setup "prem17" (style_parm_premise 17) #>
  setup "prem18" (style_parm_premise 18) #>
  setup "prem19" (style_parm_premise 19)));

end;
