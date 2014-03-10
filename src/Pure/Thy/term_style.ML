(*  Title:      Pure/Thy/term_style.ML
    Author:     Florian Haftmann, TU Muenchen

Styles for term printing.
*)

signature TERM_STYLE =
sig
  val setup: string -> (Proof.context -> term -> term) parser -> theory -> theory
  val parse: (term -> term) context_parser
end;

structure Term_Style: TERM_STYLE =
struct

(* style data *)

fun err_dup_style name =
  error ("Duplicate declaration of antiquote style: " ^ quote name);

structure Styles = Theory_Data
(
  type T = ((Proof.context -> term -> term) parser * stamp) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (eq_snd (op =)) data
    handle Symtab.DUP dup => err_dup_style dup;
);


(* accessors *)

fun the_style thy name =
  (case Symtab.lookup (Styles.get thy) name of
    NONE => error ("Unknown antiquote style: " ^ quote name)
  | SOME (style, _) => style);

fun setup name style thy =
  Styles.map (Symtab.update_new (name, (style, stamp ()))) thy
    handle Symtab.DUP _ => err_dup_style name;


(* style parsing *)

fun parse_single ctxt = Parse.position Parse.xname -- Args.parse
  >> (fn ((name, pos), args) => fst (Args.context_syntax "style"
       (Scan.lift (the_style (Proof_Context.theory_of ctxt) name))
         (Args.src (name, pos) args) ctxt |>> (fn f => f ctxt)));

val parse = Args.context :|-- (fn ctxt => Scan.lift
  (Args.parens (parse_single ctxt ::: Scan.repeat (Args.$$$ "," |-- parse_single ctxt))
      >> fold I
  || Scan.succeed I));


(* predefined styles *)

fun style_lhs_rhs proj = Scan.succeed (fn ctxt => fn t =>
  let
    val concl =
      Object_Logic.drop_judgment (Proof_Context.theory_of ctxt) (Logic.strip_imp_concl t)
  in
    (case concl of
      (_ $ l $ r) => proj (l, r)
    | _ => error ("Binary operator expected in term: " ^ Syntax.string_of_term ctxt concl))
  end);

val style_prem = Parse.nat >> (fn i => fn ctxt => fn t =>
  let
    val prems = Logic.strip_imp_prems t;
  in
    if i <= length prems then nth prems (i - 1)
    else
      error ("Not enough premises for prem " ^ string_of_int i ^
        " in propositon: " ^ Syntax.string_of_term ctxt t)
  end);

fun sub_symbols (d :: s :: ss) =
      if Symbol.is_ascii_digit d andalso not (String.isPrefix ("\\<^") s)
      then d :: "\\<^sub>" :: sub_symbols (s :: ss)
      else d :: s :: ss
  | sub_symbols cs = cs;

val sub_name = implode o rev o sub_symbols o rev o Symbol.explode;

fun sub_term (Free (n, T)) = Free (sub_name n, T)
  | sub_term (Var ((n, idx), T)) =
      if idx <> 0 then Var ((sub_name (n ^ string_of_int idx), 0), T)
      else Var ((sub_name n, 0), T)
  | sub_term (t $ u) = sub_term t $ sub_term u
  | sub_term (Abs (n, T, b)) = Abs (sub_name n, T, sub_term b)
  | sub_term t = t;

val _ = Theory.setup
 (setup "lhs" (style_lhs_rhs fst) #>
  setup "rhs" (style_lhs_rhs snd) #>
  setup "prem" style_prem #>
  setup "concl" (Scan.succeed (K Logic.strip_imp_concl)) #>
  setup "sub" (Scan.succeed (K sub_term)));

end;
