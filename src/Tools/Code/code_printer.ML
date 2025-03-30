(*  Title:      Tools/Code/code_printer.ML
    Author:     Florian Haftmann, TU Muenchen

Generic operations for pretty printing of target language code.
*)

signature CODE_PRINTER =
sig
  type itype = Code_Thingol.itype
  type iterm = Code_Thingol.iterm
  type const = Code_Thingol.const

  val eqn_error: theory -> thm option -> string -> 'a

  val @@ : 'a * 'a -> 'a list
  val @| : 'a list * 'a -> 'a list
  val concat: Pretty.T list -> Pretty.T
  val brackets: Pretty.T list -> Pretty.T
  val enum_default: string -> string -> string -> string -> Pretty.T list -> Pretty.T
  val semicolon: Pretty.T list -> Pretty.T
  val doublesemicolon: Pretty.T list -> Pretty.T
  val markup_stmt: Code_Symbol.T -> Pretty.T -> Pretty.T
  val format: Code_Symbol.T list -> int -> Pretty.T -> Bytes.T

  type var_ctxt
  val make_vars: string list -> var_ctxt
  val intro_vars: string list -> var_ctxt -> var_ctxt
  val lookup_var: var_ctxt -> string -> string
  val intro_base_names: (string -> bool) -> (string -> string)
    -> string list -> var_ctxt -> var_ctxt
  val intro_base_names_for: (string -> bool) -> (Code_Symbol.T -> string)
    -> iterm list -> var_ctxt -> var_ctxt
  val aux_params: var_ctxt -> iterm list list -> string list

  type literals
  val Literals: { literal_string: string -> string,
        literal_numeral: int -> string,
        literal_list: Pretty.T list -> Pretty.T, infix_cons: int * string }
    -> literals
  val literal_string: literals -> string -> string
  val literal_numeral: literals -> int -> string
  val literal_list: literals -> Pretty.T list -> Pretty.T
  val infix_cons: literals -> int * string

  type lrx
  val L: lrx
  val R: lrx
  val X: lrx
  type fixity
  val BR: fixity
  val NOBR: fixity
  val INFX: int * lrx -> fixity
  val APP: fixity
  val brackify: fixity -> Pretty.T list -> Pretty.T
  val brackify_infix: int * lrx -> fixity -> Pretty.T * Pretty.T * Pretty.T -> Pretty.T
  val brackify_block: fixity -> Pretty.T -> Pretty.T list -> Pretty.T -> Pretty.T
  val gen_applify: bool -> string -> string -> ('a -> Pretty.T) -> fixity -> Pretty.T -> 'a list -> Pretty.T
  val applify: string -> string -> ('a -> Pretty.T) -> fixity -> Pretty.T -> 'a list -> Pretty.T
  val tuplify: (fixity -> 'a -> Pretty.T) -> fixity -> 'a list -> Pretty.T option

  val parse_target_source: string parser
  type raw_const_syntax
  val plain_const_syntax: string -> raw_const_syntax
  type simple_const_syntax
  val simple_const_syntax: simple_const_syntax -> raw_const_syntax
  type complex_const_syntax
  val complex_const_syntax: complex_const_syntax -> raw_const_syntax
  val parse_const_syntax: raw_const_syntax parser
  val requires_args: raw_const_syntax -> int
  datatype const_printer = Plain_printer of string
    | Complex_printer of (var_ctxt -> fixity -> iterm -> Pretty.T)
        -> thm option -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T
  type const_syntax = int * const_printer
  val prep_const_syntax: theory -> literals
    -> string -> raw_const_syntax -> const_syntax
  type tyco_syntax
  val parse_tyco_syntax: tyco_syntax parser
  val gen_print_app: (thm option -> var_ctxt -> const * iterm list -> Pretty.T list)
    -> (thm option -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> (string -> const_syntax option)
    -> thm option -> var_ctxt -> fixity -> const * iterm list -> Pretty.T
  val gen_print_bind: (thm option -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm option -> fixity
    -> iterm -> var_ctxt -> Pretty.T * var_ctxt

  type identifiers
  type printings
  type data
  val empty_data: data
  val map_data: (string list * identifiers * printings
    -> string list * identifiers * printings)
    -> data -> data
  val merge_data: data * data -> data
  val the_reserved: data -> string list;
  val the_identifiers: data -> identifiers;
  val the_printings: data -> printings;
end;

structure Code_Printer : CODE_PRINTER =
struct

open Basic_Code_Symbol;
open Code_Thingol;

(** generic nonsense *)

fun eqn_error thy (SOME thm) s =
      error (s ^ ",\nin equation " ^ Thm.string_of_thm_global thy thm)
  | eqn_error _ NONE s = error s;


(** assembling and printing text pieces **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val concat = Pretty.block o Pretty.breaks;
val commas = Pretty.commas;
val brackets = Pretty.enclose "(" ")" o Pretty.breaks;
fun enum_default default sep l r [] = Pretty.str default
  | enum_default default sep l r xs = Pretty.enum sep l r xs;
fun semicolon ps = Pretty.block [concat ps, Pretty.str ";"];
fun doublesemicolon ps = Pretty.block [concat ps, Pretty.str ";;"];

fun markup_stmt sym =
  Pretty.mark (Markup.code_presentationN, [(Markup.stmt_nameN, Code_Symbol.marker sym)]);

fun filter_presentation [] xml =
      Bytes.build (XML.traverse_texts Bytes.add xml)
  | filter_presentation presentation_syms xml =
      let
        val presentation_idents = map Code_Symbol.marker presentation_syms
        fun is_selected (name, attrs) =
          name = Markup.code_presentationN
          andalso member (op =) presentation_idents (the (Properties.get attrs Markup.stmt_nameN));
        fun add_content_with_space tree (is_first, buf) =
          buf
          |> not is_first ? Bytes.add "\n\n"
          |> XML.traverse_text Bytes.add tree
          |> pair false;
        fun filter (XML.Elem (elem, body)) =
              fold (if is_selected elem then add_content_with_space else filter) body
          | filter (XML.Text _) = I;
      in snd (fold filter xml (true, Bytes.empty)) end;

fun format presentation_names width =
  Pretty.output (Pretty.markup_output_ops (SOME width))
  #> YXML.parse_body_bytes
  #> filter_presentation presentation_names
  #> Bytes.add "\n";


(** names and variable name contexts **)

type var_ctxt = string Symtab.table * Name.context;

fun make_vars names = (fold (fn name => Symtab.update_new (name, name)) names Symtab.empty,
  Name.make_context names);

fun intro_vars names (namemap, namectxt) =
  let
    val (names', namectxt') = fold_map Name.variant names namectxt;
    val namemap' = fold2 (curry Symtab.update) names names' namemap;
  in (namemap', namectxt') end;

fun lookup_var (namemap, _) name =
  case Symtab.lookup namemap name of
    SOME name' => name'
  | NONE => error ("Invalid name in context: " ^ quote name);

fun aux_params vars lhss =
  let
    fun fish_param _ (w as SOME _) = w
      | fish_param (IVar (SOME v)) NONE = SOME v
      | fish_param _ NONE = NONE;
    fun fillup_param _ (_, SOME v) = v
      | fillup_param x (i, NONE) = x ^ string_of_int i;
    val fished1 = fold (map2 fish_param) lhss (replicate (length (hd lhss)) NONE);
    val x = singleton (Name.variant_list (map_filter I fished1)) "x";
    val fished2 = map_index (fillup_param x) fished1;
    val fished3 = Name.variants Name.context fished2;
    val vars' = intro_vars fished3 vars;
  in map (lookup_var vars') fished3 end;

fun intro_base_names no_syntax deresolve =
  map_filter (fn name => if no_syntax name then
      let val name' = deresolve name in
        if Long_Name.is_qualified name' then NONE else SOME name'
      end else NONE)
  #> intro_vars;

fun intro_base_names_for no_syntax deresolve ts =
  []
  |> fold Code_Thingol.add_constsyms ts 
  |> intro_base_names (fn Constant const => no_syntax const | _ => true) deresolve;


(** pretty literals **)

datatype literals = Literals of {
  literal_string: string -> string,
  literal_numeral: int -> string,
  literal_list: Pretty.T list -> Pretty.T,
  infix_cons: int * string
};

fun dest_Literals (Literals lits) = lits;

val literal_string = #literal_string o dest_Literals;
val literal_numeral = #literal_numeral o dest_Literals;
val literal_list = #literal_list o dest_Literals;
val infix_cons = #infix_cons o dest_Literals;


(** syntax printer **)

(* binding priorities *)

datatype lrx = L | R | X;

datatype fixity =
    BR
  | NOBR
  | INFX of (int * lrx);

val APP = INFX (~1, L);

fun fixity_lrx L L = false
  | fixity_lrx R R = false
  | fixity_lrx _ _ = true;

fun fixity NOBR _ = false
  | fixity _ NOBR = false
  | fixity (INFX (pr, lr)) (INFX (pr_ctxt, lr_ctxt)) =
      pr < pr_ctxt
      orelse pr = pr_ctxt
        andalso fixity_lrx lr lr_ctxt
      orelse pr_ctxt = ~1
  | fixity BR (INFX _) = false
  | fixity _ _ = true;

fun gen_brackify _ [p] = p
  | gen_brackify true (ps as _::_) = Pretty.enclose "(" ")" ps
  | gen_brackify false (ps as _::_) = Pretty.block ps;

fun brackify fxy_ctxt =
  gen_brackify (fixity BR fxy_ctxt) o Pretty.breaks;

fun brackify_infix infx fxy_ctxt (l, m, r) =
  gen_brackify (fixity (INFX infx) fxy_ctxt) [l, Pretty.str " ", m, Pretty.brk 1, r];

fun brackify_block fxy_ctxt p1 ps p2 =
  let val p = Pretty.block_enclose (p1, p2) ps
  in if fixity BR fxy_ctxt
    then Pretty.enclose "(" ")" [p]
    else p
  end;

fun gen_applify strict opn cls f fxy_ctxt p [] =
      if strict
      then gen_brackify (fixity BR fxy_ctxt) [p, Pretty.str (opn ^ cls)]
      else p
  | gen_applify strict opn cls f fxy_ctxt p ps =
      gen_brackify (fixity BR fxy_ctxt) (p @@ Pretty.enum "," opn cls (map f ps));

fun applify opn = gen_applify false opn;

fun tuplify _ _ [] = NONE
  | tuplify print fxy [x] = SOME (print fxy x)
  | tuplify print _ xs = SOME (Pretty.enum "," "(" ")" (map (print NOBR) xs));


(* generic syntax *)

local

val target = Markup.language'
  {name = "code target language", symbols = false, antiquotes = false};

fun markup_target source =
  let
    val pos = Input.pos_of source;
    val _ =
      if Position.is_reported_range pos
      then Position.report pos (target (Input.is_delimited source))
      else ();
  in Input.string_of source end;

in

val parse_target_source = Parse.input Parse.embedded >> markup_target;

end

type simple_const_syntax = int * ((fixity -> iterm -> Pretty.T)
  -> fixity -> (iterm * itype) list -> Pretty.T);

type complex_const_syntax = int * (literals
  -> (var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm option -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T);

datatype raw_const_syntax = plain_const_syntax of string
  | complex_const_syntax of complex_const_syntax;

fun simple_const_syntax syn =
  complex_const_syntax
    (apsnd (fn f => fn _ => fn print => fn _ => fn vars => f (print vars)) syn);

fun requires_args (plain_const_syntax _) = 0
  | requires_args (complex_const_syntax (k, _)) = k;

datatype const_printer = Plain_printer of string
  | Complex_printer of (var_ctxt -> fixity -> iterm -> Pretty.T)
      -> thm option -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T;

type const_syntax = int * const_printer;

fun prep_const_syntax thy literals c (plain_const_syntax s) =
      (Code.args_number thy c, Plain_printer s)
  | prep_const_syntax thy literals c (complex_const_syntax (n, f))=
      (n, Complex_printer (f literals));

fun gen_print_app print_app_expr print_term const_syntax some_thm vars fxy
    (app as (const as { sym, dom, ... }, ts)) =
  case sym of
    Constant name => (case const_syntax name of
      NONE => brackify fxy (print_app_expr some_thm vars app)
    | SOME (_, Plain_printer s) =>
        brackify fxy (Pretty.str s :: map (print_term some_thm vars BR) ts)
    | SOME (wanted, Complex_printer print) =>
        let
          val ((vs_tys, (ts1, rty)), ts2) =
            Code_Thingol.satisfied_application wanted app;
          fun print' fxy =
            print (print_term some_thm) some_thm vars fxy (ts1 ~~ take wanted dom);
        in
          if null vs_tys then
            if null ts2 then
              print' fxy
            else
              brackify fxy (print' APP :: map (print_term some_thm vars BR) ts2)
          else
            print_term some_thm vars fxy (vs_tys `|==> (IConst const `$$ ts1, rty))
        end)
  | _ => brackify fxy (print_app_expr some_thm vars app);

fun gen_print_bind print_term thm (fxy : fixity) pat vars =
  let
    val vs = build (Code_Thingol.add_varnames pat);
    val vars' = intro_vars vs vars;
  in (print_term thm vars' fxy pat, vars') end;

type tyco_syntax = int * ((fixity -> itype -> Pretty.T)
  -> fixity -> itype list -> Pretty.T);


(* mixfix syntax *)

datatype 'a mixfix =
    Arg of fixity
  | String of string
  | Break;

fun printer_of_mixfix prep_arg (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o filter is_arg) mfx;
    fun fillin _ [] [] =
          []
      | fillin print (Arg fxy :: mfx) (a :: args) =
          (print fxy o prep_arg) a :: fillin print mfx args
      | fillin print (String s :: mfx) args =
          Pretty.str s :: fillin print mfx args
      | fillin print (Break :: mfx) args =
          Pretty.brk 1 :: fillin print mfx args;
  in
    (i, fn print => fn fixity_ctxt => fn args =>
      gen_brackify (fixity fixity_this fixity_ctxt) (fillin print mfx args))
  end;

fun read_infix (fixity_this, i) s =
  let
    val l = case fixity_this of L => INFX (i, L) | _ => INFX (i, X);
    val r = case fixity_this of R => INFX (i, R) | _ => INFX (i, X);
  in
    (INFX (i, fixity_this), [Arg l, String " ", String s, Break, Arg r])
  end;

fun read_mixfix s =
  let
    val sym_any = Scan.one Symbol.not_eof;
    val parse = Scan.optional ($$ "!" >> K NOBR) BR -- Scan.repeat (
         ($$ "(" -- $$ "_" -- $$ ")" >> K (Arg NOBR))
      || ($$ "_" >> K (Arg BR))
      || ($$ "/" |-- Scan.repeat ($$ " ") >> (K Break))
      || (Scan.repeat1
           (   $$ "'" |-- sym_any
            || Scan.unless ($$ "_" || $$ "/" || $$ "(" |-- $$ "_" |-- $$ ")")
                 sym_any) >> (String o implode)));
    fun err s (_, NONE) = (fn () => "malformed mixfix annotation: " ^ quote s)
      | err _ (_, SOME msg) = msg;
  in
    case Scan.finite Symbol.stopper parse (Symbol.explode s) of
        (fixity_mixfix, []) => fixity_mixfix
      | _ => Scan.!! (err s) Scan.fail ()
  end;

val parse_fixity =
  (\<^keyword>\<open>infix\<close> >> K X) || (\<^keyword>\<open>infixl\<close> >> K L) || (\<^keyword>\<open>infixr\<close> >> K R)

fun parse_mixfix x =
  (parse_target_source >> read_mixfix
  || parse_fixity -- Parse.nat -- parse_target_source
     >> (fn ((fixity, i), s) => read_infix (fixity, i) s)) x;

fun syntax_of_mixfix of_plain of_printer prep_arg (BR, [String s]) = of_plain s
  | syntax_of_mixfix of_plain of_printer prep_arg (fixity, mfx) =
      of_printer (printer_of_mixfix prep_arg (fixity, mfx));

fun parse_tyco_syntax x =
  (parse_mixfix >> syntax_of_mixfix (fn s => (0, (K o K o K o Pretty.str) s)) I I) x;

val parse_const_syntax =
  parse_mixfix >> syntax_of_mixfix plain_const_syntax simple_const_syntax fst;


(** custom data structure **)

type identifiers = (string list * string, string list * string, string list * string, string list * string,
  string list * string, string list * string) Code_Symbol.data;
type printings = (const_syntax, tyco_syntax, string, unit, unit,
    (Pretty.T * Code_Symbol.T list)) Code_Symbol.data;

datatype data = Data of { reserved: string list, identifiers: identifiers,
  printings: printings };

fun make_data (reserved, identifiers, printings) =
  Data { reserved = reserved, identifiers = identifiers, printings = printings };
val empty_data = make_data ([], Code_Symbol.empty_data, Code_Symbol.empty_data);
fun map_data f (Data { reserved, identifiers, printings }) =
  make_data (f (reserved, identifiers, printings));
fun merge_data (Data { reserved = reserved1, identifiers = identifiers1, printings = printings1 },
    Data { reserved = reserved2, identifiers = identifiers2, printings = printings2 }) =
  make_data (merge (op =) (reserved1, reserved2),
    Code_Symbol.merge_data (identifiers1, identifiers2), Code_Symbol.merge_data (printings1, printings2));

fun the_reserved (Data { reserved, ... }) = reserved;
fun the_identifiers (Data { identifiers , ... }) = identifiers;
fun the_printings (Data { printings, ... }) = printings;


end; (*struct*)
