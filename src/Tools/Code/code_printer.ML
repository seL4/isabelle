(*  Title:      Tools/Code/code_printer.ML
    Author:     Florian Haftmann, TU Muenchen

Generic operations for pretty printing of target language code.
*)

signature CODE_PRINTER =
sig
  type itype = Code_Thingol.itype
  type iterm = Code_Thingol.iterm
  type const = Code_Thingol.const
  type dict = Code_Thingol.dict

  val eqn_error: thm option -> string -> 'a

  val @@ : 'a * 'a -> 'a list
  val @| : 'a list * 'a -> 'a list
  val str: string -> Pretty.T
  val concat: Pretty.T list -> Pretty.T
  val brackets: Pretty.T list -> Pretty.T
  val enclose: string -> string -> Pretty.T list -> Pretty.T
  val commas: Pretty.T list -> Pretty.T list
  val enum: string -> string -> string -> Pretty.T list -> Pretty.T
  val enum_default: string -> string -> string -> string -> Pretty.T list -> Pretty.T
  val semicolon: Pretty.T list -> Pretty.T
  val doublesemicolon: Pretty.T list -> Pretty.T
  val indent: int -> Pretty.T -> Pretty.T
  val markup_stmt: string -> Pretty.T -> Pretty.T
  val format: string list -> int -> Pretty.T -> string

  val first_upper: string -> string
  val first_lower: string -> string
  type var_ctxt
  val make_vars: string list -> var_ctxt
  val intro_vars: string list -> var_ctxt -> var_ctxt
  val lookup_var: var_ctxt -> string -> string
  val intro_base_names: (string -> bool) -> (string -> string)
    -> string list -> var_ctxt -> var_ctxt
  val aux_params: var_ctxt -> iterm list list -> string list

  type literals
  val Literals: { literal_char: string -> string, literal_string: string -> string,
        literal_numeral: int -> string,
        literal_positive_numeral: int -> string,
        literal_alternative_numeral: int -> string,
        literal_naive_numeral: int -> string,
        literal_list: Pretty.T list -> Pretty.T, infix_cons: int * string }
    -> literals
  val literal_char: literals -> string -> string
  val literal_string: literals -> string -> string
  val literal_numeral: literals -> int -> string
  val literal_positive_numeral: literals -> int -> string
  val literal_alternative_numeral: literals -> int -> string
  val literal_naive_numeral: literals -> int -> string
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
  val applify: string -> string -> ('a -> Pretty.T) -> fixity -> Pretty.T -> 'a list -> Pretty.T
  val tuplify: (fixity -> 'a -> Pretty.T) -> fixity -> 'a list -> Pretty.T option

  type tyco_syntax
  type simple_const_syntax
  type complex_const_syntax
  type const_syntax
  type activated_complex_const_syntax
  datatype activated_const_syntax = Plain_const_syntax of int * string
    | Complex_const_syntax of activated_complex_const_syntax
  val requires_args: const_syntax -> int
  val parse_const_syntax: Token.T list -> const_syntax option * Token.T list
  val parse_tyco_syntax: Token.T list -> tyco_syntax option * Token.T list
  val plain_const_syntax: string -> const_syntax
  val simple_const_syntax: simple_const_syntax -> const_syntax
  val complex_const_syntax: complex_const_syntax -> const_syntax
  val activate_const_syntax: theory -> literals
    -> string -> const_syntax -> Code_Thingol.naming -> activated_const_syntax * Code_Thingol.naming
  val gen_print_app: (thm option -> var_ctxt -> const * iterm list -> Pretty.T list)
    -> (thm option -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> (string -> activated_const_syntax option)
    -> thm option -> var_ctxt -> fixity -> const * iterm list -> Pretty.T
  val gen_print_bind: (thm option -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm option -> fixity
    -> iterm -> var_ctxt -> Pretty.T * var_ctxt
end;

structure Code_Printer : CODE_PRINTER =
struct

open Code_Thingol;

(** generic nonsense *)

fun eqn_error (SOME thm) s =
      error (s ^ ",\nin equation " ^ Display.string_of_thm_without_context thm)
  | eqn_error NONE s = error s;

val code_presentationN = "code_presentation";
val stmt_nameN = "stmt_name";
val _ = Markup.add_mode code_presentationN YXML.output_markup;


(** assembling and printing text pieces **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val str = Print_Mode.setmp [] Pretty.str;
val concat = Pretty.block o Pretty.breaks;
val commas = Print_Mode.setmp [] Pretty.commas;
fun enclose l r = Print_Mode.setmp [] (Pretty.enclose l r);
val brackets = enclose "(" ")" o Pretty.breaks;
fun enum sep l r = Print_Mode.setmp [] (Pretty.enum sep l r);
fun enum_default default sep l r [] = str default
  | enum_default default sep l r xs = enum sep l r xs;
fun semicolon ps = Pretty.block [concat ps, str ";"];
fun doublesemicolon ps = Pretty.block [concat ps, str ";;"];
fun indent i = Print_Mode.setmp [] (Pretty.indent i);

fun markup_stmt name = Print_Mode.setmp [code_presentationN]
  (Pretty.mark (code_presentationN, [(stmt_nameN, name)]));

fun filter_presentation [] tree =
      Buffer.empty
      |> fold XML.add_content tree
  | filter_presentation presentation_names tree =
      let
        fun is_selected (name, attrs) =
          name = code_presentationN
          andalso member (op =) presentation_names (the (Properties.get attrs stmt_nameN));
        fun add_content_with_space tree (is_first, buf) =
          buf
          |> not is_first ? Buffer.add "\n\n"
          |> XML.add_content tree
          |> pair false;
        fun filter (XML.Elem (name_attrs, xs)) =
              fold (if is_selected name_attrs then add_content_with_space else filter) xs
          | filter (XML.Text _) = I;
      in snd (fold filter tree (true, Buffer.empty)) end;

fun format presentation_names width =
  Print_Mode.setmp [code_presentationN] (Pretty.string_of_margin width)
  #> YXML.parse_body
  #> filter_presentation presentation_names
  #> Buffer.add "\n"
  #> Buffer.content;


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

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o raw_explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o raw_explode;

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
    val (fished3, _) = fold_map Name.variant fished2 Name.context;
    val vars' = intro_vars fished3 vars;
  in map (lookup_var vars') fished3 end;

fun intro_base_names no_syntax deresolve names = names
  |> map_filter (fn name => if no_syntax name then
      let val name' = deresolve name in
        if Long_Name.is_qualified name' then NONE else SOME name'
      end else NONE)
  |> intro_vars;


(** pretty literals **)

datatype literals = Literals of {
  literal_char: string -> string,
  literal_string: string -> string,
  literal_numeral: int -> string,
  literal_positive_numeral: int -> string,
  literal_alternative_numeral: int -> string,
  literal_naive_numeral: int -> string,
  literal_list: Pretty.T list -> Pretty.T,
  infix_cons: int * string
};

fun dest_Literals (Literals lits) = lits;

val literal_char = #literal_char o dest_Literals;
val literal_string = #literal_string o dest_Literals;
val literal_numeral = #literal_numeral o dest_Literals;
val literal_positive_numeral = #literal_positive_numeral o dest_Literals;
val literal_alternative_numeral = #literal_alternative_numeral o dest_Literals;
val literal_naive_numeral = #literal_naive_numeral o dest_Literals;
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
  | fixity (INFX (pr, lr)) (INFX (print_ctxt, lr_ctxt)) =
      pr < print_ctxt
      orelse pr = print_ctxt
        andalso fixity_lrx lr lr_ctxt
      orelse print_ctxt = ~1
  | fixity BR (INFX _) = false
  | fixity _ _ = true;

fun gen_brackify _ [p] = p
  | gen_brackify true (ps as _::_) = enclose "(" ")" ps
  | gen_brackify false (ps as _::_) = Pretty.block ps;

fun brackify fxy_ctxt =
  gen_brackify (fixity BR fxy_ctxt) o Pretty.breaks;

fun brackify_infix infx fxy_ctxt (l, m, r) =
  (if fixity (INFX infx) fxy_ctxt then enclose "(" ")" else Pretty.block)
    ([l, str " ", m, Pretty.brk 1, r]);

fun brackify_block fxy_ctxt p1 ps p2 =
  let val p = Pretty.block_enclose (p1, p2) ps
  in if fixity BR fxy_ctxt
    then enclose "(" ")" [p]
    else p
  end;

fun applify opn cls f fxy_ctxt p [] = p
  | applify opn cls f fxy_ctxt p ps =
      (if (fixity BR fxy_ctxt) then enclose "(" ")" else Pretty.block)
        (p @@ enum "," opn cls (map f ps));

fun tuplify _ _ [] = NONE
  | tuplify print fxy [x] = SOME (print fxy x)
  | tuplify print _ xs = SOME (enum "," "(" ")" (map (print NOBR) xs));


(* generic syntax *)

type tyco_syntax = int * ((fixity -> itype -> Pretty.T)
  -> fixity -> itype list -> Pretty.T);

type simple_const_syntax = int * ((fixity -> iterm -> Pretty.T)
  -> fixity -> (iterm * itype) list -> Pretty.T);

type complex_const_syntax = int * (string list * (literals -> string list
  -> (var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm option -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T));

datatype const_syntax = plain_const_syntax of string
  | complex_const_syntax of complex_const_syntax;

fun requires_args (plain_const_syntax _) = 0
  | requires_args (complex_const_syntax (k, _)) = k;

fun simple_const_syntax syn =
  complex_const_syntax
    (apsnd (fn f => ([], (fn _ => fn _ => fn print => fn _ => fn vars => f (print vars)))) syn);

type activated_complex_const_syntax = int * ((var_ctxt -> fixity -> iterm -> Pretty.T)
  -> thm option -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T)

datatype activated_const_syntax = Plain_const_syntax of int * string
  | Complex_const_syntax of activated_complex_const_syntax;

fun activate_const_syntax thy literals c (plain_const_syntax s) naming =
      (Plain_const_syntax (Code.args_number thy c, s), naming)
  | activate_const_syntax thy literals c (complex_const_syntax (n, (cs, f))) naming =
      fold_map (Code_Thingol.ensure_declared_const thy) cs naming
      |-> (fn cs' => pair (Complex_const_syntax (n, f literals cs')));

fun gen_print_app print_app_expr print_term const_syntax some_thm vars fxy
    (app as ({ name = c, dom, ... }, ts)) =
  case const_syntax c of
    NONE => brackify fxy (print_app_expr some_thm vars app)
  | SOME (Plain_const_syntax (_, s)) =>
      brackify fxy (str s :: map (print_term some_thm vars BR) ts)
  | SOME (Complex_const_syntax (k, print)) =>
      let
        fun print' fxy ts =
          print (print_term some_thm) some_thm vars fxy (ts ~~ take k dom);
      in
        if k = length ts
        then print' fxy ts
        else if k < length ts
        then case chop k ts of (ts1, ts2) =>
          brackify fxy (print' APP ts1 :: map (print_term some_thm vars BR) ts2)
        else print_term some_thm vars fxy (Code_Thingol.eta_expand k app)
      end;

fun gen_print_bind print_term thm (fxy : fixity) pat vars =
  let
    val vs = Code_Thingol.fold_varnames (insert (op =)) pat [];
    val vars' = intro_vars vs vars;
  in (print_term thm vars' fxy pat, vars') end;


(* mixfix syntax *)

datatype 'a mixfix =
    Arg of fixity
  | String of string
  | Break;

fun mk_mixfix prep_arg (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o filter is_arg) mfx;
    fun fillin _ [] [] =
          []
      | fillin print (Arg fxy :: mfx) (a :: args) =
          (print fxy o prep_arg) a :: fillin print mfx args
      | fillin print (String s :: mfx) args =
          str s :: fillin print mfx args
      | fillin print (Break :: mfx) args =
          Pretty.brk 1 :: fillin print mfx args;
  in
    (i, fn print => fn fixity_ctxt => fn args =>
      gen_brackify (fixity fixity_this fixity_ctxt) (fillin print mfx args))
  end;

fun parse_infix prep_arg (x, i) s =
  let
    val l = case x of L => INFX (i, L) | _ => INFX (i, X);
    val r = case x of R => INFX (i, R) | _ => INFX (i, X);
  in
    mk_mixfix prep_arg (INFX (i, x), [Arg l, String " ", String s, Break, Arg r])
  end;

fun parse_mixfix mk_plain mk_complex prep_arg s =
  let
    val sym_any = Scan.one Symbol.is_regular;
    val parse = Scan.optional ($$ "!" >> K true) false -- Scan.repeat (
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
      ((false, [String s]), []) => mk_plain s
    | ((_, p as [_]), []) => mk_complex (mk_mixfix prep_arg (NOBR, p))
    | ((b, p as _ :: _ :: _), []) => mk_complex (mk_mixfix prep_arg (if b then NOBR else BR, p))
    | _ => Scan.!! (err s) Scan.fail ()
  end;

fun parse_syntax mk_plain mk_complex prep_arg =
  Scan.option (
      ((@{keyword "infix"} >> K X)
        || (@{keyword "infixl"} >> K L)
        || (@{keyword "infixr"} >> K R))
        -- Parse.nat -- Parse.string
        >> (fn ((x, i), s) => mk_complex (parse_infix prep_arg (x, i) s))
      || Parse.string >> (fn s => (parse_mixfix mk_plain mk_complex prep_arg s)));

fun parse_tyco_syntax x = parse_syntax (fn s => (0, (K o K o K o str) s)) I I x;

val parse_const_syntax = parse_syntax plain_const_syntax simple_const_syntax fst;

end; (*struct*)
