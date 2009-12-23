(*  Title:      Tools/code/code_printer.ML
    Author:     Florian Haftmann, TU Muenchen

Generic operations for pretty printing of target language code.
*)

signature CODE_PRINTER =
sig
  type itype = Code_Thingol.itype
  type iterm = Code_Thingol.iterm
  type const = Code_Thingol.const
  type dict = Code_Thingol.dict

  val eqn_error: thm -> string -> 'a

  val @@ : 'a * 'a -> 'a list
  val @| : 'a list * 'a -> 'a list
  val str: string -> Pretty.T
  val concat: Pretty.T list -> Pretty.T
  val brackets: Pretty.T list -> Pretty.T
  val enclose: string -> string -> Pretty.T list -> Pretty.T
  val enum: string -> string -> string -> Pretty.T list -> Pretty.T
  val enum_default: string -> string -> string -> string -> Pretty.T list -> Pretty.T
  val semicolon: Pretty.T list -> Pretty.T
  val doublesemicolon: Pretty.T list -> Pretty.T
  val indent: int -> Pretty.T -> Pretty.T
  val string_of_pretty: int -> Pretty.T -> string
  val writeln_pretty: int -> Pretty.T -> unit

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
        literal_numeral: bool -> int -> string,
        literal_list: Pretty.T list -> Pretty.T, infix_cons: int * string }
    -> literals
  val literal_char: literals -> string -> string
  val literal_string: literals -> string -> string
  val literal_numeral: literals -> bool -> int -> string
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
  val brackify_infix: int * lrx -> fixity -> Pretty.T list -> Pretty.T
  val brackify_block: fixity -> Pretty.T -> Pretty.T list -> Pretty.T -> Pretty.T

  type tyco_syntax
  type simple_const_syntax
  type proto_const_syntax
  type const_syntax
  val parse_infix: ('a -> 'b) -> lrx * int -> string
    -> int * ((fixity -> 'b -> Pretty.T)
    -> fixity -> 'a list -> Pretty.T)
  val parse_syntax: ('a -> 'b) -> OuterParse.token list
    -> (int * ((fixity -> 'b -> Pretty.T)
    -> fixity -> 'a list -> Pretty.T)) option * OuterParse.token list
  val simple_const_syntax: simple_const_syntax -> proto_const_syntax
  val activate_const_syntax: theory -> literals
    -> proto_const_syntax -> Code_Thingol.naming -> const_syntax * Code_Thingol.naming
  val gen_print_app: (thm -> var_ctxt -> const * iterm list -> Pretty.T list)
    -> (thm -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> (string -> const_syntax option)
    -> thm -> var_ctxt -> fixity -> const * iterm list -> Pretty.T
  val gen_print_bind: (thm -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm -> fixity
    -> iterm -> var_ctxt -> Pretty.T * var_ctxt

  val mk_name_module: Name.context -> string option -> (string -> string option)
    -> 'a Graph.T -> string -> string
  val dest_name: string -> string * string
end;

structure Code_Printer : CODE_PRINTER =
struct

open Code_Thingol;

fun eqn_error thm s = error (s ^ ",\nin equation " ^ Display.string_of_thm_without_context thm);

(** assembling and printing text pieces **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val str = PrintMode.setmp [] Pretty.str;
val concat = Pretty.block o Pretty.breaks;
fun enclose l r = PrintMode.setmp [] (Pretty.enclose l r);
val brackets = enclose "(" ")" o Pretty.breaks;
fun enum sep l r = PrintMode.setmp [] (Pretty.enum sep l r);
fun enum_default default sep l r [] = str default
  | enum_default default sep l r xs = enum sep l r xs;
fun semicolon ps = Pretty.block [concat ps, str ";"];
fun doublesemicolon ps = Pretty.block [concat ps, str ";;"];
fun indent i = PrintMode.setmp [] (Pretty.indent i);

fun string_of_pretty width p = PrintMode.setmp [] (Pretty.setmp_margin_CRITICAL width Pretty.string_of) p ^ "\n";
fun writeln_pretty width p = PrintMode.setmp [] (Pretty.setmp_margin_CRITICAL width Pretty.writeln) p;


(** names and variable name contexts **)

type var_ctxt = string Symtab.table * Name.context;

fun make_vars names = (fold (fn name => Symtab.update_new (name, name)) names Symtab.empty,
  Name.make_context names);

fun intro_vars names (namemap, namectxt) =
  let
    val (names', namectxt') = Name.variants names namectxt;
    val namemap' = fold2 (curry Symtab.update) names names' namemap;
  in (namemap', namectxt') end;

fun lookup_var (namemap, _) name = case Symtab.lookup namemap name
 of SOME name' => name'
  | NONE => error ("Invalid name in context: " ^ quote name);

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;

fun aux_params vars lhss =
  let
    fun fish_param _ (w as SOME _) = w
      | fish_param (IVar (SOME v)) NONE = SOME v
      | fish_param _ NONE = NONE;
    fun fillup_param _ (_, SOME v) = v
      | fillup_param x (i, NONE) = x ^ string_of_int i;
    val fished1 = fold (map2 fish_param) lhss (replicate (length (hd lhss)) NONE);
    val x = Name.variant (map_filter I fished1) "x";
    val fished2 = map_index (fillup_param x) fished1;
    val (fished3, _) = Name.variants fished2 Name.context;
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
  literal_numeral: bool -> int -> string,
  literal_list: Pretty.T list -> Pretty.T,
  infix_cons: int * string
};

fun dest_Literals (Literals lits) = lits;

val literal_char = #literal_char o dest_Literals;
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

fun brackify_infix infx fxy_ctxt =
  gen_brackify (fixity (INFX infx) fxy_ctxt) o Pretty.breaks;

fun brackify_block fxy_ctxt p1 ps p2 =
  let val p = Pretty.block_enclose (p1, p2) ps
  in if fixity BR fxy_ctxt
    then enclose "(" ")" [p]
    else p
  end;


(* generic syntax *)

type tyco_syntax = int * ((fixity -> itype -> Pretty.T)
  -> fixity -> itype list -> Pretty.T);

type simple_const_syntax = int * ((fixity -> iterm -> Pretty.T)
  -> fixity -> (iterm * itype) list -> Pretty.T);
type proto_const_syntax = int * (string list * (literals -> string list
  -> (var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T));
type const_syntax = int * ((var_ctxt -> fixity -> iterm -> Pretty.T)
  -> thm -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T);

fun simple_const_syntax syn =
  apsnd (fn f => ([], (fn _ => fn _ => fn print => fn _ => fn vars => f (print vars)))) syn;

fun activate_const_syntax thy literals (n, (cs, f)) naming =
  fold_map (Code_Thingol.ensure_declared_const thy) cs naming
  |-> (fn cs' => pair (n, f literals cs'));

fun gen_print_app print_app_expr print_term syntax_const thm vars fxy (app as ((c, (_, tys)), ts)) =
  case syntax_const c
   of NONE => brackify fxy (print_app_expr thm vars app)
    | SOME (k, print) =>
        let
          fun print' fxy ts = print (print_term thm) thm vars fxy (ts ~~ take k tys);
        in if k = length ts
          then print' fxy ts
        else if k < length ts
          then case chop k ts of (ts1, ts2) =>
            brackify fxy (print' APP ts1 :: map (print_term thm vars BR) ts2)
          else print_term thm vars fxy (Code_Thingol.eta_expand k app)
        end;

fun gen_print_bind print_term thm (fxy : fixity) pat vars =
  let
    val vs = Code_Thingol.fold_varnames (insert (op =)) pat [];
    val vars' = intro_vars vs vars;
  in (print_term thm vars' fxy pat, vars') end;


(* mixfix syntax *)

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T;

fun mk_mixfix prep_arg (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o filter is_arg) mfx;
    fun fillin _ [] [] =
          []
      | fillin print (Arg fxy :: mfx) (a :: args) =
          (print fxy o prep_arg) a :: fillin print mfx args
      | fillin print (Pretty p :: mfx) args =
          p :: fillin print mfx args;
  in
    (i, fn print => fn fixity_ctxt => fn args =>
      gen_brackify (fixity fixity_this fixity_ctxt) (fillin print mfx args))
  end;

fun parse_infix prep_arg (x, i) s =
  let
    val l = case x of L => INFX (i, L) | _ => INFX (i, X);
    val r = case x of R => INFX (i, R) | _ => INFX (i, X);
  in
    mk_mixfix prep_arg (INFX (i, x),
      [Arg l, (Pretty o Pretty.brk) 1, (Pretty o str) s, (Pretty o Pretty.brk) 1, Arg r])
  end;

fun parse_mixfix prep_arg s =
  let
    val sym_any = Scan.one Symbol.is_regular;
    val parse = Scan.optional ($$ "!" >> K true) false -- Scan.repeat (
         ($$ "(" -- $$ "_" -- $$ ")" >> K (Arg NOBR))
      || ($$ "_" >> K (Arg BR))
      || ($$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length))
      || (Scan.repeat1
           (   $$ "'" |-- sym_any
            || Scan.unless ($$ "_" || $$ "/" || $$ "(" |-- $$ "_" |-- $$ ")")
                 sym_any) >> (Pretty o str o implode)));
  in case Scan.finite Symbol.stopper parse (Symbol.explode s)
   of ((_, p as [_]), []) => mk_mixfix prep_arg (NOBR, p)
    | ((b, p as _ :: _ :: _), []) => mk_mixfix prep_arg (if b then NOBR else BR, p)
    | _ => Scan.!!
        (the_default ("malformed mixfix annotation: " ^ quote s) o snd) Scan.fail ()
  end;

val (infixK, infixlK, infixrK) = ("infix", "infixl", "infixr");

fun parse_syntax prep_arg xs =
  Scan.option ((
      ((OuterParse.$$$ infixK >> K X)
        || (OuterParse.$$$ infixlK >> K L)
        || (OuterParse.$$$ infixrK >> K R))
        -- OuterParse.nat >> parse_infix prep_arg
      || Scan.succeed (parse_mixfix prep_arg))
      -- OuterParse.string
      >> (fn (parse, s) => parse s)) xs;

val _ = List.app OuterKeyword.keyword [infixK, infixlK, infixrK];


(** module name spaces **)

val dest_name =
  apfst Long_Name.implode o split_last o fst o split_last o Long_Name.explode;

fun mk_name_module reserved module_prefix module_alias program =
  let
    fun mk_alias name = case module_alias name
     of SOME name' => name'
      | NONE => name
          |> Long_Name.explode
          |> map (fn name => (the_single o fst) (Name.variants [name] reserved))
          |> Long_Name.implode;
    fun mk_prefix name = case module_prefix
     of SOME module_prefix => Long_Name.append module_prefix name
      | NONE => name;
    val tab =
      Symtab.empty
      |> Graph.fold ((fn name => Symtab.default (name, (mk_alias #> mk_prefix) name))
           o fst o dest_name o fst)
             program
  in the o Symtab.lookup tab end;

end; (*struct*)
