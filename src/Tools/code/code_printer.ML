(*  Title:      Tools/code/code_printer.ML
    Author:     Florian Haftmann, TU Muenchen

Generic operations for pretty printing of target language code.
*)

signature CODE_PRINTER =
sig
  val nerror: thm -> string -> 'a

  val @@ : 'a * 'a -> 'a list
  val @| : 'a list * 'a -> 'a list
  val str: string -> Pretty.T
  val concat: Pretty.T list -> Pretty.T
  val brackets: Pretty.T list -> Pretty.T
  val semicolon: Pretty.T list -> Pretty.T
  val enum_default: string -> string -> string -> string -> Pretty.T list -> Pretty.T

  val first_upper: string -> string
  val first_lower: string -> string
  type var_ctxt
  val make_vars: string list -> var_ctxt
  val intro_vars: string list -> var_ctxt -> var_ctxt
  val lookup_var: var_ctxt -> string -> string

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

  type itype = Code_Thingol.itype
  type iterm = Code_Thingol.iterm
  type const = Code_Thingol.const
  type dict = Code_Thingol.dict
  type tyco_syntax
  type const_syntax
  val parse_infix: ('a -> 'b) -> lrx * int -> string
    -> int * ((fixity -> 'b -> Pretty.T)
    -> fixity -> 'a list -> Pretty.T)
  val parse_syntax: ('a -> 'b) -> OuterParse.token list
    -> (int * ((fixity -> 'b -> Pretty.T)
    -> fixity -> 'a list -> Pretty.T)) option * OuterParse.token list
  val simple_const_syntax: (int * ((fixity -> iterm -> Pretty.T)
    -> fixity -> (iterm * itype) list -> Pretty.T)) option -> const_syntax option
  val gen_pr_app: (thm -> var_ctxt -> const * iterm list -> Pretty.T list)
    -> (thm -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> (string -> const_syntax option) -> Code_Thingol.naming
    -> thm -> var_ctxt -> fixity -> const * iterm list -> Pretty.T
  val gen_pr_bind: ((string option * Pretty.T option) * itype -> Pretty.T)
    -> (thm -> var_ctxt -> fixity -> iterm -> Pretty.T)
    -> thm -> fixity
    -> (string option * iterm option) * itype -> var_ctxt -> Pretty.T * var_ctxt

  type literals
  val Literals: { literal_char: string -> string, literal_string: string -> string,
        literal_numeral: bool -> int -> string, literal_list: Pretty.T list -> Pretty.T, infix_cons: int * string }
    -> literals
  val literal_char: literals -> string -> string
  val literal_string: literals -> string -> string
  val literal_numeral: literals -> bool -> int -> string
  val literal_list: literals -> Pretty.T list -> Pretty.T
  val infix_cons: literals -> int * string

  val mk_name_module: Name.context -> string option -> (string -> string option)
    -> 'a Graph.T -> string -> string
  val dest_name: string -> string * string
end;

structure Code_Printer : CODE_PRINTER =
struct

open Code_Thingol;

fun nerror thm s = error (s ^ ",\nin equation " ^ Display.string_of_thm thm);

(** assembling text pieces **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val str = PrintMode.setmp [] Pretty.str;
val concat = Pretty.block o Pretty.breaks;
val brackets = Pretty.enclose "(" ")" o Pretty.breaks;
fun semicolon ps = Pretty.block [concat ps, str ";"];
fun enum_default default sep opn cls [] = str default
  | enum_default default sep opn cls xs = Pretty.enum sep opn cls xs;


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

fun brackify_infix infx fxy_ctxt =
  gen_brackify (fixity (INFX infx) fxy_ctxt) o Pretty.breaks;


(* generic syntax *)

type tyco_syntax = int * ((fixity -> itype -> Pretty.T)
  -> fixity -> itype list -> Pretty.T);
type const_syntax = int * ((var_ctxt -> fixity -> iterm -> Pretty.T)
  -> Code_Thingol.naming -> thm -> var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T);

fun simple_const_syntax x = (Option.map o apsnd)
  (fn pretty => fn pr => fn naming => fn thm => fn vars => pretty (pr vars)) x;

fun gen_pr_app pr_app pr_term syntax_const naming thm vars fxy (app as ((c, (_, tys)), ts)) =
  case syntax_const c
   of NONE => brackify fxy (pr_app thm vars app)
    | SOME (k, pr) =>
        let
          fun pr' fxy ts = pr (pr_term thm) naming thm vars fxy (ts ~~ curry Library.take k tys);
        in if k = length ts
          then pr' fxy ts
        else if k < length ts
          then case chop k ts of (ts1, ts2) =>
            brackify fxy (pr' APP ts1 :: map (pr_term thm vars BR) ts2)
          else pr_term thm vars fxy (Code_Thingol.eta_expand k app)
        end;

fun gen_pr_bind pr_bind pr_term thm (fxy : fixity) ((v, pat), ty : itype) vars =
  let
    val vs = case pat
     of SOME pat => Code_Thingol.fold_varnames (insert (op =)) pat []
      | NONE => [];
    val vars' = intro_vars (the_list v) vars;
    val vars'' = intro_vars vs vars';
    val v' = Option.map (lookup_var vars') v;
    val pat' = Option.map (pr_term thm vars'' fxy) pat;
  in (pr_bind ((v', pat'), ty), vars'') end;


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
      | fillin pr (Arg fxy :: mfx) (a :: args) =
          (pr fxy o prep_arg) a :: fillin pr mfx args
      | fillin pr (Pretty p :: mfx) args =
          p :: fillin pr mfx args;
  in
    (i, fn pr => fn fixity_ctxt => fn args =>
      gen_brackify (fixity fixity_this fixity_ctxt) (fillin pr mfx args))
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
      ((OuterParse.$$$ infixK  >> K X)
        || (OuterParse.$$$ infixlK >> K L)
        || (OuterParse.$$$ infixrK >> K R))
        -- OuterParse.nat >> parse_infix prep_arg
      || Scan.succeed (parse_mixfix prep_arg))
      -- OuterParse.string
      >> (fn (parse, s) => parse s)) xs;

val _ = List.app OuterKeyword.keyword [infixK, infixlK, infixrK];


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


(** module name spaces **)

val dest_name =
  apfst Long_Name.implode o split_last o fst o split_last o Long_Name.explode;

fun mk_name_module reserved_names module_prefix module_alias program =
  let
    fun mk_alias name = case module_alias name
     of SOME name' => name'
      | NONE => name
          |> Long_Name.explode
          |> map (fn name => (the_single o fst) (Name.variants [name] reserved_names))
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
