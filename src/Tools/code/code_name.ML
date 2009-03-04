(*  Title:      Tools/code/code_name.ML
    Author:     Florian Haftmann, TU Muenchen

Some code generator infrastructure concerning names.
*)

signature CODE_NAME =
sig
  structure StringPairTab: TABLE
  val first_upper: string -> string
  val first_lower: string -> string
  val dest_name: string -> string * string

  val purify_var: string -> string
  val purify_tvar: string -> string
  val purify_sym: string -> string
  val purify_base: bool -> string -> string
  val check_modulename: string -> string

  type var_ctxt
  val make_vars: string list -> var_ctxt
  val intro_vars: string list -> var_ctxt -> var_ctxt
  val lookup_var: var_ctxt -> string -> string

  val read_const_exprs: theory -> string list -> string list * string list
  val mk_name_module: Name.context -> string option -> (string -> string option)
    -> 'a Graph.T -> string -> string
end;

structure Code_Name: CODE_NAME =
struct

(** auxiliary **)

structure StringPairTab =
  TableFun(type key = string * string val ord = prod_ord fast_string_ord fast_string_ord);

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;

val dest_name =
  apfst NameSpace.implode o split_last o fst o split_last o NameSpace.explode;


(** purification **)

fun purify_name upper lower =
  let
    fun is_valid s = Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "'";
    val is_junk = not o is_valid andf Symbol.is_regular;
    val junk = Scan.many is_junk;
    val scan_valids = Symbol.scanner "Malformed input"
      ((junk |--
        (Scan.optional (Scan.one Symbol.is_ascii_letter) "x" ^^ (Scan.many is_valid >> implode)
        --| junk))
      ::: Scan.repeat ((Scan.many1 is_valid >> implode) --| junk));
    fun upper_lower cs = if upper then nth_map 0 Symbol.to_ascii_upper cs
      else if lower then (if forall Symbol.is_ascii_upper cs
        then map else nth_map 0) Symbol.to_ascii_lower cs
      else cs;
  in
    explode
    #> scan_valids
    #> space_implode "_"
    #> explode
    #> upper_lower
    #> implode
  end;

fun purify_var "" = "x"
  | purify_var v = purify_name false true v;

fun purify_tvar "" = "'a"
  | purify_tvar v =
      (unprefix "'" #> explode #> filter Symbol.is_ascii_letter #> cons "'" #> implode) v;

val purify_prefix =
  explode
  (*FIMXE should disappear as soon as hierarchical theory name spaces are available*)
  #> Symbol.scanner "Malformed name"
      (Scan.repeat ($$ "_" |-- $$ "_" >> (fn _ => ".") || Scan.one Symbol.is_regular))
  #> implode
  #> NameSpace.explode
  #> map (purify_name true false);

(*FIMXE non-canonical function treating non-canonical names*)
fun purify_base _ "op &" = "and"
  | purify_base _ "op |" = "or"
  | purify_base _ "op -->" = "implies"
  | purify_base _ "{}" = "empty"
  | purify_base _ "op :" = "member"
  | purify_base _ "op Int" = "intersect"
  | purify_base _ "op Un" = "union"
  | purify_base _ "*" = "product"
  | purify_base _ "+" = "sum"
  | purify_base lower s = if String.isPrefix "op =" s
      then "eq" ^ purify_name false lower s
      else purify_name false lower s;

val purify_sym = purify_base false;

fun check_modulename mn =
  let
    val mns = NameSpace.explode mn;
    val mns' = map (purify_name true false) mns;
  in
    if mns' = mns then mn else error ("Invalid module name: " ^ quote mn ^ "\n"
      ^ "perhaps try " ^ quote (NameSpace.implode mns'))
  end;


(** variable name contexts **)

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


(** misc **)

fun read_const_exprs thy =
  let
    fun consts_of some_thyname =
      let
        val thy' = case some_thyname
         of SOME thyname => ThyInfo.the_theory thyname thy
          | NONE => thy;
        val cs = Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
          ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) thy') [];
        fun belongs_here c =
          not (exists (fn thy'' => Sign.declared_const thy'' c) (Theory.parents_of thy'))
      in case some_thyname
       of NONE => cs
        | SOME thyname => filter belongs_here cs
      end;
    fun read_const_expr "*" = ([], consts_of NONE)
      | read_const_expr s = if String.isSuffix ".*" s
          then ([], consts_of (SOME (unsuffix ".*" s)))
          else ([Code_Unit.read_const thy s], []);
  in pairself flat o split_list o map read_const_expr end;

fun mk_name_module reserved_names module_prefix module_alias program =
  let
    fun mk_alias name = case module_alias name
     of SOME name' => name'
      | NONE => name
          |> NameSpace.explode
          |> map (fn name => (the_single o fst) (Name.variants [name] reserved_names))
          |> NameSpace.implode;
    fun mk_prefix name = case module_prefix
     of SOME module_prefix => NameSpace.append module_prefix name
      | NONE => name;
    val tab =
      Symtab.empty
      |> Graph.fold ((fn name => Symtab.default (name, (mk_alias #> mk_prefix) name))
           o fst o dest_name o fst)
             program
  in the o Symtab.lookup tab end;

end;
