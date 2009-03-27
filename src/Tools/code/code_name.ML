(*  Title:      Tools/code/code_name.ML
    Author:     Florian Haftmann, TU Muenchen

Some code generator infrastructure concerning names.
*)

signature CODE_NAME =
sig
  val purify_var: string -> string
  val purify_tvar: string -> string
  val purify_base: string -> string
  val check_modulename: string -> string

  val read_const_exprs: theory -> string list -> string list * string list
end;

structure Code_Name: CODE_NAME =
struct

(** purification **)

fun purify_name upper =
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
      else (if forall Symbol.is_ascii_upper cs
        then map else nth_map 0) Symbol.to_ascii_lower cs;
  in
    explode
    #> scan_valids
    #> space_implode "_"
    #> explode
    #> upper_lower
    #> implode
  end;

fun purify_var "" = "x"
  | purify_var v = purify_name false v;

fun purify_tvar "" = "'a"
  | purify_tvar v =
      (unprefix "'" #> explode #> filter Symbol.is_ascii_letter #> cons "'" #> implode) v;

val purify_prefix =
  explode
  (*FIMXE should disappear as soon as hierarchical theory name spaces are available*)
  #> Symbol.scanner "Malformed name"
      (Scan.repeat ($$ "_" |-- $$ "_" >> (fn _ => ".") || Scan.one Symbol.is_regular))
  #> implode
  #> Long_Name.explode
  #> map (purify_name true);

(*FIMXE non-canonical function treating non-canonical names*)
fun purify_base "op &" = "and"
  | purify_base "op |" = "or"
  | purify_base "op -->" = "implies"
  | purify_base "op :" = "member"
  | purify_base "*" = "product"
  | purify_base "+" = "sum"
  | purify_base s = if String.isPrefix "op =" s
      then "eq" ^ purify_name false s
      else purify_name false s;

fun check_modulename mn =
  let
    val mns = Long_Name.explode mn;
    val mns' = map (purify_name true) mns;
  in
    if mns' = mns then mn else error ("Invalid module name: " ^ quote mn ^ "\n"
      ^ "perhaps try " ^ quote (Long_Name.implode mns'))
  end;


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

end;
