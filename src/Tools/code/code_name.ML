(*  Title:      Tools/code/code_name.ML
    Author:     Florian Haftmann, TU Muenchen

Some code generator infrastructure concerning names.
*)

signature CODE_NAME =
sig
  val purify_name: bool -> string -> string
  val purify_var: string -> string
  val purify_tvar: string -> string
  val purify_base: string -> string

  val read_const_exprs: theory -> string list -> string list * string list
end;

structure Code_Name: CODE_NAME =
struct

(** purification **)

fun purify_name upper = 
  let
    fun upper_lower cs = if upper then nth_map 0 Symbol.to_ascii_upper cs
      else (if forall Symbol.is_ascii_upper cs
        then map else nth_map 0) Symbol.to_ascii_lower cs;
  in
    Name.desymbolize
    #> explode
    #> upper_lower
    #> implode
  end;

val purify_var = purify_name false;

fun purify_tvar "" = "'a"
  | purify_tvar v =
      (unprefix "'" #> purify_name false #> prefix "'") v;

(*FIMXE non-canonical function treating non-canonical names*)
fun purify_base "op &" = "and"
  | purify_base "op |" = "or"
  | purify_base "op -->" = "implies"
  | purify_base "op :" = "member"
  | purify_base "op =" = "eq"
  | purify_base "*" = "product"
  | purify_base "+" = "sum"
  | purify_base s = purify_name false s;


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
