(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Logic specific patterns and automatic term bindings.

Note: the current implementation is not quite 'generic', but works
fine with common object-logics (HOL, FOL, ZF etc.).
*)

signature AUTO_BIND =
sig
  val is_judgment: term -> bool
  val drop_judgment: term -> term
  val atomic_judgment: theory -> string -> term
  val add_judgment: bstring * string * mixfix -> theory -> theory
  val add_judgment_i: bstring * typ * mixfix -> theory -> theory
  val goal: term -> (indexname * term option) list
  val facts: string -> term list -> (indexname * term option) list
  val thesisN: string
end;

structure AutoBind: AUTO_BIND =
struct


(** judgments **)

val TruepropN = "Trueprop";

fun is_judgment (Const (c, _) $ _) = c = TruepropN
  | is_judgment _ = false;

fun drop_judgment (Abs (x, T, t)) = Abs (x, T, drop_judgment t)
  | drop_judgment (tm as (Const (c, _) $ t)) = if c = TruepropN then t else tm
  | drop_judgment tm = tm;

val strip_judgment = drop_judgment o Logic.strip_assums_concl;

fun atomic_judgment thy x =
  let  (*be robust wrt. low-level errors*)
    val aT = TFree ("'a", logicS);
    val T =
      if_none (Sign.const_type (Theory.sign_of thy) TruepropN) (aT --> propT)
      |> Term.map_type_tvar (fn ((x, _), S) => TFree (x, S));
    val U = Term.domain_type T handle Match => aT;
  in Const (TruepropN, T) $ Free (x, U) end;


fun gen_add_judgment add (name, T, syn) thy =
  if name = TruepropN then
    thy |> PureThy.global_path |> add [(name, T, syn)] |> PureThy.local_path
  else error ("Judgment name has to be " ^ quote TruepropN);

val add_judgment = gen_add_judgment Theory.add_consts;
val add_judgment_i = gen_add_judgment Theory.add_consts_i;



(** bindings **)

val thesisN = "thesis";
val thisN = "this";

fun statement_binds name prop =
  [((name, 0), Some (Term.list_abs (Logic.strip_params prop, strip_judgment prop)))];


(* goal *)

fun goal prop = statement_binds thesisN prop;


(* facts *)

fun get_arg prop =
  (case strip_judgment prop of
    _ $ t => Some (Term.list_abs (Logic.strip_params prop, t))
  | _ => None);

fun facts _ [] = []
  | facts name props =
      let val prop = Library.last_elem props
      in [(Syntax.dddot_indexname, get_arg prop)] @ statement_binds thisN prop end;


end;
