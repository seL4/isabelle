(*  Title:      Pure/Isar/auto_bind.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Automatic term bindings -- logic specific patterns.

Note: the current implementation is not quite 'generic', but works
fine with the more common object-logics (HOL, FOL, ZF etc.).
*)

signature AUTO_BIND =
sig
  val goal: term -> (indexname * term option) list
  val facts: string -> term list -> (indexname * term option) list
  val thesisN: string
  val is_judgment: term -> bool
  val add_judgment: bstring * string * mixfix -> theory -> theory
  val add_judgment_i: bstring * typ * mixfix -> theory -> theory
end;

structure AutoBind: AUTO_BIND =
struct

val thesisN = "thesis";
val thisN = "this";


(** bindings **)

fun list_abs parms tm = foldr (fn ((x, T), t) => Abs (x, T, t)) (parms, tm);


(* goal *)

fun statement_binds (name, prop) =
  let
    val concl = Logic.strip_assums_concl prop;
    val parms = Logic.strip_params prop;

    val env = [(name ^ "_prop", Some prop), (name ^ "_concl", Some (list_abs parms concl)),
      (name, case concl of Const ("Trueprop", _) $ t => Some (list_abs parms t) | _ => None)];
  in map (fn (s, t) => ((s, 0), t)) env end;

fun goal prop = statement_binds (thesisN, prop);


(* facts *)

fun get_subject prop =
  (case (Logic.strip_assums_concl prop) of
    Const ("Trueprop", _) $ (_ $ t) => Some (list_abs (Logic.strip_params prop) t)
  | _ => None);

fun facts _ [] = []
  | facts name props =
      let val prop = Library.last_elem props
      in [(Syntax.dddot_indexname, get_subject prop)] @ statement_binds (thisN, prop) end;



(** judgments **)

fun is_judgment (Const ("Trueprop", _) $ _) = true
  | is_judgment _ = false;


fun gen_add_judgment add (name, T, syn) thy =
  if name = "Trueprop" then
    thy |> PureThy.global_path |> add [(name, T, syn)] |> PureThy.local_path
  else error "Judgment name has to be \"Trueprop\"";

val add_judgment = gen_add_judgment Theory.add_consts;
val add_judgment_i = gen_add_judgment Theory.add_consts_i;


end;
