(* Author: Alexander Krauss, TU Muenchen
   Author: Christian Sternagel, University of Innsbruck

Ad-hoc overloading of constants based on their types.
*)

signature ADHOC_OVERLOADING =
sig
  val add_overloaded: string -> theory -> theory
  val add_variant: string -> string -> theory -> theory

  val show_variants: bool Config.T
  val setup: theory -> theory
end

structure Adhoc_Overloading: ADHOC_OVERLOADING =
struct

val show_variants = Attrib.setup_config_bool @{binding show_variants} (K false);


(* errors *)

fun duplicate_variant_err int_name ext_name =
  error ("Constant " ^ quote int_name ^ " is already a variant of " ^ quote ext_name);

fun not_overloaded_err name =
  error ("Constant " ^ quote name ^ " is not declared as overloaded");

fun already_overloaded_err name =
  error ("Constant " ^ quote name ^ " is already declared as overloaded");

fun unresolved_err ctxt (c, T) t reason =
  error ("Unresolved overloading of  " ^ quote c ^ " :: " ^
    quote (Syntax.string_of_typ ctxt T) ^ " in " ^
    quote (Syntax.string_of_term ctxt t) ^ " (" ^ reason ^ ")");


(* theory data *)

structure Overload_Data = Theory_Data
(
  type T =
    { internalize : (string * typ) list Symtab.table,
      externalize : string Symtab.table };
  val empty = {internalize=Symtab.empty, externalize=Symtab.empty};
  val extend = I;

  fun merge_ext int_name (ext_name1, ext_name2) =
    if ext_name1 = ext_name2 then ext_name1
    else duplicate_variant_err int_name ext_name1;

  fun merge
    ({internalize = int1, externalize = ext1},
      {internalize = int2, externalize = ext2}) : T =
    {internalize = Symtab.join (K (Library.merge (op =))) (int1, int2),
      externalize = Symtab.join merge_ext (ext1, ext2)};
);

fun map_tables f g =
  Overload_Data.map (fn {internalize=int, externalize=ext} =>
    {internalize=f int, externalize=g ext});

val is_overloaded = Symtab.defined o #internalize o Overload_Data.get;
val get_variants = Symtab.lookup o #internalize o Overload_Data.get;
val get_external = Symtab.lookup o #externalize o Overload_Data.get;

fun add_overloaded ext_name thy =
  let val _ = not (is_overloaded thy ext_name) orelse already_overloaded_err ext_name;
  in map_tables (Symtab.update (ext_name, [])) I thy end;

fun add_variant ext_name name thy =
  let
    val _ = is_overloaded thy ext_name orelse not_overloaded_err ext_name;
    val _ =
      (case get_external thy name of
        NONE => ()
      | SOME gen' => duplicate_variant_err name gen');
    val T = Sign.the_const_type thy name;
  in
    map_tables (Symtab.cons_list (ext_name, (name, T)))
      (Symtab.update (name, ext_name)) thy
  end


(* check / uncheck *)

fun unifiable_with ctxt T1 (c, T2) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val maxidx1 = Term.maxidx_of_typ T1;
    val T2' = Logic.incr_tvar (maxidx1 + 1) T2;
    val maxidx2 = Int.max (maxidx1, Term.maxidx_of_typ T2');
  in
    (Sign.typ_unify thy (T1, T2') (Vartab.empty, maxidx2); SOME c)
    handle Type.TUNIFY => NONE
  end;

fun insert_internal_same ctxt t (Const (c, T)) =
      (case map_filter (unifiable_with ctxt T)
         (Same.function (get_variants (Proof_Context.theory_of ctxt)) c) of
        [] => unresolved_err ctxt (c, T) t "no instances"
      | [c'] => Const (c', dummyT)
      | _ => raise Same.SAME)
  | insert_internal_same _ _ _ = raise Same.SAME;

fun insert_external_same ctxt _ (Const (c, T)) =
      Const (Same.function (get_external (Proof_Context.theory_of ctxt)) c, T)
  | insert_external_same _ _ _ = raise Same.SAME;

fun gen_check_uncheck replace ts ctxt =
  Same.capture (Same.map (fn t => Term_Subst.map_aterms_same (replace ctxt t) t)) ts
  |> Option.map (rpair ctxt);

val check = gen_check_uncheck insert_internal_same;

fun uncheck ts ctxt =
  if Config.get ctxt show_variants then NONE
  else gen_check_uncheck insert_external_same ts ctxt;

fun reject_unresolved ts ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun check_unresolved t =
      (case filter (is_overloaded thy o fst) (Term.add_consts t []) of
        [] => ()
      | ((c, T) :: _) => unresolved_err ctxt (c, T) t "multiple instances");
    val _ = map check_unresolved ts;
  in NONE end;


(* setup *)

val setup = Context.theory_map
  (Syntax_Phases.context_term_check 0 "adhoc_overloading" check
   #> Syntax_Phases.context_term_check 1 "adhoc_overloading_unresolved_check" reject_unresolved
   #> Syntax_Phases.context_term_uncheck 0 "adhoc_overloading" uncheck);

end;
