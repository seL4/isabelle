(*  Title:      Pure/Tools/adhoc_overloading.ML
    Author:     Alexander Krauss, TU Muenchen
    Author:     Christian Sternagel, University of Innsbruck

Adhoc overloading of constants based on their types.
*)

signature ADHOC_OVERLOADING =
sig
  val show_variants: bool Config.T
  val adhoc_overloading: bool -> (string * term list) list -> local_theory -> local_theory
  val adhoc_overloading_cmd: bool -> (string * string list) list -> local_theory -> local_theory
end

structure Adhoc_Overloading: ADHOC_OVERLOADING =
struct

val show_variants = Attrib.setup_config_bool \<^binding>\<open>show_variants\<close> (K false);


(* errors *)

fun err_duplicate_variant oconst =
  error ("Duplicate variant of " ^ quote oconst);

fun err_not_a_variant oconst =
  error ("Not a variant of " ^  quote oconst);

fun err_not_overloaded oconst =
  error ("Constant " ^ quote oconst ^ " is not declared as overloaded");

fun err_unresolved_overloading ctxt0 (c, T) t instances =
  let
    val ctxt = Config.put show_variants true ctxt0
    val const_space = Proof_Context.const_space ctxt
    val prt_const =
      Pretty.block [Name_Space.pretty ctxt const_space c, Pretty.str " ::", Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ ctxt T)]
  in
    error (Pretty.string_of (Pretty.chunks [
      Pretty.block [
        Pretty.str "Unresolved adhoc overloading of constant", Pretty.brk 1,
        prt_const, Pretty.brk 1, Pretty.str "in term", Pretty.brk 1,
        Pretty.block [Pretty.quote (Syntax.pretty_term ctxt t)]],
      Pretty.block (
        (if null instances then [Pretty.str "no instances"]
        else Pretty.fbreaks (
          Pretty.str "multiple instances:" ::
          map (Pretty.mark Markup.item o Syntax.pretty_term ctxt) instances)))]))
  end;


(* generic data *)

fun variants_eq ((v1, T1), (v2, T2)) =
  Term.aconv_untyped (v1, v2) andalso Type.raw_equiv (T1, T2);

structure Data = Generic_Data
(
  type T =
    {variants : (term * typ) list Symtab.table,
     oconsts : string Termtab.table};
  val empty : T = {variants = Symtab.empty, oconsts = Termtab.empty};

  fun merge
    ({variants = vtab1, oconsts = otab1},
     {variants = vtab2, oconsts = otab2}) : T =
    let
      fun join (oconst1, oconst2) =
        if oconst1 = oconst2 then oconst1
        else err_duplicate_variant oconst1;
    in
      {variants = Symtab.merge_list variants_eq (vtab1, vtab2),
       oconsts = Termtab.join (K join) (otab1, otab2)}
    end;
);

fun map_data f =
  Data.map (fn {variants, oconsts} =>
    let val (variants', oconsts') = f (variants, oconsts)
    in {variants = variants', oconsts = oconsts'} end);

val no_variants = Symtab.is_empty o #variants o Data.get;
val has_variants = Symtab.defined o #variants o Data.get;
val get_variants = Symtab.lookup o #variants o Data.get;
val get_overloaded = Termtab.lookup o #oconsts o Data.get;

fun generic_add_overloaded oconst context =
  if has_variants context oconst then context
  else (map_data o apfst) (Symtab.update (oconst, [])) context;

(*If the list of variants is empty at the end of "generic_remove_variant", then
  "generic_remove_overloaded" is called implicitly.*)
fun generic_remove_overloaded oconst context =
  let
    fun remove_oconst_and_variants context oconst =
      let
        val remove_variants =
          (case get_variants context oconst of
            NONE => I
          | SOME vs => fold (Termtab.remove (op =) o rpair oconst o fst) vs);
      in
        context |> map_data (fn (variants, oconsts) =>
          (Symtab.delete_safe oconst variants, remove_variants oconsts))
      end;
  in
    if has_variants context oconst then remove_oconst_and_variants context oconst
    else err_not_overloaded oconst
  end;

local
  fun generic_variant add oconst t context =
    let
      val _ = if has_variants context oconst then () else err_not_overloaded oconst;
      val T = t |> fastype_of;
      val t' = Term.map_types (K dummyT) t;
    in
      if add then
        let
          val _ =
            (case get_overloaded context t' of
              NONE => ()
            | SOME oconst' => err_duplicate_variant oconst');
        in
          context |> map_data (fn (variants, oconsts) =>
            (Symtab.cons_list (oconst, (t', T)) variants, Termtab.update (t', oconst) oconsts))
        end
      else
        let
          val _ =
            if member variants_eq (the (get_variants context oconst)) (t', T) then ()
            else err_not_a_variant oconst;
          val context' =
            context |> map_data (fn (variants, oconsts) =>
              (Symtab.map_entry oconst (remove1 variants_eq (t', T)) variants,
               Termtab.delete_safe t' oconsts));
        in
          (case get_variants context' oconst of
            SOME [] => generic_remove_overloaded oconst context'
          | _ => context')
        end
    end;
in
  val generic_add_variant = generic_variant true;
  val generic_remove_variant = generic_variant false;
end;


(* check / uncheck *)

local

fun unifiable_types ctxt (T1, T2) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val maxidx1 = Term.maxidx_of_typ T1;
    val T2' = Logic.incr_tvar (maxidx1 + 1) T2;
    val maxidx2 = Term.maxidx_typ T2' maxidx1;
  in can (Sign.typ_unify thy (T1, T2')) (Vartab.empty, maxidx2) end;

fun get_candidates ctxt (c, T) =
  get_variants (Context.Proof ctxt) c
  |> Option.map (map_filter (fn (t, T') =>
    if unifiable_types ctxt (T, T')
    (*keep the type constraint for the type-inference check phase*)
    then SOME (Type.constraint T t)
    else NONE));

val the_candidates = the oo get_candidates;

fun insert_variants_same ctxt t : term Same.operation =
  (fn Const const =>
      (case get_candidates ctxt const of
        SOME [] => err_unresolved_overloading ctxt const t []
      | SOME [variant] => variant
      | _ => raise Same.SAME)
    | _ => raise Same.SAME);

fun insert_overloaded ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun proc t =
      Term.map_types (K dummyT) t
      |> get_overloaded (Context.Proof ctxt)
      |> Option.map (Const o rpair (Term.type_of t));
  in
    Pattern.rewrite_term_yoyo thy [] [proc]
  end;

fun add_consts_overloaded ctxt =
  let
    val context = Context.Proof ctxt;
    val overloaded = has_variants context;
  in
    if no_variants context then K I
    else fold_aterms (fn Const (c, T) => if overloaded c then insert (op =) (c, T) else I | _ => I)
  end;

in

fun check ctxt =
  if no_variants (Context.Proof ctxt) then I
  else map (fn t => Term.map_aterms (insert_variants_same ctxt t) t);

fun uncheck ctxt ts =
  if Config.get ctxt show_variants orelse exists (not o can Term.type_of) ts then ts
  else map (insert_overloaded ctxt) ts;

fun reject_unresolved ctxt =
  let
    fun check_unresolved t =
      (case add_consts_overloaded ctxt t [] of
        [] => t
      | const :: _ => err_unresolved_overloading ctxt const t (the_candidates ctxt const));
  in map check_unresolved end;

end;


(* setup *)

val _ = Context.>>
  (Syntax_Phases.term_check 0 "adhoc_overloading" check
   #> Syntax_Phases.term_check 1 "adhoc_overloading_unresolved_check" reject_unresolved
   #> Syntax_Phases.term_uncheck 0 "adhoc_overloading" uncheck);


(* commands *)

local

fun generic_adhoc_overloading add args context =
  if Syntax.effective_polarity_generic context add then
    fold (fn (oconst, ts) =>
      generic_add_overloaded oconst
      #> fold (generic_add_variant oconst) ts) args context
  else
    fold (fn (oconst, ts) =>
      fold (generic_remove_variant oconst) ts) args context;

fun gen_adhoc_overloading prep_arg add raw_args lthy =
  let
    val args = map (prep_arg lthy) raw_args;
  in
    lthy |> Local_Theory.declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
      (fn phi =>
        let val args' = args
          |> map (apsnd (map_filter (fn t =>
               let val t' = Morphism.term phi t;
               in if Term.aconv_untyped (t, t') then SOME t' else NONE end)));
        in generic_adhoc_overloading add args' end)
  end;

fun cert_const_name ctxt c =
  (Consts.the_const_type (Proof_Context.consts_of ctxt) c; c);

fun read_const_name ctxt =
  dest_Const_name o Proof_Context.read_const {proper = true, strict = true} ctxt;

fun cert_term ctxt = Proof_Context.cert_term ctxt #> singleton (Variable.polymorphic ctxt);
fun read_term ctxt = Syntax.read_term ctxt #> singleton (Variable.polymorphic ctxt);

in

val adhoc_overloading =
  gen_adhoc_overloading (fn ctxt => fn (c, ts) => (cert_const_name ctxt c, map (cert_term ctxt) ts));

val adhoc_overloading_cmd =
  gen_adhoc_overloading (fn ctxt => fn (c, ts) => (read_const_name ctxt c, map (read_term ctxt) ts));

end;

end;
