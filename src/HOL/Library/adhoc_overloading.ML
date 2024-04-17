(*  Author:     Alexander Krauss, TU Muenchen
    Author:     Christian Sternagel, University of Innsbruck

Adhoc overloading of constants based on their types.
*)

signature ADHOC_OVERLOADING =
sig
  val is_overloaded: Proof.context -> string -> bool
  val generic_add_overloaded: string -> Context.generic -> Context.generic
  val generic_remove_overloaded: string -> Context.generic -> Context.generic
  val generic_add_variant: string -> term -> Context.generic -> Context.generic
  (*If the list of variants is empty at the end of "generic_remove_variant", then
  "generic_remove_overloaded" is called implicitly.*)
  val generic_remove_variant: string -> term -> Context.generic -> Context.generic
  val show_variants: bool Config.T
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
  Term.aconv_untyped (v1, v2) andalso T1 = T2;

structure Overload_Data = Generic_Data
(
  type T =
    {variants : (term * typ) list Symtab.table,
     oconsts : string Termtab.table};
  val empty = {variants = Symtab.empty, oconsts = Termtab.empty};

  fun merge
    ({variants = vtab1, oconsts = otab1},
     {variants = vtab2, oconsts = otab2}) : T =
    let
      fun merge_oconsts _ (oconst1, oconst2) =
        if oconst1 = oconst2 then oconst1
        else err_duplicate_variant oconst1;
    in
      {variants = Symtab.merge_list variants_eq (vtab1, vtab2),
       oconsts = Termtab.join merge_oconsts (otab1, otab2)}
    end;
);

fun map_tables f g =
  Overload_Data.map (fn {variants = vtab, oconsts = otab} =>
    {variants = f vtab, oconsts = g otab});

val is_overloaded = Symtab.defined o #variants o Overload_Data.get o Context.Proof;
val get_variants = Symtab.lookup o #variants o Overload_Data.get o Context.Proof;
val get_overloaded = Termtab.lookup o #oconsts o Overload_Data.get o Context.Proof;

fun generic_add_overloaded oconst context =
  if is_overloaded (Context.proof_of context) oconst then context
  else map_tables (Symtab.update (oconst, [])) I context;

fun generic_remove_overloaded oconst context =
  let
    fun remove_oconst_and_variants context oconst =
      let
        val remove_variants =
          (case get_variants (Context.proof_of context) oconst of
            NONE => I
          | SOME vs => fold (Termtab.remove (op =) o rpair oconst o fst) vs);
      in map_tables (Symtab.delete_safe oconst) remove_variants context end;
  in
    if is_overloaded (Context.proof_of context) oconst then remove_oconst_and_variants context oconst
    else err_not_overloaded oconst
  end;

local
  fun generic_variant add oconst t context =
    let
      val ctxt = Context.proof_of context;
      val _ = if is_overloaded ctxt oconst then () else err_not_overloaded oconst;
      val T = t |> fastype_of;
      val t' = Term.map_types (K dummyT) t;
    in
      if add then
        let
          val _ =
            (case get_overloaded ctxt t' of
              NONE => ()
            | SOME oconst' => err_duplicate_variant oconst');
        in
          map_tables (Symtab.cons_list (oconst, (t', T))) (Termtab.update (t', oconst)) context
        end
      else
        let
          val _ =
            if member variants_eq (the (get_variants ctxt oconst)) (t', T) then ()
            else err_not_a_variant oconst;
        in
          map_tables (Symtab.map_entry oconst (remove1 variants_eq (t', T)))
            (Termtab.delete_safe t') context
          |> (fn context =>
            (case get_variants (Context.proof_of context) oconst of
              SOME [] => generic_remove_overloaded oconst context
            | _ => context))
        end
    end;
in
  val generic_add_variant = generic_variant true;
  val generic_remove_variant = generic_variant false;
end;


(* check / uncheck *)

fun unifiable_with thy T1 T2 =
  let
    val maxidx1 = Term.maxidx_of_typ T1;
    val T2' = Logic.incr_tvar (maxidx1 + 1) T2;
    val maxidx2 = Term.maxidx_typ T2' maxidx1;
  in can (Sign.typ_unify thy (T1, T2')) (Vartab.empty, maxidx2) end;

fun get_candidates ctxt (c, T) =
  get_variants ctxt c
  |> Option.map (map_filter (fn (t, T') =>
    if unifiable_with (Proof_Context.theory_of ctxt) T T'
    (*keep the type constraint for the type-inference check phase*)
    then SOME (Type.constraint T t)
    else NONE));

fun insert_variants ctxt t (oconst as Const (c, T)) =
      (case get_candidates ctxt (c, T) of
        SOME [] => err_unresolved_overloading ctxt (c, T) t []
      | SOME [variant] => variant
      | _ => oconst)
  | insert_variants _ _ oconst = oconst;

fun insert_overloaded ctxt =
  let
    fun proc t =
      Term.map_types (K dummyT) t
      |> get_overloaded ctxt
      |> Option.map (Const o rpair (Term.type_of t));
  in
    Pattern.rewrite_term_top (Proof_Context.theory_of ctxt) [] [proc]
  end;

fun check ctxt =
  map (fn t => Term.map_aterms (insert_variants ctxt t) t);

fun uncheck ctxt ts =
  if Config.get ctxt show_variants orelse exists (is_none o try Term.type_of) ts then ts
  else map (insert_overloaded ctxt) ts;

fun reject_unresolved ctxt =
  let
    val the_candidates = the o get_candidates ctxt;
    fun check_unresolved t =
      (case filter (is_overloaded ctxt o fst) (Term.add_consts t []) of
        [] => t
      | (cT :: _) => err_unresolved_overloading ctxt cT t (the_candidates cT));
  in map check_unresolved end;


(* setup *)

val _ = Context.>>
  (Syntax_Phases.term_check 0 "adhoc_overloading" check
   #> Syntax_Phases.term_check 1 "adhoc_overloading_unresolved_check" reject_unresolved
   #> Syntax_Phases.term_uncheck 0 "adhoc_overloading" uncheck);


(* commands *)

fun generic_adhoc_overloading_cmd add =
  if add then
    fold (fn (oconst, ts) =>
      generic_add_overloaded oconst
      #> fold (generic_add_variant oconst) ts)
  else
    fold (fn (oconst, ts) =>
      fold (generic_remove_variant oconst) ts);

fun adhoc_overloading_cmd' add args phi =
  let val args' = args
    |> map (apsnd (map_filter (fn t =>
         let val t' = Morphism.term phi t;
         in if Term.aconv_untyped (t, t') then SOME t' else NONE end)));
  in generic_adhoc_overloading_cmd add args' end;

fun adhoc_overloading_cmd add raw_args lthy =
  let
    fun const_name ctxt =
      fst o dest_Const o Proof_Context.read_const {proper = false, strict = false} ctxt;  (* FIXME {proper = true, strict = true} (!?) *)
    fun read_term ctxt = singleton (Variable.polymorphic ctxt) o Syntax.read_term ctxt;
    val args =
      raw_args
      |> map (apfst (const_name lthy))
      |> map (apsnd (map (read_term lthy)));
  in
    Local_Theory.declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
      (adhoc_overloading_cmd' add args) lthy
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>adhoc_overloading\<close>
    "add adhoc overloading for constants / fixed variables"
    (Parse.and_list1 (Parse.const -- Scan.repeat Parse.term) >> adhoc_overloading_cmd true);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>no_adhoc_overloading\<close>
    "delete adhoc overloading for constants / fixed variables"
    (Parse.and_list1 (Parse.const -- Scan.repeat Parse.term) >> adhoc_overloading_cmd false);

end;

