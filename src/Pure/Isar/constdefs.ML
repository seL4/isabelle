(*  Title:      Pure/Isar/constdefs.ML
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)

Old-style constant definitions, with type-inference and optional
structure context; specifications need to observe strictly sequential
dependencies; no support for overloading.
*)

signature CONSTDEFS =
sig
  val add_constdefs: (binding * string option) list *
    ((binding * string option * mixfix) option * (Attrib.binding * string)) list -> theory -> theory
  val add_constdefs_i: (binding * typ option) list *
    ((binding * typ option * mixfix) option * (Thm.binding * term)) list -> theory -> theory
end;

structure Constdefs: CONSTDEFS =
struct

(** add_constdefs(_i) **)

fun gen_constdef prep_vars prep_prop prep_att
    structs (raw_decl, ((raw_name, raw_atts), raw_prop)) thy =
  let
    fun err msg ts = error (cat_lines (msg :: map (Syntax.string_of_term_global thy) ts));

    val thy_ctxt = ProofContext.init thy;
    val struct_ctxt = #2 (ProofContext.add_fixes structs thy_ctxt);
    val ((d, mx), var_ctxt) =
      (case raw_decl of
        NONE => ((NONE, NoSyn), struct_ctxt)
      | SOME raw_var =>
          struct_ctxt |> prep_vars [raw_var] |-> (fn [(x, T, mx)] =>
            ProofContext.add_fixes [(x, T, mx)] #> snd #> pair (SOME x, mx)));

    val prop = prep_prop var_ctxt raw_prop;
    val (c, T) = #1 (LocalDefs.cert_def thy_ctxt (Logic.strip_imp_concl prop));
    val _ =
      (case Option.map Name.of_binding d of
        NONE => ()
      | SOME c' =>
          if c <> c' then
            err ("Head of definition " ^ quote c ^ " differs from declaration " ^ quote c') []
          else ());
    val b = Binding.name c;

    val head = Const (Sign.full_bname thy c, T);
    val def = Term.subst_atomic [(Free (c, T), head)] prop;
    val name = Thm.def_binding_optional b raw_name;
    val atts = map (prep_att thy) raw_atts;

    val thy' =
      thy
      |> Sign.add_consts_i [(b, T, mx)]
      |> PureThy.add_defs false [((name, def), atts)]
      |-> (fn [thm] =>  (* FIXME thm vs. atts !? *)
        Spec_Rules.add_global Spec_Rules.Equational ([Logic.varify head], [thm]) #>
        Code.add_default_eqn thm #>
        Context.theory_map (Predicate_Compile_Preproc_Const_Defs.add_thm thm));
  in ((c, T), thy') end;

fun gen_constdefs prep_vars prep_prop prep_att (raw_structs, specs) thy =
  let
    val ctxt = ProofContext.init thy;
    val (structs, _) = prep_vars (map (fn (x, T) => (x, T, Structure)) raw_structs) ctxt;
    val (decls, thy') = fold_map (gen_constdef prep_vars prep_prop prep_att structs) specs thy;
  in Pretty.writeln (Proof_Display.pretty_consts ctxt (K true) decls); thy' end;

val add_constdefs = gen_constdefs ProofContext.read_vars Syntax.read_prop Attrib.attribute;
val add_constdefs_i = gen_constdefs ProofContext.cert_vars ProofContext.cert_prop (K I);

end;
