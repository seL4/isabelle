(*  Title:      HOLCF/Tools/repdef.ML
    Author:     Brian Huffman

Defining representable domains using algebraic deflations.
*)

signature REPDEF =
sig
  type rep_info =
    { emb_def: thm, prj_def: thm, defl_def: thm, DEFL: thm }

  val add_repdef: bool -> binding option -> binding * (string * sort) list * mixfix ->
    term -> (binding * binding) option -> theory ->
    (Typedef.info * Pcpodef.cpo_info * Pcpodef.pcpo_info * rep_info) * theory

  val repdef_cmd: (bool * binding) * (binding * (string * string option) list * mixfix) * string
    * (binding * binding) option -> theory -> theory
end;

structure Repdef :> REPDEF =
struct

open HOLCF_Library;

infixr 6 ->>;
infix -->>;

(** type definitions **)

type rep_info =
  { emb_def: thm, prj_def: thm, defl_def: thm, DEFL: thm };

(* building types and terms *)

val udomT = @{typ udom};
val deflT = @{typ defl};
fun emb_const T = Const (@{const_name emb}, T ->> udomT);
fun prj_const T = Const (@{const_name prj}, udomT ->> T);
fun defl_const T = Const (@{const_name defl}, Term.itselfT T --> deflT);

fun mk_cast (t, x) =
  capply_const (udomT, udomT)
  $ (capply_const (deflT, udomT ->> udomT) $ @{const cast} $ t)
  $ x;

(* manipulating theorems *)

(* proving class instances *)

fun declare_type_name a =
  Variable.declare_constraints (Logic.mk_type (TFree (a, dummyS)));

fun gen_add_repdef
      (prep_term: Proof.context -> 'a -> term)
      (def: bool)
      (name: binding)
      (typ as (tname, raw_args, mx) : binding * (string * sort) list * mixfix)
      (raw_defl: 'a)
      (opt_morphs: (binding * binding) option)
      (thy: theory)
    : (Typedef.info * Pcpodef.cpo_info * Pcpodef.pcpo_info * rep_info) * theory =
  let
    val _ = Theory.requires thy "Representable" "repdefs";

    (*rhs*)
    val tmp_ctxt =
      ProofContext.init_global thy
      |> fold (Variable.declare_typ o TFree) raw_args;
    val defl = prep_term tmp_ctxt raw_defl;
    val tmp_ctxt = tmp_ctxt |> Variable.declare_constraints defl;

    val deflT = Term.fastype_of defl;
    val _ = if deflT = @{typ "defl"} then ()
            else error ("Not type defl: " ^ quote (Syntax.string_of_typ tmp_ctxt deflT));

    (*lhs*)
    val lhs_tfrees = map (ProofContext.check_tfree tmp_ctxt) raw_args;
    val lhs_sorts = map snd lhs_tfrees;
    val full_tname = Sign.full_name thy tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    (*morphisms*)
    val morphs = opt_morphs
      |> the_default (Binding.prefix_name "Rep_" name, Binding.prefix_name "Abs_" name);

    (*set*)
    val in_defl = @{term "in_defl :: udom => defl => bool"};
    val set = HOLogic.Collect_const udomT $ Abs ("x", udomT, in_defl $ Bound 0 $ defl);

    (*pcpodef*)
    val tac1 = rtac @{thm CollectI} 1 THEN rtac @{thm bottom_in_defl} 1;
    val tac2 = rtac @{thm adm_mem_Collect_in_defl} 1;
    val ((info, cpo_info, pcpo_info), thy) = thy
      |> Pcpodef.add_pcpodef def (SOME name) typ set (SOME morphs) (tac1, tac2);

    (*definitions*)
    val Rep_const = Const (#Rep_name (#1 info), newT --> udomT);
    val Abs_const = Const (#Abs_name (#1 info), udomT --> newT);
    val emb_eqn = Logic.mk_equals (emb_const newT, cabs_const (newT, udomT) $ Rep_const);
    val prj_eqn = Logic.mk_equals (prj_const newT, cabs_const (udomT, newT) $
      Abs ("x", udomT, Abs_const $ mk_cast (defl, Bound 0)));
    val defl_eqn = Logic.mk_equals (defl_const newT,
      Abs ("x", Term.itselfT newT, defl));
    val name_def = Binding.suffix_name "_def" name;
    val emb_bind = (Binding.prefix_name "emb_" name_def, []);
    val prj_bind = (Binding.prefix_name "prj_" name_def, []);
    val defl_bind = (Binding.prefix_name "defl_" name_def, []);

    (*instantiate class rep*)
    val lthy = thy
      |> Class.instantiation ([full_tname], lhs_tfrees, @{sort bifinite});
    val ((_, (_, emb_ldef)), lthy) =
        Specification.definition (NONE, (emb_bind, emb_eqn)) lthy;
    val ((_, (_, prj_ldef)), lthy) =
        Specification.definition (NONE, (prj_bind, prj_eqn)) lthy;
    val ((_, (_, defl_ldef)), lthy) =
        Specification.definition (NONE, (defl_bind, defl_eqn)) lthy;
    val ctxt_thy = ProofContext.init_global (ProofContext.theory_of lthy);
    val emb_def = singleton (ProofContext.export lthy ctxt_thy) emb_ldef;
    val prj_def = singleton (ProofContext.export lthy ctxt_thy) prj_ldef;
    val defl_def = singleton (ProofContext.export lthy ctxt_thy) defl_ldef;
    val type_definition_thm =
      MetaSimplifier.rewrite_rule
        (the_list (#set_def (#2 info)))
        (#type_definition (#2 info));
    val typedef_thms =
      [type_definition_thm, #below_def cpo_info, emb_def, prj_def, defl_def];
    val thy = lthy
      |> Class.prove_instantiation_instance
          (K (Tactic.rtac (@{thm typedef_rep_class} OF typedef_thms) 1))
      |> Local_Theory.exit_global;

    (*other theorems*)
    val defl_thm' = Thm.transfer thy defl_def;
    val (DEFL_thm, thy) = thy
      |> Sign.add_path (Binding.name_of name)
      |> Global_Theory.add_thm
         ((Binding.prefix_name "DEFL_" name,
          Drule.zero_var_indexes (@{thm typedef_DEFL} OF [defl_thm'])), [])
      ||> Sign.restore_naming thy;

    val rep_info =
      { emb_def = emb_def, prj_def = prj_def, defl_def = defl_def, DEFL = DEFL_thm };
  in
    ((info, cpo_info, pcpo_info, rep_info), thy)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in repdef " ^ quote (Binding.str_of name));

fun add_repdef def opt_name typ defl opt_morphs thy =
  let
    val name = the_default (#1 typ) opt_name;
  in
    gen_add_repdef Syntax.check_term def name typ defl opt_morphs thy
  end;

fun repdef_cmd ((def, name), (b, raw_args, mx), A, morphs) thy =
  let
    val ctxt = ProofContext.init_global thy;
    val args = map (apsnd (Typedecl.read_constraint ctxt)) raw_args;
  in snd (gen_add_repdef Syntax.read_term def name (b, args, mx) A morphs thy) end;


(** outer syntax **)

val repdef_decl =
  Scan.optional (Parse.$$$ "(" |--
      ((Parse.$$$ "open" >> K false) -- Scan.option Parse.binding ||
        Parse.binding >> (fn s => (true, SOME s)))
        --| Parse.$$$ ")") (true, NONE) --
    (Parse.type_args_constrained -- Parse.binding) --
    Parse.opt_mixfix -- (Parse.$$$ "=" |-- Parse.term) --
    Scan.option (Parse.$$$ "morphisms" |-- Parse.!!! (Parse.binding -- Parse.binding));

fun mk_repdef ((((((def, opt_name), (args, t)), mx), A), morphs)) =
  repdef_cmd ((def, the_default t opt_name), (t, args, mx), A, morphs);

val _ =
  Outer_Syntax.command "repdef" "HOLCF definition of representable domains" Keyword.thy_decl
    (repdef_decl >>
      (Toplevel.print oo (Toplevel.theory o mk_repdef)));

end;
