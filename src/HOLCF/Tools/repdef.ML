(*  Title:      HOLCF/Tools/repdef.ML
    Author:     Brian Huffman

Defining representable domains using algebraic deflations.
*)

signature REPDEF =
sig
  type rep_info =
    { emb_def: thm, prj_def: thm, approx_def: thm, REP: thm }

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
  { emb_def: thm, prj_def: thm, approx_def: thm, REP: thm };

(* building types and terms *)

val udomT = @{typ udom};
fun alg_deflT T = Type (@{type_name alg_defl}, [T]);
fun emb_const T = Const (@{const_name emb}, T ->> udomT);
fun prj_const T = Const (@{const_name prj}, udomT ->> T);
fun approx_const T = Const (@{const_name approx}, natT --> (T ->> T));

fun cast_const T = Const (@{const_name cast}, alg_deflT T ->> T ->> T);
fun mk_cast (t, x) =
  capply_const (udomT, udomT)
  $ (capply_const (alg_deflT udomT, udomT ->> udomT) $ cast_const udomT $ t)
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
    val _ = if deflT = @{typ "udom alg_defl"} then ()
            else error ("Not type udom alg_defl: " ^ quote (Syntax.string_of_typ tmp_ctxt deflT));

    (*lhs*)
    val lhs_tfrees = map (ProofContext.check_tfree tmp_ctxt) raw_args;
    val lhs_sorts = map snd lhs_tfrees;
    val full_tname = Sign.full_name thy tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    (*morphisms*)
    val morphs = opt_morphs
      |> the_default (Binding.prefix_name "Rep_" name, Binding.prefix_name "Abs_" name);

    (*set*)
    val in_defl = @{term "in_deflation :: udom => udom alg_defl => bool"};
    val set = HOLogic.Collect_const udomT $ Abs ("x", udomT, in_defl $ Bound 0 $ defl);

    (*pcpodef*)
    val tac1 = rtac @{thm CollectI} 1 THEN rtac @{thm bottom_in_deflation} 1;
    val tac2 = rtac @{thm adm_mem_Collect_in_deflation} 1;
    val ((info, cpo_info, pcpo_info), thy) = thy
      |> Pcpodef.add_pcpodef def (SOME name) typ set (SOME morphs) (tac1, tac2);

    (*definitions*)
    val Rep_const = Const (#Rep_name (#1 info), newT --> udomT);
    val Abs_const = Const (#Abs_name (#1 info), udomT --> newT);
    val emb_eqn = Logic.mk_equals (emb_const newT, cabs_const (newT, udomT) $ Rep_const);
    val prj_eqn = Logic.mk_equals (prj_const newT, cabs_const (udomT, newT) $
      Abs ("x", udomT, Abs_const $ mk_cast (defl, Bound 0)));
    val repdef_approx_const =
      Const (@{const_name repdef_approx}, (newT --> udomT) --> (udomT --> newT)
        --> alg_deflT udomT --> natT --> (newT ->> newT));
    val approx_eqn = Logic.mk_equals (approx_const newT,
      repdef_approx_const $ Rep_const $ Abs_const $ defl);
    val name_def = Binding.suffix_name "_def" name;
    val emb_bind = (Binding.prefix_name "emb_" name_def, []);
    val prj_bind = (Binding.prefix_name "prj_" name_def, []);
    val approx_bind = (Binding.prefix_name "approx_" name_def, []);

    (*instantiate class rep*)
    val lthy = thy
      |> Theory_Target.instantiation ([full_tname], lhs_tfrees, @{sort rep});
    val ((_, (_, emb_ldef)), lthy) =
        Specification.definition (NONE, (emb_bind, emb_eqn)) lthy;
    val ((_, (_, prj_ldef)), lthy) =
        Specification.definition (NONE, (prj_bind, prj_eqn)) lthy;
    val ((_, (_, approx_ldef)), lthy) =
        Specification.definition (NONE, (approx_bind, approx_eqn)) lthy;
    val ctxt_thy = ProofContext.init_global (ProofContext.theory_of lthy);
    val emb_def = singleton (ProofContext.export lthy ctxt_thy) emb_ldef;
    val prj_def = singleton (ProofContext.export lthy ctxt_thy) prj_ldef;
    val approx_def = singleton (ProofContext.export lthy ctxt_thy) approx_ldef;
    val type_definition_thm =
      MetaSimplifier.rewrite_rule
        (the_list (#set_def (#2 info)))
        (#type_definition (#2 info));
    val typedef_thms =
      [type_definition_thm, #below_def cpo_info, emb_def, prj_def, approx_def];
    val thy = lthy
      |> Class.prove_instantiation_instance
          (K (Tactic.rtac (@{thm typedef_rep_class} OF typedef_thms) 1))
      |> Local_Theory.exit_global;

    (*other theorems*)
    val typedef_thms' = map (Thm.transfer thy)
      [type_definition_thm, #below_def cpo_info, emb_def, prj_def];
    val (REP_thm, thy) = thy
      |> Sign.add_path (Binding.name_of name)
      |> PureThy.add_thm
         ((Binding.prefix_name "REP_" name,
          Drule.zero_var_indexes (@{thm typedef_REP} OF typedef_thms')), [])
      ||> Sign.restore_naming thy;

    val rep_info =
      { emb_def = emb_def, prj_def = prj_def, approx_def = approx_def, REP = REP_thm };
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

local structure P = OuterParse and K = OuterKeyword in

val repdef_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.binding || P.binding >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args_constrained -- P.binding) -- P.opt_mixfix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.binding -- P.binding));

fun mk_repdef ((((((def, opt_name), (args, t)), mx), A), morphs)) =
  repdef_cmd ((def, the_default t opt_name), (t, args, mx), A, morphs);

val _ =
  OuterSyntax.command "repdef" "HOLCF definition of representable domains" K.thy_decl
    (repdef_decl >>
      (Toplevel.print oo (Toplevel.theory o mk_repdef)));

end;

end;
