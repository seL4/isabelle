(*  Title:      HOLCF/Tools/repdef.ML
    Author:     Brian Huffman

Defining representable domains using algebraic deflations.
*)

signature REPDEF =
sig
  type rep_info =
    { emb_def: thm, prj_def: thm, approx_def: thm, REP: thm }

  val add_repdef: bool -> binding option -> binding * string list * mixfix ->
    term -> (binding * binding) option -> theory ->
    (Typedef.info * Pcpodef.cpo_info * Pcpodef.pcpo_info * rep_info) * theory

  val repdef_cmd: (bool * binding) * (binding * string list * mixfix) * string
    * (binding * binding) option -> theory -> theory
end;

structure Repdef :> REPDEF =
struct

(** type definitions **)

type rep_info =
  { emb_def: thm, prj_def: thm, approx_def: thm, REP: thm };

(* building terms *)

fun adm_const T = Const (@{const_name adm}, (T --> HOLogic.boolT) --> HOLogic.boolT);
fun mk_adm (x, T, P) = adm_const T $ absfree (x, T, P);

fun below_const T = Const (@{const_name below}, T --> T --> HOLogic.boolT);

val natT = @{typ nat};
val udomT = @{typ udom};
fun alg_deflT T = Type (@{type_name alg_defl}, [T]);
fun cfunT (T, U) = Type (@{type_name "->"}, [T, U]);
fun emb_const T = Const (@{const_name emb}, cfunT (T, udomT));
fun prj_const T = Const (@{const_name prj}, cfunT (udomT, T));
fun approx_const T = Const (@{const_name approx}, natT --> cfunT (T, T));

fun LAM_const (T, U) = Const (@{const_name Abs_CFun}, (T --> U) --> cfunT (T, U));
fun APP_const (T, U) = Const (@{const_name Rep_CFun}, cfunT (T, U) --> (T --> U));
fun cast_const T = Const (@{const_name cast}, cfunT (alg_deflT T, cfunT (T, T)));
fun mk_cast (t, x) =
  APP_const (udomT, udomT)
  $ (APP_const (alg_deflT udomT, cfunT (udomT, udomT)) $ cast_const udomT $ t)
  $ x;

(* manipulating theorems *)

(* proving class instances *)

fun declare_type_name a =
  Variable.declare_constraints (Logic.mk_type (TFree (a, dummyS)));

fun gen_add_repdef
      (prep_term: Proof.context -> 'a -> term)
      (def: bool)
      (name: binding)
      (typ as (t, vs, mx) : binding * string list * mixfix)
      (raw_defl: 'a)
      (opt_morphs: (binding * binding) option)
      (thy: theory)
    : (Typedef.info * Pcpodef.cpo_info * Pcpodef.pcpo_info * rep_info) * theory =
  let
    val _ = Theory.requires thy "Representable" "repdefs";
    val ctxt = ProofContext.init thy;

    (*rhs*)
    val defl = prep_term (ctxt |> fold declare_type_name vs) raw_defl;
    val deflT = Term.fastype_of defl;
    val _ = if deflT = @{typ "udom alg_defl"} then ()
            else error ("Not type udom alg_defl: " ^ quote (Syntax.string_of_typ ctxt deflT));
    val rhs_tfrees = Term.add_tfrees defl [];

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, the_default defS (AList.lookup (op =) rhs_tfrees v))) vs;
    val lhs_sorts = map snd lhs_tfrees;
    val tname = Binding.map_name (Syntax.type_name mx) t;
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
    val ((info, cpo_info, pcpo_info), thy2) = thy
      |> Pcpodef.add_pcpodef def (SOME name) typ set (SOME morphs) (tac1, tac2);

    (*definitions*)
    val Rep_const = Const (#Rep_name info, newT --> udomT);
    val Abs_const = Const (#Abs_name info, udomT --> newT);
    val emb_eqn = Logic.mk_equals (emb_const newT, LAM_const (newT, udomT) $ Rep_const);
    val prj_eqn = Logic.mk_equals (prj_const newT, LAM_const (udomT, newT) $
      Abs ("x", udomT, Abs_const $ mk_cast (defl, Bound 0)));
    val repdef_approx_const =
      Const (@{const_name repdef_approx}, (newT --> udomT) --> (udomT --> newT)
        --> alg_deflT udomT --> natT --> cfunT (newT, newT));
    val approx_eqn = Logic.mk_equals (approx_const newT,
      repdef_approx_const $ Rep_const $ Abs_const $ defl);

    (*instantiate class rep*)
    val name_def = Binding.suffix_name "_def" name;
    val ([emb_ldef, prj_ldef, approx_ldef], lthy3) = thy2
      |> Theory_Target.instantiation ([full_tname], lhs_tfrees, @{sort rep})
      |> fold_map Specification.definition
          [ (NONE, ((Binding.prefix_name "emb_" name_def, []), emb_eqn))
          , (NONE, ((Binding.prefix_name "prj_" name_def, []), prj_eqn))
          , (NONE, ((Binding.prefix_name "approx_" name_def, []), approx_eqn)) ]
      |>> map (snd o snd);
    val ctxt_thy = ProofContext.init (ProofContext.theory_of lthy3);
    val [emb_def, prj_def, approx_def] =
      ProofContext.export lthy3 ctxt_thy [emb_ldef, prj_ldef, approx_ldef];
    val typedef_thms =
      [#type_definition info, #below_def cpo_info, emb_def, prj_def, approx_def];
    val thy4 = lthy3
      |> Class.prove_instantiation_instance
          (K (Tactic.rtac (@{thm typedef_rep_class} OF typedef_thms) 1))
      |> Local_Theory.exit_global;

    (*other theorems*)
    val typedef_thms' = map (Thm.transfer thy4)
      [#type_definition info, #below_def cpo_info, emb_def, prj_def];
    val ([REP_thm], thy5) = thy4
      |> Sign.add_path (Binding.name_of name)
      |> PureThy.add_thms
        [((Binding.prefix_name "REP_" name,
          Drule.standard (@{thm typedef_REP} OF typedef_thms')), [])]
      ||> Sign.parent_path;

    val rep_info =
      { emb_def = emb_def, prj_def = prj_def, approx_def = approx_def, REP = REP_thm };
  in
    ((info, cpo_info, pcpo_info, rep_info), thy5)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in repdef " ^ quote (Binding.str_of name));

fun add_repdef def opt_name typ defl opt_morphs thy =
  let
    val name = the_default (#1 typ) opt_name;
  in
    gen_add_repdef Syntax.check_term def name typ defl opt_morphs thy
  end;

fun repdef_cmd ((def, name), typ, A, morphs) =
  snd o gen_add_repdef Syntax.read_term def name typ A morphs;

(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val repdef_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.binding || P.binding >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.binding) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.binding -- P.binding));

fun mk_repdef ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  repdef_cmd
    ((def, the_default (Binding.map_name (Syntax.type_name mx) t) opt_name), (t, vs, mx), A, morphs);

val _ =
  OuterSyntax.command "repdef" "HOLCF definition of representable domains" K.thy_goal
    (repdef_decl >>
      (Toplevel.print oo (Toplevel.theory o mk_repdef)));

end;

end;
