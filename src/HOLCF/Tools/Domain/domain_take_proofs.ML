(*  Title:      HOLCF/Tools/domain/domain_take_proofs.ML
    Author:     Brian Huffman

Defines take functions for the given domain equation
and proves related theorems.
*)

signature DOMAIN_TAKE_PROOFS =
sig
  type iso_info =
    {
      absT : typ,
      repT : typ,
      abs_const : term,
      rep_const : term,
      abs_inverse : thm,
      rep_inverse : thm
    }

  val define_take_functions :
    (binding * iso_info) list -> theory ->
    { take_consts : term list,
      take_defs : thm list,
      chain_take_thms : thm list,
      take_0_thms : thm list,
      take_Suc_thms : thm list,
      deflation_take_thms : thm list,
      finite_consts : term list,
      finite_defs : thm list
    } * theory

  val map_of_typ :
    theory -> (typ * term) list -> typ -> term

  val add_map_function :
    (string * string * thm) -> theory -> theory

  val get_map_tab : theory -> string Symtab.table
  val get_deflation_thms : theory -> thm list
end;

structure Domain_Take_Proofs : DOMAIN_TAKE_PROOFS =
struct

type iso_info =
  {
    absT : typ,
    repT : typ,
    abs_const : term,
    rep_const : term,
    abs_inverse : thm,
    rep_inverse : thm
  };

val beta_ss =
  HOL_basic_ss
    addsimps simp_thms
    addsimps [@{thm beta_cfun}]
    addsimprocs [@{simproc cont_proc}];

val beta_tac = simp_tac beta_ss;

(******************************************************************************)
(******************************** theory data *********************************)
(******************************************************************************)

structure MapData = Theory_Data
(
  (* constant names like "foo_map" *)
  type T = string Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

structure DeflMapData = Theory_Data
(
  (* theorems like "deflation a ==> deflation (foo_map$a)" *)
  type T = thm list;
  val empty = [];
  val extend = I;
  val merge = Thm.merge_thms;
);

fun add_map_function (tname, map_name, deflation_map_thm) =
    MapData.map (Symtab.insert (K true) (tname, map_name))
    #> DeflMapData.map (Thm.add_thm deflation_map_thm);

val get_map_tab = MapData.get;
val get_deflation_thms = DeflMapData.get;

(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)

open HOLCF_Library;

infixr 6 ->>;
infix -->>;
infix 9 `;

val deflT = @{typ "udom alg_defl"};

fun mapT (T as Type (_, Ts)) =
    (map (fn T => T ->> T) Ts) -->> (T ->> T)
  | mapT T = T ->> T;

fun mk_Rep_of T =
  Const (@{const_name Rep_of}, Term.itselfT T --> deflT) $ Logic.mk_type T;

fun coerce_const T = Const (@{const_name coerce}, T);

fun isodefl_const T =
  Const (@{const_name isodefl}, (T ->> T) --> deflT --> HOLogic.boolT);

fun mk_deflation t =
  Const (@{const_name deflation}, Term.fastype_of t --> boolT) $ t;

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u));

(******************************************************************************)
(****************************** isomorphism info ******************************)
(******************************************************************************)

fun deflation_abs_rep (info : iso_info) : thm =
  let
    val abs_iso = #abs_inverse info;
    val rep_iso = #rep_inverse info;
    val thm = @{thm deflation_abs_rep} OF [abs_iso, rep_iso];
  in
    Drule.export_without_context thm
  end

(******************************************************************************)
(********************* building map functions over types **********************)
(******************************************************************************)

fun map_of_typ (thy : theory) (sub : (typ * term) list) (T : typ) : term =
  let
    val map_tab = get_map_tab thy;
    fun auto T = T ->> T;
    fun map_of T =
        case AList.lookup (op =) sub T of
          SOME m => (m, true) | NONE => map_of' T
    and map_of' (T as (Type (c, Ts))) =
        (case Symtab.lookup map_tab c of
          SOME map_name =>
          let
            val map_type = map auto Ts -->> auto T;
            val (ms, bs) = map_split map_of Ts;
          in
            if exists I bs
            then (list_ccomb (Const (map_name, map_type), ms), true)
            else (mk_ID T, false)
          end
        | NONE => (mk_ID T, false))
      | map_of' T = (mk_ID T, false);
  in
    fst (map_of T)
  end;


(******************************************************************************)
(********************* declaring definitions and theorems *********************)
(******************************************************************************)

fun define_const
    (bind : binding, rhs : term)
    (thy : theory)
    : (term * thm) * theory =
  let
    val typ = Term.fastype_of rhs;
    val (const, thy) = Sign.declare_const ((bind, typ), NoSyn) thy;
    val eqn = Logic.mk_equals (const, rhs);
    val def = Thm.no_attributes (Binding.suffix_name "_def" bind, eqn);
    val (def_thm, thy) = yield_singleton (PureThy.add_defs false) def thy;
  in
    ((const, def_thm), thy)
  end;

fun add_qualified_thm name (path, thm) thy =
    thy
    |> Sign.add_path path
    |> yield_singleton PureThy.add_thms
        (Thm.no_attributes (Binding.name name, thm))
    ||> Sign.parent_path;

fun add_qualified_simp_thm name (path, thm) thy =
    thy
    |> Sign.add_path path
    |> yield_singleton PureThy.add_thms
        ((Binding.name name, thm), [Simplifier.simp_add])
    ||> Sign.parent_path;

(******************************************************************************)
(************************** defining take functions ***************************)
(******************************************************************************)

fun define_take_functions
    (spec : (binding * iso_info) list)
    (thy : theory) =
  let

    (* retrieve components of spec *)
    val dom_binds = map fst spec;
    val iso_infos = map snd spec;
    val dom_eqns = map (fn x => (#absT x, #repT x)) iso_infos;
    val rep_abs_consts = map (fn x => (#rep_const x, #abs_const x)) iso_infos;
    val dnames = map Binding.name_of dom_binds;

    (* get table of map functions *)
    val map_tab = MapData.get thy;

    fun mk_projs []      t = []
      | mk_projs (x::[]) t = [(x, t)]
      | mk_projs (x::xs) t = (x, mk_fst t) :: mk_projs xs (mk_snd t);

    fun mk_cfcomp2 ((rep_const, abs_const), f) =
        mk_cfcomp (abs_const, mk_cfcomp (f, rep_const));

    (* define take functional *)
    val newTs : typ list = map fst dom_eqns;
    val copy_arg_type = mk_tupleT (map (fn T => T ->> T) newTs);
    val copy_arg = Free ("f", copy_arg_type);
    val copy_args = map snd (mk_projs dom_binds copy_arg);
    fun one_copy_rhs (rep_abs, (lhsT, rhsT)) =
      let
        val body = map_of_typ thy (newTs ~~ copy_args) rhsT;
      in
        mk_cfcomp2 (rep_abs, body)
      end;
    val take_functional =
        big_lambda copy_arg
          (mk_tuple (map one_copy_rhs (rep_abs_consts ~~ dom_eqns)));
    val take_rhss =
      let
        val n = Free ("n", HOLogic.natT);
        val rhs = mk_iterate (n, take_functional);
      in
        map (lambda n o snd) (mk_projs dom_binds rhs)
      end;

    (* define take constants *)
    fun define_take_const ((tbind, take_rhs), (lhsT, rhsT)) thy =
      let
        val take_type = HOLogic.natT --> lhsT ->> lhsT;
        val take_bind = Binding.suffix_name "_take" tbind;
        val (take_const, thy) =
          Sign.declare_const ((take_bind, take_type), NoSyn) thy;
        val take_eqn = Logic.mk_equals (take_const, take_rhs);
        val (take_def_thm, thy) =
          thy
          |> Sign.add_path (Binding.name_of tbind)
          |> yield_singleton
              (PureThy.add_defs false o map Thm.no_attributes)
              (Binding.name "take_def", take_eqn)
          ||> Sign.parent_path;
      in ((take_const, take_def_thm), thy) end;
    val ((take_consts, take_defs), thy) = thy
      |> fold_map define_take_const (dom_binds ~~ take_rhss ~~ dom_eqns)
      |>> ListPair.unzip;

    (* prove chain_take lemmas *)
    fun prove_chain_take (take_const, dname) thy =
      let
        val goal = mk_trp (mk_chain take_const);
        val rules = take_defs @ @{thms chain_iterate ch2ch_fst ch2ch_snd};
        val tac = simp_tac (HOL_basic_ss addsimps rules) 1;
        val thm = Goal.prove_global thy [] [] goal (K tac);
      in
        add_qualified_simp_thm "chain_take" (dname, thm) thy
      end;
    val (chain_take_thms, thy) =
      fold_map prove_chain_take (take_consts ~~ dnames) thy;

    (* prove take_0 lemmas *)
    fun prove_take_0 ((take_const, dname), (lhsT, rhsT)) thy =
      let
        val lhs = take_const $ @{term "0::nat"};
        val goal = mk_eqs (lhs, mk_bottom (lhsT ->> lhsT));
        val rules = take_defs @ @{thms iterate_0 fst_strict snd_strict};
        val tac = simp_tac (HOL_basic_ss addsimps rules) 1;
        val take_0_thm = Goal.prove_global thy [] [] goal (K tac);
      in
        add_qualified_thm "take_0" (dname, take_0_thm) thy
      end;
    val (take_0_thms, thy) =
      fold_map prove_take_0 (take_consts ~~ dnames ~~ dom_eqns) thy;

    (* prove take_Suc lemmas *)
    val n = Free ("n", natT);
    val take_is = map (fn t => t $ n) take_consts;
    fun prove_take_Suc
          (((take_const, rep_abs), dname), (lhsT, rhsT)) thy =
      let
        val lhs = take_const $ (@{term Suc} $ n);
        val body = map_of_typ thy (newTs ~~ take_is) rhsT;
        val rhs = mk_cfcomp2 (rep_abs, body);
        val goal = mk_eqs (lhs, rhs);
        val simps = @{thms iterate_Suc fst_conv snd_conv}
        val rules = take_defs @ simps;
        val tac = simp_tac (beta_ss addsimps rules) 1;
        val take_Suc_thm = Goal.prove_global thy [] [] goal (K tac);
      in
        add_qualified_thm "take_Suc" (dname, take_Suc_thm) thy
      end;
    val (take_Suc_thms, thy) =
      fold_map prove_take_Suc
        (take_consts ~~ rep_abs_consts ~~ dnames ~~ dom_eqns) thy;

    (* prove deflation theorems for take functions *)
    val deflation_abs_rep_thms = map deflation_abs_rep iso_infos;
    val deflation_take_thm =
      let
        val n = Free ("n", natT);
        fun mk_goal take_const = mk_deflation (take_const $ n);
        val goal = mk_trp (foldr1 mk_conj (map mk_goal take_consts));
        val adm_rules =
          @{thms adm_conj adm_subst [OF _ adm_deflation]
                 cont2cont_fst cont2cont_snd cont_id};
        val bottom_rules =
          take_0_thms @ @{thms deflation_UU simp_thms};
        val deflation_rules =
          @{thms conjI deflation_ID}
          @ deflation_abs_rep_thms
          @ DeflMapData.get thy;
      in
        Goal.prove_global thy [] [] goal (fn _ =>
         EVERY
          [rtac @{thm nat.induct} 1,
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           asm_simp_tac (HOL_basic_ss addsimps take_Suc_thms) 1,
           REPEAT (etac @{thm conjE} 1
                   ORELSE resolve_tac deflation_rules 1
                   ORELSE atac 1)])
      end;
    fun conjuncts [] thm = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1};
          val thmR = thm RS @{thm conjunct2};
        in (n, thmL):: conjuncts ns thmR end;
    val (deflation_take_thms, thy) =
      fold_map (add_qualified_thm "deflation_take")
        (map (apsnd Drule.export_without_context)
          (conjuncts dnames deflation_take_thm)) thy;

    (* prove strictness of take functions *)
    fun prove_take_strict (deflation_take, dname) thy =
      let
        val take_strict_thm =
            Drule.export_without_context
            (@{thm deflation_strict} OF [deflation_take]);
      in
        add_qualified_thm "take_strict" (dname, take_strict_thm) thy
      end;
    val (take_strict_thms, thy) =
      fold_map prove_take_strict
        (deflation_take_thms ~~ dnames) thy;

    (* prove take/take rules *)
    fun prove_take_take ((chain_take, deflation_take), dname) thy =
      let
        val take_take_thm =
            Drule.export_without_context
            (@{thm deflation_chain_min} OF [chain_take, deflation_take]);
      in
        add_qualified_thm "take_take" (dname, take_take_thm) thy
      end;
    val (take_take_thms, thy) =
      fold_map prove_take_take
        (chain_take_thms ~~ deflation_take_thms ~~ dnames) thy;

    (* prove take_below rules *)
    fun prove_take_below (deflation_take, dname) thy =
      let
        val take_below_thm =
            Drule.export_without_context
            (@{thm deflation.below} OF [deflation_take]);
      in
        add_qualified_thm "take_below" (dname, take_below_thm) thy
      end;
    val (take_below_thms, thy) =
      fold_map prove_take_below
        (deflation_take_thms ~~ dnames) thy;

    (* define finiteness predicates *)
    fun define_finite_const ((tbind, take_const), (lhsT, rhsT)) thy =
      let
        val finite_type = lhsT --> boolT;
        val finite_bind = Binding.suffix_name "_finite" tbind;
        val (finite_const, thy) =
          Sign.declare_const ((finite_bind, finite_type), NoSyn) thy;
        val x = Free ("x", lhsT);
        val n = Free ("n", natT);
        val finite_rhs =
          lambda x (HOLogic.exists_const natT $
            (lambda n (mk_eq (mk_capply (take_const $ n, x), x))));
        val finite_eqn = Logic.mk_equals (finite_const, finite_rhs);
        val (finite_def_thm, thy) =
          thy
          |> Sign.add_path (Binding.name_of tbind)
          |> yield_singleton
              (PureThy.add_defs false o map Thm.no_attributes)
              (Binding.name "finite_def", finite_eqn)
          ||> Sign.parent_path;
      in ((finite_const, finite_def_thm), thy) end;
    val ((finite_consts, finite_defs), thy) = thy
      |> fold_map define_finite_const (dom_binds ~~ take_consts ~~ dom_eqns)
      |>> ListPair.unzip;

    val result =
      {
        take_consts = take_consts,
        take_defs = take_defs,
        chain_take_thms = chain_take_thms,
        take_0_thms = take_0_thms,
        take_Suc_thms = take_Suc_thms,
        deflation_take_thms = deflation_take_thms,
        finite_consts = finite_consts,
        finite_defs = finite_defs
      };

  in
    (result, thy)
  end;

end;
