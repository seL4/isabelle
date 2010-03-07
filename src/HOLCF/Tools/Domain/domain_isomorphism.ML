(*  Title:      HOLCF/Tools/domain/domain_isomorphism.ML
    Author:     Brian Huffman

Defines new types satisfying the given domain equations.
*)

signature DOMAIN_ISOMORPHISM =
sig
  val domain_isomorphism :
    (string list * binding * mixfix * typ * (binding * binding) option) list
      -> theory -> Domain_Take_Proofs.iso_info list * theory
  val domain_isomorphism_cmd :
    (string list * binding * mixfix * string * (binding * binding) option) list
      -> theory -> theory
  val add_type_constructor :
    (string * term * string * thm  * thm * thm * thm) -> theory -> theory
end;

structure Domain_Isomorphism : DOMAIN_ISOMORPHISM =
struct

val beta_ss =
  HOL_basic_ss
    addsimps simp_thms
    addsimps [@{thm beta_cfun}]
    addsimprocs [@{simproc cont_proc}];

val beta_tac = simp_tac beta_ss;

(******************************************************************************)
(******************************** theory data *********************************)
(******************************************************************************)

structure DeflData = Theory_Data
(
  (* terms like "foo_defl" *)
  type T = term Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

structure RepData = Theory_Data
(
  (* theorems like "REP('a foo) = foo_defl$REP('a)" *)
  type T = thm list;
  val empty = [];
  val extend = I;
  val merge = Thm.merge_thms;
);

structure MapIdData = Theory_Data
(
  (* theorems like "foo_map$ID = ID" *)
  type T = thm list;
  val empty = [];
  val extend = I;
  val merge = Thm.merge_thms;
);

structure IsodeflData = Theory_Data
(
  (* theorems like "isodefl d t ==> isodefl (foo_map$d) (foo_defl$t)" *)
  type T = thm list;
  val empty = [];
  val extend = I;
  val merge = Thm.merge_thms;
);

fun add_type_constructor
  (tname, defl_const, map_name, REP_thm,
   isodefl_thm, map_ID_thm, defl_map_thm) =
    DeflData.map (Symtab.insert (K true) (tname, defl_const))
    #> Domain_Take_Proofs.add_map_function (tname, map_name, defl_map_thm)
    #> RepData.map (Thm.add_thm REP_thm)
    #> IsodeflData.map (Thm.add_thm isodefl_thm)
    #> MapIdData.map (Thm.add_thm map_ID_thm);


(* val get_map_tab = MapData.get; *)


(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)

open HOLCF_Library;

infixr 6 ->>;
infix -->>;

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

fun deflation_abs_rep (info : Domain_Take_Proofs.iso_info) : thm =
  let
    val abs_iso = #abs_inverse info;
    val rep_iso = #rep_inverse info;
    val thm = @{thm deflation_abs_rep} OF [abs_iso, rep_iso];
  in
    Drule.export_without_context thm
  end

(******************************************************************************)
(*************** fixed-point definitions and unfolding theorems ***************)
(******************************************************************************)

fun add_fixdefs
    (spec : (binding * term) list)
    (thy : theory) : (thm list * thm list) * theory =
  let
    val binds = map fst spec;
    val (lhss, rhss) = ListPair.unzip (map (dest_eqs o snd) spec);
    val functional = lambda_tuple lhss (mk_tuple rhss);
    val fixpoint = mk_fix (mk_cabs functional);

    (* project components of fixpoint *)
    fun mk_projs []      t = []
      | mk_projs (x::[]) t = [(x, t)]
      | mk_projs (x::xs) t = (x, mk_fst t) :: mk_projs xs (mk_snd t);
    val projs = mk_projs lhss fixpoint;

    (* convert parameters to lambda abstractions *)
    fun mk_eqn (lhs, rhs) =
        case lhs of
          Const (@{const_name Rep_CFun}, _) $ f $ (x as Free _) =>
            mk_eqn (f, big_lambda x rhs)
        | Const _ => Logic.mk_equals (lhs, rhs)
        | _ => raise TERM ("lhs not of correct form", [lhs, rhs]);
    val eqns = map mk_eqn projs;

    (* register constant definitions *)
    val (fixdef_thms, thy) =
      (PureThy.add_defs false o map Thm.no_attributes)
        (map (Binding.suffix_name "_def") binds ~~ eqns) thy;

    (* prove applied version of definitions *)
    fun prove_proj (lhs, rhs) =
      let
        val tac = rewrite_goals_tac fixdef_thms THEN beta_tac 1;
        val goal = Logic.mk_equals (lhs, rhs);
      in Goal.prove_global thy [] [] goal (K tac) end;
    val proj_thms = map prove_proj projs;

    (* mk_tuple lhss == fixpoint *)
    fun pair_equalI (thm1, thm2) = @{thm Pair_equalI} OF [thm1, thm2];
    val tuple_fixdef_thm = foldr1 pair_equalI proj_thms;

    val cont_thm =
      Goal.prove_global thy [] [] (mk_trp (mk_cont functional))
        (K (beta_tac 1));
    val tuple_unfold_thm =
      (@{thm def_cont_fix_eq} OF [tuple_fixdef_thm, cont_thm])
      |> Local_Defs.unfold (ProofContext.init thy) @{thms split_conv};

    fun mk_unfold_thms [] thm = []
      | mk_unfold_thms (n::[]) thm = [(n, thm)]
      | mk_unfold_thms (n::ns) thm = let
          val thmL = thm RS @{thm Pair_eqD1};
          val thmR = thm RS @{thm Pair_eqD2};
        in (n, thmL) :: mk_unfold_thms ns thmR end;
    val unfold_binds = map (Binding.suffix_name "_unfold") binds;

    (* register unfold theorems *)
    val (unfold_thms, thy) =
      (PureThy.add_thms o map (Thm.no_attributes o apsnd Drule.export_without_context))
        (mk_unfold_thms unfold_binds tuple_unfold_thm) thy;
  in
    ((proj_thms, unfold_thms), thy)
  end;


(******************************************************************************)
(****************** deflation combinators and map functions *******************)
(******************************************************************************)

fun defl_of_typ
    (tab : term Symtab.table)
    (T : typ) : term =
  let
    fun is_closed_typ (Type (_, Ts)) = forall is_closed_typ Ts
      | is_closed_typ _ = false;
    fun defl_of (TFree (a, _)) = Free (Library.unprefix "'" a, deflT)
      | defl_of (TVar _) = error ("defl_of_typ: TVar")
      | defl_of (T as Type (c, Ts)) =
        case Symtab.lookup tab c of
          SOME t => list_ccomb (t, map defl_of Ts)
        | NONE => if is_closed_typ T
                  then mk_Rep_of T
                  else error ("defl_of_typ: type variable under unsupported type constructor " ^ c);
  in defl_of T end;


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

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun read_typ thy str sorts =
  let
    val ctxt = ProofContext.init thy
      |> fold (Variable.declare_typ o TFree) sorts;
    val T = Syntax.read_typ ctxt str;
  in (T, Term.add_tfreesT T sorts) end;

fun cert_typ sign raw_T sorts =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T)
      handle TYPE (msg, _, _) => error msg;
    val sorts' = Term.add_tfreesT T sorts;
    val _ =
      case duplicates (op =) (map fst sorts') of
        [] => ()
      | dups => error ("Inconsistent sort constraints for " ^ commas dups)
  in (T, sorts') end;

fun gen_domain_isomorphism
    (prep_typ: theory -> 'a -> (string * sort) list -> typ * (string * sort) list)
    (doms_raw: (string list * binding * mixfix * 'a * (binding * binding) option) list)
    (thy: theory)
    : Domain_Take_Proofs.iso_info list * theory =
  let
    val _ = Theory.requires thy "Representable" "domain isomorphisms";

    (* this theory is used just for parsing *)
    val tmp_thy = thy |>
      Theory.copy |>
      Sign.add_types (map (fn (tvs, tname, mx, _, morphs) =>
        (tname, length tvs, mx)) doms_raw);

    fun prep_dom thy (vs, t, mx, typ_raw, morphs) sorts =
      let val (typ, sorts') = prep_typ thy typ_raw sorts
      in ((vs, t, mx, typ, morphs), sorts') end;

    val (doms : (string list * binding * mixfix * typ * (binding * binding) option) list,
         sorts : (string * sort) list) =
      fold_map (prep_dom tmp_thy) doms_raw [];

    (* domain equations *)
    fun mk_dom_eqn (vs, tbind, mx, rhs, morphs) =
      let fun arg v = TFree (v, the (AList.lookup (op =) sorts v));
      in (Type (Sign.full_name tmp_thy tbind, map arg vs), rhs) end;
    val dom_eqns = map mk_dom_eqn doms;

    (* check for valid type parameters *)
    val (tyvars, _, _, _, _) = hd doms;
    val new_doms = map (fn (tvs, tname, mx, _, _) =>
      let val full_tname = Sign.full_name tmp_thy tname
      in
        (case duplicates (op =) tvs of
          [] =>
            if eq_set (op =) (tyvars, tvs) then (full_tname, tvs)
            else error ("Mutually recursive domains must have same type parameters")
        | dups => error ("Duplicate parameter(s) for domain " ^ quote (Binding.str_of tname) ^
            " : " ^ commas dups))
      end) doms;
    val dom_binds = map (fn (_, tbind, _, _, _) => tbind) doms;
    val morphs = map (fn (_, _, _, _, morphs) => morphs) doms;

    (* declare deflation combinator constants *)
    fun declare_defl_const (vs, tbind, mx, rhs, morphs) thy =
      let
        val defl_type = map (K deflT) vs -->> deflT;
        val defl_bind = Binding.suffix_name "_defl" tbind;
      in
        Sign.declare_const ((defl_bind, defl_type), NoSyn) thy
      end;
    val (defl_consts, thy) = fold_map declare_defl_const doms thy;

    (* defining equations for type combinators *)
    val defl_tab1 = DeflData.get thy;
    val defl_tab2 =
      Symtab.make (map (fst o dest_Type o fst) dom_eqns ~~ defl_consts);
    val defl_tab' = Symtab.merge (K true) (defl_tab1, defl_tab2);
    val thy = DeflData.put defl_tab' thy;
    fun mk_defl_spec (lhsT, rhsT) =
      mk_eqs (defl_of_typ defl_tab' lhsT,
              defl_of_typ defl_tab' rhsT);
    val defl_specs = map mk_defl_spec dom_eqns;

    (* register recursive definition of deflation combinators *)
    val defl_binds = map (Binding.suffix_name "_defl") dom_binds;
    val ((defl_apply_thms, defl_unfold_thms), thy) =
      add_fixdefs (defl_binds ~~ defl_specs) thy;

    (* define types using deflation combinators *)
    fun make_repdef ((vs, tbind, mx, _, _), defl_const) thy =
      let
        fun tfree a = TFree (a, the (AList.lookup (op =) sorts a))
        val reps = map (mk_Rep_of o tfree) vs;
        val defl = list_ccomb (defl_const, reps);
        val ((_, _, _, {REP, ...}), thy) =
          Repdef.add_repdef false NONE (tbind, vs, mx) defl NONE thy;
      in
        (REP, thy)
      end;
    val (REP_thms, thy) = fold_map make_repdef (doms ~~ defl_consts) thy;
    val thy = RepData.map (fold Thm.add_thm REP_thms) thy;

    (* prove REP equations *)
    fun mk_REP_eq_thm (lhsT, rhsT) =
      let
        val goal = mk_eqs (mk_Rep_of lhsT, mk_Rep_of rhsT);
        val REP_simps = RepData.get thy;
        val tac =
          rewrite_goals_tac (map mk_meta_eq REP_simps)
          THEN resolve_tac defl_unfold_thms 1;
      in
        Goal.prove_global thy [] [] goal (K tac)
      end;
    val REP_eq_thms = map mk_REP_eq_thm dom_eqns;

    (* register REP equations *)
    val REP_eq_binds = map (Binding.prefix_name "REP_eq_") dom_binds;
    val (_, thy) = thy |>
      (PureThy.add_thms o map Thm.no_attributes)
        (REP_eq_binds ~~ REP_eq_thms);

    (* define rep/abs functions *)
    fun mk_rep_abs ((tbind, morphs), (lhsT, rhsT)) thy =
      let
        val rep_bind = Binding.suffix_name "_rep" tbind;
        val abs_bind = Binding.suffix_name "_abs" tbind;
        val ((rep_const, rep_def), thy) =
            define_const (rep_bind, coerce_const (lhsT ->> rhsT)) thy;
        val ((abs_const, abs_def), thy) =
            define_const (abs_bind, coerce_const (rhsT ->> lhsT)) thy;
      in
        (((rep_const, abs_const), (rep_def, abs_def)), thy)
      end;
    val ((rep_abs_consts, rep_abs_defs), thy) = thy
      |> fold_map mk_rep_abs (dom_binds ~~ morphs ~~ dom_eqns)
      |>> ListPair.unzip;

    (* prove isomorphism and isodefl rules *)
    fun mk_iso_thms ((tbind, REP_eq), (rep_def, abs_def)) thy =
      let
        fun make thm = Drule.export_without_context (thm OF [REP_eq, abs_def, rep_def]);
        val rep_iso_thm = make @{thm domain_rep_iso};
        val abs_iso_thm = make @{thm domain_abs_iso};
        val isodefl_thm = make @{thm isodefl_abs_rep};
        val rep_iso_bind = Binding.name "rep_iso";
        val abs_iso_bind = Binding.name "abs_iso";
        val isodefl_bind = Binding.name "isodefl_abs_rep";
        val (_, thy) = thy
          |> Sign.add_path (Binding.name_of tbind)
          |> (PureThy.add_thms o map Thm.no_attributes)
              [(rep_iso_bind, rep_iso_thm),
               (abs_iso_bind, abs_iso_thm),
               (isodefl_bind, isodefl_thm)]
          ||> Sign.parent_path;
      in
        (((rep_iso_thm, abs_iso_thm), isodefl_thm), thy)
      end;
    val ((iso_thms, isodefl_abs_rep_thms), thy) =
      thy
      |> fold_map mk_iso_thms (dom_binds ~~ REP_eq_thms ~~ rep_abs_defs)
      |>> ListPair.unzip;

    (* collect info about rep/abs *)
    val iso_infos : Domain_Take_Proofs.iso_info list =
      let
        fun mk_info (((lhsT, rhsT), (repC, absC)), (rep_iso, abs_iso)) =
          {
            repT = rhsT,
            absT = lhsT,
            rep_const = repC,
            abs_const = absC,
            rep_inverse = rep_iso,
            abs_inverse = abs_iso
          };
      in
        map mk_info (dom_eqns ~~ rep_abs_consts ~~ iso_thms)
      end

    (* declare map functions *)
    fun declare_map_const (tbind, (lhsT, rhsT)) thy =
      let
        val map_type = mapT lhsT;
        val map_bind = Binding.suffix_name "_map" tbind;
      in
        Sign.declare_const ((map_bind, map_type), NoSyn) thy
      end;
    val (map_consts, thy) = thy |>
      fold_map declare_map_const (dom_binds ~~ dom_eqns);

    (* defining equations for map functions *)
    local
      fun unprime a = Library.unprefix "'" a;
      fun mapvar T = Free (unprime (fst (dest_TFree T)), T ->> T);
      fun map_lhs (map_const, lhsT) =
          (lhsT, list_ccomb (map_const, map mapvar (snd (dest_Type lhsT))));
      val tab1 = map map_lhs (map_consts ~~ map fst dom_eqns);
      val Ts = (snd o dest_Type o fst o hd) dom_eqns;
      val tab = (Ts ~~ map mapvar Ts) @ tab1;
      fun mk_map_spec (((rep_const, abs_const), map_const), (lhsT, rhsT)) =
        let
          val lhs = Domain_Take_Proofs.map_of_typ thy tab lhsT;
          val body = Domain_Take_Proofs.map_of_typ thy tab rhsT;
          val rhs = mk_cfcomp (abs_const, mk_cfcomp (body, rep_const));
        in mk_eqs (lhs, rhs) end;
    in
      val map_specs =
          map mk_map_spec (rep_abs_consts ~~ map_consts ~~ dom_eqns);
    end;

    (* register recursive definition of map functions *)
    val map_binds = map (Binding.suffix_name "_map") dom_binds;
    val ((map_apply_thms, map_unfold_thms), thy) =
      add_fixdefs (map_binds ~~ map_specs) thy;

    (* prove isodefl rules for map functions *)
    val isodefl_thm =
      let
        fun unprime a = Library.unprefix "'" a;
        fun mk_d T = Free ("d" ^ unprime (fst (dest_TFree T)), deflT);
        fun mk_f T = Free ("f" ^ unprime (fst (dest_TFree T)), T ->> T);
        fun mk_assm T = mk_trp (isodefl_const T $ mk_f T $ mk_d T);
        fun mk_goal ((map_const, defl_const), (T, rhsT)) =
          let
            val (_, Ts) = dest_Type T;
            val map_term = list_ccomb (map_const, map mk_f Ts);
            val defl_term = list_ccomb (defl_const, map mk_d Ts);
          in isodefl_const T $ map_term $ defl_term end;
        val assms = (map mk_assm o snd o dest_Type o fst o hd) dom_eqns;
        val goals = map mk_goal (map_consts ~~ defl_consts ~~ dom_eqns);
        val goal = mk_trp (foldr1 HOLogic.mk_conj goals);
        val start_thms =
          @{thm split_def} :: defl_apply_thms @ map_apply_thms;
        val adm_rules =
          @{thms adm_conj adm_isodefl cont2cont_fst cont2cont_snd cont_id};
        val bottom_rules =
          @{thms fst_strict snd_strict isodefl_bottom simp_thms};
        val REP_simps = map (fn th => th RS sym) (RepData.get thy);
        val isodefl_rules =
          @{thms conjI isodefl_ID_REP}
          @ isodefl_abs_rep_thms
          @ IsodeflData.get thy;
      in
        Goal.prove_global thy [] assms goal (fn {prems, ...} =>
         EVERY
          [simp_tac (HOL_basic_ss addsimps start_thms) 1,
           (* FIXME: how reliable is unification here? *)
           (* Maybe I should instantiate the rule. *)
           rtac @{thm parallel_fix_ind} 1,
           REPEAT (resolve_tac adm_rules 1),
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           simp_tac beta_ss 1,
           simp_tac (HOL_basic_ss addsimps @{thms fst_conv snd_conv}) 1,
           simp_tac (HOL_basic_ss addsimps REP_simps) 1,
           REPEAT (etac @{thm conjE} 1),
           REPEAT (resolve_tac (isodefl_rules @ prems) 1 ORELSE atac 1)])
      end;
    val isodefl_binds = map (Binding.prefix_name "isodefl_") dom_binds;
    fun conjuncts [] thm = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1};
          val thmR = thm RS @{thm conjunct2};
        in (n, thmL):: conjuncts ns thmR end;
    val (isodefl_thms, thy) = thy |>
      (PureThy.add_thms o map (Thm.no_attributes o apsnd Drule.export_without_context))
        (conjuncts isodefl_binds isodefl_thm);
    val thy = IsodeflData.map (fold Thm.add_thm isodefl_thms) thy;

    (* prove map_ID theorems *)
    fun prove_map_ID_thm
        (((map_const, (lhsT, _)), REP_thm), isodefl_thm) =
      let
        val Ts = snd (dest_Type lhsT);
        val lhs = list_ccomb (map_const, map mk_ID Ts);
        val goal = mk_eqs (lhs, mk_ID lhsT);
        val tac = EVERY
          [rtac @{thm isodefl_REP_imp_ID} 1,
           stac REP_thm 1,
           rtac isodefl_thm 1,
           REPEAT (rtac @{thm isodefl_ID_REP} 1)];
      in
        Goal.prove_global thy [] [] goal (K tac)
      end;
    val map_ID_binds = map (Binding.suffix_name "_map_ID") dom_binds;
    val map_ID_thms =
      map prove_map_ID_thm
        (map_consts ~~ dom_eqns ~~ REP_thms ~~ isodefl_thms);
    val (_, thy) = thy |>
      (PureThy.add_thms o map Thm.no_attributes)
        (map_ID_binds ~~ map_ID_thms);
    val thy = MapIdData.map (fold Thm.add_thm map_ID_thms) thy;

    (* prove deflation theorems for map functions *)
    val deflation_abs_rep_thms = map deflation_abs_rep iso_infos;
    val deflation_map_thm =
      let
        fun unprime a = Library.unprefix "'" a;
        fun mk_f T = Free (unprime (fst (dest_TFree T)), T ->> T);
        fun mk_assm T = mk_trp (mk_deflation (mk_f T));
        fun mk_goal (map_const, (lhsT, rhsT)) =
          let
            val (_, Ts) = dest_Type lhsT;
            val map_term = list_ccomb (map_const, map mk_f Ts);
          in mk_deflation map_term end;
        val assms = (map mk_assm o snd o dest_Type o fst o hd) dom_eqns;
        val goals = map mk_goal (map_consts ~~ dom_eqns);
        val goal = mk_trp (foldr1 HOLogic.mk_conj goals);
        val start_thms =
          @{thm split_def} :: map_apply_thms;
        val adm_rules =
          @{thms adm_conj adm_subst [OF _ adm_deflation]
                 cont2cont_fst cont2cont_snd cont_id};
        val bottom_rules =
          @{thms fst_strict snd_strict deflation_UU simp_thms};
        val deflation_rules =
          @{thms conjI deflation_ID}
          @ deflation_abs_rep_thms
          @ Domain_Take_Proofs.get_deflation_thms thy;
      in
        Goal.prove_global thy [] assms goal (fn {prems, ...} =>
         EVERY
          [simp_tac (HOL_basic_ss addsimps start_thms) 1,
           rtac @{thm fix_ind} 1,
           REPEAT (resolve_tac adm_rules 1),
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           simp_tac beta_ss 1,
           simp_tac (HOL_basic_ss addsimps @{thms fst_conv snd_conv}) 1,
           REPEAT (etac @{thm conjE} 1),
           REPEAT (resolve_tac (deflation_rules @ prems) 1 ORELSE atac 1)])
      end;
    val deflation_map_binds = dom_binds |>
        map (Binding.prefix_name "deflation_" o Binding.suffix_name "_map");
    val (deflation_map_thms, thy) = thy |>
      (PureThy.add_thms o map (Thm.no_attributes o apsnd Drule.export_without_context))
        (conjuncts deflation_map_binds deflation_map_thm);

    (* register map functions in theory data *)
    local
      fun register_map ((dname, map_name), defl_thm) =
          Domain_Take_Proofs.add_map_function (dname, map_name, defl_thm);
      val dnames = map (fst o dest_Type o fst) dom_eqns;
      val map_names = map (fst o dest_Const) map_consts;
    in
      val thy =
          fold register_map (dnames ~~ map_names ~~ deflation_map_thms) thy;
    end;

    (* definitions and proofs related to take functions *)
    val (take_info, thy) =
        Domain_Take_Proofs.define_take_functions
          (dom_binds ~~ iso_infos) thy;
    val { take_consts, take_defs, chain_take_thms, take_0_thms,
          take_Suc_thms, deflation_take_thms,
          finite_consts, finite_defs } = take_info;

    (* least-upper-bound lemma for take functions *)
    val lub_take_lemma =
      let
        val lhs = mk_tuple (map mk_lub take_consts);
        fun mk_map_ID (map_const, (lhsT, rhsT)) =
          list_ccomb (map_const, map mk_ID (snd (dest_Type lhsT)));
        val rhs = mk_tuple (map mk_map_ID (map_consts ~~ dom_eqns));
        val goal = mk_trp (mk_eq (lhs, rhs));
        val start_rules =
            @{thms thelub_Pair [symmetric] ch2ch_Pair} @ chain_take_thms
            @ @{thms pair_collapse split_def}
            @ map_apply_thms @ MapIdData.get thy;
        val rules0 =
            @{thms iterate_0 Pair_strict} @ take_0_thms;
        val rules1 =
            @{thms iterate_Suc Pair_fst_snd_eq fst_conv snd_conv}
            @ take_Suc_thms;
        val tac =
            EVERY
            [simp_tac (HOL_basic_ss addsimps start_rules) 1,
             simp_tac (HOL_basic_ss addsimps @{thms fix_def2}) 1,
             rtac @{thm lub_eq} 1,
             rtac @{thm nat.induct} 1,
             simp_tac (HOL_basic_ss addsimps rules0) 1,
             asm_full_simp_tac (beta_ss addsimps rules1) 1];
      in
        Goal.prove_global thy [] [] goal (K tac)
      end;

    (* prove lub of take equals ID *)
    fun prove_lub_take (((bind, take_const), map_ID_thm), (lhsT, rhsT)) thy =
      let
        val n = Free ("n", natT);
        val goal = mk_eqs (mk_lub (lambda n (take_const $ n)), mk_ID lhsT);
        val tac =
            EVERY
            [rtac @{thm trans} 1, rtac map_ID_thm 2,
             cut_facts_tac [lub_take_lemma] 1,
             REPEAT (etac @{thm Pair_inject} 1), atac 1];
        val lub_take_thm = Goal.prove_global thy [] [] goal (K tac);
      in
        add_qualified_thm "lub_take" (Binding.name_of bind, lub_take_thm) thy
      end;
    val (lub_take_thms, thy) =
        fold_map prove_lub_take
          (dom_binds ~~ take_consts ~~ map_ID_thms ~~ dom_eqns) thy;

  in
    (iso_infos, thy)
  end;

val domain_isomorphism = gen_domain_isomorphism cert_typ;
val domain_isomorphism_cmd = snd oo gen_domain_isomorphism read_typ;

(******************************************************************************)
(******************************** outer syntax ********************************)
(******************************************************************************)

local

structure P = OuterParse and K = OuterKeyword

val parse_domain_iso :
    (string list * binding * mixfix * string * (binding * binding) option)
      parser =
  (P.type_args -- P.binding -- P.opt_mixfix -- (P.$$$ "=" |-- P.typ) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.binding -- P.binding)))
    >> (fn ((((vs, t), mx), rhs), morphs) => (vs, t, mx, rhs, morphs));

val parse_domain_isos = P.and_list1 parse_domain_iso;

in

val _ =
  OuterSyntax.command "domain_isomorphism" "define domain isomorphisms (HOLCF)" K.thy_decl
    (parse_domain_isos >> (Toplevel.theory o domain_isomorphism_cmd));

end;

end;
