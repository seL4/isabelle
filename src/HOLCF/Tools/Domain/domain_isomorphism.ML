(*  Title:      HOLCF/Tools/domain/domain_isomorphism.ML
    Author:     Brian Huffman

Defines new types satisfying the given domain equations.
*)

signature DOMAIN_ISOMORPHISM =
sig
  val domain_isomorphism:
     (string list * binding * mixfix * typ) list -> theory -> theory
  val domain_isomorphism_cmd:
     (string list * binding * mixfix * string) list -> theory -> theory
  val add_defl_const: (string * term) -> theory -> theory
  val get_defl_consts: theory -> (string * term) list
  val add_map_const: (string * string) -> theory -> theory
  val get_map_consts: theory -> (string * string) list
end;

structure Domain_Isomorphism :> DOMAIN_ISOMORPHISM =
struct

val beta_ss =
  HOL_basic_ss
    addsimps simp_thms
    addsimps [@{thm beta_cfun}]
    addsimprocs [@{simproc cont_proc}];

val beta_tac = simp_tac beta_ss;

(******************************************************************************)
(******************************* building types *******************************)
(******************************************************************************)

(* ->> is taken from holcf_logic.ML *)
fun cfunT (T, U) = Type(@{type_name "->"}, [T, U]);

infixr 6 ->>; val (op ->>) = cfunT;

fun dest_cfunT (Type(@{type_name "->"}, [T, U])) = (T, U)
  | dest_cfunT T = raise TYPE ("dest_cfunT", [T], []);

fun tupleT [] = HOLogic.unitT
  | tupleT [T] = T
  | tupleT (T :: Ts) = HOLogic.mk_prodT (T, tupleT Ts);

val deflT = @{typ "udom alg_defl"};

fun mapT (T as Type (_, Ts)) =
  Library.foldr cfunT (map (fn T => T ->> T) Ts, T ->> T);     

(******************************************************************************)
(******************************* building terms *******************************)
(******************************************************************************)

(* builds the expression (v1,v2,..,vn) *)
fun mk_tuple [] = HOLogic.unit
|   mk_tuple (t::[]) = t
|   mk_tuple (t::ts) = HOLogic.mk_prod (t, mk_tuple ts);

(* builds the expression (%(v1,v2,..,vn). rhs) *)
fun lambda_tuple [] rhs = Term.lambda (Free("unit", HOLogic.unitT)) rhs
  | lambda_tuple (v::[]) rhs = Term.lambda v rhs
  | lambda_tuple (v::vs) rhs =
      HOLogic.mk_split (Term.lambda v (lambda_tuple vs rhs));

(* continuous application and abstraction *)

fun capply_const (S, T) =
  Const(@{const_name Rep_CFun}, (S ->> T) --> (S --> T));

fun cabs_const (S, T) =
  Const(@{const_name Abs_CFun}, (S --> T) --> (S ->> T));

fun mk_cabs t =
  let val T = Term.fastype_of t
  in cabs_const (Term.domain_type T, Term.range_type T) $ t end

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs =
  cabs_const (Term.fastype_of v, Term.fastype_of rhs) $ Term.lambda v rhs;

(* builds the expression (LAM v1 v2 .. vn. rhs) *)
fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs);

fun mk_capply (t, u) =
  let val (S, T) =
    case Term.fastype_of t of
        Type(@{type_name "->"}, [S, T]) => (S, T)
      | _ => raise TERM ("mk_capply " ^ ML_Syntax.print_list ML_Syntax.print_term [t, u], [t, u]);
  in capply_const (S, T) $ t $ u end;

(* miscellaneous term constructions *)

val mk_trp = HOLogic.mk_Trueprop;

val mk_fst = HOLogic.mk_fst;
val mk_snd = HOLogic.mk_snd;

fun mk_cont t =
  let val T = Term.fastype_of t
  in Const(@{const_name cont}, T --> HOLogic.boolT) $ t end;

fun mk_fix t =
  let val (T, _) = dest_cfunT (Term.fastype_of t)
  in mk_capply (Const(@{const_name fix}, (T ->> T) ->> T), t) end;

fun ID_const T = Const (@{const_name ID}, cfunT (T, T));

fun cfcomp_const (T, U, V) =
  Const (@{const_name cfcomp}, (U ->> V) ->> (T ->> U) ->> (T ->> V));

fun mk_cfcomp (f, g) =
  let
    val (U, V) = dest_cfunT (Term.fastype_of f);
    val (T, U') = dest_cfunT (Term.fastype_of g);
  in
    if U = U'
    then mk_capply (mk_capply (cfcomp_const (T, U, V), f), g)
    else raise TYPE ("mk_cfcomp", [U, U'], [f, g])
  end;

fun mk_Rep_of T =
  Const (@{const_name Rep_of}, Term.itselfT T --> deflT) $ Logic.mk_type T;

fun coerce_const T = Const (@{const_name coerce}, T);

fun isodefl_const T =
  Const (@{const_name isodefl}, (T ->> T) --> deflT --> HOLogic.boolT);

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u));

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
    fun mk_projs (x::[]) t = [(x, t)]
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
      |> LocalDefs.unfold (ProofContext.init thy) @{thms split_conv};

    fun mk_unfold_thms [] thm = []
      | mk_unfold_thms (n::[]) thm = [(n, thm)]
      | mk_unfold_thms (n::ns) thm = let
          val thmL = thm RS @{thm Pair_eqD1};
          val thmR = thm RS @{thm Pair_eqD2};
        in (n, thmL) :: mk_unfold_thms ns thmR end;
    val unfold_binds = map (Binding.suffix_name "_unfold") binds;

    (* register unfold theorems *)
    val (unfold_thms, thy) =
      (PureThy.add_thms o map (Thm.no_attributes o apsnd Drule.standard))
        (mk_unfold_thms unfold_binds tuple_unfold_thm) thy;
  in
    ((proj_thms, unfold_thms), thy)
  end;


(******************************************************************************)
(****************** deflation combinators and map functions *******************)
(******************************************************************************)

structure DeflData = Theory_Data
(
  type T = term Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

fun add_defl_const data = DeflData.map (Symtab.insert (K true) data);
fun get_defl_consts thy = Symtab.dest (DeflData.get thy);

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
          SOME t => Library.foldl mk_capply (t, map defl_of Ts)
        | NONE => if is_closed_typ T
                  then mk_Rep_of T
                  else error ("defl_of_typ: type variable under unsupported type constructor " ^ c);
  in defl_of T end;

structure MapData = Theory_Data
(
  type T = string Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

fun add_map_const data = MapData.map (Symtab.insert (K true) data);
fun get_map_consts thy = Symtab.dest (MapData.get thy);

fun map_of_typ
    (tab : string Symtab.table)
    (T : typ) : term =
  let
    fun is_closed_typ (Type (_, Ts)) = forall is_closed_typ Ts
      | is_closed_typ _ = false;
    fun map_of (T as TFree (a, _)) = Free (Library.unprefix "'" a, T ->> T)
      | map_of (T as TVar _) = error ("map_of_typ: TVar")
      | map_of (T as Type (c, Ts)) =
        case Symtab.lookup tab c of
          SOME t => Library.foldl mk_capply (Const (t, mapT T), map map_of Ts)
        | NONE => if is_closed_typ T
                  then ID_const T
                  else error ("map_of_typ: type variable under unsupported type constructor " ^ c);
  in map_of T end;


(******************************************************************************)
(* prepare datatype specifications *)

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
    (doms_raw: (string list * binding * mixfix * 'a) list)
    (thy: theory)
    : theory =
  let
    val _ = Theory.requires thy "Domain" "domain definitions";

    (* this theory is used just for parsing *)
    val tmp_thy = thy |>
      Theory.copy |>
      Sign.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) doms_raw);

    fun prep_dom thy (vs, t, mx, typ_raw) sorts =
      let val (typ, sorts') = prep_typ thy typ_raw sorts
      in ((vs, t, mx, typ), sorts') end;

    val (doms : (string list * binding * mixfix * typ) list,
         sorts : (string * sort) list) =
      fold_map (prep_dom tmp_thy) doms_raw [];

    (* domain equations *)
    fun mk_dom_eqn (vs, tbind, mx, rhs) =
      let fun arg v = TFree (v, the (AList.lookup (op =) sorts v));
      in (Type (Sign.full_name tmp_thy tbind, map arg vs), rhs) end;
    val dom_eqns = map mk_dom_eqn doms;

    (* check for valid type parameters *)
    val (tyvars, _, _, _)::_ = doms;
    val new_doms = map (fn (tvs, tname, mx, _) =>
      let val full_tname = Sign.full_name tmp_thy tname
      in
        (case duplicates (op =) tvs of
          [] =>
            if eq_set (op =) (tyvars, tvs) then (full_tname, tvs)
            else error ("Mutually recursive domains must have same type parameters")
        | dups => error ("Duplicate parameter(s) for domain " ^ quote (Binding.str_of tname) ^
            " : " ^ commas dups))
      end) doms;
    val dom_binds = map (fn (_, tbind, _, _) => tbind) doms;

    (* declare deflation combinator constants *)
    fun declare_defl_const (vs, tbind, mx, rhs) thy =
      let
        val defl_type = Library.foldr cfunT (map (K deflT) vs, deflT);
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
    fun make_repdef ((vs, tbind, mx, _), defl_const) thy =
      let
        fun tfree a = TFree (a, the (AList.lookup (op =) sorts a))
        val reps = map (mk_Rep_of o tfree) vs;
        val defl = Library.foldl mk_capply (defl_const, reps);
        val ((_, _, _, {REP, ...}), thy) =
          Repdef.add_repdef false NONE (tbind, vs, mx) defl NONE thy;
      in
        (REP, thy)
      end;
    val (REP_thms, thy) = fold_map make_repdef (doms ~~ defl_consts) thy;

    (* FIXME: use theory data for this *)
    val REP_simps = REP_thms @
      @{thms REP_cfun REP_ssum REP_sprod REP_cprod REP_up
             REP_upper REP_lower REP_convex};

    (* prove REP equations *)
    fun mk_REP_eq_thm (lhsT, rhsT) =
      let
        val goal = mk_eqs (mk_Rep_of lhsT, mk_Rep_of rhsT);
        val tac =
          simp_tac (HOL_basic_ss addsimps REP_simps) 1
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
    fun mk_rep_abs (tbind, (lhsT, rhsT)) thy =
      let
        val rep_type = cfunT (lhsT, rhsT);
        val abs_type = cfunT (rhsT, lhsT);
        val rep_bind = Binding.suffix_name "_rep" tbind;
        val abs_bind = Binding.suffix_name "_abs" tbind;
        val (rep_const, thy) = thy |>
          Sign.declare_const ((rep_bind, rep_type), NoSyn);
        val (abs_const, thy) = thy |>
          Sign.declare_const ((abs_bind, abs_type), NoSyn);
        val rep_eqn = Logic.mk_equals (rep_const, coerce_const rep_type);
        val abs_eqn = Logic.mk_equals (abs_const, coerce_const abs_type);
        val ([rep_def, abs_def], thy) = thy |>
          (PureThy.add_defs false o map Thm.no_attributes)
            [(Binding.suffix_name "_rep_def" tbind, rep_eqn),
             (Binding.suffix_name "_abs_def" tbind, abs_eqn)];
      in
        (((rep_const, abs_const), (rep_def, abs_def)), thy)
      end;
    val ((rep_abs_consts, rep_abs_defs), thy) = thy
      |> fold_map mk_rep_abs (dom_binds ~~ dom_eqns)
      |>> ListPair.unzip;

    (* prove isomorphism and isodefl rules *)
    fun mk_iso_thms ((tbind, REP_eq), (rep_def, abs_def)) thy =
      let
        fun make thm = Drule.standard (thm OF [REP_eq, abs_def, rep_def]);
        val rep_iso_thm = make @{thm domain_rep_iso};
        val abs_iso_thm = make @{thm domain_abs_iso};
        val isodefl_thm = make @{thm isodefl_abs_rep};
        val rep_iso_bind = Binding.suffix_name "_rep_iso" tbind;
        val abs_iso_bind = Binding.suffix_name "_abs_iso" tbind;
        val isodefl_bind = Binding.prefix_name "isodefl_abs_rep_" tbind;
        val (_, thy) = thy |>
          (PureThy.add_thms o map Thm.no_attributes)
            [(rep_iso_bind, rep_iso_thm),
             (abs_iso_bind, abs_iso_thm),
             (isodefl_bind, isodefl_thm)];
      in
        (((rep_iso_thm, abs_iso_thm), isodefl_thm), thy)
      end;
    val ((iso_thms, isodefl_abs_rep_thms), thy) = thy
      |> fold_map mk_iso_thms (dom_binds ~~ REP_eq_thms ~~ rep_abs_defs)
      |>> ListPair.unzip;

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
    val map_tab1 = MapData.get thy;
    val map_tab2 =
      Symtab.make (map (fst o dest_Type o fst) dom_eqns
                   ~~ map (fst o dest_Const) map_consts);
    val map_tab' = Symtab.merge (K true) (map_tab1, map_tab2);
    val thy = MapData.put map_tab' thy;
    fun mk_map_spec ((rep_const, abs_const), (lhsT, rhsT)) =
      let
        val lhs = map_of_typ map_tab' lhsT;
        val body = map_of_typ map_tab' rhsT;
        val rhs = mk_cfcomp (abs_const, mk_cfcomp (body, rep_const));
      in mk_eqs (lhs, rhs) end;
    val map_specs = map mk_map_spec (rep_abs_consts ~~ dom_eqns);

    (* register recursive definition of map functions *)
    val map_binds = map (Binding.suffix_name "_map") dom_binds;
    val ((map_apply_thms, map_unfold_thms), thy) =
      add_fixdefs (map_binds ~~ map_specs) thy;

    (* prove isodefl rules for map functions *)
    val isodefl_thm =
      let
        fun unprime a = Library.unprefix "'" a;
        fun mk_d (TFree (a, _)) = Free ("d" ^ unprime a, deflT);
        fun mk_f (T as TFree (a, _)) = Free ("f" ^ unprime a, T ->> T);
        fun mk_assm T = mk_trp (isodefl_const T $ mk_f T $ mk_d T);
        fun mk_goal ((map_const, defl_const), (T as Type (c, Ts), rhsT)) =
          let
            val map_term = Library.foldl mk_capply (map_const, map mk_f Ts);
            val defl_term = Library.foldl mk_capply (defl_const, map mk_d Ts);
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
        (* FIXME: use theory data for this *)
        val isodefl_rules =
          @{thms conjI isodefl_ID_REP} @ isodefl_abs_rep_thms @
          @{thms isodefl_cfun isodefl_ssum isodefl_sprod isodefl_cprod
                 isodefl_u isodefl_upper isodefl_lower isodefl_convex};
        fun tacf {prems, ...} = EVERY
          [simp_tac (HOL_basic_ss addsimps start_thms) 1,
           rtac @{thm parallel_fix_ind} 1,
           REPEAT (resolve_tac adm_rules 1),
           simp_tac (HOL_basic_ss addsimps bottom_rules) 1,
           simp_tac beta_ss 1,
           simp_tac (HOL_basic_ss addsimps @{thms fst_conv snd_conv}) 1,
           REPEAT (etac @{thm conjE} 1),
           REPEAT (resolve_tac (isodefl_rules @ prems) 1 ORELSE atac 1)];
      in
        Goal.prove_global thy [] assms goal tacf
      end;
    val isodefl_binds = map (Binding.prefix_name "isodefl_") dom_binds;
    fun conjuncts [] thm = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1};
          val thmR = thm RS @{thm conjunct2};
        in (n, thmL):: conjuncts ns thmR end;
    val (isodefl_thms, thy) = thy |>
      (PureThy.add_thms o map (Thm.no_attributes o apsnd Drule.standard))
        (conjuncts isodefl_binds isodefl_thm);
  in
    thy
  end;

val domain_isomorphism = gen_domain_isomorphism cert_typ;
val domain_isomorphism_cmd = gen_domain_isomorphism read_typ;

(******************************************************************************)
(******************************** outer syntax ********************************)
(******************************************************************************)

local

structure P = OuterParse and K = OuterKeyword

val parse_domain_iso : (string list * binding * mixfix * string) parser =
  (P.type_args -- P.binding -- P.opt_infix -- (P.$$$ "=" |-- P.typ))
    >> (fn (((vs, t), mx), rhs) => (vs, t, mx, rhs));

val parse_domain_isos = P.and_list1 parse_domain_iso;

in

val _ =
  OuterSyntax.command "domain_isomorphism" "define domain isomorphisms (HOLCF)" K.thy_decl
    (parse_domain_isos >> (Toplevel.theory o domain_isomorphism_cmd));

end;

end;
