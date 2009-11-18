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

fun mk_Rep_of T =
  Const (@{const_name Rep_of}, Term.itselfT T --> deflT) $ Logic.mk_type T;

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u));

(******************************************************************************)
(*************** fixed-point definitions and unfolding theorems ***************)
(******************************************************************************)

fun add_fixdefs
    (spec : (binding * term) list)
    (thy : theory) : thm list * theory =
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
    (unfold_thms, thy)
  end;


(******************************************************************************)

fun typ_of_dtyp
    (descr : (string * string list) list)
    (sorts : (string * sort) list)
    : DatatypeAux.dtyp -> typ =
  let
    fun tfree a = TFree (a, the (AList.lookup (op =) sorts a))
    fun typ_of (DatatypeAux.DtTFree a) = tfree a
      | typ_of (DatatypeAux.DtType (s, ds)) = Type (s, map typ_of ds)
      | typ_of (DatatypeAux.DtRec i) =
          let val (s, vs) = nth descr i
          in Type (s, map tfree vs) end
  in typ_of end;

fun is_closed_dtyp (DatatypeAux.DtTFree a) = false
  | is_closed_dtyp (DatatypeAux.DtRec i) = false
  | is_closed_dtyp (DatatypeAux.DtType (s, ds)) = forall is_closed_dtyp ds;

(* FIXME: use theory data for this *)
val defl_tab : term Symtab.table =
    Symtab.make [(@{type_name "->"}, @{term "cfun_typ"}),
                 (@{type_name "++"}, @{term "ssum_typ"}),
                 (@{type_name "**"}, @{term "sprod_typ"}),
                 (@{type_name "*"}, @{term "cprod_typ"}),
                 (@{type_name "u"}, @{term "u_typ"}),
                 (@{type_name "upper_pd"}, @{term "upper_typ"}),
                 (@{type_name "lower_pd"}, @{term "lower_typ"}),
                 (@{type_name "convex_pd"}, @{term "convex_typ"})];

fun defl_of_typ
    (tab : term Symtab.table)
    (free : string -> term)
    (T : typ) : term =
  let
    fun is_closed_typ (Type (_, Ts)) = forall is_closed_typ Ts
      | is_closed_typ _ = false;
    fun defl_of (TFree (a, _)) = free a
      | defl_of (TVar _) = error ("defl_of_typ: TVar")
      | defl_of (T as Type (c, Ts)) =
        case Symtab.lookup tab c of
          SOME t => Library.foldl mk_capply (t, map defl_of Ts)
        | NONE => if is_closed_typ T
                  then mk_Rep_of T
                  else error ("defl_of_typ: type variable under unsupported type constructor " ^ c);
  in defl_of T end;

fun defl_of_dtyp
    (descr : (string * string list) list)
    (sorts : (string * sort) list)
    (f : string -> term)
    (r : int -> term)
    (dt : DatatypeAux.dtyp) : term =
  let
    fun tfree a = TFree (a, the (AList.lookup (op =) sorts a))
    fun defl_of (DatatypeAux.DtTFree a) = f a
      | defl_of (DatatypeAux.DtRec i) = r i
      | defl_of (dt as DatatypeAux.DtType (s, ds)) =
        case Symtab.lookup defl_tab s of
          SOME t => Library.foldl mk_capply (t, map defl_of ds)
        | NONE => if DatatypeAux.is_rec_type dt
                  then error ("defl_of_dtyp: recursion under unsupported type constructor " ^ s)
                  else if is_closed_dtyp dt
                  then mk_Rep_of (typ_of_dtyp descr sorts dt)
                  else error ("defl_of_dtyp: type variable under unsupported type constructor " ^ s);
  in defl_of dt end;

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
    val dom_names = map fst new_doms;

    (* declare type combinator constants *)
    fun declare_typ_const (vs, tbind, mx, rhs) thy =
      let
        val typ_type = Library.foldr cfunT (map (K deflT) vs, deflT);
        val typ_bind = Binding.suffix_name "_typ" tbind;
      in
        Sign.declare_const ((typ_bind, typ_type), NoSyn) thy
      end;
    val (typ_consts, thy) = fold_map declare_typ_const doms thy;

    (* defining equations for type combinators *)
    val defl_tab1 = defl_tab; (* FIXME: use theory data *)
    val defl_tab2 =
      Symtab.make (map (fst o dest_Type o fst) dom_eqns ~~ typ_consts);
    val defl_tab' = Symtab.merge (K true) (defl_tab1, defl_tab2);
    fun free a = Free (Library.unprefix "'" a, deflT);
    fun mk_defl_spec (lhsT, rhsT) =
      mk_eqs (defl_of_typ defl_tab' free lhsT,
              defl_of_typ defl_tab' free rhsT);
    val defl_specs = map mk_defl_spec dom_eqns;

    (* register recursive definition of type combinators *)
    val typ_binds = map (Binding.suffix_name "_typ" o #2) doms;
    val (typ_unfold_thms, thy) = add_fixdefs (typ_binds ~~ defl_specs) thy;

    (* define types using deflation combinators *)
    fun make_repdef ((vs, tbind, mx, _), typ_const) thy =
      let
        fun tfree a = TFree (a, the (AList.lookup (op =) sorts a))
        val reps = map (mk_Rep_of o tfree) vs;
        val defl = Library.foldl mk_capply (typ_const, reps);
        val ((_, _, _, {REP, ...}), thy) =
          Repdef.add_repdef false NONE (tbind, vs, mx) defl NONE thy;
      in
        (REP, thy)
      end;
    val (REP_thms, thy) =
      fold_map make_repdef (doms ~~ typ_consts) thy;

    (* FIXME: use theory data for this *)
    val REP_simps = REP_thms @
      @{thms REP_cfun REP_ssum REP_sprod REP_cprod REP_up
             REP_upper REP_lower REP_convex};

    (* prove REP equations *)
    fun mk_REP_eqn_thm (lhsT, rhsT) =
      let
        val goal = mk_eqs (mk_Rep_of lhsT, mk_Rep_of rhsT);
        val tac =
          simp_tac (HOL_basic_ss addsimps REP_simps) 1
          THEN resolve_tac typ_unfold_thms 1;
      in
        Goal.prove_global thy [] [] goal (K tac)
      end;
    val REP_eqn_thms = map mk_REP_eqn_thm dom_eqns;

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
