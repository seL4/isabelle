(*  Title:      HOLCF/Tools/domain/domain_constructors.ML
    Author:     Brian Huffman

Defines constructor functions for a given domain isomorphism
and proves related theorems.
*)

signature DOMAIN_CONSTRUCTORS =
sig
  val add_domain_constructors :
      string
      -> typ * (binding * (bool * binding option * typ) list * mixfix) list
      -> term * term
      -> thm * thm
      -> theory
      -> { con_consts : term list,
           con_defs : thm list }
         * theory;
end;


structure Domain_Constructors :> DOMAIN_CONSTRUCTORS =
struct

(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)


(*** Continuous function space ***)

(* ->> is taken from holcf_logic.ML *)
fun mk_cfunT (T, U) = Type(@{type_name "->"}, [T, U]);

infixr 6 ->>; val (op ->>) = mk_cfunT;

fun dest_cfunT (Type(@{type_name "->"}, [T, U])) = (T, U)
  | dest_cfunT T = raise TYPE ("dest_cfunT", [T], []);

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

infix 9 ` ; val (op `) = mk_capply;


(*** Product type ***)

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT [T] = T
  | mk_tupleT (T :: Ts) = HOLogic.mk_prodT (T, mk_tupleT Ts);

(* builds the expression (v1,v2,..,vn) *)
fun mk_tuple [] = HOLogic.unit
  | mk_tuple (t::[]) = t
  | mk_tuple (t::ts) = HOLogic.mk_prod (t, mk_tuple ts);

(* builds the expression (%(v1,v2,..,vn). rhs) *)
fun lambda_tuple [] rhs = Term.lambda (Free("unit", HOLogic.unitT)) rhs
  | lambda_tuple (v::[]) rhs = Term.lambda v rhs
  | lambda_tuple (v::vs) rhs =
      HOLogic.mk_split (Term.lambda v (lambda_tuple vs rhs));


(*** Lifted cpo type ***)

fun mk_upT T = Type(@{type_name "u"}, [T]);

fun up_const T = Const(@{const_name up}, T ->> mk_upT T);

fun mk_up t = up_const (Term.fastype_of t) ` t;


(*** Strict product type ***)

val oneT = @{typ "one"};

fun mk_sprodT (T, U) = Type(@{type_name "**"}, [T, U]);

fun spair_const (T, U) =
  Const(@{const_name spair}, T ->> U ->> mk_sprodT (T, U));

(* builds the expression (:t, u:) *)
fun mk_spair (t, u) =
  spair_const (Term.fastype_of t, Term.fastype_of u) ` t ` u;

(* builds the expression (:t1,t2,..,tn:) *)
fun mk_stuple [] = @{term "ONE"}
  | mk_stuple (t::[]) = t
  | mk_stuple (t::ts) = mk_spair (t, mk_stuple ts);


(*** Strict sum type ***)

fun mk_ssumT (T, U) = Type(@{type_name "++"}, [T, U]);

fun dest_ssumT (Type(@{type_name "++"}, [T, U])) = (T, U)
  | dest_ssumT T = raise TYPE ("dest_ssumT", [T], []);

fun sinl_const (T, U) = Const(@{const_name sinl}, T ->> mk_ssumT (T, U));
fun sinr_const (T, U) = Const(@{const_name sinr}, U ->> mk_ssumT (T, U));

(* builds the list [sinl(t1), sinl(sinr(t2)), ... sinr(...sinr(tn))] *)
fun mk_sinjects ts =
  let
    val Ts = map Term.fastype_of ts;
    fun combine (t, T) (us, U) =
      let
        val v = sinl_const (T, U) ` t;
        val vs = map (fn u => sinr_const (T, U) ` u) us;
      in
        (v::vs, mk_ssumT (T, U))
      end
    fun inj [] = error "mk_sinjects: empty list"
      | inj ((t, T)::[]) = ([t], T)
      | inj ((t, T)::ts) = combine (t, T) (inj ts);
  in
    fst (inj (ts ~~ Ts))
  end;


(*** miscellaneous constructions ***)

val trT = @{typ "tr"};

val deflT = @{typ "udom alg_defl"};

fun mapT T =
  let
    fun argTs (Type (_, Ts)) = Ts | argTs _ = [];
    fun auto T = T ->> T;
  in
    Library.foldr mk_cfunT (map auto (argTs T), auto T)
  end;

val mk_equals = Logic.mk_equals;
val mk_eq = HOLogic.mk_eq;
val mk_trp = HOLogic.mk_Trueprop;
val mk_fst = HOLogic.mk_fst;
val mk_snd = HOLogic.mk_snd;

fun mk_cont t =
  let val T = Term.fastype_of t
  in Const(@{const_name cont}, T --> HOLogic.boolT) $ t end;

fun mk_fix t =
  let val (T, _) = dest_cfunT (Term.fastype_of t)
  in mk_capply (Const(@{const_name fix}, (T ->> T) ->> T), t) end;

fun ID_const T = Const (@{const_name ID}, T ->> T);

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

(*** miscellaneous ***)

fun declare_consts
    (decls : (binding * typ * mixfix) list)
    (thy : theory)
    : term list * theory =
  let
    fun con (b, T, mx) = Const (Sign.full_name thy b, T);
    val thy = Cont_Consts.add_consts decls thy;
  in
    (map con decls, thy)
  end;

fun define_consts
    (specs : (binding * term * mixfix) list)
    (thy : theory)
    : (term list * thm list) * theory =
  let
    fun mk_decl (b, t, mx) = (b, Term.fastype_of t, mx);
    val decls = map mk_decl specs;
    val thy = Cont_Consts.add_consts decls thy;
    fun mk_const (b, T, mx) = Const (Sign.full_name thy b, T);
    val consts = map mk_const decls;
    fun mk_def c (b, t, mx) =
      (Binding.suffix_name "_def" b, Logic.mk_equals (c, t));
    val defs = map2 mk_def consts specs;
    val (def_thms, thy) =
      PureThy.add_defs false (map Thm.no_attributes defs) thy;
  in
    ((consts, def_thms), thy)
  end;


(************** generating beta reduction rules from definitions **************)

local
  fun arglist (Const _ $ Abs (s, T, t)) =
      let
        val arg = Free (s, T);
        val (args, body) = arglist (subst_bound (arg, t));
      in (arg :: args, body) end
    | arglist t = ([], t);
in
  fun beta_of_def thy def_thm =
      let
        val (con, lam) = Logic.dest_equals (concl_of def_thm);
        val (args, rhs) = arglist lam;
        val lhs = Library.foldl mk_capply (con, args);
        val goal = mk_equals (lhs, rhs);
        val cs = ContProc.cont_thms lam;
        val betas = map (fn c => mk_meta_eq (c RS @{thm beta_cfun})) cs;
        val tac =
            rewrite_goals_tac (def_thm::betas)
            THEN rtac reflexive_thm 1;
      in
        Goal.prove_global thy [] [] goal (K tac)
      end;
end;

(******************************* main function ********************************)

fun add_domain_constructors
    (dname : string)
    (lhsT : typ,
     cons : (binding * (bool * binding option * typ) list * mixfix) list)
    (rep_const : term, abs_const : term)
    (rep_iso_thm : thm, abs_iso_thm : thm)
    (thy : theory) =
  let
    (* TODO: re-enable this *)
    (* val thy = Sign.add_path dname thy; *)

    (* define constructor functions *)
    val ((con_consts, con_def_thms), thy) =
      let
        fun prep_con (bind, args, mx) =
          (bind, args ~~ Datatype_Prop.make_tnames (map #3 args), mx);
        fun var_of ((lazy, sel, T), name) = Free (name, T);
        fun is_lazy ((lazy, sel, T), name) = lazy;
        val cons' = map prep_con cons;
        fun one_arg arg = (if is_lazy arg then mk_up else I) (var_of arg);
        fun one_con (bind, args, mx) = mk_stuple (map one_arg args);
        fun mk_abs t = abs_const ` t;
        val rhss = map mk_abs (mk_sinjects (map one_con cons'));
        fun mk_def (bind, args, mx) rhs =
          (bind, big_lambdas (map var_of args) rhs, mx);
      in
        define_consts (map2 mk_def cons' rhss) thy
      end;

    val con_beta_thms = map (beta_of_def thy) con_def_thms;

    (* TODO: re-enable this *)
    (* val thy = Sign.parent_path thy; *)

    val result =
      { con_consts = con_consts,
        con_defs = con_def_thms };
  in
    (result, thy)
  end;

end;
