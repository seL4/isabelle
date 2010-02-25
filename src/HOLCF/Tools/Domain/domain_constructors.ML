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
           con_defs : thm list,
           sel_rews : thm list }
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
infix -->>; val (op -->>) = Library.foldr mk_cfunT;

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

val list_ccomb : term * term list -> term = Library.foldl mk_capply;

fun mk_ID T = Const (@{const_name ID}, T ->> T);

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

fun mk_bottom T = Const (@{const_name UU}, T);


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

fun dest_upT (Type(@{type_name "u"}, [T])) = T
  | dest_upT T = raise TYPE ("dest_upT", [T], []);

fun up_const T = Const(@{const_name up}, T ->> mk_upT T);

fun mk_up t = up_const (Term.fastype_of t) ` t;

fun fup_const (T, U) =
  Const(@{const_name fup}, (T ->> U) ->> mk_upT T ->> U);

fun from_up T = fup_const (T, T) ` mk_ID T;


(*** Strict product type ***)

val oneT = @{typ "one"};

fun mk_sprodT (T, U) = Type(@{type_name "**"}, [T, U]);

fun dest_sprodT (Type(@{type_name "**"}, [T, U])) = (T, U)
  | dest_sprodT T = raise TYPE ("dest_sprodT", [T], []);

fun spair_const (T, U) =
  Const(@{const_name spair}, T ->> U ->> mk_sprodT (T, U));

(* builds the expression (:t, u:) *)
fun mk_spair (t, u) =
  spair_const (Term.fastype_of t, Term.fastype_of u) ` t ` u;

(* builds the expression (:t1,t2,..,tn:) *)
fun mk_stuple [] = @{term "ONE"}
  | mk_stuple (t::[]) = t
  | mk_stuple (t::ts) = mk_spair (t, mk_stuple ts);

fun sfst_const (T, U) =
  Const(@{const_name sfst}, mk_sprodT (T, U) ->> T);

fun ssnd_const (T, U) =
  Const(@{const_name ssnd}, mk_sprodT (T, U) ->> U);


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

fun sscase_const (T, U, V) =
  Const(@{const_name sscase},
    (T ->> V) ->> (U ->> V) ->> mk_ssumT (T, U) ->> V);

fun from_sinl (T, U) =
  sscase_const (T, U, T) ` mk_ID T ` mk_bottom (U ->> T);

fun from_sinr (T, U) =
  sscase_const (T, U, U) ` mk_bottom (T ->> U) ` mk_ID U;


(*** miscellaneous constructions ***)

val trT = @{typ "tr"};

val deflT = @{typ "udom alg_defl"};

fun mapT T =
  let
    fun argTs (Type (_, Ts)) = Ts | argTs _ = [];
    fun auto T = T ->> T;
  in
    map auto (argTs T) -->> auto T
  end;

val mk_equals = Logic.mk_equals;
val mk_eq = HOLogic.mk_eq;
val mk_trp = HOLogic.mk_Trueprop;
val mk_fst = HOLogic.mk_fst;
val mk_snd = HOLogic.mk_snd;
val mk_not = HOLogic.mk_not;

fun mk_strict t =
  let val (T, U) = dest_cfunT (Term.fastype_of t);
  in mk_eq (t ` mk_bottom T, mk_bottom U) end;

fun mk_defined t = mk_not (mk_eq (t, mk_bottom (Term.fastype_of t)));

fun mk_cont t =
  let val T = Term.fastype_of t
  in Const(@{const_name cont}, T --> HOLogic.boolT) $ t end;

fun mk_fix t =
  let val (T, _) = dest_cfunT (Term.fastype_of t)
  in mk_capply (Const(@{const_name fix}, (T ->> T) ->> T), t) end;

fun mk_Rep_of T =
  Const (@{const_name Rep_of}, Term.itselfT T --> deflT) $ Logic.mk_type T;

fun coerce_const T = Const (@{const_name coerce}, T);

fun isodefl_const T =
  Const (@{const_name isodefl}, (T ->> T) --> deflT --> HOLogic.boolT);

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u));


(************************** miscellaneous functions ***************************)

(*
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
*)

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

fun define_const
    (spec : binding * term * mixfix)
    (thy : theory)
    : (term * thm) * theory =
  let
    val ((consts, def_thms), thy) = define_consts [spec] thy;
  in
    ((hd consts, hd def_thms), thy)
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
        val lhs = list_ccomb (con, args);
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

(******************************************************************************)
(************** definitions and theorems for selector functions ***************)
(******************************************************************************)

fun add_selectors
    (spec : (term * (bool * binding option * typ) list) list)
    (rep_const : term)
    (abs_inv : thm)
    (rep_strict : thm)
    (rep_strict_iff : thm)
    (con_betas : thm list)
    (thy : theory)
    : thm list * theory =
  let

    (* define selector functions *)
    val ((sel_consts, sel_defs), thy) =
      let
        fun rangeT s = snd (dest_cfunT (Term.fastype_of s));
        fun mk_outl s = mk_cfcomp (from_sinl (dest_ssumT (rangeT s)), s);
        fun mk_outr s = mk_cfcomp (from_sinr (dest_ssumT (rangeT s)), s);
        fun mk_sfst s = mk_cfcomp (sfst_const (dest_sprodT (rangeT s)), s);
        fun mk_ssnd s = mk_cfcomp (ssnd_const (dest_sprodT (rangeT s)), s);
        fun mk_down s = mk_cfcomp (from_up (dest_upT (rangeT s)), s);

        fun sels_of_arg s (lazy, NONE,   T) = []
          | sels_of_arg s (lazy, SOME b, T) =
            [(b, if lazy then mk_down s else s, NoSyn)];
        fun sels_of_args s [] = []
          | sels_of_args s (v :: []) = sels_of_arg s v
          | sels_of_args s (v :: vs) =
            sels_of_arg (mk_sfst s) v @ sels_of_args (mk_ssnd s) vs;
        fun sels_of_cons s [] = []
          | sels_of_cons s ((con, args) :: []) = sels_of_args s args
          | sels_of_cons s ((con, args) :: cs) =
            sels_of_args (mk_outl s) args @ sels_of_cons (mk_outr s) cs;
        val sel_eqns : (binding * term * mixfix) list =
            sels_of_cons rep_const spec;
      in
        define_consts sel_eqns thy
      end

    (* replace bindings with terms in constructor spec *)
    val spec2 : (term * (bool * term option * typ) list) list =
      let
        fun prep_arg (lazy, NONE, T) sels = ((lazy, NONE, T), sels)
          | prep_arg (lazy, SOME _, T) sels =
            ((lazy, SOME (hd sels), T), tl sels);
        fun prep_con (con, args) sels =
            apfst (pair con) (fold_map prep_arg args sels);
      in
        fst (fold_map prep_con spec sel_consts)
      end;

    (* prove selector strictness rules *)
    val sel_stricts : thm list =
      let
        val rules = rep_strict :: sel_defs @ @{thms sel_strict_rules};
        val tac = simp_tac (HOL_basic_ss addsimps rules) 1;
        fun sel_strict sel =
          let
            val goal = mk_trp (mk_strict sel);
          in
            Goal.prove_global thy [] [] goal (K tac)
          end
      in
        map sel_strict sel_consts
      end

    (* prove selector application rules *)
    val sel_apps : thm list =
      let
        val rules = @{thms sel_app_rules};
        val simps = simp_thms @ [abs_inv] @ con_betas @ sel_defs @ rules;
        val tac = asm_simp_tac (HOL_basic_ss addsimps simps) 1;
        fun sel_apps_of (i, (con, args)) =
          let
            val Ts : typ list = map #3 args;
            val ns : string list = Datatype_Prop.make_tnames Ts;
            val vs : term list = map Free (ns ~~ Ts);
            val con_app : term = list_ccomb (con, vs);
            val vs' : (bool * term) list = map #1 args ~~ vs;
            fun one_same (n, sel, T) =
              let
                val xs = map snd (filter_out fst (nth_drop n vs'));
                val assms = map (mk_trp o mk_defined) xs;
                val concl = mk_trp (mk_eq (sel ` con_app, nth vs n));
                val goal = Logic.list_implies (assms, concl);
              in
                Goal.prove_global thy [] [] goal (K tac)
              end;
            fun one_diff (n, sel, T) =
              let
                val goal = mk_trp (mk_eq (sel ` con_app, mk_bottom T));
              in
                Goal.prove_global thy [] [] goal (K tac)
              end;
            fun one_con (j, (_, args')) : thm list =
              let
                fun prep (i, (lazy, NONE, T)) = NONE
                  | prep (i, (lazy, SOME sel, T)) = SOME (i, sel, T);
                val sels : (int * term * typ) list =
                  map_filter prep (map_index I args');
              in
                if i = j
                then map one_same sels
                else map one_diff sels
              end
          in
            flat (map_index one_con spec2)
          end
      in
        flat (map_index sel_apps_of spec2)
      end

  (* prove selector definedness rules *)
    val sel_defins : thm list =
      let
        val rules = @{thms sel_defined_iff_rules};
        val simps = rep_strict_iff :: sel_defs @ rules;
        val tac = simp_tac (HOL_basic_ss addsimps simps) 1;
        fun sel_defin sel =
          let
            val (T, U) = dest_cfunT (Term.fastype_of sel);
            val x = Free ("x", T);
            val lhs = mk_eq (sel ` x, mk_bottom U);
            val rhs = mk_eq (x, mk_bottom T);
            val goal = mk_trp (mk_eq (lhs, rhs));
          in
            Goal.prove_global thy [] [] goal (K tac)
          end
        fun one_arg (false, SOME sel, T) = SOME (sel_defin sel)
          | one_arg _                    = NONE;
      in
        case spec2 of
          [(con, args)] => map_filter one_arg args
        | _             => []
      end;

  in
    (sel_stricts @ sel_defins @ sel_apps, thy)
  end

(******************************************************************************)
(************* definitions and theorems for constructor functions *************)
(******************************************************************************)

fun add_domain_constructors
    (dname : string)
    (lhsT : typ,
     spec : (binding * (bool * binding option * typ) list * mixfix) list)
    (rep_const : term, abs_const : term)
    (rep_iso_thm : thm, abs_iso_thm : thm)
    (thy : theory) =
  let

    (* prove rep/abs strictness rules *)
    val iso_locale = @{thm iso.intro} OF [abs_iso_thm, rep_iso_thm];
    val rep_strict = iso_locale RS @{thm iso.rep_strict};
    val abs_strict = iso_locale RS @{thm iso.abs_strict};
    val rep_defined_iff = iso_locale RS @{thm iso.rep_defined_iff};
    val abs_defined_iff = iso_locale RS @{thm iso.abs_defined_iff};

    (* define constructor functions *)
    val ((con_consts, con_def_thms), thy) =
      let
        fun vars_of args =
          let
            val Ts = map (fn (lazy,sel,T) => T) args;
            val ns = Datatype_Prop.make_tnames Ts;
          in
            map Free (ns ~~ Ts)
          end;
        fun one_arg (lazy,_,_) var = if lazy then mk_up var else var;
        fun one_con (_,args,_) = mk_stuple (map2 one_arg args (vars_of args));
        fun mk_abs t = abs_const ` t;
        val rhss = map mk_abs (mk_sinjects (map one_con spec));
        fun mk_def (bind, args, mx) rhs =
          (bind, big_lambdas (vars_of args) rhs, mx);
      in
        define_consts (map2 mk_def spec rhss) thy
      end;

    (* prove beta reduction rules for constructors *)
    val con_beta_thms = map (beta_of_def thy) con_def_thms;

    (* TODO: enable this earlier *)
    val thy = Sign.add_path dname thy;

    (* replace bindings with terms in constructor spec *)
    val spec2 : (term * (bool * binding option * typ) list) list =
      map2 (fn con => fn (b, args, mx) => (con, args)) con_consts spec;

    (* define and prove theorems for selector functions *)
    val (sel_thms : thm list, thy : theory) =
      add_selectors spec2 rep_const
        abs_iso_thm rep_strict rep_defined_iff con_beta_thms thy;

    (* restore original signature path *)
    val thy = Sign.parent_path thy;

    val result =
      { con_consts = con_consts,
        con_defs = con_def_thms,
        sel_rews = sel_thms };
  in
    (result, thy)
  end;

end;
