(*  Title:      HOLCF/Tools/holcf_library.ML
    Author:     Brian Huffman

Functions for constructing HOLCF types and terms.
*)

structure HOLCF_Library =
struct

infixr 6 ->>;
infix -->>;
infix 9 `;

(*** Operations from Isabelle/HOL ***)

val boolT = HOLogic.boolT;
val natT = HOLogic.natT;

val mk_equals = Logic.mk_equals;
val mk_eq = HOLogic.mk_eq;
val mk_trp = HOLogic.mk_Trueprop;
val mk_fst = HOLogic.mk_fst;
val mk_snd = HOLogic.mk_snd;
val mk_not = HOLogic.mk_not;
val mk_conj = HOLogic.mk_conj;
val mk_disj = HOLogic.mk_disj;

fun mk_ex (x, t) = HOLogic.exists_const (fastype_of x) $ Term.lambda x t;


(*** Basic HOLCF concepts ***)

fun mk_bottom T = Const (@{const_name UU}, T);

fun below_const T = Const (@{const_name below}, [T, T] ---> boolT);
fun mk_below (t, u) = below_const (fastype_of t) $ t $ u;

fun mk_undef t = mk_eq (t, mk_bottom (fastype_of t));

fun mk_defined t = mk_not (mk_undef t);

fun mk_compact t =
  Const (@{const_name compact}, fastype_of t --> boolT) $ t;

fun mk_cont t =
  Const (@{const_name cont}, fastype_of t --> boolT) $ t;

fun mk_chain t =
  Const (@{const_name chain}, Term.fastype_of t --> boolT) $ t;

fun mk_lub t =
  let
    val T = Term.range_type (Term.fastype_of t);
    val lub_const = Const (@{const_name lub}, (T --> boolT) --> T);
    val UNIV_const = @{term "UNIV :: nat set"};
    val image_type = (natT --> T) --> (natT --> boolT) --> T --> boolT;
    val image_const = Const (@{const_name image}, image_type);
  in
    lub_const $ (image_const $ t $ UNIV_const)
  end;


(*** Continuous function space ***)

fun mk_cfunT (T, U) = Type(@{type_name cfun}, [T, U]);

val (op ->>) = mk_cfunT;
val (op -->>) = Library.foldr mk_cfunT;

fun dest_cfunT (Type(@{type_name cfun}, [T, U])) = (T, U)
  | dest_cfunT T = raise TYPE ("dest_cfunT", [T], []);

fun capply_const (S, T) =
  Const(@{const_name Rep_CFun}, (S ->> T) --> (S --> T));

fun cabs_const (S, T) =
  Const(@{const_name Abs_CFun}, (S --> T) --> (S ->> T));

fun mk_cabs t =
  let val T = fastype_of t
  in cabs_const (Term.domain_type T, Term.range_type T) $ t end

(* builds the expression (% v1 v2 .. vn. rhs) *)
fun lambdas [] rhs = rhs
  | lambdas (v::vs) rhs = Term.lambda v (lambdas vs rhs);

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs =
  cabs_const (fastype_of v, fastype_of rhs) $ Term.lambda v rhs;

(* builds the expression (LAM v1 v2 .. vn. rhs) *)
fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs);

fun mk_capply (t, u) =
  let val (S, T) =
    case fastype_of t of
        Type(@{type_name cfun}, [S, T]) => (S, T)
      | _ => raise TERM ("mk_capply " ^ ML_Syntax.print_list ML_Syntax.print_term [t, u], [t, u]);
  in capply_const (S, T) $ t $ u end;

val (op `) = mk_capply;

val list_ccomb : term * term list -> term = Library.foldl mk_capply;

fun mk_ID T = Const (@{const_name ID}, T ->> T);

fun cfcomp_const (T, U, V) =
  Const (@{const_name cfcomp}, (U ->> V) ->> (T ->> U) ->> (T ->> V));

fun mk_cfcomp (f, g) =
  let
    val (U, V) = dest_cfunT (fastype_of f);
    val (T, U') = dest_cfunT (fastype_of g);
  in
    if U = U'
    then mk_capply (mk_capply (cfcomp_const (T, U, V), f), g)
    else raise TYPE ("mk_cfcomp", [U, U'], [f, g])
  end;

fun strictify_const T = Const (@{const_name strictify}, T ->> T);
fun mk_strictify t = strictify_const (fastype_of t) ` t;

fun mk_strict t =
  let val (T, U) = dest_cfunT (fastype_of t);
  in mk_eq (t ` mk_bottom T, mk_bottom U) end;


(*** Product type ***)

val mk_prodT = HOLogic.mk_prodT

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT [T] = T
  | mk_tupleT (T :: Ts) = mk_prodT (T, mk_tupleT Ts);

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

fun mk_up t = up_const (fastype_of t) ` t;

fun fup_const (T, U) =
  Const(@{const_name fup}, (T ->> U) ->> mk_upT T ->> U);

fun mk_fup t = fup_const (dest_cfunT (fastype_of t)) ` t;

fun from_up T = fup_const (T, T) ` mk_ID T;


(*** Lifted unit type ***)

val oneT = @{typ "one"};

fun one_when_const T = Const (@{const_name one_when}, T ->> oneT ->> T);
fun mk_one_when t = one_when_const (fastype_of t) ` t;


(*** Strict product type ***)

fun mk_sprodT (T, U) = Type(@{type_name sprod}, [T, U]);

fun dest_sprodT (Type(@{type_name sprod}, [T, U])) = (T, U)
  | dest_sprodT T = raise TYPE ("dest_sprodT", [T], []);

fun spair_const (T, U) =
  Const(@{const_name spair}, T ->> U ->> mk_sprodT (T, U));

(* builds the expression (:t, u:) *)
fun mk_spair (t, u) =
  spair_const (fastype_of t, fastype_of u) ` t ` u;

(* builds the expression (:t1,t2,..,tn:) *)
fun mk_stuple [] = @{term "ONE"}
  | mk_stuple (t::[]) = t
  | mk_stuple (t::ts) = mk_spair (t, mk_stuple ts);

fun sfst_const (T, U) =
  Const(@{const_name sfst}, mk_sprodT (T, U) ->> T);

fun ssnd_const (T, U) =
  Const(@{const_name ssnd}, mk_sprodT (T, U) ->> U);

fun ssplit_const (T, U, V) =
  Const (@{const_name ssplit}, (T ->> U ->> V) ->> mk_sprodT (T, U) ->> V);

fun mk_ssplit t =
  let val (T, (U, V)) = apsnd dest_cfunT (dest_cfunT (fastype_of t));
  in ssplit_const (T, U, V) ` t end;


(*** Strict sum type ***)

fun mk_ssumT (T, U) = Type(@{type_name ssum}, [T, U]);

fun dest_ssumT (Type(@{type_name ssum}, [T, U])) = (T, U)
  | dest_ssumT T = raise TYPE ("dest_ssumT", [T], []);

fun sinl_const (T, U) = Const(@{const_name sinl}, T ->> mk_ssumT (T, U));
fun sinr_const (T, U) = Const(@{const_name sinr}, U ->> mk_ssumT (T, U));

(* builds the list [sinl(t1), sinl(sinr(t2)), ... sinr(...sinr(tn))] *)
fun mk_sinjects ts =
  let
    val Ts = map fastype_of ts;
    fun combine (t, T) (us, U) =
      let
        val v = sinl_const (T, U) ` t;
        val vs = map (fn u => sinr_const (T, U) ` u) us;
      in
        (v::vs, mk_ssumT (T, U))
      end
    fun inj [] = raise Fail "mk_sinjects: empty list"
      | inj ((t, T)::[]) = ([t], T)
      | inj ((t, T)::ts) = combine (t, T) (inj ts);
  in
    fst (inj (ts ~~ Ts))
  end;

fun sscase_const (T, U, V) =
  Const(@{const_name sscase},
    (T ->> V) ->> (U ->> V) ->> mk_ssumT (T, U) ->> V);

fun mk_sscase (t, u) =
  let val (T, V) = dest_cfunT (fastype_of t);
      val (U, V) = dest_cfunT (fastype_of u);
  in sscase_const (T, U, V) ` t ` u end;

fun from_sinl (T, U) =
  sscase_const (T, U, T) ` mk_ID T ` mk_bottom (U ->> T);

fun from_sinr (T, U) =
  sscase_const (T, U, U) ` mk_bottom (T ->> U) ` mk_ID U;


(*** pattern match monad type ***)

fun mk_matchT T = Type (@{type_name "maybe"}, [T]);

fun dest_matchT (Type(@{type_name "maybe"}, [T])) = T
  | dest_matchT T = raise TYPE ("dest_matchT", [T], []);

fun mk_fail T = Const (@{const_name "Fixrec.fail"}, mk_matchT T);

fun return_const T = Const (@{const_name "Fixrec.return"}, T ->> mk_matchT T);
fun mk_return t = return_const (fastype_of t) ` t;


(*** lifted boolean type ***)

val trT = @{typ "tr"};


(*** theory of fixed points ***)

fun mk_fix t =
  let val (T, _) = dest_cfunT (fastype_of t)
  in mk_capply (Const(@{const_name fix}, (T ->> T) ->> T), t) end;

fun iterate_const T =
  Const (@{const_name iterate}, natT --> (T ->> T) ->> (T ->> T));

fun mk_iterate (n, f) =
  let val (T, _) = dest_cfunT (Term.fastype_of f);
  in (iterate_const T $ n) ` f ` mk_bottom T end;

end;
