(*  Title:      HOL/HOLCF/Tools/holcf_library.ML
    Author:     Brian Huffman

Functions for constructing HOLCF types and terms.
*)

structure HOLCF_Library =
struct

infixr 6 ->>
infixr -->>
infix 9 `

(*** Operations from Isabelle/HOL ***)

val mk_equals = Logic.mk_equals
val mk_eq = HOLogic.mk_eq
val mk_trp = HOLogic.mk_Trueprop
val mk_fst = HOLogic.mk_fst
val mk_snd = HOLogic.mk_snd
val mk_not = HOLogic.mk_not
val mk_conj = HOLogic.mk_conj
val mk_disj = HOLogic.mk_disj
val mk_imp = HOLogic.mk_imp

fun mk_ex (x, t) = HOLogic.exists_const (fastype_of x) $ Term.lambda x t
fun mk_all (x, t) = HOLogic.all_const (fastype_of x) $ Term.lambda x t


(*** Basic HOLCF concepts ***)

fun mk_bottom T = \<^Const>\<open>bottom T\<close>

fun below_const T = \<^Const>\<open>below T\<close>
fun mk_below (t, u) = below_const (fastype_of t) $ t $ u

fun mk_undef t = mk_eq (t, mk_bottom (fastype_of t))

fun mk_defined t = mk_not (mk_undef t)

fun mk_adm t =
  let val T = Term.domain_type (fastype_of t)
  in \<^Const>\<open>adm T for t\<close> end

fun mk_compact t =
  let val T = fastype_of t
  in \<^Const>\<open>compact T for t\<close> end

fun mk_cont t =
  let val \<^Type>\<open>fun A B\<close> = fastype_of t
  in \<^Const>\<open>cont A B for t\<close> end

fun mk_chain t =
  let val T = Term.range_type (Term.fastype_of t)
  in \<^Const>\<open>chain T for t\<close> end

fun mk_lub t =
  let
    val T = Term.range_type (Term.fastype_of t)
    val UNIV_const = \<^term>\<open>UNIV :: nat set\<close>
  in \<^Const>\<open>lub T for \<open>\<^Const>\<open>image \<open>\<^Type>\<open>nat\<close>\<close> T for t UNIV_const\<close>\<close>\<close> end


(*** Continuous function space ***)

fun mk_cfunT (T, U) = \<^Type>\<open>cfun T U\<close>

val (op ->>) = mk_cfunT
val (op -->>) = Library.foldr mk_cfunT

fun dest_cfunT \<^Type>\<open>cfun T U\<close> = (T, U)
  | dest_cfunT T = raise TYPE ("dest_cfunT", [T], [])

fun capply_const (S, T) = \<^Const>\<open>Rep_cfun S T\<close>
fun cabs_const (S, T) = \<^Const>\<open>Abs_cfun S T\<close>

fun mk_cabs t =
  let val T = fastype_of t
  in cabs_const (Term.dest_funT T) $ t end

(* builds the expression (% v1 v2 .. vn. rhs) *)
fun lambdas [] rhs = rhs
  | lambdas (v::vs) rhs = Term.lambda v (lambdas vs rhs)

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs =
  cabs_const (fastype_of v, fastype_of rhs) $ Term.lambda v rhs

(* builds the expression (LAM v1 v2 .. vn. rhs) *)
fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs)

fun mk_capply (t, u) =
  let val (S, T) =
    case fastype_of t of
        \<^Type>\<open>cfun S T\<close> => (S, T)
      | _ => raise TERM ("mk_capply " ^ ML_Syntax.print_list ML_Syntax.print_term [t, u], [t, u])
  in capply_const (S, T) $ t $ u end

val (op `) = mk_capply

val list_ccomb : term * term list -> term = Library.foldl mk_capply

fun mk_ID T = \<^Const>\<open>ID T\<close>

fun mk_cfcomp (f, g) =
  let
    val (U, V) = dest_cfunT (fastype_of f)
    val (T, U') = dest_cfunT (fastype_of g)
  in
    if U = U'
    then mk_capply (mk_capply (\<^Const>\<open>cfcomp U V T\<close>, f), g)
    else raise TYPE ("mk_cfcomp", [U, U'], [f, g])
  end

fun mk_strictify t =
  let val (T, U) = dest_cfunT (fastype_of t)
  in \<^Const>\<open>strictify T U\<close> ` t end;

fun mk_strict t =
  let val (T, U) = dest_cfunT (fastype_of t)
  in mk_eq (t ` mk_bottom T, mk_bottom U) end


(*** Product type ***)

val mk_prodT = HOLogic.mk_prodT

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT [T] = T
  | mk_tupleT (T :: Ts) = mk_prodT (T, mk_tupleT Ts)

(* builds the expression (v1,v2,..,vn) *)
fun mk_tuple [] = HOLogic.unit
  | mk_tuple (t::[]) = t
  | mk_tuple (t::ts) = HOLogic.mk_prod (t, mk_tuple ts)

(* builds the expression (%(v1,v2,..,vn). rhs) *)
fun lambda_tuple [] rhs = Term.lambda (Free("unit", HOLogic.unitT)) rhs
  | lambda_tuple (v::[]) rhs = Term.lambda v rhs
  | lambda_tuple (v::vs) rhs =
      HOLogic.mk_case_prod (Term.lambda v (lambda_tuple vs rhs))


(*** Lifted cpo type ***)

fun mk_upT T = \<^Type>\<open>u T\<close>

fun dest_upT \<^Type>\<open>u T\<close> = T
  | dest_upT T = raise TYPE ("dest_upT", [T], [])

fun up_const T = \<^Const>\<open>up T\<close>

fun mk_up t = up_const (fastype_of t) ` t

fun fup_const (T, U) = \<^Const>\<open>fup T U\<close>

fun mk_fup t = fup_const (dest_cfunT (fastype_of t)) ` t

fun from_up T = fup_const (T, T) ` mk_ID T


(*** Lifted unit type ***)

val oneT = \<^typ>\<open>one\<close>

fun one_case_const T = \<^Const>\<open>one_case T\<close>
fun mk_one_case t = one_case_const (fastype_of t) ` t


(*** Strict product type ***)

fun mk_sprodT (T, U) = \<^Type>\<open>sprod T U\<close>

fun dest_sprodT \<^Type>\<open>sprod T U\<close> = (T, U)
  | dest_sprodT T = raise TYPE ("dest_sprodT", [T], [])

fun spair_const (T, U) = \<^Const>\<open>spair T U\<close>

(* builds the expression (:t, u:) *)
fun mk_spair (t, u) =
  spair_const (fastype_of t, fastype_of u) ` t ` u

(* builds the expression (:t1,t2,..,tn:) *)
fun mk_stuple [] = \<^term>\<open>ONE\<close>
  | mk_stuple (t::[]) = t
  | mk_stuple (t::ts) = mk_spair (t, mk_stuple ts)

fun sfst_const (T, U) = \<^Const>\<open>sfst T U\<close>

fun ssnd_const (T, U) = \<^Const>\<open>ssnd T U\<close>

fun ssplit_const (T, U, V) = \<^Const>\<open>ssplit T U V\<close>

fun mk_ssplit t =
  let val (T, (U, V)) = apsnd dest_cfunT (dest_cfunT (fastype_of t))
  in ssplit_const (T, U, V) ` t end


(*** Strict sum type ***)

fun mk_ssumT (T, U) = \<^Type>\<open>ssum T U\<close>

fun dest_ssumT \<^Type>\<open>ssum T U\<close> = (T, U)
  | dest_ssumT T = raise TYPE ("dest_ssumT", [T], [])

fun sinl_const (T, U) = \<^Const>\<open>sinl T U\<close>
fun sinr_const (T, U) = \<^Const>\<open>sinr U T\<close>

(* builds the list [sinl(t1), sinl(sinr(t2)), ... sinr(...sinr(tn))] *)
fun mk_sinjects ts =
  let
    val Ts = map fastype_of ts
    fun combine (t, T) (us, U) =
      let
        val v = sinl_const (T, U) ` t
        val vs = map (fn u => sinr_const (T, U) ` u) us
      in
        (v::vs, mk_ssumT (T, U))
      end
    fun inj [] = raise Fail "mk_sinjects: empty list"
      | inj ((t, T)::[]) = ([t], T)
      | inj ((t, T)::ts) = combine (t, T) (inj ts)
  in
    fst (inj (ts ~~ Ts))
  end

fun sscase_const (T, U, V) = \<^Const>\<open>sscase T V U\<close>

fun mk_sscase (t, u) =
  let val (T, _) = dest_cfunT (fastype_of t)
      val (U, V) = dest_cfunT (fastype_of u)
  in sscase_const (T, U, V) ` t ` u end

fun from_sinl (T, U) =
  sscase_const (T, U, T) ` mk_ID T ` mk_bottom (U ->> T)

fun from_sinr (T, U) =
  sscase_const (T, U, U) ` mk_bottom (T ->> U) ` mk_ID U


(*** pattern match monad type ***)

fun mk_matchT T = \<^Type>\<open>match T\<close>

fun dest_matchT \<^Type>\<open>match T\<close> = T
  | dest_matchT T = raise TYPE ("dest_matchT", [T], [])

fun mk_fail T = \<^Const>\<open>Fixrec.fail T\<close>

fun succeed_const T = \<^Const>\<open>Fixrec.succeed T\<close>
fun mk_succeed t = succeed_const (fastype_of t) ` t


(*** lifted boolean type ***)

val trT = \<^typ>\<open>tr\<close>


(*** theory of fixed points ***)

fun mk_fix t =
  let val (T, _) = dest_cfunT (fastype_of t)
  in mk_capply (\<^Const>\<open>fix T\<close>, t) end

fun iterate_const T = \<^Const>\<open>iterate T\<close>

fun mk_iterate (n, f) =
  let val (T, _) = dest_cfunT (Term.fastype_of f)
  in (iterate_const T $ n) ` f ` mk_bottom T end

end
