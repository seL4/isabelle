(*  Title:      HOL/Tools/SMT/z3_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to Z3 based on a relaxed version of SMT-LIB.
*)

signature Z3_INTERFACE =
sig
  type builtin_fun = string * typ -> term list -> (string * term list) option
  val add_builtin_funs: builtin_fun -> Context.generic -> Context.generic
  val interface: SMT_Solver.interface

  datatype sym = Sym of string * sym list
  type mk_builtins = {
    mk_builtin_typ: sym -> typ option,
    mk_builtin_num: theory -> int -> typ -> cterm option,
    mk_builtin_fun: theory -> sym -> cterm list -> cterm option }
  val add_mk_builtins: mk_builtins -> Context.generic -> Context.generic
  val mk_builtin_typ: Proof.context -> sym -> typ option
  val mk_builtin_num: Proof.context -> int -> typ -> cterm option
  val mk_builtin_fun: Proof.context -> sym -> cterm list -> cterm option

  val is_builtin_theory_term: Proof.context -> term -> bool
end

structure Z3_Interface: Z3_INTERFACE =
struct

structure U = SMT_Utils


(** Z3-specific builtins **)

type builtin_fun = string * typ -> term list -> (string * term list) option

fun fst_int_ord ((s1, _), (s2, _)) = int_ord (s1, s2)

structure Builtins = Generic_Data
(
  type T = (int * builtin_fun) list
  val empty = []
  val extend = I
  fun merge (bs1, bs2) = Ord_List.union fst_int_ord bs2 bs1
)

fun add_builtin_funs b =
  Builtins.map (Ord_List.insert fst_int_ord (serial (), b))

fun get_builtin_funs ctxt c ts =
  let
    fun chained [] = NONE
      | chained (b :: bs) = (case b c ts of SOME x => SOME x | _ => chained bs)
  in chained (map snd (Builtins.get (Context.Proof ctxt))) end

fun z3_builtin_fun builtin_fun ctxt c ts =
  (case builtin_fun ctxt c ts of
    SOME x => SOME x
  | _ => get_builtin_funs ctxt c ts)



(** interface **)

local
  val {translate, ...} = SMTLIB_Interface.interface
  val {prefixes, strict, header, builtins, serialize} = translate
  val {is_builtin_pred, ...}= the strict
  val {builtin_typ, builtin_num, builtin_fun, ...} = builtins

  fun is_int_div_mod @{const div (int)} = true
    | is_int_div_mod @{const mod (int)} = true
    | is_int_div_mod _ = false

  fun add_div_mod irules =
    if exists (Term.exists_subterm is_int_div_mod o Thm.prop_of o snd) irules
    then [(~1, @{thm div_by_z3div}), (~1, @{thm mod_by_z3mod})] @ irules
    else irules

  fun extra_norm' has_datatypes =
    SMTLIB_Interface.extra_norm has_datatypes o add_div_mod

  fun z3_builtin_fun' _ (@{const_name z3div}, _) ts = SOME ("div", ts)
    | z3_builtin_fun' _ (@{const_name z3mod}, _) ts = SOME ("mod", ts)
    | z3_builtin_fun' ctxt c ts = z3_builtin_fun builtin_fun ctxt c ts

  val as_propT = (fn @{typ bool} => @{typ prop} | T => T)
in

fun is_builtin_num ctxt (T, i) = is_some (builtin_num ctxt T i)

fun is_builtin_fun ctxt (c as (n, T)) ts =
  is_some (z3_builtin_fun' ctxt c ts) orelse 
  is_builtin_pred ctxt (n, Term.strip_type T ||> as_propT |> (op --->))

val interface = {
  extra_norm = extra_norm',
  translate = {
    prefixes = prefixes,
    strict = strict,
    header = header,
    builtins = {
      builtin_typ = builtin_typ,
      builtin_num = builtin_num,
      builtin_fun = z3_builtin_fun',
      has_datatypes = true},
    serialize = serialize}}

end



(** constructors **)

datatype sym = Sym of string * sym list


(* additional constructors *)

type mk_builtins = {
  mk_builtin_typ: sym -> typ option,
  mk_builtin_num: theory -> int -> typ -> cterm option,
  mk_builtin_fun: theory -> sym -> cterm list -> cterm option }

fun chained _ [] = NONE
  | chained f (b :: bs) = (case f b of SOME y => SOME y | NONE => chained f bs)

fun chained_mk_builtin_typ bs sym =
  chained (fn {mk_builtin_typ=mk, ...} : mk_builtins => mk sym) bs

fun chained_mk_builtin_num ctxt bs i T =
  let val thy = ProofContext.theory_of ctxt
  in chained (fn {mk_builtin_num=mk, ...} : mk_builtins => mk thy i T) bs end

fun chained_mk_builtin_fun ctxt bs s cts =
  let val thy = ProofContext.theory_of ctxt
  in chained (fn {mk_builtin_fun=mk, ...} : mk_builtins => mk thy s cts) bs end

structure Mk_Builtins = Generic_Data
(
  type T = (int * mk_builtins) list
  val empty = []
  val extend = I
  fun merge (bs1, bs2) = Ord_List.union fst_int_ord bs2 bs1
)

fun add_mk_builtins mk =
  Mk_Builtins.map (Ord_List.insert fst_int_ord (serial (), mk))

fun get_mk_builtins ctxt = map snd (Mk_Builtins.get (Context.Proof ctxt))


(* basic and additional constructors *)

fun mk_builtin_typ _ (Sym ("bool", _)) = SOME @{typ bool}
  | mk_builtin_typ _ (Sym ("Int", _)) = SOME @{typ int}
  | mk_builtin_typ _ (Sym ("int", _)) = SOME @{typ int}  (*FIXME: delete*)
  | mk_builtin_typ ctxt sym = chained_mk_builtin_typ (get_mk_builtins ctxt) sym

fun mk_builtin_num _ i @{typ int} = SOME (Numeral.mk_cnumber @{ctyp int} i)
  | mk_builtin_num ctxt i T =
      chained_mk_builtin_num ctxt (get_mk_builtins ctxt) i T

val mk_true = Thm.cterm_of @{theory} (@{const Not} $ @{const False})
val mk_false = Thm.cterm_of @{theory} @{const False}
val mk_not = Thm.capply (Thm.cterm_of @{theory} @{const Not})
val mk_implies = Thm.mk_binop (Thm.cterm_of @{theory} @{const HOL.implies})
val mk_iff = Thm.mk_binop (Thm.cterm_of @{theory} @{const HOL.eq (bool)})
val conj = Thm.cterm_of @{theory} @{const HOL.conj}
val disj = Thm.cterm_of @{theory} @{const HOL.disj}

fun mk_nary _ cu [] = cu
  | mk_nary ct _ cts = uncurry (fold_rev (Thm.mk_binop ct)) (split_last cts)

val eq = U.mk_const_pat @{theory} @{const_name HOL.eq} U.destT1
fun mk_eq ct cu = Thm.mk_binop (U.instT' ct eq) ct cu

val if_term = U.mk_const_pat @{theory} @{const_name If} (U.destT1 o U.destT2)
fun mk_if cc ct cu = Thm.mk_binop (Thm.capply (U.instT' ct if_term) cc) ct cu

val nil_term = U.mk_const_pat @{theory} @{const_name Nil} U.destT1
val cons_term = U.mk_const_pat @{theory} @{const_name Cons} U.destT1
fun mk_list cT cts =
  fold_rev (Thm.mk_binop (U.instT cT cons_term)) cts (U.instT cT nil_term)

val distinct = U.mk_const_pat @{theory} @{const_name distinct}
  (U.destT1 o U.destT1)
fun mk_distinct [] = mk_true
  | mk_distinct (cts as (ct :: _)) =
      Thm.capply (U.instT' ct distinct) (mk_list (Thm.ctyp_of_term ct) cts)

val access = U.mk_const_pat @{theory} @{const_name fun_app}
  (Thm.dest_ctyp o U.destT1)
fun mk_access array index =
  let val cTs = Thm.dest_ctyp (Thm.ctyp_of_term array)
  in Thm.mk_binop (U.instTs cTs access) array index end

val update = U.mk_const_pat @{theory} @{const_name fun_upd}
  (Thm.dest_ctyp o U.destT1)
fun mk_update array index value =
  let val cTs = Thm.dest_ctyp (Thm.ctyp_of_term array)
  in Thm.capply (Thm.mk_binop (U.instTs cTs update) array index) value end

val mk_uminus = Thm.capply (Thm.cterm_of @{theory} @{const uminus (int)})
val mk_add = Thm.mk_binop (Thm.cterm_of @{theory} @{const plus (int)})
val mk_sub = Thm.mk_binop (Thm.cterm_of @{theory} @{const minus (int)})
val mk_mul = Thm.mk_binop (Thm.cterm_of @{theory} @{const times (int)})
val mk_div = Thm.mk_binop (Thm.cterm_of @{theory} @{const z3div})
val mk_mod = Thm.mk_binop (Thm.cterm_of @{theory} @{const z3mod})
val mk_lt = Thm.mk_binop (Thm.cterm_of @{theory} @{const less (int)})
val mk_le = Thm.mk_binop (Thm.cterm_of @{theory} @{const less_eq (int)})

fun mk_builtin_fun ctxt sym cts =
  (case (sym, cts) of
    (Sym ("true", _), []) => SOME mk_true
  | (Sym ("false", _), []) => SOME mk_false
  | (Sym ("not", _), [ct]) => SOME (mk_not ct)
  | (Sym ("and", _), _) => SOME (mk_nary conj mk_true cts)
  | (Sym ("or", _), _) => SOME (mk_nary disj mk_false cts)
  | (Sym ("implies", _), [ct, cu]) => SOME (mk_implies ct cu)
  | (Sym ("iff", _), [ct, cu]) => SOME (mk_iff ct cu)
  | (Sym ("~", _), [ct, cu]) => SOME (mk_iff ct cu)
  | (Sym ("xor", _), [ct, cu]) => SOME (mk_not (mk_iff ct cu))
  | (Sym ("ite", _), [ct1, ct2, ct3]) => SOME (mk_if ct1 ct2 ct3)
  | (Sym ("=", _), [ct, cu]) => SOME (mk_eq ct cu)
  | (Sym ("distinct", _), _) => SOME (mk_distinct cts)
  | (Sym ("select", _), [ca, ck]) => SOME (mk_access ca ck)
  | (Sym ("store", _), [ca, ck, cv]) => SOME (mk_update ca ck cv)
  | _ =>
    (case (sym, try (#T o Thm.rep_cterm o hd) cts, cts) of
      (Sym ("+", _), SOME @{typ int}, [ct, cu]) => SOME (mk_add ct cu)
    | (Sym ("-", _), SOME @{typ int}, [ct]) => SOME (mk_uminus ct)
    | (Sym ("-", _), SOME @{typ int}, [ct, cu]) => SOME (mk_sub ct cu)
    | (Sym ("*", _), SOME @{typ int}, [ct, cu]) => SOME (mk_mul ct cu)
    | (Sym ("div", _), SOME @{typ int}, [ct, cu]) => SOME (mk_div ct cu)
    | (Sym ("mod", _), SOME @{typ int}, [ct, cu]) => SOME (mk_mod ct cu)
    | (Sym ("<", _), SOME @{typ int}, [ct, cu]) => SOME (mk_lt ct cu)
    | (Sym ("<=", _), SOME @{typ int}, [ct, cu]) => SOME (mk_le ct cu)
    | (Sym (">", _), SOME @{typ int}, [ct, cu]) => SOME (mk_lt cu ct)
    | (Sym (">=", _), SOME @{typ int}, [ct, cu]) => SOME (mk_le cu ct)
    | _ => chained_mk_builtin_fun ctxt (get_mk_builtins ctxt) sym cts))



(** abstraction **)

fun is_builtin_theory_term ctxt t =
  (case try HOLogic.dest_number t of
    SOME n => is_builtin_num ctxt n
  | NONE =>
      (case Term.strip_comb t of
        (Const c, ts) => is_builtin_fun ctxt c ts
      | _ => false))

end
