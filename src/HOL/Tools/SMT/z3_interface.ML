(*  Title:      HOL/Tools/SMT/z3_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to Z3 based on a relaxed version of SMT-LIB.
*)

signature Z3_INTERFACE =
sig
  val smtlib_z3C: SMT_Utils.class
  val setup: theory -> theory

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

val smtlib_z3C = SMTLIB_Interface.smtlibC @ ["z3"]



(* interface *)

local
  fun translate_config ctxt =
    let
      val {prefixes, header, is_fol, serialize, ...} =
        SMTLIB_Interface.translate_config ctxt
    in
      {prefixes=prefixes, header=header, is_fol=is_fol, serialize=serialize,
        has_datatypes=true}
    end

  fun is_div_mod @{const div (int)} = true
    | is_div_mod @{const mod (int)} = true
    | is_div_mod _ = false

  val div_by_z3div = @{lemma
    "ALL k l. k div l = (
      if k = 0 | l = 0 then 0
      else if (0 < k & 0 < l) | (k < 0 & 0 < l) then z3div k l
      else z3div (-k) (-l))"
    by (simp add: SMT.z3div_def)}

  val mod_by_z3mod = @{lemma
    "ALL k l. k mod l = (
      if l = 0 then k
      else if k = 0 then 0
      else if (0 < k & 0 < l) | (k < 0 & 0 < l) then z3mod k l
      else - z3mod (-k) (-l))"
    by (simp add: z3mod_def)}

  val have_int_div_mod =
    exists (Term.exists_subterm is_div_mod o Thm.prop_of)

  fun add_div_mod _ (thms, extra_thms) =
    if have_int_div_mod thms orelse have_int_div_mod extra_thms then
      (thms, div_by_z3div :: mod_by_z3mod :: extra_thms)
    else (thms, extra_thms)

  val setup_builtins =
    SMT_Builtin.add_builtin_fun' smtlib_z3C (@{const times (int)}, "*") #>
    SMT_Builtin.add_builtin_fun' smtlib_z3C (@{const z3div}, "div") #>
    SMT_Builtin.add_builtin_fun' smtlib_z3C (@{const z3mod}, "mod")
in

val setup = Context.theory_map (
  setup_builtins #>
  SMT_Normalize.add_extra_norm (smtlib_z3C, add_div_mod) #>
  SMT_Translate.add_config (smtlib_z3C, translate_config))

end



(* constructors *)

datatype sym = Sym of string * sym list


(** additional constructors **)

type mk_builtins = {
  mk_builtin_typ: sym -> typ option,
  mk_builtin_num: theory -> int -> typ -> cterm option,
  mk_builtin_fun: theory -> sym -> cterm list -> cterm option }

fun chained _ [] = NONE
  | chained f (b :: bs) = (case f b of SOME y => SOME y | NONE => chained f bs)

fun chained_mk_builtin_typ bs sym =
  chained (fn {mk_builtin_typ=mk, ...} : mk_builtins => mk sym) bs

fun chained_mk_builtin_num ctxt bs i T =
  let val thy = Proof_Context.theory_of ctxt
  in chained (fn {mk_builtin_num=mk, ...} : mk_builtins => mk thy i T) bs end

fun chained_mk_builtin_fun ctxt bs s cts =
  let val thy = Proof_Context.theory_of ctxt
  in chained (fn {mk_builtin_fun=mk, ...} : mk_builtins => mk thy s cts) bs end

fun fst_int_ord ((i1, _), (i2, _)) = int_ord (i1, i2)

structure Mk_Builtins = Generic_Data
(
  type T = (int * mk_builtins) list
  val empty = []
  val extend = I
  fun merge data = Ord_List.merge fst_int_ord data
)

fun add_mk_builtins mk =
  Mk_Builtins.map (Ord_List.insert fst_int_ord (serial (), mk))

fun get_mk_builtins ctxt = map snd (Mk_Builtins.get (Context.Proof ctxt))


(** basic and additional constructors **)

fun mk_builtin_typ _ (Sym ("bool", _)) = SOME @{typ bool}
  | mk_builtin_typ _ (Sym ("Int", _)) = SOME @{typ int}
  | mk_builtin_typ _ (Sym ("int", _)) = SOME @{typ int}  (*FIXME: delete*)
  | mk_builtin_typ ctxt sym = chained_mk_builtin_typ (get_mk_builtins ctxt) sym

fun mk_builtin_num _ i @{typ int} = SOME (Numeral.mk_cnumber @{ctyp int} i)
  | mk_builtin_num ctxt i T =
      chained_mk_builtin_num ctxt (get_mk_builtins ctxt) i T

val mk_true = Thm.cterm_of @{theory} (@{const Not} $ @{const False})
val mk_false = Thm.cterm_of @{theory} @{const False}
val mk_not = Thm.apply (Thm.cterm_of @{theory} @{const Not})
val mk_implies = Thm.mk_binop (Thm.cterm_of @{theory} @{const HOL.implies})
val mk_iff = Thm.mk_binop (Thm.cterm_of @{theory} @{const HOL.eq (bool)})
val conj = Thm.cterm_of @{theory} @{const HOL.conj}
val disj = Thm.cterm_of @{theory} @{const HOL.disj}

fun mk_nary _ cu [] = cu
  | mk_nary ct _ cts = uncurry (fold_rev (Thm.mk_binop ct)) (split_last cts)

val eq = SMT_Utils.mk_const_pat @{theory} @{const_name HOL.eq} SMT_Utils.destT1
fun mk_eq ct cu = Thm.mk_binop (SMT_Utils.instT' ct eq) ct cu

val if_term =
  SMT_Utils.mk_const_pat @{theory} @{const_name If}
    (SMT_Utils.destT1 o SMT_Utils.destT2)
fun mk_if cc ct cu =
  Thm.mk_binop (Thm.apply (SMT_Utils.instT' ct if_term) cc) ct cu

val nil_term =
  SMT_Utils.mk_const_pat @{theory} @{const_name Nil} SMT_Utils.destT1
val cons_term =
  SMT_Utils.mk_const_pat @{theory} @{const_name Cons} SMT_Utils.destT1
fun mk_list cT cts =
  fold_rev (Thm.mk_binop (SMT_Utils.instT cT cons_term)) cts
    (SMT_Utils.instT cT nil_term)

val distinct = SMT_Utils.mk_const_pat @{theory} @{const_name distinct}
  (SMT_Utils.destT1 o SMT_Utils.destT1)
fun mk_distinct [] = mk_true
  | mk_distinct (cts as (ct :: _)) =
      Thm.apply (SMT_Utils.instT' ct distinct)
        (mk_list (Thm.ctyp_of_term ct) cts)

val access =
  SMT_Utils.mk_const_pat @{theory} @{const_name fun_app} SMT_Utils.destT1
fun mk_access array = Thm.apply (SMT_Utils.instT' array access) array

val update = SMT_Utils.mk_const_pat @{theory} @{const_name fun_upd}
  (Thm.dest_ctyp o SMT_Utils.destT1)
fun mk_update array index value =
  let val cTs = Thm.dest_ctyp (Thm.ctyp_of_term array)
  in
    Thm.apply (Thm.mk_binop (SMT_Utils.instTs cTs update) array index) value
  end

val mk_uminus = Thm.apply (Thm.cterm_of @{theory} @{const uminus (int)})
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
  | (Sym ("if", _), [ct1, ct2, ct3]) => SOME (mk_if ct1 ct2 ct3)
  | (Sym ("ite", _), [ct1, ct2, ct3]) => SOME (mk_if ct1 ct2 ct3) (* FIXME: remove *)
  | (Sym ("=", _), [ct, cu]) => SOME (mk_eq ct cu)
  | (Sym ("distinct", _), _) => SOME (mk_distinct cts)
  | (Sym ("select", _), [ca, ck]) => SOME (Thm.apply (mk_access ca) ck)
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



(* abstraction *)

fun is_builtin_theory_term ctxt t =
  if SMT_Builtin.is_builtin_num ctxt t then true
  else
    (case Term.strip_comb t of
      (Const c, ts) => SMT_Builtin.is_builtin_fun ctxt c ts
    | _ => false)

end
