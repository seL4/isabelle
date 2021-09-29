(*  Title:      HOL/Tools/SMT/z3_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to Z3 based on a relaxed version of SMT-LIB.
*)

signature Z3_INTERFACE =
sig
  val smtlib_z3C: SMT_Util.class

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
end;

structure Z3_Interface: Z3_INTERFACE =
struct

val z3C = ["z3"]

val smtlib_z3C = SMTLIB_Interface.smtlibC @ z3C


(* interface *)

local
  fun translate_config ctxt =
    {order = SMT_Util.First_Order,
     logic = K "",
     fp_kinds = [BNF_Util.Least_FP],
     serialize = #serialize (SMTLIB_Interface.translate_config SMT_Util.First_Order ctxt)}

  fun is_div_mod \<^Const_>\<open>divide \<^Type>\<open>int\<close>\<close> = true
    | is_div_mod \<^Const>\<open>modulo \<^Type>\<open>int\<close>\<close> = true
    | is_div_mod _ = false

  val have_int_div_mod = exists (Term.exists_subterm is_div_mod o Thm.prop_of)

  fun add_div_mod _ (thms, extra_thms) =
    if have_int_div_mod thms orelse have_int_div_mod extra_thms then
      (thms, @{thms div_as_z3div mod_as_z3mod} @ extra_thms)
    else (thms, extra_thms)

  val setup_builtins =
    SMT_Builtin.add_builtin_fun' smtlib_z3C (\<^Const>\<open>times \<^Type>\<open>int\<close>\<close>, "*") #>
    SMT_Builtin.add_builtin_fun' smtlib_z3C (\<^Const>\<open>z3div\<close>, "div") #>
    SMT_Builtin.add_builtin_fun' smtlib_z3C (\<^Const>\<open>z3mod\<close>, "mod")
in

val _ = Theory.setup (Context.theory_map (
  setup_builtins #>
  SMT_Normalize.add_extra_norm (smtlib_z3C, add_div_mod) #>
  SMT_Translate.add_config (smtlib_z3C, translate_config)))

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

fun add_mk_builtins mk = Mk_Builtins.map (Ord_List.insert fst_int_ord (serial (), mk))

fun get_mk_builtins ctxt = map snd (Mk_Builtins.get (Context.Proof ctxt))


(** basic and additional constructors **)

fun mk_builtin_typ _ (Sym ("Bool", _)) = SOME \<^typ>\<open>bool\<close>
  | mk_builtin_typ _ (Sym ("Int", _)) = SOME \<^typ>\<open>int\<close>
  | mk_builtin_typ _ (Sym ("bool", _)) = SOME \<^typ>\<open>bool\<close>  (*FIXME: legacy*)
  | mk_builtin_typ _ (Sym ("int", _)) = SOME \<^typ>\<open>int\<close>  (*FIXME: legacy*)
  | mk_builtin_typ ctxt sym = chained_mk_builtin_typ (get_mk_builtins ctxt) sym

fun mk_builtin_num _ i \<^typ>\<open>int\<close> = SOME (Numeral.mk_cnumber \<^ctyp>\<open>int\<close> i)
  | mk_builtin_num ctxt i T =
      chained_mk_builtin_num ctxt (get_mk_builtins ctxt) i T

val mk_true = \<^cterm>\<open>\<not> False\<close>
val mk_false = \<^cterm>\<open>False\<close>
val mk_not = Thm.apply \<^cterm>\<open>HOL.Not\<close>
val mk_implies = Thm.mk_binop \<^cterm>\<open>HOL.implies\<close>
val mk_iff = Thm.mk_binop \<^cterm>\<open>(=) :: bool \<Rightarrow> _\<close>
val conj = \<^cterm>\<open>HOL.conj\<close>
val disj = \<^cterm>\<open>HOL.disj\<close>

fun mk_nary _ cu [] = cu
  | mk_nary ct _ cts = uncurry (fold_rev (Thm.mk_binop ct)) (split_last cts)

val eq = SMT_Util.mk_const_pat \<^theory> \<^const_name>\<open>HOL.eq\<close> Thm.dest_ctyp0
fun mk_eq ct cu = Thm.mk_binop (SMT_Util.instT' ct eq) ct cu

val if_term =
  SMT_Util.mk_const_pat \<^theory> \<^const_name>\<open>If\<close> (Thm.dest_ctyp0 o Thm.dest_ctyp1)
fun mk_if cc ct = Thm.mk_binop (Thm.apply (SMT_Util.instT' ct if_term) cc) ct

val access = SMT_Util.mk_const_pat \<^theory> \<^const_name>\<open>fun_app\<close> Thm.dest_ctyp0
fun mk_access array = Thm.apply (SMT_Util.instT' array access) array

val update =
  SMT_Util.mk_const_pat \<^theory> \<^const_name>\<open>fun_upd\<close> (Thm.dest_ctyp o Thm.dest_ctyp0)
fun mk_update array index value =
  let val cTs = Thm.dest_ctyp (Thm.ctyp_of_cterm array)
  in Thm.apply (Thm.mk_binop (SMT_Util.instTs cTs update) array index) value end

val mk_uminus = Thm.apply \<^cterm>\<open>uminus :: int \<Rightarrow> _\<close>
val add = \<^cterm>\<open>(+) :: int \<Rightarrow> _\<close>
val int0 = Numeral.mk_cnumber \<^ctyp>\<open>int\<close> 0
val mk_sub = Thm.mk_binop \<^cterm>\<open>(-) :: int \<Rightarrow> _\<close>
val mk_mul = Thm.mk_binop \<^cterm>\<open>(*) :: int \<Rightarrow> _\<close>
val mk_div = Thm.mk_binop \<^cterm>\<open>z3div\<close>
val mk_mod = Thm.mk_binop \<^cterm>\<open>z3mod\<close>
val mk_lt = Thm.mk_binop \<^cterm>\<open>(<) :: int \<Rightarrow> _\<close>
val mk_le = Thm.mk_binop \<^cterm>\<open>(\<le>) :: int \<Rightarrow> _\<close>

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
  | (Sym ("select", _), [ca, ck]) => SOME (Thm.apply (mk_access ca) ck)
  | (Sym ("store", _), [ca, ck, cv]) => SOME (mk_update ca ck cv)
  | _ =>
    (case (sym, try (Thm.typ_of_cterm o hd) cts, cts) of
      (Sym ("+", _), SOME \<^typ>\<open>int\<close>, _) => SOME (mk_nary add int0 cts)
    | (Sym ("-", _), SOME \<^typ>\<open>int\<close>, [ct]) => SOME (mk_uminus ct)
    | (Sym ("-", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_sub ct cu)
    | (Sym ("*", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_mul ct cu)
    | (Sym ("div", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_div ct cu)
    | (Sym ("mod", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_mod ct cu)
    | (Sym ("<", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_lt ct cu)
    | (Sym ("<=", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_le ct cu)
    | (Sym (">", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_lt cu ct)
    | (Sym (">=", _), SOME \<^typ>\<open>int\<close>, [ct, cu]) => SOME (mk_le cu ct)
    | _ => chained_mk_builtin_fun ctxt (get_mk_builtins ctxt) sym cts))


(* abstraction *)

fun is_builtin_theory_term ctxt t =
  if SMT_Builtin.is_builtin_num ctxt t then true
  else
    (case Term.strip_comb t of
      (Const c, ts) => SMT_Builtin.is_builtin_fun ctxt c ts
    | _ => false)

end;
