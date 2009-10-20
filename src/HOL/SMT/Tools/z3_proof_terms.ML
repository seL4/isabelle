(*  Title:      HOL/SMT/Tools/z3_proof_terms.ML
    Author:     Sascha Boehme, TU Muenchen

Reconstruction functions for terms occurring in Z3 proofs.
*)

signature Z3_PROOF_TERMS =
sig
  val mk_prop: Thm.cterm -> Thm.cterm
  val mk_meta_eq: Thm.cterm -> Thm.cterm -> Thm.cterm

  type preterm

  val compile: theory -> Name.context -> preterm -> Thm.cterm * Thm.cterm list

  val mk_bound: theory -> int -> typ -> preterm
  val mk_fun: Thm.cterm -> preterm list -> preterm
  val mk_forall: theory -> string * typ -> preterm -> preterm
  val mk_exists: theory -> string * typ -> preterm -> preterm

  val mk_true: preterm
  val mk_false: preterm
  val mk_not: preterm -> preterm
  val mk_and: preterm list -> preterm
  val mk_or: preterm list -> preterm
  val mk_implies: preterm -> preterm -> preterm
  val mk_iff: preterm -> preterm -> preterm

  val mk_eq: preterm -> preterm -> preterm
  val mk_if: preterm -> preterm -> preterm -> preterm
  val mk_distinct: preterm list -> preterm

  val mk_pat: preterm list -> preterm
  val mk_nopat: preterm list -> preterm
  val mk_trigger: preterm list -> preterm -> preterm

  val mk_access: preterm -> preterm -> preterm
  val mk_update: preterm -> preterm -> preterm -> preterm

  val mk_int_num: int -> preterm
  val mk_real_frac_num: int * int option -> preterm
  val mk_uminus: preterm -> preterm
  val mk_add: preterm -> preterm -> preterm
  val mk_sub: preterm -> preterm -> preterm
  val mk_mul: preterm -> preterm -> preterm
  val mk_int_div: preterm -> preterm -> preterm
  val mk_real_div: preterm -> preterm -> preterm
  val mk_rem: preterm -> preterm -> preterm
  val mk_mod: preterm -> preterm -> preterm
  val mk_lt: preterm -> preterm -> preterm
  val mk_le: preterm -> preterm -> preterm

  val wordT : int -> typ
  val mk_bv_num : theory -> int -> int -> preterm

  val var_prefix: string
end

structure Z3_Proof_Terms: Z3_PROOF_TERMS =
struct

fun instTs cUs (cTs, ct) = Thm.instantiate_cterm (cTs ~~ cUs, []) ct
fun instT cU (cT, ct) = instTs [cU] ([cT], ct)
fun mk_inst_pair destT cpat = (destT (Thm.ctyp_of_term cpat), cpat)
val destT1 = hd o Thm.dest_ctyp
val destT2 = hd o tl o Thm.dest_ctyp


val mk_prop = Thm.capply @{cterm Trueprop}

val meta_eq = mk_inst_pair destT1 @{cpat "op =="}
fun mk_meta_eq ct = Thm.mk_binop (instT (Thm.ctyp_of_term ct) meta_eq) ct


datatype preterm = Preterm of {
  cterm: Thm.cterm,
  vars: (int * Thm.cterm) list }

fun mk_preterm (ct, vs) = Preterm {cterm=ct, vars=vs}
fun dest_preterm (Preterm {cterm, vars}) = (cterm, vars)
fun ctyp_of_preterm (Preterm {cterm, ...}) = Thm.ctyp_of_term cterm

fun instT' e = instT (ctyp_of_preterm e)

val maxidx_of = #maxidx o Thm.rep_cterm

val var_prefix = "v"

local
fun mk_inst nctxt cert vs =
  let
    val max = fold (Integer.max o fst) vs 0
    val names = fst (Name.variants (replicate (max + 1) var_prefix) nctxt)
    fun mk (i, v) = (v, cert (Free (nth names i, #T (Thm.rep_cterm v))))
  in map mk vs end

fun fix_vars _ _ ct [] = (ct, [])
  | fix_vars thy nctxt ct vs =
      let
        val cert = Thm.cterm_of thy
        val inst = mk_inst nctxt cert vs
      in (Thm.instantiate_cterm ([], inst) ct, map snd inst) end
in
fun compile thy nctxt (Preterm {cterm, vars}) = fix_vars thy nctxt cterm vars
end

local
fun app e (ct1, vs1) =
  let
    fun part (var as (i, v)) (inst, vs) =
      (case AList.lookup (op =) vs1 i of
        NONE => (inst, var :: vs)
      | SOME v' => ((v, v') :: inst, vs))

    val (ct2, vs2) = dest_preterm e
    val incr =
      if maxidx_of ct1 < 0 orelse maxidx_of ct2 < 0 then I
      else Thm.incr_indexes_cterm (maxidx_of ct1 + 1)

    val (inst, vs) = fold (part o apsnd incr) vs2 ([], vs1)
    val ct2' = Thm.instantiate_cterm ([], inst) (incr ct2)
  in (Thm.capply ct1 ct2', vs) end
in
fun mk_fun ct es = mk_preterm (fold app es (ct, []))
fun mk_binop f t u = mk_fun f [t, u]
fun mk_nary _ e [] = e
  | mk_nary ct _ es = uncurry (fold_rev (mk_binop ct)) (split_last es)
end

fun mk_bound thy i T =
  let val ct = Thm.cterm_of thy (Var ((Name.uu, 0), T))
  in mk_preterm (ct, [(i, ct)]) end

local
fun mk_quant q thy (n, T) e =
  let
    val (ct, vs) = dest_preterm e
    val cv =
      (case AList.lookup (op =) vs 0 of
        SOME cv => cv
      | _ => Thm.cterm_of thy (Var ((Name.uu, maxidx_of ct + 1), T)))
    val cq = instT (Thm.ctyp_of_term cv) q
    fun dec (i, v) = if i = 0 then NONE else SOME (i - 1, v)
  in mk_preterm (Thm.capply cq (Thm.cabs cv ct), map_filter dec vs) end
in
val mk_forall = mk_quant (mk_inst_pair (destT1 o destT1) @{cpat All})
val mk_exists = mk_quant (mk_inst_pair (destT1 o destT1) @{cpat Ex})
end


val mk_false = mk_fun @{cterm False} []
val mk_not = mk_fun @{cterm Not} o single
val mk_true = mk_not mk_false
val mk_and = mk_nary @{cterm "op &"} mk_true
val mk_or = mk_nary @{cterm "op |"} mk_false
val mk_implies = mk_binop @{cterm "op -->"}
val mk_iff = mk_binop @{cterm "op = :: bool => _"}

val eq = mk_inst_pair destT1 @{cpat "op ="}
fun mk_eq t u = mk_binop (instT' t eq) t u

val if_term = mk_inst_pair (destT1 o destT2) @{cpat If}
fun mk_if c t u = mk_fun (instT' t if_term) [c, t, u]

val nil_term = mk_inst_pair destT1 @{cpat Nil}
val cons_term = mk_inst_pair destT1 @{cpat Cons}
fun mk_list cT es =
  fold_rev (mk_binop (instT cT cons_term)) es (mk_fun (instT cT nil_term) [])

val distinct = mk_inst_pair (destT1 o destT1) @{cpat distinct}
fun mk_distinct [] = mk_true
  | mk_distinct (es as (e :: _)) =
      mk_fun (instT' e distinct) [mk_list (ctyp_of_preterm e) es]

val pat = mk_inst_pair destT1 @{cpat pat}
val nopat = mk_inst_pair destT1 @{cpat nopat}
val andpat = mk_inst_pair (destT1 o destT2) @{cpat "op andpat"}
fun mk_gen_pat _ [] = raise TERM ("mk_gen_pat: empty pattern", [])
  | mk_gen_pat pat (e :: es) =
      let fun mk t p = mk_fun (instT' t andpat) [p, t]
      in fold mk es (mk_fun (instT' e pat) [e]) end
val mk_pat = mk_gen_pat pat
val mk_nopat = mk_gen_pat nopat

fun mk_trigger es e = mk_fun @{cterm trigger} [mk_list @{ctyp pattern} es, e]


val access = mk_inst_pair (Thm.dest_ctyp o destT1) @{cpat apply}
fun mk_access array index =
  let val cTs = Thm.dest_ctyp (ctyp_of_preterm array)
  in mk_fun (instTs cTs access) [array, index] end

val update = mk_inst_pair (Thm.dest_ctyp o destT1) @{cpat fun_upd}
fun mk_update array index value =
  let val cTs = Thm.dest_ctyp (ctyp_of_preterm array)
  in mk_fun (instTs cTs update) [array, index, value] end


fun mk_int_num i = mk_fun (Numeral.mk_cnumber @{ctyp int} i) []
fun mk_real_num i = mk_fun (Numeral.mk_cnumber @{ctyp real} i) []

fun mk_real_frac_num (e, NONE) = mk_real_num e
  | mk_real_frac_num (e, SOME d) =
      mk_binop @{cterm "op / :: real => _"} (mk_real_num e) (mk_real_num d)

fun has_int_type e = (Thm.typ_of (ctyp_of_preterm e) = @{typ int})
fun choose e i r = if has_int_type e then i else r

val uminus_i = @{cterm "uminus :: int => _"}
val uminus_r = @{cterm "uminus :: real => _"}
fun mk_uminus e = mk_fun (choose e uminus_i uminus_r) [e]

fun arith_op int_op real_op t u = mk_binop (choose t int_op real_op) t u

val mk_add = arith_op @{cterm "op + :: int => _"} @{cterm "op + :: real => _"}
val mk_sub = arith_op @{cterm "op - :: int => _"} @{cterm "op - :: real => _"}
val mk_mul = arith_op @{cterm "op * :: int => _"} @{cterm "op * :: real => _"}
val mk_int_div = mk_binop @{cterm "op div :: int => _"}
val mk_real_div = mk_binop @{cterm "op / :: real => _"}
val mk_rem = mk_binop @{cterm "op rem :: int => _"}
val mk_mod = mk_binop @{cterm "op mod :: int => _"}
val mk_lt = arith_op @{cterm "op < :: int => _"} @{cterm "op < :: real => _"}
val mk_le = arith_op @{cterm "op <= :: int => _"} @{cterm "op <= :: real => _"}

fun binT size =
  let
    fun bitT i T =
      if i = 0
      then Type (@{type_name "Numeral_Type.bit0"}, [T])
      else Type (@{type_name "Numeral_Type.bit1"}, [T])

    fun binT i =
      if i = 0 then @{typ "Numeral_Type.num0"}
      else if i = 1 then @{typ "Numeral_Type.num1"}
      else let val (q, r) = Integer.div_mod i 2 in bitT r (binT q) end
  in
    if size >= 0 then binT size
    else raise TYPE ("mk_binT: " ^ string_of_int size, [], [])
  end

fun wordT size = Type (@{type_name "word"}, [binT size])

fun mk_bv_num thy num size =
  mk_fun (Numeral.mk_cnumber (Thm.ctyp_of thy (wordT size)) num) []

end
