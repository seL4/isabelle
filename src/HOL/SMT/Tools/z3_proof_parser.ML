(*  Title:      HOL/SMT/Tools/z3_proof_parser.ML
    Author:     Sascha Boehme, TU Muenchen

Parser for Z3 proofs.
*)

signature Z3_PROOF_PARSER =
sig
  (* proof rules *)
  datatype rule = TrueAxiom | Asserted | Goal | ModusPonens | Reflexivity |
    Symmetry | Transitivity | TransitivityStar | Monotonicity | QuantIntro |
    Distributivity | AndElim | NotOrElim | Rewrite | RewriteStar | PullQuant |
    PullQuantStar | PushQuant | ElimUnusedVars | DestEqRes | QuantInst |
    Hypothesis | Lemma | UnitResolution | IffTrue | IffFalse | Commutativity |
    DefAxiom | IntroDef | ApplyDef | IffOeq | NnfPos | NnfNeg | NnfStar |
    CnfStar | Skolemize | ModusPonensOeq | ThLemma
  val string_of_rule: rule -> string

  (* proof parser *)
  datatype proof_step = Proof_Step of {
    rule: rule,
    prems: int list,
    prop: cterm }
  val parse: Proof.context -> typ Symtab.table -> term Symtab.table ->
    string list ->
    int * (proof_step Inttab.table * string list * Proof.context)
end

structure Z3_Proof_Parser: Z3_PROOF_PARSER =
struct

(** proof rules **)

datatype rule = TrueAxiom | Asserted | Goal | ModusPonens | Reflexivity |
  Symmetry | Transitivity | TransitivityStar | Monotonicity | QuantIntro |
  Distributivity | AndElim | NotOrElim | Rewrite | RewriteStar | PullQuant |
  PullQuantStar | PushQuant | ElimUnusedVars | DestEqRes | QuantInst |
  Hypothesis | Lemma | UnitResolution | IffTrue | IffFalse | Commutativity |
  DefAxiom | IntroDef | ApplyDef | IffOeq | NnfPos | NnfNeg | NnfStar |
  CnfStar | Skolemize | ModusPonensOeq | ThLemma

val rule_names = Symtab.make [
  ("true-axiom", TrueAxiom),
  ("asserted", Asserted),
  ("goal", Goal),
  ("mp", ModusPonens),
  ("refl", Reflexivity),
  ("symm", Symmetry),
  ("trans", Transitivity),
  ("trans*", TransitivityStar),
  ("monotonicity", Monotonicity),
  ("quant-intro", QuantIntro),
  ("distributivity", Distributivity),
  ("and-elim", AndElim),
  ("not-or-elim", NotOrElim),
  ("rewrite", Rewrite),
  ("rewrite*", RewriteStar),
  ("pull-quant", PullQuant),
  ("pull-quant*", PullQuantStar),
  ("push-quant", PushQuant),
  ("elim-unused", ElimUnusedVars),
  ("der", DestEqRes),
  ("quant-inst", QuantInst),
  ("hypothesis", Hypothesis),
  ("lemma", Lemma),
  ("unit-resolution", UnitResolution),
  ("iff-true", IffTrue),
  ("iff-false", IffFalse),
  ("commutativity", Commutativity),
  ("def-axiom", DefAxiom),
  ("intro-def", IntroDef),
  ("apply-def", ApplyDef),
  ("iff~", IffOeq),
  ("nnf-pos", NnfPos),
  ("nnf-neg", NnfNeg),
  ("nnf*", NnfStar),
  ("cnf*", CnfStar),
  ("sk", Skolemize),
  ("mp~", ModusPonensOeq),
  ("th-lemma", ThLemma)]

fun string_of_rule r =
  let fun eq_rule (s, r') = if r = r' then SOME s else NONE 
  in the (Symtab.get_first eq_rule rule_names) end



(** certified terms and variables **)

val (var_prefix, decl_prefix) = ("v", "sk")  (* must be distinct *)

fun instTs cUs (cTs, ct) = Thm.instantiate_cterm (cTs ~~ cUs, []) ct
fun instT cU (cT, ct) = instTs [cU] ([cT], ct)
fun mk_inst_pair destT cpat = (destT (Thm.ctyp_of_term cpat), cpat)
val destT1 = hd o Thm.dest_ctyp
val destT2 = hd o tl o Thm.dest_ctyp

fun ctyp_of (ct, _) = Thm.ctyp_of_term ct
fun instT' t = instT (ctyp_of t)

fun certify ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)

val maxidx_of = #maxidx o Thm.rep_cterm

fun mk_inst ctxt vars =
  let
    val max = fold (Integer.max o fst) vars 0
    val ns = fst (Variable.variant_fixes (replicate (max + 1) var_prefix) ctxt)
    fun mk (i, v) = (v, certify ctxt (Free (nth ns i, #T (Thm.rep_cterm v))))
  in map mk vars end

fun close ctxt (ct, vars) =
  let
    val inst = mk_inst ctxt vars
    val mk_prop = Thm.capply @{cterm Trueprop}
    val names = fold (Term.add_free_names o Thm.term_of o snd) inst []
  in (mk_prop (Thm.instantiate_cterm ([], inst) ct), names) end


fun mk_bound thy (i, T) =
  let val ct = Thm.cterm_of thy (Var ((Name.uu, 0), T))
  in (ct, [(i, ct)]) end

local
  fun mk_quant thy q T (ct, vars) =
    let
      val cv =
        (case AList.lookup (op =) vars 0 of
          SOME cv => cv
        | _ => Thm.cterm_of thy (Var ((Name.uu, maxidx_of ct + 1), T)))
      val cq = instT (Thm.ctyp_of_term cv) q
      fun dec (i, v) = if i = 0 then NONE else SOME (i-1, v)
    in (Thm.capply cq (Thm.cabs cv ct), map_filter dec vars) end

  val forall = mk_inst_pair (destT1 o destT1) @{cpat All}
  val exists = mk_inst_pair (destT1 o destT1) @{cpat Ex}
in
fun mk_forall thy = fold_rev (mk_quant thy forall)
fun mk_exists thy = fold_rev (mk_quant thy exists)
end


local
  fun equal_var cv (_, cu) = (cv aconvc cu)

  fun apply (ct2, vars2) (ct1, vars1) =
    let
      val incr = Thm.incr_indexes_cterm (maxidx_of ct1 + maxidx_of ct2 + 2)

      fun part (v as (i, cv)) =
        (case AList.lookup (op =) vars1 i of
          SOME cu => apfst (if cu aconvc cv then I else cons (cv, cu))
        | NONE =>
            if not (exists (equal_var cv) vars1) then apsnd (cons v)
            else
              let val cv' = incr cv
              in apfst (cons (cv, cv')) #> apsnd (cons (i, cv')) end)

      val (ct2', vars2') =
        if null vars1 then (ct2, vars2)
        else fold part vars2 ([], [])
          |>> (fn inst => Thm.instantiate_cterm ([], inst) ct2)

    in (Thm.capply ct1 ct2', vars1 @ vars2') end
in
fun mk_fun ct ts = fold apply ts (ct, [])
fun mk_binop f t u = mk_fun f [t, u]
fun mk_nary _ e [] = e
  | mk_nary ct _ es = uncurry (fold_rev (mk_binop ct)) (split_last es)
end


val mk_true = mk_fun @{cterm "~False"} []
val mk_false = mk_fun @{cterm "False"} []
fun mk_not t = mk_fun @{cterm Not} [t]
val mk_imp = mk_binop @{cterm "op -->"}
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
      mk_fun (instT' e distinct) [mk_list (ctyp_of e) es]


(* arithmetic *)

fun mk_int_num i = mk_fun (Numeral.mk_cnumber @{ctyp int} i) []
fun mk_real_num i = mk_fun (Numeral.mk_cnumber @{ctyp real} i) []
fun mk_real_frac_num (e, NONE) = mk_real_num e
  | mk_real_frac_num (e, SOME d) =
      mk_binop @{cterm "op / :: real => _"} (mk_real_num e) (mk_real_num d)

fun has_int_type e = (Thm.typ_of (ctyp_of e) = @{typ int})
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
val mk_mod = mk_binop @{cterm "op mod :: int => _"}
val mk_lt = arith_op @{cterm "op < :: int => _"} @{cterm "op < :: real => _"}
val mk_le = arith_op @{cterm "op <= :: int => _"} @{cterm "op <= :: real => _"}


(* arrays *)

val access = mk_inst_pair (Thm.dest_ctyp o destT1) @{cpat apply}
fun mk_access array index =
  let val cTs = Thm.dest_ctyp (ctyp_of array)
  in mk_fun (instTs cTs access) [array, index] end

val update = mk_inst_pair (Thm.dest_ctyp o destT1) @{cpat fun_upd}
fun mk_update array index value =
  let val cTs = Thm.dest_ctyp (ctyp_of array)
  in mk_fun (instTs cTs update) [array, index, value] end


(* bitvectors *)

fun mk_binT size =
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

fun mk_wordT size = Type (@{type_name "word"}, [mk_binT size])

fun mk_bv_num thy (num, size) =
  mk_fun (Numeral.mk_cnumber (Thm.ctyp_of thy (mk_wordT size)) num) []



(** proof parser **)

datatype proof_step = Proof_Step of {
  rule: rule,
  prems: int list,
  prop: cterm }


(* parser context *)

fun make_context ctxt typs terms =
  let
    val ctxt' = 
      ctxt
      |> Symtab.fold (Variable.declare_typ o snd) typs
      |> Symtab.fold (Variable.declare_term o snd) terms

    fun cert @{term True} = @{cterm "~False"}
      | cert t = certify ctxt' t
  in (typs, Symtab.map cert terms, Inttab.empty, Inttab.empty, [], ctxt') end

fun fresh_name n (typs, terms, exprs, steps, vars, ctxt) =
  let val (n', ctxt') = yield_singleton Variable.variant_fixes n ctxt
  in (n', (typs, terms, exprs, steps, vars, ctxt')) end

fun theory_of (_, _, _, _, _, ctxt) = ProofContext.theory_of ctxt

fun typ_of_sort n (cx as (typs, _, _, _, _, _)) =
  (case Symtab.lookup typs n of
    SOME T => (T, cx)
  | NONE => cx
      |> fresh_name ("'" ^ n) |>> TFree o rpair @{sort type}
      |> (fn (T, (typs, terms, exprs, steps, vars, ctxt)) =>
           (T, (Symtab.update (n, T) typs, terms, exprs, steps, vars, ctxt))))

fun add_decl (n, T) (cx as (_, terms, _, _, _, _)) =
  (case Symtab.lookup terms n of
    SOME _ => cx
  | NONE => cx |> fresh_name (decl_prefix ^ n)
      |> (fn (m, (typs, terms, exprs, steps, vars, ctxt)) =>
           let val upd = Symtab.update (n, certify ctxt (Free (m, T)))
           in (typs, upd terms, exprs, steps, vars, ctxt) end))

datatype sym = Sym of string * sym list

fun mk_app _ (Sym ("true", _), _) = SOME mk_true
  | mk_app _ (Sym ("false", _), _) = SOME mk_false
  | mk_app _ (Sym ("=", _), [t, u]) = SOME (mk_eq t u)
  | mk_app _ (Sym ("distinct", _), ts) = SOME (mk_distinct ts)
  | mk_app _ (Sym ("ite", _), [s, t, u]) = SOME (mk_if s t u)
  | mk_app _ (Sym ("and", _), ts) = SOME (mk_nary @{cterm "op &"} mk_true ts)
  | mk_app _ (Sym ("or", _), ts) = SOME (mk_nary @{cterm "op |"} mk_false ts)
  | mk_app _ (Sym ("iff", _), [t, u]) = SOME (mk_iff t u)
  | mk_app _ (Sym ("xor", _), [t, u]) = SOME (mk_not (mk_iff t u))
  | mk_app _ (Sym ("not", _), [t]) = SOME (mk_not t)
  | mk_app _ (Sym ("implies", _), [t, u]) = SOME (mk_imp t u)
  | mk_app _ (Sym ("~", _), [t, u]) = SOME (mk_iff t u)
  | mk_app _ (Sym ("<", _), [t, u]) = SOME (mk_lt t u)
  | mk_app _ (Sym ("<=", _), [t, u]) = SOME (mk_le t u)
  | mk_app _ (Sym (">", _), [t, u]) = SOME (mk_lt u t)
  | mk_app _ (Sym (">=", _), [t, u]) = SOME (mk_le u t)
  | mk_app _ (Sym ("+", _), [t, u]) = SOME (mk_add t u)
  | mk_app _ (Sym ("-", _), [t, u]) = SOME (mk_sub t u)
  | mk_app _ (Sym ("-", _), [t]) = SOME (mk_uminus t)
  | mk_app _ (Sym ("*", _), [t, u]) = SOME (mk_mul t u)
  | mk_app _ (Sym ("/", _), [t, u]) = SOME (mk_real_div t u)
  | mk_app _ (Sym ("div", _), [t, u]) = SOME (mk_int_div t u)
  | mk_app _ (Sym ("mod", _), [t, u]) = SOME (mk_mod t u)
  | mk_app _ (Sym ("select", _), [m, k]) = SOME (mk_access m k)
  | mk_app _ (Sym ("store", _), [m, k, v]) = SOME (mk_update m k v)
  | mk_app _ (Sym ("pattern", _), _) = SOME mk_true
  | mk_app (_, terms, _, _, _, _) (Sym (n, _), ts) =
      Symtab.lookup terms n |> Option.map (fn ct => mk_fun ct ts)

fun add_expr k t (typs, terms, exprs, steps, vars, ctxt) =
  (typs, terms, Inttab.update (k, t) exprs, steps, vars, ctxt)

fun lookup_expr (_, _, exprs, _, _, _) = Inttab.lookup exprs

fun add_proof_step k ((r, prems), prop) cx =
  let
    val (typs, terms, exprs, steps, vars, ctxt) = cx
    val (ct, vs) = close ctxt prop
    val step = Proof_Step {rule=r, prems=prems, prop=ct}
    val vars' = union (op =) vs vars
  in (typs, terms, exprs, Inttab.update (k, step) steps, vars', ctxt) end

fun finish (_, _, _, steps, vars, ctxt) = (steps, vars, ctxt)


(* core parser *)

fun parse_exn line_no msg = raise SMT_Solver.SMT ("Z3 proof parser (line " ^
  string_of_int line_no ^ "): " ^ msg)

fun scan_exn msg ((line_no, _), _) = parse_exn line_no msg

fun with_info f cx =
  (case f ((NONE, 1), cx) of
    ((SOME root, _), cx') => (root, cx')
  | ((_, line_no), _) => parse_exn line_no "bad proof")

fun parse_line _ _ (st as ((SOME _, _), _)) = st
  | parse_line scan line ((_, line_no), cx) =
      let val st = ((line_no, cx), explode line)
      in
        (case Scan.catch (Scan.finite' Symbol.stopper (Scan.option scan)) st of
          (SOME r, ((_, cx'), _)) => ((r, line_no+1), cx')
        | (NONE, _) => parse_exn line_no ("bad proof line: " ^ quote line))
      end

fun with_context f x ((line_no, cx), st) =
  let val (y, cx') = f x cx
  in (y, ((line_no, cx'), st)) end
  

fun lookup_context f x (st as ((_, cx), _)) = (f cx x, st)


(* parser combinators and parsers for basic entities *)

fun $$ s = Scan.lift (Scan.$$ s)
fun this s = Scan.lift (Scan.this_string s)
fun blank st = Scan.lift (Scan.many1 Symbol.is_ascii_blank) st
fun sep scan = blank |-- scan
fun seps scan = Scan.repeat (sep scan)
fun seps1 scan = Scan.repeat1 (sep scan)
fun seps_by scan_sep scan = scan ::: Scan.repeat (scan_sep |-- scan)

fun par scan = $$ "(" |-- scan --| $$ ")"
fun bra scan = $$ "[" |-- scan --| $$ "]"

val digit = (fn
  "0" => SOME 0 | "1" => SOME 1 | "2" => SOME 2 | "3" => SOME 3 |
  "4" => SOME 4 | "5" => SOME 5 | "6" => SOME 6 | "7" => SOME 7 |
  "8" => SOME 8 | "9" => SOME 9 | _ => NONE)

fun mk_num ds = fold (fn d => fn i => i * 10 + d) ds 0
val nat_num = Scan.lift (Scan.repeat1 (Scan.some digit)) >> mk_num
val int_num = Scan.optional ($$ "-" >> K (fn i => ~i)) I :|--
  (fn sign => nat_num >> sign)

val is_char = Symbol.is_ascii_letter orf Symbol.is_ascii_digit orf
  member (op =) (explode "_+*-/%~=<>$&|?!.@^#")
val name = Scan.lift (Scan.many1 is_char) >> implode

fun sym st = (name -- Scan.optional (bra (seps_by ($$ ":") sym)) [] >> Sym) st

fun id st = ($$ "#" |-- nat_num) st


(* parsers for various parts of Z3 proofs *)

fun sort st = Scan.first [
  this "bool" >> K @{typ bool},
  this "int" >> K @{typ int},
  this "real" >> K @{typ real},
  this "bv" |-- bra nat_num >> mk_wordT,
  this "array" |-- bra (sort --| $$ ":" -- sort) >> (op -->),
  par (this "->" |-- seps1 sort) >> ((op --->) o split_last),
  name :|-- with_context typ_of_sort] st

fun bound st = (par (this ":var" |-- sep nat_num -- sep sort) :|--
  lookup_context (mk_bound o theory_of)) st

fun number st = st |> (
  int_num -- Scan.option ($$ "/" |-- int_num) --| this "::" :|--
  (fn num as (n, _) =>
    this "int" >> K (mk_int_num n) ||
    this "real" >> K (mk_real_frac_num num)))

fun bv_number st = (this "bv" |-- bra (nat_num --| $$ ":" -- nat_num) :|--
  lookup_context (mk_bv_num o theory_of)) st

fun appl (app as (Sym (n, _), _)) = lookup_context mk_app app :|-- (fn 
    SOME app' => Scan.succeed app'
  | NONE => scan_exn ("unknown function: " ^ quote n))

fun constant st = ((sym >> rpair []) :|-- appl) st

fun expr_id st = (id :|-- (fn i => lookup_context lookup_expr i :|-- (fn
    SOME e => Scan.succeed e
  | NONE => scan_exn ("unknown term id: " ^ quote (string_of_int i))))) st

fun arg st = Scan.first [expr_id, number, bv_number, constant] st

fun application st = par ((sym -- Scan.repeat1 (sep arg)) :|-- appl) st

fun variables st = par (this "vars" |-- seps1 (par (name |-- sep sort))) st

fun patterns st = seps (par ((this ":pat" || this ":nopat") |-- seps1 id)) st

fun quant_kind st = st |> (
  this "forall" >> K (mk_forall o theory_of) ||
  this "exists" >> K (mk_exists o theory_of))

fun quantifier st =
  (par (quant_kind -- sep variables --| patterns -- sep arg) :|--
     lookup_context (fn cx => fn ((mk_q, Ts), body) => mk_q cx Ts body)) st

fun expr k =
  Scan.first [bound, quantifier, application, number, bv_number, constant] :|--
  with_context (pair NONE oo add_expr k)

fun rule_name st = ((name >> `(Symtab.lookup rule_names)) :|-- (fn 
    (SOME r, _) => Scan.succeed r
  | (NONE, n) => scan_exn ("unknown proof rule: " ^ quote n))) st

fun rule f k =
  bra (rule_name -- seps id) --| $$ ":" -- sep arg #->
  with_context (pair (f k) oo add_proof_step k)

fun decl st = (this "decl" |-- sep name --| sep (this "::") -- sep sort :|--
  with_context (pair NONE oo add_decl)) st

fun def st = (id --| sep (this ":=")) st

fun node st = st |> (
  decl ||
  def :|-- (fn k => sep (expr k) || sep (rule (K NONE) k)) ||
  rule SOME ~1)


(* overall parser *)

(* Currently, terms are parsed bottom-up (i.e., along with parsing the proof
   text line by line), but proofs are reconstructed top-down (i.e. by an
   in-order top-down traversal of the proof tree/graph).  The latter approach
   was taken because some proof texts comprise irrelevant proof steps which
   will thus not be reconstructed.  This approach might also be beneficial
   for constructing terms, but it would also increase the complexity of the
   (otherwise rather modular) code. *)

fun parse ctxt typs terms proof_text =
  make_context ctxt typs terms
  |> with_info (fold (parse_line node) proof_text)
  ||> finish

end
