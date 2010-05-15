(*  Title:      HOL/Tools/SMT/z3_proof_parser.ML
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

structure I = Z3_Interface



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

val (var_prefix, decl_prefix) = ("v", "sk")
(* "decl_prefix" is for skolem constants (represented by free variables)
   "var_prefix" is for pseudo-schematic variables (schematic with respect
     to the Z3 proof, but represented by free variables)

     Both prefixes must be distinct to avoid name interferences.
   More precisely, the naming of pseudo-schematic variables must be
   context-independent modulo the current proof context to be able to
   use fast inference kernel rules during proof reconstruction. *)

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
      fun dec (i, v) = if i = 0 then NONE else SOME (i-1, v)
    in (Thm.capply (I.instT' cv q) (Thm.cabs cv ct), map_filter dec vars) end

  val forall = I.mk_inst_pair (I.destT1 o I.destT1) @{cpat All}
  val exists = I.mk_inst_pair (I.destT1 o I.destT1) @{cpat Ex}
in
fun mk_forall thy = fold_rev (mk_quant thy forall)
fun mk_exists thy = fold_rev (mk_quant thy exists)
end


local
  fun equal_var cv (_, cu) = (cv aconvc cu)

  fun prep (ct, vars) (maxidx, all_vars) =
    let
      val maxidx' = maxidx_of ct + maxidx + 1

      fun part (v as (i, cv)) =
        (case AList.lookup (op =) all_vars i of
          SOME cu => apfst (if cu aconvc cv then I else cons (cv, cu))
        | NONE =>
            if not (exists (equal_var cv) all_vars) then apsnd (cons v)
            else
              let val cv' = Thm.incr_indexes_cterm maxidx' cv
              in apfst (cons (cv, cv')) #> apsnd (cons (i, cv')) end)

      val (inst, vars') =
        if null vars then ([], vars)
        else fold part vars ([], [])

    in (Thm.instantiate_cterm ([], inst) ct, (maxidx', vars' @ all_vars)) end
in
fun mk_fun f ts =
  let val (cts, (_, vars)) = fold_map prep ts (~1, [])
  in f cts |> Option.map (rpair vars) end
end



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

fun add_decl (n, T) (cx as (_, terms, _, _, _, _)) =
  (case Symtab.lookup terms n of
    SOME _ => cx
  | NONE => cx |> fresh_name (decl_prefix ^ n)
      |> (fn (m, (typs, terms, exprs, steps, vars, ctxt)) =>
           let val upd = Symtab.update (n, certify ctxt (Free (m, T)))
           in (typs, upd terms, exprs, steps, vars, ctxt) end))

fun mk_typ (typs, _, _, _, _, ctxt) (s as I.Sym (n, _)) = 
  (case I.mk_builtin_typ ctxt s of
    SOME T => SOME T
  | NONE => Symtab.lookup typs n)

fun mk_num (_, _, _, _, _, ctxt) (i, T) =
  mk_fun (K (I.mk_builtin_num ctxt i T)) []

fun mk_app (_, terms, _, _, _, ctxt) (s as I.Sym (n, _), es) =
  mk_fun (fn cts =>
    (case I.mk_builtin_fun ctxt s cts of
      SOME ct => SOME ct
    | NONE =>
        Symtab.lookup terms n |> Option.map (Drule.list_comb o rpair cts))) es

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

fun digits st = (Scan.lift (Scan.many1 Symbol.is_ascii_digit) >> implode) st
fun nat_num st = (Scan.lift (Scan.repeat1 (Scan.some digit)) >> (fn ds =>
  fold (fn d => fn i => i * 10 + d) ds 0)) st
fun int_num st = (Scan.optional ($$ "-" >> K (fn i => ~i)) I :|--
  (fn sign => nat_num >> sign)) st

val is_char = Symbol.is_ascii_letter orf Symbol.is_ascii_digit orf
  member (op =) (explode "_+*-/%~=<>$&|?!.@^#")
fun name st = (Scan.lift (Scan.many1 is_char) >> implode) st

fun sym st =
  (name -- Scan.optional (bra (seps_by ($$ ":") sym)) [] >> I.Sym) st

fun id st = ($$ "#" |-- nat_num) st


(* parsers for various parts of Z3 proofs *)

fun sort st = Scan.first [
  this "array" |-- bra (sort --| $$ ":" -- sort) >> (op -->),
  par (this "->" |-- seps1 sort) >> ((op --->) o split_last),
  sym :|-- (fn s as I.Sym (n, _) => lookup_context mk_typ s :|-- (fn
    SOME T => Scan.succeed T
  | NONE => scan_exn ("unknown sort: " ^ quote n)))] st

fun bound st = (par (this ":var" |-- sep nat_num -- sep sort) :|--
  lookup_context (mk_bound o theory_of)) st

fun numb (n as (i, _)) = lookup_context mk_num n :|-- (fn
    SOME n' => Scan.succeed n'
  | NONE => scan_exn ("unknown number: " ^ quote (string_of_int i)))

fun appl (app as (I.Sym (n, _), _)) = lookup_context mk_app app :|-- (fn 
    SOME app' => Scan.succeed app'
  | NONE => scan_exn ("unknown function symbol: " ^ quote n))

fun bv_size st = (digits >> (fn sz => I.Sym ("bv", [I.Sym (sz, [])]))) st

fun bv_number_sort st = (bv_size :|-- lookup_context mk_typ :|-- (fn
    SOME cT => Scan.succeed cT
  | NONE => scan_exn ("unknown sort: " ^ quote "bv"))) st

fun bv_number st =
  (this "bv" |-- bra (nat_num --| $$ ":" -- bv_number_sort) :|-- numb) st

fun frac_number st = (
  int_num --| $$ "/" -- int_num --| this "::" -- sort :|-- (fn ((i, j), T) =>
    numb (i, T) -- numb (j, T) :|-- (fn (n, m) =>
      appl (I.Sym ("/", []), [n, m])))) st

fun plain_number st = (int_num --| this "::" -- sort :|-- numb) st

fun number st = Scan.first [bv_number, frac_number, plain_number] st

fun constant st = ((sym >> rpair []) :|-- appl) st

fun expr_id st = (id :|-- (fn i => lookup_context lookup_expr i :|-- (fn
    SOME e => Scan.succeed e
  | NONE => scan_exn ("unknown term id: " ^ quote (string_of_int i))))) st

fun arg st = Scan.first [expr_id, number, constant] st

fun application st = par ((sym -- Scan.repeat1 (sep arg)) :|-- appl) st

fun variables st = par (this "vars" |-- seps1 (par (name |-- sep sort))) st

fun pats st = seps (par ((this ":pat" || this ":nopat") |-- seps1 id)) st

fun pattern st = par (this "pattern" |-- Scan.repeat1 (sep arg) >>
  (the o mk_fun (K (SOME @{cterm True})))) st

fun quant_kind st = st |> (
  this "forall" >> K (mk_forall o theory_of) ||
  this "exists" >> K (mk_exists o theory_of))

fun quantifier st =
  (par (quant_kind -- sep variables --| pats -- sep arg) :|--
     lookup_context (fn cx => fn ((mk_q, Ts), body) => mk_q cx Ts body)) st

fun expr k =
  Scan.first [bound, quantifier, pattern, application, number, constant] :|--
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
