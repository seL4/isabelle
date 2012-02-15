(*  Title:      HOL/Tools/SMT/z3_proof_parser.ML
    Author:     Sascha Boehme, TU Muenchen

Parser for Z3 proofs.
*)

signature Z3_PROOF_PARSER =
sig
  (*proof rules*)
  datatype rule = True_Axiom | Asserted | Goal | Modus_Ponens | Reflexivity |
    Symmetry | Transitivity | Transitivity_Star | Monotonicity | Quant_Intro |
    Distributivity | And_Elim | Not_Or_Elim | Rewrite | Rewrite_Star |
    Pull_Quant | Pull_Quant_Star | Push_Quant | Elim_Unused_Vars |
    Dest_Eq_Res | Quant_Inst | Hypothesis | Lemma | Unit_Resolution |
    Iff_True | Iff_False | Commutativity | Def_Axiom | Intro_Def | Apply_Def |
    Iff_Oeq | Nnf_Pos | Nnf_Neg | Nnf_Star | Cnf_Star | Skolemize |
    Modus_Ponens_Oeq | Th_Lemma of string list
  val string_of_rule: rule -> string

  (*proof parser*)
  datatype proof_step = Proof_Step of {
    rule: rule,
    args: cterm list,
    prems: int list,
    prop: cterm }
  val parse: Proof.context -> typ Symtab.table -> term Symtab.table ->
    string list ->
    (int * cterm) list * (int * proof_step) list * string list * Proof.context
end

structure Z3_Proof_Parser: Z3_PROOF_PARSER =
struct


(* proof rules *)

datatype rule = True_Axiom | Asserted | Goal | Modus_Ponens | Reflexivity |
  Symmetry | Transitivity | Transitivity_Star | Monotonicity | Quant_Intro |
  Distributivity | And_Elim | Not_Or_Elim | Rewrite | Rewrite_Star |
  Pull_Quant | Pull_Quant_Star | Push_Quant | Elim_Unused_Vars | Dest_Eq_Res |
  Quant_Inst | Hypothesis | Lemma | Unit_Resolution | Iff_True | Iff_False |
  Commutativity | Def_Axiom | Intro_Def | Apply_Def | Iff_Oeq | Nnf_Pos |
  Nnf_Neg | Nnf_Star | Cnf_Star | Skolemize | Modus_Ponens_Oeq |
  Th_Lemma of string list

val rule_names = Symtab.make [
  ("true-axiom", True_Axiom),
  ("asserted", Asserted),
  ("goal", Goal),
  ("mp", Modus_Ponens),
  ("refl", Reflexivity),
  ("symm", Symmetry),
  ("trans", Transitivity),
  ("trans*", Transitivity_Star),
  ("monotonicity", Monotonicity),
  ("quant-intro", Quant_Intro),
  ("distributivity", Distributivity),
  ("and-elim", And_Elim),
  ("not-or-elim", Not_Or_Elim),
  ("rewrite", Rewrite),
  ("rewrite*", Rewrite_Star),
  ("pull-quant", Pull_Quant),
  ("pull-quant*", Pull_Quant_Star),
  ("push-quant", Push_Quant),
  ("elim-unused", Elim_Unused_Vars),
  ("der", Dest_Eq_Res),
  ("quant-inst", Quant_Inst),
  ("hypothesis", Hypothesis),
  ("lemma", Lemma),
  ("unit-resolution", Unit_Resolution),
  ("iff-true", Iff_True),
  ("iff-false", Iff_False),
  ("commutativity", Commutativity),
  ("def-axiom", Def_Axiom),
  ("intro-def", Intro_Def),
  ("apply-def", Apply_Def),
  ("iff~", Iff_Oeq),
  ("nnf-pos", Nnf_Pos),
  ("nnf-neg", Nnf_Neg),
  ("nnf*", Nnf_Star),
  ("cnf*", Cnf_Star),
  ("sk", Skolemize),
  ("mp~", Modus_Ponens_Oeq),
  ("th-lemma", Th_Lemma [])]

fun string_of_rule (Th_Lemma args) = space_implode " " ("th-lemma" :: args)
  | string_of_rule r =
      let fun eq_rule (s, r') = if r = r' then SOME s else NONE 
      in the (Symtab.get_first eq_rule rule_names) end



(* certified terms and variables *)

val (var_prefix, decl_prefix) = ("v", "sk")
(*
  "decl_prefix" is for skolem constants (represented by free variables),
  "var_prefix" is for pseudo-schematic variables (schematic with respect
  to the Z3 proof, but represented by free variables).

  Both prefixes must be distinct to avoid name interferences.
  More precisely, the naming of pseudo-schematic variables must be
  context-independent modulo the current proof context to be able to
  use fast inference kernel rules during proof reconstruction.
*)

val maxidx_of = #maxidx o Thm.rep_cterm

fun mk_inst ctxt vars =
  let
    val max = fold (Integer.max o fst) vars 0
    val ns = fst (Variable.variant_fixes (replicate (max + 1) var_prefix) ctxt)
    fun mk (i, v) =
      (v, SMT_Utils.certify ctxt (Free (nth ns i, #T (Thm.rep_cterm v))))
  in map mk vars end

fun close ctxt (ct, vars) =
  let
    val inst = mk_inst ctxt vars
    val names = fold (Term.add_free_names o Thm.term_of o snd) inst []
  in (Thm.instantiate_cterm ([], inst) ct, names) end


fun mk_bound ctxt (i, T) =
  let val ct = SMT_Utils.certify ctxt (Var ((Name.uu, 0), T))
  in (ct, [(i, ct)]) end

local
  fun mk_quant1 ctxt q T (ct, vars) =
    let
      val cv =
        (case AList.lookup (op =) vars 0 of
          SOME cv => cv
        | _ => SMT_Utils.certify ctxt (Var ((Name.uu, maxidx_of ct + 1), T)))
      fun dec (i, v) = if i = 0 then NONE else SOME (i-1, v)
      val vars' = map_filter dec vars
    in (Thm.apply (SMT_Utils.instT' cv q) (Thm.lambda cv ct), vars') end

  fun quant name =
    SMT_Utils.mk_const_pat @{theory} name (SMT_Utils.destT1 o SMT_Utils.destT1)
  val forall = quant @{const_name All}
  val exists = quant @{const_name Ex}
in

fun mk_quant is_forall ctxt =
  fold_rev (mk_quant1 ctxt (if is_forall then forall else exists))

end

local
  fun prep (ct, vars) (maxidx, all_vars) =
    let
      val maxidx' = maxidx + maxidx_of ct + 1

      fun part (i, cv) =
        (case AList.lookup (op =) all_vars i of
          SOME cu => apfst (if cu aconvc cv then I else cons (cv, cu))
        | NONE =>
            let val cv' = Thm.incr_indexes_cterm maxidx cv
            in apfst (cons (cv, cv')) #> apsnd (cons (i, cv')) end)

      val (inst, vars') =
        if null vars then ([], vars)
        else fold part vars ([], [])

    in (Thm.instantiate_cterm ([], inst) ct, (maxidx', vars' @ all_vars)) end
in
fun mk_fun f ts =
  let val (cts, (_, vars)) = fold_map prep ts (0, [])
  in f cts |> Option.map (rpair vars) end
end



(* proof parser *)

datatype proof_step = Proof_Step of {
  rule: rule,
  args: cterm list,
  prems: int list,
  prop: cterm }


(** parser context **)

val not_false = Thm.cterm_of @{theory} (@{const Not} $ @{const False})

fun make_context ctxt typs terms =
  let
    val ctxt' = 
      ctxt
      |> Symtab.fold (Variable.declare_typ o snd) typs
      |> Symtab.fold (Variable.declare_term o snd) terms

    fun cert @{const True} = not_false
      | cert t = SMT_Utils.certify ctxt' t

  in (typs, Symtab.map (K cert) terms, Inttab.empty, [], [], ctxt') end

fun fresh_name n (typs, terms, exprs, steps, vars, ctxt) =
  let val (n', ctxt') = yield_singleton Variable.variant_fixes n ctxt
  in (n', (typs, terms, exprs, steps, vars, ctxt')) end

fun context_of (_, _, _, _, _, ctxt) = ctxt

fun add_decl (n, T) (cx as (_, terms, _, _, _, _)) =
  (case Symtab.lookup terms n of
    SOME _ => cx
  | NONE => cx |> fresh_name (decl_prefix ^ n)
      |> (fn (m, (typs, terms, exprs, steps, vars, ctxt)) =>
           let
             val upd = Symtab.update (n, SMT_Utils.certify ctxt (Free (m, T)))
           in (typs, upd terms, exprs, steps, vars, ctxt) end))

fun mk_typ (typs, _, _, _, _, ctxt) (s as Z3_Interface.Sym (n, _)) = 
  (case Z3_Interface.mk_builtin_typ ctxt s of
    SOME T => SOME T
  | NONE => Symtab.lookup typs n)

fun mk_num (_, _, _, _, _, ctxt) (i, T) =
  mk_fun (K (Z3_Interface.mk_builtin_num ctxt i T)) []

fun mk_app (_, terms, _, _, _, ctxt) (s as Z3_Interface.Sym (n, _), es) =
  mk_fun (fn cts =>
    (case Z3_Interface.mk_builtin_fun ctxt s cts of
      SOME ct => SOME ct
    | NONE =>
        Symtab.lookup terms n |> Option.map (Drule.list_comb o rpair cts))) es

fun add_expr k t (typs, terms, exprs, steps, vars, ctxt) =
  (typs, terms, Inttab.update (k, t) exprs, steps, vars, ctxt)

fun lookup_expr (_, _, exprs, _, _, _) = Inttab.lookup exprs

fun add_proof_step k ((r, args), prop) cx =
  let
    val (typs, terms, exprs, steps, vars, ctxt) = cx
    val (ct, vs) = close ctxt prop
    fun part (SOME e, _) (cts, ps) = (close ctxt e :: cts, ps)
      | part (NONE, i) (cts, ps) = (cts, i :: ps)
    val (args', prems) = fold (part o `(lookup_expr cx)) args ([], [])
    val (cts, vss) = split_list args'
    val step = Proof_Step {rule=r, args=rev cts, prems=rev prems,
      prop = SMT_Utils.mk_cprop ct}
    val vars' = fold (union (op =)) (vs :: vss) vars
  in (typs, terms, exprs, (k, step) :: steps, vars', ctxt) end

fun finish (_, _, _, steps, vars, ctxt) =
  let
    fun coll (p as (k, Proof_Step {prems, rule, prop, ...})) (ars, ps, ids) =
      (case rule of
        Asserted => ((k, prop) :: ars, ps, ids)
      | Goal => ((k, prop) :: ars, ps, ids)
      | _ =>
          if Inttab.defined ids k then
            (ars, p :: ps, fold (Inttab.update o rpair ()) prems ids)
          else (ars, ps, ids))

    val (ars, steps', _) = fold coll steps ([], [], Inttab.make [(~1, ())])
  in (ars, steps', vars, ctxt) end


(** core parser **)

fun parse_exn line_no msg = raise SMT_Failure.SMT (SMT_Failure.Other_Failure
  ("Z3 proof parser (line " ^ string_of_int line_no ^ "): " ^ msg))

fun scan_exn msg ((line_no, _), _) = parse_exn line_no msg

fun with_info f cx =
  (case f ((NONE, 1), cx) of
    ((SOME _, _), cx') => cx'
  | ((_, line_no), _) => parse_exn line_no "bad proof")

fun parse_line _ _ (st as ((SOME _, _), _)) = st
  | parse_line scan line ((_, line_no), cx) =
      let val st = ((line_no, cx), raw_explode line)
      in
        (case Scan.catch (Scan.finite' Symbol.stopper (Scan.option scan)) st of
          (SOME r, ((_, cx'), _)) => ((r, line_no+1), cx')
        | (NONE, _) => parse_exn line_no ("bad proof line: " ^ quote line))
      end

fun with_context f x ((line_no, cx), st) =
  let val (y, cx') = f x cx
  in (y, ((line_no, cx'), st)) end
  

fun lookup_context f x (st as ((_, cx), _)) = (f cx x, st)


(** parser combinators and parsers for basic entities **)

fun $$ s = Scan.lift (Scan.$$ s)
fun this s = Scan.lift (Scan.this_string s)
val is_blank = Symbol.is_ascii_blank
fun blank st = Scan.lift (Scan.many1 is_blank) st
fun sep scan = blank |-- scan
fun seps scan = Scan.repeat (sep scan)
fun seps1 scan = Scan.repeat1 (sep scan)
fun seps_by scan_sep scan = scan ::: Scan.repeat (scan_sep |-- scan)

val lpar = "(" and rpar = ")"
val lbra = "[" and rbra = "]"
fun par scan = $$ lpar |-- scan --| $$ rpar
fun bra scan = $$ lbra |-- scan --| $$ rbra

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
  member (op =) (raw_explode "_+*-/%~=<>$&|?!.@^#")

fun name st = (Scan.lift (Scan.many1 is_char) >> implode) st

fun sym st = (name --
  Scan.optional (bra (seps_by ($$ ":") sym)) [] >> Z3_Interface.Sym) st

fun id st = ($$ "#" |-- nat_num) st


(** parsers for various parts of Z3 proofs **)

fun sort st = Scan.first [
  this "array" |-- bra (sort --| $$ ":" -- sort) >> (op -->),
  par (this "->" |-- seps1 sort) >> ((op --->) o split_last),
  sym :|-- (fn s as Z3_Interface.Sym (n, _) => lookup_context mk_typ s :|-- (fn
    SOME T => Scan.succeed T
  | NONE => scan_exn ("unknown sort: " ^ quote n)))] st

fun bound st = (par (this ":var" |-- sep nat_num -- sep sort) :|--
  lookup_context (mk_bound o context_of)) st

fun numb (n as (i, _)) = lookup_context mk_num n :|-- (fn
    SOME n' => Scan.succeed n'
  | NONE => scan_exn ("unknown number: " ^ quote (string_of_int i)))

fun appl (app as (Z3_Interface.Sym (n, _), _)) =
  lookup_context mk_app app :|-- (fn 
      SOME app' => Scan.succeed app'
    | NONE => scan_exn ("unknown function symbol: " ^ quote n))

fun bv_size st = (digits >> (fn sz =>
  Z3_Interface.Sym ("bv", [Z3_Interface.Sym (sz, [])]))) st

fun bv_number_sort st = (bv_size :|-- lookup_context mk_typ :|-- (fn
    SOME cT => Scan.succeed cT
  | NONE => scan_exn ("unknown sort: " ^ quote "bv"))) st

fun bv_number st =
  (this "bv" |-- bra (nat_num --| $$ ":" -- bv_number_sort) :|-- numb) st

fun frac_number st = (
  int_num --| $$ "/" -- int_num --| this "::" -- sort :|-- (fn ((i, j), T) =>
    numb (i, T) -- numb (j, T) :|-- (fn (n, m) =>
      appl (Z3_Interface.Sym ("/", []), [n, m])))) st

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

val ctrue = Thm.cterm_of @{theory} @{const True}

fun pattern st = par (this "pattern" |-- Scan.repeat1 (sep arg) >>
  (the o mk_fun (K (SOME ctrue)))) st

fun quant_kind st = st |> (
  this "forall" >> K (mk_quant true o context_of) ||
  this "exists" >> K (mk_quant false o context_of))

fun quantifier st =
  (par (quant_kind -- sep variables --| pats -- sep arg) :|--
     lookup_context (fn cx => fn ((mk_q, Ts), body) => mk_q cx Ts body)) st

fun expr k =
  Scan.first [bound, quantifier, pattern, application, number, constant] :|--
  with_context (pair NONE oo add_expr k)

val rule_arg = id
  (* if this is modified, then 'th_lemma_arg' needs reviewing *)

fun th_lemma_arg st = Scan.unless (sep rule_arg >> K "" || $$ rbra) (sep name) st

fun rule_name st = ((name >> `(Symtab.lookup rule_names)) :|-- (fn 
    (SOME (Th_Lemma _), _) => Scan.repeat th_lemma_arg >> Th_Lemma
  | (SOME r, _) => Scan.succeed r
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


(** overall parser **)

(*
  Currently, terms are parsed bottom-up (i.e., along with parsing the proof
  text line by line), but proofs are reconstructed top-down (i.e. by an
  in-order top-down traversal of the proof tree/graph).  The latter approach
  was taken because some proof texts comprise irrelevant proof steps which
  will thus not be reconstructed.  This approach might also be beneficial
  for constructing terms, but it would also increase the complexity of the
  (otherwise rather modular) code.
*)

fun parse ctxt typs terms proof_text =
  make_context ctxt typs terms
  |> with_info (fold (parse_line node) proof_text)
  |> finish

end
