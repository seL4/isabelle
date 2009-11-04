(*  Title:      HOL/SMT/Tools/z3_proof.ML
    Author:     Sascha Boehme, TU Muenchen

Proof reconstruction for proofs found by Z3.
*)

signature Z3_PROOF =
sig
  val reconstruct: Proof.context -> thm list option -> SMT_Translate.recon ->
    string list -> thm
end

structure Z3_Proof: Z3_PROOF =
struct

structure T = Z3_Proof_Terms
structure R = Z3_Proof_Rules

fun z3_exn msg = raise SMT_Solver.SMT ("Z3 proof reconstruction: " ^ msg)


fun lift f (x, y) = apsnd (pair x) (f y)
fun lift' f v (x, y) = apsnd (rpair y) (f v x)

fun $$ s = lift (Scan.$$ s)
fun this s = lift (Scan.this_string s)

fun blank s = lift (Scan.many1 Symbol.is_ascii_blank) s

fun par scan = $$ "(" |-- scan --| $$ ")"
fun bra scan = $$ "[" |-- scan --| $$ "]"

val digit = (fn
  "0" => SOME 0 | "1" => SOME 1 | "2" => SOME 2 | "3" => SOME 3 |
  "4" => SOME 4 | "5" => SOME 5 | "6" => SOME 6 | "7" => SOME 7 |
  "8" => SOME 8 | "9" => SOME 9 | _ => NONE)

val nat_num = Scan.repeat1 (Scan.some digit) >>
  (fn ds => fold (fn d => fn i => i * 10 + d) ds 0)
val int_num = Scan.optional (Scan.$$ "-" >> K (fn i => ~i)) I :|--
  (fn sign => nat_num >> sign)

val is_char = Symbol.is_ascii_letter orf Symbol.is_ascii_digit orf
  member (op =) (explode "_+*-/%~=<>$&|?!.@^#")
val name = Scan.many1 is_char >> implode

datatype sym = Sym of string * sym list

datatype context = Context of {
  Ttab: typ Symtab.table,
  ttab: cterm Symtab.table,
  etab: T.preterm Inttab.table,
  ptab: R.proof Inttab.table,
  nctxt: Name.context }

fun make_context (Ttab, ttab, etab, ptab, nctxt) =
  Context {Ttab=Ttab, ttab=ttab, etab=etab, ptab=ptab, nctxt=nctxt}

fun empty_context thy ({typs, terms=ttab} : SMT_Translate.recon) =
  let
    val ttab' = Symtab.map (fn @{term True} => @{term "~False"} | t => t) ttab
    val ns = Symtab.fold (Term.add_free_names o snd) ttab' []
    val nctxt = Name.make_context ns
    val tt = Symtab.map (Thm.cterm_of thy) ttab'
  in make_context (typs, tt, Inttab.empty, Inttab.empty, nctxt) end

fun map_context f (Context {Ttab, ttab, etab, ptab, nctxt}) =
  make_context (f (Ttab, ttab, etab, ptab, nctxt))

fun map_type_tab f = map_context (fn (Ttab, ttab, etab, ptab, nctxt) =>
  (f Ttab, ttab, etab, ptab, nctxt))

fun map_term_tab f = map_context (fn (Ttab, ttab, etab, ptab, nctxt) =>
  (Ttab, f ttab, etab, ptab, nctxt))

fun map_expr_tab f = map_context (fn (Ttab, ttab, etab, ptab, nctxt) =>
  (Ttab, ttab, f etab, ptab, nctxt))

fun map_proof_tab f = map_context (fn (Ttab, ttab, etab, ptab, nctxt) =>
  (Ttab, ttab, etab, f ptab, nctxt))

val free_prefix = "f"

fun fresh_name (cx as Context {nctxt, ...}) =
  let val (n, nctxt') = yield_singleton Name.variants free_prefix nctxt
  in
    (n, map_context (fn (Ttab, ttab, etab, ptab, _) =>
      (Ttab, ttab, etab, ptab, nctxt')) cx)
  end

fun typ_of_sort name (cx as Context {Ttab, ...}) =
  (case Symtab.lookup Ttab name of
    SOME T => (T, cx)
  | _ => cx |> fresh_name |-> (fn n =>
      let val T = TFree ("'" ^ n, @{sort type})
      in pair T o map_type_tab (Symtab.update (name, T)) end))

fun lookup_expr id (cx as Context {etab, ...}) =
  (case Inttab.lookup etab id of
    SOME e => (e, cx)
  | _ => z3_exn ("unknown term id: " ^ quote (string_of_int id)))

fun add_expr k t = map_expr_tab (Inttab.update (k, t))

fun add_proof thy k ((r, ps), t) (cx as Context {nctxt, ...}) =
  let val p = R.make_proof r ps (T.compile thy nctxt t)
  in (k, map_proof_tab (Inttab.update (k, p)) cx) end

fun mk_app app (cx as Context {ttab, ...}) =
  let
    val mk = 
      (fn
        (Sym ("true", _), _) => T.mk_true
      | (Sym ("false", _), _) => T.mk_false
      | (Sym ("=", _), [t, u]) => T.mk_eq t u
      | (Sym ("distinct", _), ts) => T.mk_distinct ts
      | (Sym ("ite", _), [s, t, u]) => T.mk_if s t u
      | (Sym ("and", _), ts) => T.mk_and ts
      | (Sym ("or", _), ts) => T.mk_or ts
      | (Sym ("iff", _), [t, u]) => T.mk_iff t u
      | (Sym ("xor", _), [t, u]) => T.mk_not (T.mk_iff t u)
      | (Sym ("not", _), [t]) => T.mk_not t
      | (Sym ("implies", _), [t, u]) => T.mk_implies t u
      | (Sym ("~", _), [t, u]) => T.mk_eq t u
      | (Sym ("<", _), [t, u]) => T.mk_lt t u
      | (Sym ("<=", _), [t, u]) => T.mk_le t u
      | (Sym (">", _), [t, u]) => T.mk_lt u t
      | (Sym (">=", _), [t, u]) => T.mk_le u t
      | (Sym ("+", _), [t, u]) => T.mk_add t u
      | (Sym ("-", _), [t, u]) => T.mk_sub t u
      | (Sym ("-", _), [t]) => T.mk_uminus t
      | (Sym ("*", _), [t, u]) => T.mk_mul t u
      | (Sym ("/", _), [t, u]) => T.mk_real_div t u
      | (Sym ("div", _), [t, u]) => T.mk_int_div t u
      | (Sym ("mod", _), [t, u]) => T.mk_mod t u
      | (Sym ("rem", _), [t, u]) => T.mk_rem t u
      | (Sym ("select", _), [m, k]) => T.mk_access m k
      | (Sym ("store", _), [m, k, v]) => T.mk_update m k v
      | (Sym ("pattern", _), _) => T.mk_true
      | (Sym (n, _), ts) =>
          (case Symtab.lookup ttab n of
            SOME ct => T.mk_fun ct ts
          | NONE => z3_exn ("unknown function: " ^ quote n)))
  in (mk app, cx) end

fun add_decl thy (n, T) (cx as Context {ttab, ...}) =
  (case Symtab.lookup ttab n of
    SOME _ => cx
  | _ => cx |> fresh_name |-> (fn n' =>
      map_term_tab (Symtab.update (n, Thm.cterm_of thy (Free (n', T))))))


fun sep scan_sep scan = scan ::: Scan.repeat (scan_sep |-- scan)
fun bsep scan = Scan.repeat (blank |-- scan)
fun bsep1 scan = Scan.repeat1 (blank |-- scan)

val id = Scan.$$ "#" |-- int_num

fun sym s =
  (lift name -- Scan.optional (bra (sep ($$ ":") sym)) [] >> Sym) s

fun sort st = Scan.first [
  this "bool" >> K @{typ bool},
  this "int" >> K @{typ int},
  this "real" >> K @{typ real},
  this "bv" |-- bra (lift int_num) >> T.wordT,
  this "array" |-- bra (sort --| $$ ":" -- sort) >> (op -->),
  par (this "->" |-- bsep1 sort) >> ((op --->) o split_last),
  lift name #-> lift' typ_of_sort] st

fun bound thy =
  par (this ":var" -- blank |-- lift int_num --| blank -- sort) >>
  uncurry (T.mk_bound thy)

val number = 
  int_num -- Scan.option (Scan.$$ "/" |-- int_num) --|
  Scan.this_string "::" :|-- (fn num as (n, _) =>
    Scan.this_string "int" >> K (T.mk_int_num n) ||
    Scan.this_string "real" >> K (T.mk_real_frac_num num))

fun bv_number thy =
  this "bv" |-- bra (lift (int_num --| Scan.$$ ":" -- int_num)) >>
  uncurry (T.mk_bv_num thy)

val constant = sym #-> lift' (mk_app o rpair [])

fun arg thy = Scan.first [lift id #-> lift' lookup_expr,
  lift number, bv_number thy, constant]

fun application thy =
  par (sym -- bsep1 (arg thy)) #-> lift' mk_app

val variables =
  par (this "vars" |-- bsep1 (par ((lift name >> K "x") --| blank -- sort)))
fun patterns st =
  bsep (par ((this ":pat" || this ":nopat") |-- bsep1 (lift id))) st
fun quant_kind st =
 (this "forall" >> K T.mk_forall ||
  this "exists" >> K T.mk_exists) st
fun quantifier thy = par (quant_kind --| blank --
  variables --| patterns --| blank -- arg thy) >>
  (fn ((q, vs), body) => fold_rev (q thy) vs body)

fun expr thy k = Scan.first [bound thy, quantifier thy, application thy,
  lift number, bv_number thy, constant] #-> apfst o add_expr k

fun rule_name name =
  (case R.rule_of_string name of
    SOME r => r
  | NONE => z3_exn ("unknown proof rule: " ^ quote name))

fun rule thy k =
  bra (lift (name >> rule_name) -- bsep (lift id)) --|
  ($$ ":" -- blank) -- arg thy #-> lift' (add_proof thy k)

fun decl thy = ((this "decl" -- blank) |-- lift name --|
  (blank -- this "::" -- blank) -- sort) #-> apfst o add_decl thy

fun def st = (lift id --| (blank -- this ":=" -- blank)) st

fun node thy =
  decl thy #> pair NONE ||
  def :|-- (fn k => expr thy k #> pair NONE || rule thy k #>> K NONE) ||
  rule thy ~1 #>> SOME

fun handle_errors line_no scan (st as (_, xs)) =
  (case try scan st of
    SOME y => y
  | NONE => z3_exn ("parse error at line " ^ string_of_int line_no ^ ": " ^
      quote (implode xs)))

fun parse_line thy l (st as (stop, line_no, cx)) =
  if is_some stop then st
  else
    (cx, explode l)
    |> handle_errors line_no (Scan.finite' Symbol.stopper (node thy))
    |> (fn (stop', (cx', _)) => (stop', line_no + 1, cx'))

fun reconstruct ctxt assms recon output =
  let
    val _ = T.var_prefix <> free_prefix orelse error "Same prefixes"

    val thy = ProofContext.theory_of ctxt
  in
    (case fold (parse_line thy) output (NONE, 1, empty_context thy recon) of
      (SOME p, _, Context {ptab, ...}) => R.prove ctxt assms ptab p
    | _ => z3_exn "bad proof")
  end

end
