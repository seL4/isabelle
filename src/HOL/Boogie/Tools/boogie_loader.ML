(*  Title:      HOL/Boogie/Tools/boogie_loader.ML
    Author:     Sascha Boehme, TU Muenchen

Loading and interpreting Boogie-generated files.
*)

signature BOOGIE_LOADER =
sig
  val load_b2i: bool -> Path.T -> theory -> theory
end

structure Boogie_Loader: BOOGIE_LOADER =
struct

fun log verbose text args thy =
  if verbose
  then (Pretty.writeln (Pretty.big_list text (map Pretty.str args)); thy)
  else thy

val isabelle_name =
  let 
    fun purge s = if Symbol.is_letdig s then s else
      (case s of
        "." => "_o_"
      | "_" => "_n_"
      | "$" => "_S_"
      | "@" => "_G_"
      | "#" => "_H_"
      | "^" => "_T_"
      | _   => ("_" ^ string_of_int (ord s) ^ "_"))
  in prefix "b_" o translate_string purge end

datatype attribute_value = StringValue of string | TermValue of Term.term



local
  fun lookup_type_name thy name arity =
    let val intern = Sign.intern_type thy name
    in
      if Sign.declared_tyname thy intern
      then
        if Sign.arity_number thy intern = arity then SOME intern
        else error ("Boogie: type already declared with different arity: " ^
          quote name)
      else NONE
    end

  fun declare (name, arity) thy =
    let val isa_name = isabelle_name name
    in
      (case lookup_type_name thy isa_name arity of
        SOME type_name => ((type_name, false), thy)
      | NONE =>
          let
            val bname = Binding.name isa_name
            val args = Name.variant_list [] (replicate arity "'")
            val (T, thy') =
              ObjectLogic.typedecl (Binding.name isa_name, args, NoSyn) thy
            val type_name = fst (Term.dest_Type T)
          in ((type_name, true), thy') end)
    end

  fun type_names ((name, _), (new_name, new)) =
    if new then SOME (new_name ^ " (was " ^ name ^ ")") else NONE
in
fun declare_types verbose tys =
  fold_map declare tys #-> (fn tds =>
  log verbose "Declared types:" (map_filter type_names (tys ~~ tds)) #>
  rpair (Symtab.make (map fst tys ~~ map fst tds)))
end



local
  val quote_mixfix =
    Symbol.explode #> map
      (fn "_" => "'_"
        | "(" => "'("
        | ")" => "')"
        | "/" => "'/"
        | s => s) #>
    implode

  fun mk_syntax name i =
    let
      val syn = quote_mixfix name
      val args = concat (separate ",/ " (replicate i "_"))
    in
      if i = 0 then Mixfix (syn, [], 1000)
      else Mixfix (syn ^ "()'(/" ^ args ^ "')", replicate i 0, 1000)
    end

  fun process_attributes T =
    let
      fun const name = SOME (Const (name, T))

      fun choose builtin =
        (case builtin of
          "bvnot" => const @{const_name z3_bvnot}
        | "bvand" => const @{const_name z3_bvand}
        | "bvor" => const @{const_name z3_bvor}
        | "bvxor" => const @{const_name z3_bvxor}
        | "bvadd" => const @{const_name z3_bvadd}
        | "bvneg" => const @{const_name z3_bvneg}
        | "bvsub" => const @{const_name z3_bvsub}
        | "bvmul" => const @{const_name z3_bvmul}
        | "bvudiv" => const @{const_name z3_bvudiv}
        | "bvurem" => const @{const_name z3_bvurem}
        | "bvsdiv" => const @{const_name z3_bvsdiv}
        | "bvsrem" => const @{const_name z3_bvsrem}
        | "bvshl" => const @{const_name z3_bvshl}
        | "bvlshr" => const @{const_name z3_bvlshr}
        | "bvashr" => const @{const_name z3_bvashr}
        | "bvult" => const @{const_name z3_bvult}
        | "bvule" => const @{const_name z3_bvule}
        | "bvugt" => const @{const_name z3_bvugt}
        | "bvuge" => const @{const_name z3_bvuge}
        | "bvslt" => const @{const_name z3_bvslt}
        | "bvsle" => const @{const_name z3_bvsle}
        | "bvsgt" => const @{const_name z3_bvsgt}
        | "bvsge" => const @{const_name z3_bvsge}
        | "sign_extend" => const @{const_name z3_sign_extend}
        | _ => NONE)

      fun is_builtin att =
        (case att of
          ("bvbuiltin", [StringValue builtin]) => choose builtin
        | ("bvint", [StringValue "ITE"]) => const @{const_name If}
        | _ => NONE)
    in get_first is_builtin end

  fun lookup_const thy name T =
    let
      val intern = Sign.intern_const thy name
      val is_type_instance = Type.typ_instance o Sign.tsig_of
    in
      if Sign.declared_const thy intern
      then
        if is_type_instance thy (T, Sign.the_const_type thy intern)
        then SOME (Const (intern, T))
        else error ("Boogie: function already declared with different type: " ^
          quote name)
      else NONE
    end

  fun declare (name, ((Ts, T), atts)) thy =
    let val isa_name = isabelle_name name and U = Ts ---> T
    in
      (case lookup_const thy isa_name U of
        SOME t => (((name, t), false), thy)
      | NONE => 
          (case process_attributes U atts of
            SOME t => (((name, t), false), thy)
          | NONE =>
              thy
              |> Sign.declare_const ((Binding.name isa_name, U),
                   mk_syntax name (length Ts))
              |> apfst (rpair true o pair name)))
    end

  fun const_names ((name, _), ((_, t), new)) =
    if new then SOME (fst (Term.dest_Const t) ^ " (as " ^ name ^ ")") else NONE
in
fun declare_functions verbose fns =
  fold_map declare fns #-> (fn fds =>
  log verbose "Declared constants:" (map_filter const_names (fns ~~ fds)) #>
  rpair (Symtab.make (map fst fds)))
end



local
  fun name_axioms axs =
    let fun mk_name idx = "axiom_" ^ string_of_int (idx + 1)
    in map_index (fn (idx, t) => (mk_name idx, HOLogic.mk_Trueprop t)) axs end

  fun only_new_boogie_axioms thy =
    let val baxs = map Thm.prop_of (Boogie_Axioms.get (ProofContext.init thy))
    in filter_out (member (op aconv) baxs o snd) end
in
fun add_axioms verbose axs thy =
  let val axs' = only_new_boogie_axioms thy (name_axioms axs)
  in
    thy
    |> PureThy.add_axioms (map (rpair [] o apfst Binding.name) axs')
    |-> Context.theory_map o fold Boogie_Axioms.add_thm
    |> log verbose "The following axioms were added:" (map fst axs')
    |> Context.theory_map (fn context => fold Split_VC_SMT_Rules.add_thm
         (Boogie_Axioms.get (Context.proof_of context)) context)
  end
end



fun add_vcs verbose vcs thy =
  let
    val reused = duplicates (op =) (map (fst o fst) vcs)
    fun rename (n, i) = isabelle_name n ^
      (if member (op =) reused n then "_" ^ string_of_int i else "")

    fun decorate (name, t) = (rename name, HOLogic.mk_Trueprop t)
    val vcs' = map decorate vcs
  in
    thy
    |> Boogie_VCs.set vcs'
    |> log verbose "The following verification conditions were loaded:"
         (map fst vcs')
  end



local
  fun mk_bitT i T =
    if i = 0
    then Type (@{type_name "Numeral_Type.bit0"}, [T])
    else Type (@{type_name "Numeral_Type.bit1"}, [T])

  fun mk_binT size = 
    if size = 0 then @{typ "Numeral_Type.num0"}
    else if size = 1 then @{typ "Numeral_Type.num1"}
    else let val (q, r) = Integer.div_mod size 2 in mk_bitT r (mk_binT q) end
in
fun mk_wordT size =
  if size >= 0 then Type (@{type_name "word"}, [mk_binT size])
  else raise TYPE ("mk_wordT: " ^ quote (string_of_int size), [], [])
end

local
  fun dest_binT T =
    (case T of
      Type (@{type_name "Numeral_Type.num0"}, _) => 0
    | Type (@{type_name "Numeral_Type.num1"}, _) => 1
    | Type (@{type_name "Numeral_Type.bit0"}, [T]) => 2 * dest_binT T
    | Type (@{type_name "Numeral_Type.bit1"}, [T]) => 1 + 2 * dest_binT T
    | _ => raise TYPE ("dest_binT", [T], []))
in
val dest_wordT = (fn
    Type (@{type_name "word"}, [T]) => dest_binT T
  | T => raise TYPE ("dest_wordT", [T], []))
end

fun mk_arrayT (Ts, T) = Type (@{type_name "fun"}, [HOLogic.mk_tupleT Ts, T])



datatype token = Token of string | Newline | EOF

fun tokenize path =
  let
    fun blank c = (c = #" " orelse c = #"\t" orelse c = #"\n" orelse c = #"\r")
    fun split line (i, tss) = (i + 1,
      map (pair i) (map Token (String.tokens blank line) @ [Newline]) :: tss)
  in apsnd (flat o rev) (File.fold_lines split path (1, [])) end

fun stopper i = Scan.stopper (K (i, EOF)) (fn (_, EOF) => true | _ => false)

fun scan_err msg [] = "Boogie (at end of input): " ^ msg
  | scan_err msg ((i, _) :: _) = "Boogie (at line " ^ string_of_int i ^ "): " ^
      msg

fun scan_fail msg = Scan.fail_with (scan_err msg)

fun finite scan path =
  let val (i, ts) = tokenize path
  in
    (case Scan.error (Scan.finite (stopper i) scan) ts of
      (x, []) => x
    | (_, ts) => error (scan_err "unparsed input" ts))
  end

fun read_int' s = (case read_int (explode s) of (i, []) => SOME i | _ => NONE)

fun $$$ s = Scan.one (fn (_, Token s') => s = s' | _ => false)
val str = Scan.some (fn (_, Token s) => SOME s | _ => NONE)
val num = Scan.some (fn (_, Token s) => read_int' s | _ => NONE)

fun scan_line key scan =
  $$$ key |-- scan --| Scan.one (fn (_, Newline) => true | _ => false)
fun scan_line' key = scan_line key (Scan.succeed ())

fun scan_count scan i =
  if i > 0 then scan ::: scan_count scan (i - 1) else Scan.succeed []

fun scan_lookup kind tab key =
  (case Symtab.lookup tab key of
    SOME value => Scan.succeed value
  | NONE => scan_fail ("undefined " ^ kind ^ ": " ^ quote key))

fun typ tds =
  let
    fun tp st =
     (scan_line' "bool" >> K @{typ bool} ||
      scan_line' "int" >> K @{typ int} ||
      scan_line "bv" num >> mk_wordT ||
      scan_line "type-con" (str -- num) :|-- (fn (name, arity) =>
        scan_lookup "type constructor" tds name -- scan_count tp arity >>
        Type) ||
      scan_line "array" num :|-- (fn arity =>
        scan_count tp (arity - 1) -- tp >> mk_arrayT) ||
      scan_fail "illegal type") st
  in tp end

local
  fun mk_nary _ t [] = t
    | mk_nary f _ (t :: ts) = fold f ts t

  fun mk_distinct T ts =
    Const (@{const_name distinct}, HOLogic.listT T --> @{typ bool}) $ 
      HOLogic.mk_list T ts

  fun quant name f = scan_line name (num -- num -- num) >> pair f
  val quants =
    quant "forall" HOLogic.all_const ||
    quant "exists" HOLogic.exists_const ||
    scan_fail "illegal quantifier kind"
  fun mk_quant q (n, T) t = q T $ Term.absfree (isabelle_name n, T, t)

  val patternT = @{typ pattern}
  fun mk_pattern _ [] = raise TERM ("mk_pattern", [])
    | mk_pattern n [t] = Const (n, Term.fastype_of t --> patternT) $ t
    | mk_pattern n (t :: ts) =
        let val T = patternT --> Term.fastype_of t --> patternT
        in Const (@{const_name andpat}, T) $ mk_pattern n ts $ t end
  fun patt n c scan =
    scan_line n num :|-- scan_count scan >> (mk_pattern c)
  fun pattern scan =
    patt "pat" @{const_name pat} scan ||
    patt "nopat" @{const_name nopat} scan ||
    scan_fail "illegal pattern kind"
  fun mk_trigger [] t = t
    | mk_trigger ps t = @{term trigger} $ HOLogic.mk_list patternT ps $ t

  val label_kind =
    $$$ "pos" >> K @{term block_at} ||
    $$$ "neg" >> K @{term assert_at} ||
    scan_fail "illegal label kind"

  fun mk_select (m, k) =
    let
      val mT = Term.fastype_of m and kT = Term.fastype_of k
      val vT = Term.range_type mT
    in Const (@{const_name boogie_select}, mT --> kT --> vT) $ m $ k end

  fun mk_store ((m, k), v) =
    let
      val mT = Term.fastype_of m and kT = Term.fastype_of k
      val vT = Term.fastype_of v
    in
      Const (@{const_name boogie_store}, mT --> kT --> vT --> mT) $ m $ k $ v
    end
  
  fun mk_extract ((msb, lsb), t) =
    let
      val dT = Term.fastype_of t and rT = mk_wordT (msb - lsb)
      val nT = @{typ nat}
      val mk_nat_num = HOLogic.mk_number @{typ nat}
      val m = HOLogic.mk_number @{typ nat}
    in
      Const (@{const_name boogie_bv_extract}, [nT, nT, dT] ---> rT) $
        mk_nat_num msb $ mk_nat_num lsb $ t
    end

  fun mk_concat (t1, t2) =
    let
      val T1 = Term.fastype_of t1 and T2 = Term.fastype_of t2
      val U = mk_wordT (dest_wordT T1 + dest_wordT T2)
    in Const (@{const_name boogie_bv_concat}, [T1, T2] ---> U) $ t1 $ t2 end
in
fun expr tds fds =
  let
    fun binop t (u1, u2) = t $ u1 $ u2
    fun binexp s f = scan_line' s |-- exp -- exp >> f

    and exp st =
     (scan_line' "true" >> K @{term True} ||
      scan_line' "false" >> K @{term False} ||
      scan_line' "not" |-- exp >> HOLogic.mk_not ||
      scan_line "and" num :|-- scan_count exp >> 
        mk_nary (curry HOLogic.mk_conj) @{term True} ||
      scan_line "or" num :|-- scan_count exp >>
        mk_nary (curry HOLogic.mk_disj) @{term False} ||
      binexp "implies" (binop @{term "op -->"}) ||
      scan_line "distinct" num :|-- scan_count exp >>
        (fn [] => @{term True}
          | ts as (t :: _) => mk_distinct (Term.fastype_of t) ts) ||
      binexp "=" HOLogic.mk_eq ||
      scan_line "var" str -- typ tds >> (Free o apfst isabelle_name) ||
      scan_line "fun" (str -- num) :|-- (fn (name, arity) =>
        scan_lookup "constant" fds name -- scan_count exp arity >>
        Term.list_comb) ||
      quants :|-- (fn (q, ((n, k), i)) =>
        scan_count (scan_line "var" str -- typ tds) n --
        scan_count (pattern exp) k --
        scan_count (attribute tds fds) i --
        exp >> (fn (((vs, ps), _), t) =>
          fold_rev (mk_quant q) vs (mk_trigger ps t))) ||
      scan_line "label" (label_kind -- num -- num) -- exp >>
        (fn (((l, line), col), t) =>
          if line = 0 orelse col = 0 then t
          else l $ Free ("L_" ^ string_of_int line ^ "_" ^ string_of_int col,
            @{typ bool}) $ t) ||
      scan_line "int-num" num >> HOLogic.mk_number @{typ int} ||
      binexp "<" (binop @{term "op < :: int => _"}) ||
      binexp "<=" (binop @{term "op <= :: int => _"}) ||
      binexp ">" (binop @{term "op < :: int => _"} o swap) ||
      binexp ">=" (binop @{term "op <= :: int => _"} o swap) ||
      binexp "+" (binop @{term "op + :: int => _"}) ||
      binexp "-" (binop @{term "op + :: int => _"}) ||
      binexp "*" (binop @{term "op + :: int => _"}) ||
      binexp "/" (binop @{term boogie_div}) ||
      binexp "%" (binop @{term boogie_mod}) ||
      scan_line "select" num :|-- (fn arity =>
        exp -- (scan_count exp (arity - 1) >> HOLogic.mk_tuple) >>
          mk_select) ||
      scan_line "store" num :|-- (fn arity =>
        exp -- (scan_count exp (arity - 2) >> HOLogic.mk_tuple) -- exp >> 
          mk_store) ||
      scan_line "bv-num" (num -- num) >> (fn (size, i) =>
        HOLogic.mk_number (mk_wordT size) i) ||
      scan_line "bv-extract" (num -- num) -- exp >> mk_extract ||
      binexp "bv-concat" mk_concat ||
      scan_fail "illegal expression") st
  in exp end

and attribute tds fds =
  let
    val attr_val = 
      scan_line' "expr-attr" |-- expr tds fds >> TermValue ||
      scan_line "string-attr" (Scan.repeat1 str) >>
        (StringValue o space_implode " ") ||
      scan_fail "illegal attribute value"
  in
    scan_line "attribute" (str -- num) :|-- (fn (name, i) =>
      scan_count attr_val i >> pair name) ||
    scan_fail "illegal attribute"
  end
end

fun type_decls verbose = Scan.depend (fn thy => 
  Scan.repeat (scan_line "type-decl" (str -- num -- num) :|-- (fn (ty, i) =>
    scan_count (attribute Symtab.empty Symtab.empty) i >> K ty)) >>
    (fn tys => declare_types verbose tys thy))

fun fun_decls verbose tds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "fun-decl" (str -- num -- num) :|--
    (fn ((name, arity), i) =>
      scan_count (typ tds) (arity - 1) -- typ tds --
      scan_count (attribute tds Symtab.empty) i >> pair name)) >>
    (fn fns => declare_functions verbose fns thy))

fun axioms verbose tds fds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "axiom" num :|-- (fn i =>
    expr tds fds --| scan_count (attribute tds fds) i)) >>
    (fn axs => (add_axioms verbose axs thy, ())))

fun var_decls tds fds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "var-decl" (str -- num) :|-- (fn (_, i) =>
    typ tds -- scan_count (attribute tds fds) i >> K ())) >> K (thy, ()))

fun vcs verbose tds fds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "vc" (str -- num) -- 
    (expr tds fds >> Sign.cert_term thy)) >>
    (fn vcs => ((), add_vcs verbose vcs thy)))

fun parse verbose thy = Scan.pass thy
 (type_decls verbose :|-- (fn tds =>
  fun_decls verbose tds :|-- (fn fds =>
  axioms verbose tds fds |--
  var_decls tds fds |--
  vcs verbose tds fds)))

fun load_b2i verbose path thy = finite (parse verbose thy) path

end
