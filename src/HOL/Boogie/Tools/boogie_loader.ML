(*  Title:      HOL/Boogie/Tools/boogie_loader.ML
    Author:     Sascha Boehme, TU Muenchen

Loading and interpreting Boogie-generated files.
*)

signature BOOGIE_LOADER =
sig
  val load_b2i: bool -> (string * int) list -> Path.T -> theory -> theory
  val parse_b2i: bool -> (string * int) list -> string -> theory -> theory
end

structure Boogie_Loader: BOOGIE_LOADER =
struct

fun log verbose text args x =
  if verbose andalso not (null args)
  then (Pretty.writeln (Pretty.big_list text (map Pretty.str args)); x)
  else x

val isabelle_name =
  let 
    fun purge s = if Symbol.is_letter s orelse Symbol.is_digit s then s else
      (case s of
        "." => "_o_"
      | "_" => "_n_"
      | "$" => "_S_"
      | "@" => "_G_"
      | "#" => "_H_"
      | "^" => "_T_"
      | _   => ("_" ^ string_of_int (ord s) ^ "_"))
  in prefix "b_" o translate_string purge end

fun drop_underscore s =
  try (unsuffix "_") s
  |> Option.map drop_underscore
  |> the_default s

val short_name =
  translate_string (fn s => if Symbol.is_letdig s then s else "") #>
  drop_underscore

(* these prefixes must be distinct: *)
val var_prefix = "V_"
val label_prefix = "L_"
val position_prefix = "P_"

val no_label_name = label_prefix ^ "unknown"
fun label_name line col =
  if line = 0 orelse col = 0 then no_label_name
  else label_prefix ^ string_of_int line ^ "_" ^ string_of_int col

fun mk_syntax name i =
  let
    val syn = Syntax_Ext.escape name
    val args = space_implode ",/ " (replicate i "_")
  in
    if i = 0 then Mixfix (syn, [], 1000)
    else Mixfix (syn ^ "()'(/" ^ args ^ "')", replicate i 0, 1000)
  end


datatype attribute_value = StringValue of string | TermValue of term


fun mk_distinct [] = @{const HOL.True}
  | mk_distinct [_] = @{const HOL.True}
  | mk_distinct (t :: ts) =
      let
        fun mk_noteq u u' =
          HOLogic.mk_conj (HOLogic.mk_not (HOLogic.mk_eq (t, u)), u')
      in fold_rev mk_noteq ts (mk_distinct ts) end


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

  fun log_new bname name = bname ^ " (as " ^ name ^ ")"
  fun log_ex bname name = "[" ^ bname ^ " has already been declared as " ^
    name ^ "]"

  fun declare (name, arity) thy =
    let val isa_name = isabelle_name name
    in
      (case lookup_type_name thy isa_name arity of
        SOME type_name => (((name, type_name), log_ex name type_name), thy)
      | NONE =>
          let
            val args = map (rpair dummyS) (Name.invent Name.context "'a" arity)
            val (T, thy') =
              Typedecl.typedecl_global (Binding.name isa_name, args, mk_syntax name arity) thy
            val type_name = fst (Term.dest_Type T)
          in (((name, type_name), log_new name type_name), thy') end)
    end
in
fun declare_types verbose tys =
  fold_map declare tys #>> split_list #-> (fn (tds, logs) =>
  log verbose "Declared types:" logs #>
  rpair (Symtab.make tds))
end



local
  fun maybe_builtin T =
    let
      fun const name = SOME (Const (name, T))
      fun const2_abs name =
        let val U = Term.domain_type T
        in
          SOME (Abs (Name.uu, U, Abs (Name.uu, U,
            Const (name, T) $ Bound 0 $ Bound 1)))
        end

      fun choose builtin =
        (case builtin of
          "bvnot" => const @{const_name bitNOT}
        | "bvand" => const @{const_name bitAND}
        | "bvor" => const @{const_name bitOR}
        | "bvxor" => const @{const_name bitXOR}
        | "bvadd" => const @{const_name plus}
        | "bvneg" => const @{const_name uminus}
        | "bvsub" => const @{const_name minus}
        | "bvmul" => const @{const_name times}
(* FIXME:
        | "bvudiv" => const @{const_name div}
        | "bvurem" => const @{const_name mod}
        | "bvsdiv" => const @{const_name sdiv}
        | "bvsrem" => const @{const_name srem}
        | "bvshl" => const @{const_name bv_shl}
        | "bvlshr" => const @{const_name bv_lshr}
        | "bvashr" => const @{const_name bv_ashr}
*)
        | "bvult" => const @{const_name less}
        | "bvule" => const @{const_name less_eq}
        | "bvugt" => const2_abs @{const_name less}
        | "bvuge" => const2_abs @{const_name less_eq}
        | "bvslt" => const @{const_name word_sless}
        | "bvsle" => const @{const_name word_sle}
        | "bvsgt" => const2_abs @{const_name word_sless}
        | "bvsge" => const2_abs @{const_name word_sle}
        | "zero_extend" => const @{const_name ucast}
        | "sign_extend" => const @{const_name scast}
        | _ => NONE)

      fun is_builtin att =
        (case att of
          ("bvbuiltin", [StringValue builtin]) => choose builtin
        | ("bvint", [StringValue "ITE"]) => const @{const_name If}
        | _ => NONE)
    in get_first is_builtin end

  fun lookup_const thy name T =
    let val intern = Sign.intern_const thy name
    in
      if Sign.declared_const thy intern
      then
        if Sign.typ_instance thy (T, Sign.the_const_type thy intern)
        then SOME (Const (intern, T))
        else error ("Boogie: function already declared with different type: " ^
          quote name)
      else NONE
    end

  fun log_term thy t = Syntax.string_of_term_global thy t
  fun log_new thy name t = name ^ " (as " ^ log_term thy t ^ ")"
  fun log_ex thy name t = "[" ^ name ^ " has already been declared as " ^
    log_term thy t ^ "]"
  fun log_builtin thy name t = "[" ^ name ^ " has been identified as " ^
    log_term thy t ^ "]"

  fun declare' name isa_name T arity atts thy =
    (case lookup_const thy isa_name T of
      SOME t => (((name, t), log_ex thy name t), thy)
    | NONE =>
        (case maybe_builtin T atts of
          SOME t => (((name, t), log_builtin thy name t), thy)
        | NONE =>
            thy
            |> Sign.declare_const_global ((Binding.name isa_name, T),
                 mk_syntax name arity)
            |> (fn (t, thy') => (((name, t), log_new thy' name t), thy'))))
  fun declare (name, ((Ts, T), atts)) =
    declare' name (isabelle_name name) (Ts ---> T) (length Ts) atts

  fun uniques fns fds =
    let
      fun is_unique (name, (([], _), atts)) =
            (case AList.lookup (op =) atts "unique" of
              SOME _ => Symtab.lookup fds name
            | NONE => NONE)
        | is_unique _ = NONE
    in
      map_filter is_unique fns
      |> map (swap o Term.dest_Const)
      |> AList.group (op =)
      |> map (fn (T, ns) => mk_distinct (map (Const o rpair T) ns))
    end
in
fun declare_functions verbose fns =
  fold_map declare fns #>> split_list #-> (fn (fds, logs) =>
  log verbose "Loaded constants:" logs #>
  rpair (` (uniques fns) (Symtab.make fds)))
end



local
  fun name_axioms axs =
    let fun mk_name idx = "axiom_" ^ string_of_int (idx + 1)
    in map_index (fn (idx, t) => (mk_name idx, HOLogic.mk_Trueprop t)) axs end

  datatype kind = Unused of thm | Used of thm | New of string

  fun mark (name, t) axs =
    (case Termtab.lookup axs t of
      SOME (Unused thm) => Termtab.update (t, Used thm) axs
    | NONE => Termtab.update (t, New name) axs
    | SOME _ => axs)

  val sort_fst_str = sort (prod_ord fast_string_ord (K EQUAL)) 
  fun split_list_kind thy axs =
    let
      fun split (_, Used thm) (used, new) = (thm :: used, new)
        | split (t, New name) (used, new) = (used, (name, t) :: new)
        | split (_, Unused thm) (used, new) =
           (warning (Pretty.str_of
             (Pretty.big_list "This background axiom has not been loaded:"
               [Display.pretty_thm_global thy thm]));
            (used, new))
    in apsnd sort_fst_str (fold split axs ([], [])) end

  fun mark_axioms thy axs =
    Boogie_Axioms.get (Proof_Context.init_global thy)
    |> Termtab.make o map (fn thm => (Thm.prop_of thm, Unused thm))
    |> fold mark axs
    |> split_list_kind thy o Termtab.dest
in
fun add_axioms verbose axs thy =
  let
    val (used, new) = mark_axioms thy (name_axioms axs)
  in
    thy
    |> fold_map (fn (n, t) => Specification.axiom ((Binding.name n, []), t)) new
    |-> Context.theory_map o fold (Boogie_Axioms.add_thm o Drule.export_without_context)
    |> log verbose "The following axioms were added:" (map fst new)
    |> (fn thy' => log verbose "The following axioms already existed:"
         (map (Display.string_of_thm_global thy') used) thy')
  end
end



local
  fun burrow_distinct eq f xs =
    let
      val ys = distinct eq xs
      val tab = ys ~~ f ys
    in map (the o AList.lookup eq tab) xs end

  fun indexed names =
    let
      val dup = member (op =) (duplicates (op =) (map fst names))
      fun make_name (n, i) = n ^ (if dup n then "_" ^ string_of_int i else "")
    in map make_name names end

  fun rename idx_names =
    idx_names
    |> burrow_fst (burrow_distinct (op =)
         (map short_name #> ` (duplicates (op =)) #-> Name.variant_list))
    |> indexed
in
fun add_vcs verbose vcs thy =
  let val vcs' = burrow_fst rename vcs
  in
    thy
    |> Boogie_VCs.set vcs'
    |> log verbose "The following verification conditions were loaded:"
         (map fst vcs')
  end
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

fun tokenize fold_lines input =
  let
    fun blank c = (c = #" " orelse c = #"\t" orelse c = #"\n" orelse c = #"\r")
    fun split line (i, tss) = (i + 1,
      map (pair i) (map Token (String.tokens blank line) @ [Newline]) :: tss)
  in apsnd (flat o rev) (fold_lines split input (1, [])) end

fun stopper i = Scan.stopper (K (i, EOF)) (fn (_, EOF) => true | _ => false)

fun scan_err msg [] = (fn () => "Boogie (at end of input): " ^ msg ())
  | scan_err msg ((i, _) :: _) =
      (fn () => "Boogie (at line " ^ string_of_int i ^ "): " ^ msg ())

fun scan_fail' msg = Scan.fail_with (scan_err msg)
fun scan_fail s = scan_fail' (fn () => s)

fun finite scan fold_lines input =
  let val (i, ts) = tokenize fold_lines input
  in
    (case Scan.error (Scan.finite (stopper i) scan) ts of
      (x, []) => x
    | (_, ts') => error ((scan_err (fn () => "unparsed input") ts') ()))
  end

fun read_int' s = (case read_int (raw_explode s) of (i, []) => SOME i | _ => NONE)

fun $$$ s = Scan.one (fn (_, Token s') => s = s' | _ => false)
fun str st = Scan.some (fn (_, Token s) => SOME s | _ => NONE) st
fun num st = Scan.some (fn (_, Token s) => read_int' s | _ => NONE) st

fun scan_line key scan =
  $$$ key |-- scan --| Scan.one (fn (_, Newline) => true | _ => false)
fun scan_line' key = scan_line key (Scan.succeed ())

fun scan_count scan i =
  if i > 0 then scan ::: scan_count scan (i - 1) else Scan.succeed []

fun scan_lookup kind tab key =
  (case Symtab.lookup tab key of
    SOME value => Scan.succeed value
  | NONE => scan_fail' (fn () => "undefined " ^ kind ^ ": " ^ quote key))

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
    | mk_nary f _ ts = uncurry (fold_rev f) (split_last ts)

  fun mk_list T = HOLogic.mk_list T

  fun quant name f = scan_line name (num -- num -- num) >> pair f
  val quants =
    quant "forall" HOLogic.all_const ||
    quant "exists" HOLogic.exists_const ||
    scan_fail "illegal quantifier kind"
  fun mk_quant q (x, T) t = q T $ absfree (x, T) t

  val patternT = @{typ "SMT.pattern"}
  fun mk_pattern _ [] = raise TERM ("mk_pattern", [])
    | mk_pattern n ts =
        let fun mk_pat t = Const (n, Term.fastype_of t --> patternT) $ t
        in mk_list patternT (map mk_pat ts) end
  fun patt n c scan =
    scan_line n num :|-- scan_count scan >> (mk_pattern c)
  fun pattern scan =
    patt "pat" @{const_name "SMT.pat"} scan ||
    patt "nopat" @{const_name "SMT.nopat"} scan ||
    scan_fail "illegal pattern kind"
  fun mk_trigger [] t = t
    | mk_trigger ps t =
        @{term "SMT.trigger"} $ mk_list @{typ "SMT.pattern list"} ps $ t

  fun make_label (line, col) = Free (label_name line col, @{typ bool})
  fun labelled_by kind pos t = kind $ make_label pos $ t
  fun label offset =
    $$$ "pos" |-- num -- num >> (fn (line, col) =>
      if label_name line col = no_label_name then I
      else labelled_by @{term block_at} (line - offset, col)) ||
    $$$ "neg" |-- num -- num >> (fn (line, col) =>
      labelled_by @{term assert_at} (line - offset, col)) ||
    scan_fail "illegal label kind"

  fun mk_store ((m, k), v) =
    let
      val mT = Term.fastype_of m and kT = Term.fastype_of k
      val vT = Term.fastype_of v
    in Const (@{const_name fun_upd}, mT --> kT --> vT --> mT) $ m $ k $ v end
  
  fun mk_extract ((msb, lsb), t) =
    let
      val dT = Term.fastype_of t and rT = mk_wordT (msb - lsb)
      val nT = @{typ nat}
      val mk_nat_num = HOLogic.mk_number @{typ nat}
    in Const (@{const_name slice}, [nT, dT] ---> rT) $ mk_nat_num lsb $ t end

  fun mk_concat (t1, t2) =
    let
      val T1 = Term.fastype_of t1 and T2 = Term.fastype_of t2
      val U = mk_wordT (dest_wordT T1 + dest_wordT T2)
    in Const (@{const_name word_cat}, [T1, T2] ---> U) $ t1 $ t2 end

  fun unique_labels t =
    let
      fun names_of (@{term assert_at} $ Free (n, _) $ t) = cons n #> names_of t
        | names_of (t $ u) = names_of t #> names_of u
        | names_of (Abs (_, _, t)) = names_of t
        | names_of _ = I
      val nctxt = Name.make_context (duplicates (op =) (names_of t []))

      fun fresh (i, nctxt) = (position_prefix ^ string_of_int i, (i+1, nctxt))
      fun renamed n (i, nctxt) = Name.variant n nctxt ||> pair i
      fun mk_label (name, t) = @{term assert_at} $ Free (name, @{typ bool}) $ t

      fun unique t =
        (case t of
          @{term assert_at} $ Free (n, _) $ u =>
            if n = no_label_name
            then fresh ##>> unique u #>> mk_label
            else renamed n ##>> unique u #>> mk_label
        | u1 $ u2 => unique u1 ##>> unique u2 #>> (op $)
        | Abs (n, T, u) => unique u #>> (fn u' => Abs (n, T, u'))
        | _ => pair t)
    in fst (unique t (1, nctxt)) end

  val var_name = str >> prefix var_prefix
  val dest_var_name = unprefix var_prefix
  fun rename_variables t =
    let
      fun short_var_name n = short_name (dest_var_name n)

      val all_names = Term.add_free_names t []
      val (names, nctxt) =
        all_names
        |> map_filter (try (fn n => (n, short_var_name n)))
        |> split_list
        ||>> (fn names => fold_map Name.variant names (Name.make_context all_names))
        |>> Symtab.make o (op ~~)

      fun rename_free n = the_default n (Symtab.lookup names n)
      fun rename_abs n = Name.variant (short_var_name n)

      fun rename _ (Free (n, T)) = Free (rename_free n, T)
        | rename nctxt (Abs (n, T, t)) =
            let val (n', nctxt') = rename_abs n nctxt
            in Abs (n', T, rename nctxt' t) end
        | rename nctxt (t $ u) = rename nctxt t $ rename nctxt u
        | rename _ t = t
    in rename nctxt t end
in
fun expr offset tds fds =
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
      scan_line' "ite" |-- exp -- exp -- exp >> (fn ((c, t1), t2) =>
        let val T = Term.fastype_of t1
        in
          Const (@{const_name If}, [@{typ bool}, T, T] ---> T) $ c $ t1 $ t2
        end) ||
      binexp "implies" (binop @{term HOL.implies}) ||
      scan_line "distinct" num :|-- scan_count exp >> mk_distinct ||
      binexp "=" HOLogic.mk_eq ||
      scan_line "var" var_name -- typ tds >> Free ||
      scan_line "fun" (str -- num) :|-- (fn (name, arity) =>
        scan_lookup "constant" fds name -- scan_count exp arity >>
        Term.list_comb) ||
      quants :|-- (fn (q, ((n, k), i)) =>
        scan_count (scan_line "var" var_name -- typ tds) n --
        scan_count (pattern exp) k --
        scan_count (attribute offset tds fds) i --
        exp >> (fn (((vs, ps), _), t) =>
          fold_rev (mk_quant q) vs (mk_trigger ps t))) ||
      scan_line "label" (label offset) -- exp >> (fn (mk, t) => mk t) ||
      scan_line "int-num" num >> HOLogic.mk_number @{typ int} ||
      binexp "<" (binop @{term "op < :: int => _"}) ||
      binexp "<=" (binop @{term "op <= :: int => _"}) ||
      binexp ">" (binop @{term "op < :: int => _"} o swap) ||
      binexp ">=" (binop @{term "op <= :: int => _"} o swap) ||
      binexp "+" (binop @{term "op + :: int => _"}) ||
      binexp "-" (binop @{term "op - :: int => _"}) ||
      binexp "*" (binop @{term "op * :: int => _"}) ||
      binexp "/" (binop @{term boogie_div}) ||
      binexp "%" (binop @{term boogie_mod}) ||
      scan_line "select" num :|-- (fn arity =>
        exp -- (scan_count exp (arity - 1) >> HOLogic.mk_tuple) >> (op $)) ||
      scan_line "store" num :|-- (fn arity =>
        exp -- (scan_count exp (arity - 2) >> HOLogic.mk_tuple) -- exp >> 
          mk_store) ||
      scan_line "bv-num" (num -- num) >> (fn (size, i) =>
        HOLogic.mk_number (mk_wordT size) i) ||
      scan_line "bv-extract" (num -- num) -- exp >> mk_extract ||
      binexp "bv-concat" mk_concat ||
      scan_fail "illegal expression") st
  in exp >> (rename_variables o unique_labels) end

and attribute offset tds fds =
  let
    val attr_val = 
      scan_line' "expr-attr" |-- expr offset tds fds >> TermValue ||
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
    scan_count (attribute 0 Symtab.empty Symtab.empty) i >> K ty)) >>
    (fn tys => declare_types verbose tys thy))

fun fun_decls verbose tds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "fun-decl" (str -- num -- num) :|--
    (fn ((name, arity), i) =>
      scan_count (typ tds) (arity - 1) -- typ tds --
      scan_count (attribute 0 tds Symtab.empty) i >> pair name)) >>
    (fn fns => declare_functions verbose fns thy))

fun axioms verbose tds fds unique_axs = Scan.depend (fn thy =>
  Scan.repeat (scan_line "axiom" num :|-- (fn i =>
    expr 0 tds fds --| scan_count (attribute 0 tds fds) i)) >>
    (fn axs => (add_axioms verbose (unique_axs @ axs) thy, ())))

fun var_decls tds fds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "var-decl" (str -- num) :|-- (fn (_, i) =>
    typ tds -- scan_count (attribute 0 tds fds) i >> K ())) >> K (thy, ()))

fun local_vc_offset offsets vc_name =
   Integer.add ~1 (the_default 1 (AList.lookup (op =) offsets vc_name))

fun vcs verbose offsets tds fds = Scan.depend (fn thy =>
  Scan.repeat (scan_line "vc" (str -- num) :-- (fn (name, _) =>
    (expr (local_vc_offset offsets name) tds fds))) >> 
    (fn vcs => ((), add_vcs verbose vcs thy)))

fun parse verbose offsets thy = Scan.pass thy
 (type_decls verbose :|-- (fn tds =>
  fun_decls verbose tds :|-- (fn (unique_axs, fds) =>
  axioms verbose tds fds unique_axs |--
  var_decls tds fds |--
  vcs verbose offsets tds fds)))

fun load_b2i verbose offsets path thy = finite (parse verbose offsets thy) File.fold_lines path

fun parse_b2i verbose offsets text thy =
  finite (parse verbose offsets thy) (fn f => fold f o String.tokens (fn c => c = #"\n")) text

end
