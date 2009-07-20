(*  Title:      Pure/codegen.ML
    Author:     Stefan Berghofer, TU Muenchen

Generic code generator.
*)

signature CODEGEN =
sig
  val quiet_mode : bool ref
  val message : string -> unit
  val mode : string list ref
  val margin : int ref
  val string_of : Pretty.T -> string
  val str : string -> Pretty.T

  datatype 'a mixfix =
      Arg
    | Ignore
    | Module
    | Pretty of Pretty.T
    | Quote of 'a;

  type deftab
  type node
  type codegr
  type 'a codegen

  val add_codegen: string -> term codegen -> theory -> theory
  val add_tycodegen: string -> typ codegen -> theory -> theory
  val add_preprocessor: (theory -> thm list -> thm list) -> theory -> theory
  val preprocess: theory -> thm list -> thm list
  val preprocess_term: theory -> term -> term
  val print_codegens: theory -> unit
  val generate_code: theory -> string list -> string -> (string * string) list ->
    (string * string) list * codegr
  val generate_code_i: theory -> string list -> string -> (string * term) list ->
    (string * string) list * codegr
  val assoc_const: string * (term mixfix list *
    (string * string) list) -> theory -> theory
  val assoc_const_i: (string * typ) * (term mixfix list *
    (string * string) list) -> theory -> theory
  val assoc_type: xstring * (typ mixfix list *
    (string * string) list) -> theory -> theory
  val get_assoc_code: theory -> string * typ ->
    (term mixfix list * (string * string) list) option
  val get_assoc_type: theory -> string ->
    (typ mixfix list * (string * string) list) option
  val codegen_error: codegr -> string -> string -> 'a
  val invoke_codegen: theory -> deftab -> string -> string -> bool ->
    term -> codegr -> Pretty.T * codegr
  val invoke_tycodegen: theory -> deftab -> string -> string -> bool ->
    typ -> codegr -> Pretty.T * codegr
  val mk_id: string -> string
  val mk_qual_id: string -> string * string -> string
  val mk_const_id: string -> string -> codegr -> (string * string) * codegr
  val get_const_id: codegr -> string -> string * string
  val mk_type_id: string -> string -> codegr -> (string * string) * codegr
  val get_type_id: codegr -> string -> string * string
  val thyname_of_type: theory -> string -> string
  val thyname_of_const: theory -> string -> string
  val rename_terms: term list -> term list
  val rename_term: term -> term
  val new_names: term -> string list -> string list
  val new_name: term -> string -> string
  val if_library: 'a -> 'a -> 'a
  val get_defn: theory -> deftab -> string -> typ ->
    ((typ * (string * thm)) * int option) option
  val is_instance: typ -> typ -> bool
  val parens: Pretty.T -> Pretty.T
  val mk_app: bool -> Pretty.T -> Pretty.T list -> Pretty.T
  val mk_tuple: Pretty.T list -> Pretty.T
  val mk_let: (Pretty.T * Pretty.T) list -> Pretty.T -> Pretty.T
  val eta_expand: term -> term list -> int -> term
  val strip_tname: string -> string
  val mk_type: bool -> typ -> Pretty.T
  val mk_term_of: codegr -> string -> bool -> typ -> Pretty.T
  val mk_gen: codegr -> string -> bool -> string list -> string -> typ -> Pretty.T
  val test_fn: (int -> term list option) ref
  val test_term: Proof.context -> term -> int -> term list option
  val eval_result: (unit -> term) ref
  val eval_term: theory -> term -> term
  val evaluation_conv: cterm -> thm
  val parse_mixfix: (string -> 'a) -> string -> 'a mixfix list
  val quotes_of: 'a mixfix list -> 'a list
  val num_args_of: 'a mixfix list -> int
  val replace_quotes: 'b list -> 'a mixfix list -> 'b mixfix list
  val mk_deftab: theory -> deftab
  val map_unfold: (simpset -> simpset) -> theory -> theory
  val add_unfold: thm -> theory -> theory
  val del_unfold: thm -> theory -> theory

  val get_node: codegr -> string -> node
  val add_edge: string * string -> codegr -> codegr
  val add_edge_acyclic: string * string -> codegr -> codegr
  val del_nodes: string list -> codegr -> codegr
  val map_node: string -> (node -> node) -> codegr -> codegr
  val new_node: string * node -> codegr -> codegr

  val setup: theory -> theory
end;

structure Codegen : CODEGEN =
struct

val quiet_mode = ref true;
fun message s = if !quiet_mode then () else writeln s;

val mode = ref ([] : string list);

val margin = ref 80;

fun string_of p = (Pretty.string_of |>
  PrintMode.setmp [] |>
  Pretty.setmp_margin (!margin)) p;

val str = PrintMode.setmp [] Pretty.str;

(**** Mixfix syntax ****)

datatype 'a mixfix =
    Arg
  | Ignore
  | Module
  | Pretty of Pretty.T
  | Quote of 'a;

fun is_arg Arg = true
  | is_arg Ignore = true
  | is_arg _ = false;

fun quotes_of [] = []
  | quotes_of (Quote q :: ms) = q :: quotes_of ms
  | quotes_of (_ :: ms) = quotes_of ms;

fun args_of [] xs = ([], xs)
  | args_of (Arg :: ms) (x :: xs) = apfst (cons x) (args_of ms xs)
  | args_of (Ignore :: ms) (_ :: xs) = args_of ms xs
  | args_of (_ :: ms) xs = args_of ms xs;

fun num_args_of x = length (List.filter is_arg x);


(**** theory data ****)

(* preprocessed definition table *)

type deftab =
  (typ *              (* type of constant *)
    (string *         (* name of theory containing definition of constant *)
      thm))           (* definition theorem *)
  list Symtab.table;

(* code dependency graph *)

type nametab = (string * string) Symtab.table * unit Symtab.table;

fun merge_nametabs ((tab, used) : nametab, (tab', used')) =
  (Symtab.merge op = (tab, tab'), Symtab.merge op = (used, used'));

type node =
  (exn option *    (* slot for arbitrary data *)
   string *        (* name of structure containing piece of code *)
   string);        (* piece of code *)

type codegr =
  node Graph.T *
  (nametab *       (* table for assigned constant names *)
   nametab);       (* table for assigned type names *)

val emptygr : codegr = (Graph.empty,
  ((Symtab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)));

(* type of code generators *)

type 'a codegen =
  theory ->    (* theory in which generate_code was called *)
  deftab ->    (* definition table (for efficiency) *)
  string ->    (* node name of caller (for recording dependencies) *)
  string ->    (* module name of caller (for modular code generation) *)
  bool ->      (* whether to parenthesize generated expression *)
  'a ->        (* item to generate code from *)
  codegr ->    (* code dependency graph *)
  (Pretty.T * codegr) option;


(* theory data *)

structure CodegenData = TheoryDataFun
(
  type T =
    {codegens : (string * term codegen) list,
     tycodegens : (string * typ codegen) list,
     consts : ((string * typ) * (term mixfix list * (string * string) list)) list,
     types : (string * (typ mixfix list * (string * string) list)) list,
     preprocs: (stamp * (theory -> thm list -> thm list)) list,
     modules: codegr Symtab.table};

  val empty =
    {codegens = [], tycodegens = [], consts = [], types = [],
     preprocs = [], modules = Symtab.empty};
  val copy = I;
  val extend = I;

  fun merge _
    ({codegens = codegens1, tycodegens = tycodegens1,
      consts = consts1, types = types1,
      preprocs = preprocs1, modules = modules1} : T,
     {codegens = codegens2, tycodegens = tycodegens2,
      consts = consts2, types = types2,
      preprocs = preprocs2, modules = modules2}) =
    {codegens = AList.merge (op =) (K true) (codegens1, codegens2),
     tycodegens = AList.merge (op =) (K true) (tycodegens1, tycodegens2),
     consts = AList.merge (op =) (K true) (consts1, consts2),
     types = AList.merge (op =) (K true) (types1, types2),
     preprocs = AList.merge (op =) (K true) (preprocs1, preprocs2),
     modules = Symtab.merge (K true) (modules1, modules2)};
);

fun print_codegens thy =
  let val {codegens, tycodegens, ...} = CodegenData.get thy in
    Pretty.writeln (Pretty.chunks
      [Pretty.strs ("term code generators:" :: map fst codegens),
       Pretty.strs ("type code generators:" :: map fst tycodegens)])
  end;



(**** access modules ****)

fun get_modules thy = #modules (CodegenData.get thy);

fun map_modules f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules} =
    CodegenData.get thy;
  in CodegenData.put {codegens = codegens, tycodegens = tycodegens,
    consts = consts, types = types, preprocs = preprocs,
    modules = f modules} thy
  end;


(**** add new code generators to theory ****)

fun add_codegen name f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules} =
    CodegenData.get thy
  in (case AList.lookup (op =) codegens name of
      NONE => CodegenData.put {codegens = (name, f) :: codegens,
        tycodegens = tycodegens, consts = consts, types = types,
        preprocs = preprocs, modules = modules} thy
    | SOME _ => error ("Code generator " ^ name ^ " already declared"))
  end;

fun add_tycodegen name f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules} =
    CodegenData.get thy
  in (case AList.lookup (op =) tycodegens name of
      NONE => CodegenData.put {tycodegens = (name, f) :: tycodegens,
        codegens = codegens, consts = consts, types = types,
        preprocs = preprocs, modules = modules} thy
    | SOME _ => error ("Code generator " ^ name ^ " already declared"))
  end;


(**** preprocessors ****)

fun add_preprocessor p thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules} =
    CodegenData.get thy
  in CodegenData.put {tycodegens = tycodegens,
    codegens = codegens, consts = consts, types = types,
    preprocs = (stamp (), p) :: preprocs,
    modules = modules} thy
  end;

fun preprocess thy =
  let val {preprocs, ...} = CodegenData.get thy
  in fold (fn (_, f) => f thy) preprocs end;

fun preprocess_term thy t =
  let
    val x = Free (Name.variant (OldTerm.add_term_names (t, [])) "x", fastype_of t);
    (* fake definition *)
    val eq = setmp quick_and_dirty true (SkipProof.make_thm thy)
      (Logic.mk_equals (x, t));
    fun err () = error "preprocess_term: bad preprocessor"
  in case map prop_of (preprocess thy [eq]) of
      [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
    | _ => err ()
  end;

structure UnfoldData = TheoryDataFun
(
  type T = simpset;
  val empty = empty_ss;
  val copy = I;
  val extend = I;
  fun merge _ = merge_ss;
);

val map_unfold = UnfoldData.map;
val add_unfold = map_unfold o MetaSimplifier.add_simp;
val del_unfold = map_unfold o MetaSimplifier.del_simp;

fun unfold_preprocessor thy =
  let val ss = Simplifier.theory_context thy (UnfoldData.get thy)
  in map (Thm.transfer thy #> Simplifier.full_simplify ss) end;


(**** associate constants with target language code ****)

fun gen_assoc_const prep_const (raw_const, syn) thy =
  let
    val {codegens, tycodegens, consts, types, preprocs, modules} =
      CodegenData.get thy;
    val (cname, T) = prep_const thy raw_const;
  in
    if num_args_of (fst syn) > length (binder_types T) then
      error ("More arguments than in corresponding type of " ^ cname)
    else case AList.lookup (op =) consts (cname, T) of
      NONE => CodegenData.put {codegens = codegens,
        tycodegens = tycodegens,
        consts = ((cname, T), syn) :: consts,
        types = types, preprocs = preprocs,
        modules = modules} thy
    | SOME _ => error ("Constant " ^ cname ^ " already associated with code")
  end;

val assoc_const_i = gen_assoc_const (K I);
val assoc_const = gen_assoc_const Code.read_bare_const;


(**** associate types with target language types ****)

fun assoc_type (s, syn) thy =
  let
    val {codegens, tycodegens, consts, types, preprocs, modules} =
      CodegenData.get thy;
    val tc = Sign.intern_type thy s;
  in
    case Symtab.lookup (snd (#types (Type.rep_tsig (Sign.tsig_of thy)))) tc of
      SOME ((Type.LogicalType i, _), _) =>
        if num_args_of (fst syn) > i then
          error ("More arguments than corresponding type constructor " ^ s)
        else (case AList.lookup (op =) types tc of
          NONE => CodegenData.put {codegens = codegens,
            tycodegens = tycodegens, consts = consts,
            types = (tc, syn) :: types,
            preprocs = preprocs, modules = modules} thy
        | SOME _ => error ("Type " ^ tc ^ " already associated with code"))
    | _ => error ("Not a type constructor: " ^ s)
  end;

fun get_assoc_type thy = AList.lookup (op =) ((#types o CodegenData.get) thy);


(**** make valid ML identifiers ****)

fun is_ascii_letdig x = Symbol.is_ascii_letter x orelse
  Symbol.is_ascii_digit x orelse Symbol.is_ascii_quasi x;

fun dest_sym s = (case split_last (snd (take_prefix (fn c => c = "\\") (explode s))) of
    ("<" :: "^" :: xs, ">") => (true, implode xs)
  | ("<" :: xs, ">") => (false, implode xs)
  | _ => sys_error "dest_sym");

fun mk_id s = if s = "" then "" else
  let
    fun check_str [] = []
      | check_str xs = (case take_prefix is_ascii_letdig xs of
          ([], " " :: zs) => check_str zs
        | ([], z :: zs) =>
          if size z = 1 then string_of_int (ord z) :: check_str zs
          else (case dest_sym z of
              (true, "isub") => check_str zs
            | (true, "isup") => "" :: check_str zs
            | (ctrl, s') => (if ctrl then "ctrl_" ^ s' else s') :: check_str zs)
        | (ys, zs) => implode ys :: check_str zs);
    val s' = space_implode "_" (maps (check_str o Symbol.explode) (Long_Name.explode s))
  in
    if Symbol.is_ascii_letter (hd (explode s')) then s' else "id_" ^ s'
  end;

fun mk_long_id (p as (tab, used)) module s =
  let
    fun find_name [] = sys_error "mk_long_id"
      | find_name (ys :: yss) =
          let
            val s' = Long_Name.implode ys
            val s'' = Long_Name.append module s'
          in case Symtab.lookup used s'' of
              NONE => ((module, s'),
                (Symtab.update_new (s, (module, s')) tab,
                 Symtab.update_new (s'', ()) used))
            | SOME _ => find_name yss
          end
  in case Symtab.lookup tab s of
      NONE => find_name (Library.suffixes1 (Long_Name.explode s))
    | SOME name => (name, p)
  end;

(* module:  module name for caller                                        *)
(* module': module name for callee                                        *)
(* if caller and callee reside in different modules, use qualified access *)

fun mk_qual_id module (module', s) =
  if module = module' orelse module' = "" then s else module' ^ "." ^ s;

fun mk_const_id module cname (gr, (tab1, tab2)) =
  let
    val ((module, s), tab1') = mk_long_id tab1 module cname
    val s' = mk_id s;
    val s'' = if ML_Syntax.is_reserved s' then s' ^ "_const" else s'
  in (((module, s'')), (gr, (tab1', tab2))) end;

fun get_const_id (gr, (tab1, tab2)) cname =
  case Symtab.lookup (fst tab1) cname of
    NONE => error ("get_const_id: no such constant: " ^ quote cname)
  | SOME (module, s) =>
      let
        val s' = mk_id s;
        val s'' = if ML_Syntax.is_reserved s' then s' ^ "_const" else s'
      in (module, s'') end;

fun mk_type_id module tyname (gr, (tab1, tab2)) =
  let
    val ((module, s), tab2') = mk_long_id tab2 module tyname
    val s' = mk_id s;
    val s'' = if ML_Syntax.is_reserved s' then s' ^ "_type" else s'
  in ((module, s''), (gr, (tab1, tab2'))) end;

fun get_type_id (gr, (tab1, tab2)) tyname =
  case Symtab.lookup (fst tab2) tyname of
    NONE => error ("get_type_id: no such type: " ^ quote tyname)
  | SOME (module, s) =>
      let
        val s' = mk_id s;
        val s'' = if ML_Syntax.is_reserved s' then s' ^ "_type" else s'
      in (module, s'') end;

fun get_type_id' f tab tyname = apsnd f (get_type_id tab tyname);

fun get_node (gr, x) k = Graph.get_node gr k;
fun add_edge e (gr, x) = (Graph.add_edge e gr, x);
fun add_edge_acyclic e (gr, x) = (Graph.add_edge_acyclic e gr, x);
fun del_nodes ks (gr, x) = (Graph.del_nodes ks gr, x);
fun map_node k f (gr, x) = (Graph.map_node k f gr, x);
fun new_node p (gr, x) = (Graph.new_node p gr, x);

fun thyname_of thy f x = the (AList.lookup (op =) (f x) Markup.theory_nameN);

fun thyname_of_type thy =
  thyname_of thy (Type.the_tags (Sign.tsig_of thy));

fun thyname_of_const thy =
  thyname_of thy (Consts.the_tags (Sign.consts_of thy));

fun rename_terms ts =
  let
    val names = List.foldr OldTerm.add_term_names
      (map (fst o fst) (rev (fold Term.add_vars ts []))) ts;
    val reserved = filter ML_Syntax.is_reserved names;
    val (illegal, alt_names) = split_list (map_filter (fn s =>
      let val s' = mk_id s in if s = s' then NONE else SOME (s, s') end) names)
    val ps = (reserved @ illegal) ~~
      Name.variant_list names (map (suffix "'") reserved @ alt_names);

    fun rename_id s = AList.lookup (op =) ps s |> the_default s;

    fun rename (Var ((a, i), T)) = Var ((rename_id a, i), T)
      | rename (Free (a, T)) = Free (rename_id a, T)
      | rename (Abs (s, T, t)) = Abs (s, T, rename t)
      | rename (t $ u) = rename t $ rename u
      | rename t = t;
  in
    map rename ts
  end;

val rename_term = hd o rename_terms o single;


(**** retrieve definition of constant ****)

fun is_instance T1 T2 =
  Type.raw_instance (T1, if null (OldTerm.typ_tfrees T2) then T2 else Logic.varifyT T2);

fun get_assoc_code thy (s, T) = Option.map snd (find_first (fn ((s', T'), _) =>
  s = s' andalso is_instance T T') (#consts (CodegenData.get thy)));

fun get_aux_code xs = map_filter (fn (m, code) =>
  if m = "" orelse member (op =) (!mode) m then SOME code else NONE) xs;

fun dest_prim_def t =
  let
    val (lhs, rhs) = Logic.dest_equals t;
    val (c, args) = strip_comb lhs;
    val (s, T) = dest_Const c
  in if forall is_Var args then SOME (s, (T, (args, rhs))) else NONE
  end handle TERM _ => NONE;

fun mk_deftab thy =
  let
    val axmss = map (fn thy' => (Context.theory_name thy', Theory.axiom_table thy'))
      (thy :: Theory.ancestors_of thy);
    fun prep_def def = (case preprocess thy [def] of
      [def'] => prop_of def' | _ => error "mk_deftab: bad preprocessor");
    fun add_def thyname (name, t) = (case dest_prim_def t of
        NONE => I
      | SOME (s, (T, _)) => Symtab.map_default (s, [])
          (cons (T, (thyname, Thm.axiom thy name))));
  in
    fold (fn (thyname, axms) => Symtab.fold (add_def thyname) axms) axmss Symtab.empty
  end;

fun prep_prim_def thy thm =
  let
    val prop = case preprocess thy [thm]
     of [thm'] => Thm.prop_of thm'
      | _ => error "mk_deftab: bad preprocessor"
  in ((Option.map o apsnd o apsnd)
    (fn (args, rhs) => split_last (rename_terms (args @ [rhs]))) o dest_prim_def) prop
  end;

fun get_defn thy defs s T = (case Symtab.lookup defs s of
    NONE => NONE
  | SOME ds =>
      let val i = find_index (is_instance T o fst) ds
      in if i >= 0 then
          SOME (nth ds i, if length ds = 1 then NONE else SOME i)
        else NONE
      end);


(**** invoke suitable code generator for term / type ****)

fun codegen_error (gr, _) dep s =
  error (s ^ "\nrequired by:\n" ^ commas (Graph.all_succs gr [dep]));

fun invoke_codegen thy defs dep module brack t gr = (case get_first
   (fn (_, f) => f thy defs dep module brack t gr) (#codegens (CodegenData.get thy)) of
      NONE => codegen_error gr dep ("Unable to generate code for term:\n" ^
        Syntax.string_of_term_global thy t)
    | SOME x => x);

fun invoke_tycodegen thy defs dep module brack T gr = (case get_first
   (fn (_, f) => f thy defs dep module brack T gr ) (#tycodegens (CodegenData.get thy)) of
      NONE => codegen_error gr dep ("Unable to generate code for type:\n" ^
        Syntax.string_of_typ_global thy T)
    | SOME x => x);


(**** code generator for mixfix expressions ****)

fun parens p = Pretty.block [str "(", p, str ")"];

fun pretty_fn [] p = [p]
  | pretty_fn (x::xs) p = str ("fn " ^ x ^ " =>") ::
      Pretty.brk 1 :: pretty_fn xs p;

fun pretty_mixfix _ _ [] [] _ = []
  | pretty_mixfix module module' (Arg :: ms) (p :: ps) qs =
      p :: pretty_mixfix module module' ms ps qs
  | pretty_mixfix module module' (Ignore :: ms) ps qs =
      pretty_mixfix module module' ms ps qs
  | pretty_mixfix module module' (Module :: ms) ps qs =
      (if module <> module'
       then cons (str (module' ^ ".")) else I)
      (pretty_mixfix module module' ms ps qs)
  | pretty_mixfix module module' (Pretty p :: ms) ps qs =
      p :: pretty_mixfix module module' ms ps qs
  | pretty_mixfix module module' (Quote _ :: ms) ps (q :: qs) =
      q :: pretty_mixfix module module' ms ps qs;

fun replace_quotes [] [] = []
  | replace_quotes xs (Arg :: ms) =
      Arg :: replace_quotes xs ms
  | replace_quotes xs (Ignore :: ms) =
      Ignore :: replace_quotes xs ms
  | replace_quotes xs (Module :: ms) =
      Module :: replace_quotes xs ms
  | replace_quotes xs (Pretty p :: ms) =
      Pretty p :: replace_quotes xs ms
  | replace_quotes (x::xs) (Quote _ :: ms) =
      Quote x :: replace_quotes xs ms;


(**** default code generators ****)

fun eta_expand t ts i =
  let
    val k = length ts;
    val Ts = Library.drop (k, binder_types (fastype_of t));
    val j = i - k
  in
    List.foldr (fn (T, t) => Abs ("x", T, t))
      (list_comb (t, ts @ map Bound (j-1 downto 0))) (Library.take (j, Ts))
  end;

fun mk_app _ p [] = p
  | mk_app brack p ps = if brack then
       Pretty.block (str "(" ::
         separate (Pretty.brk 1) (p :: ps) @ [str ")"])
     else Pretty.block (separate (Pretty.brk 1) (p :: ps));

fun new_names t xs = Name.variant_list
  (map (fst o fst o dest_Var) (OldTerm.term_vars t) union
    OldTerm.add_term_names (t, ML_Syntax.reserved_names)) (map mk_id xs);

fun new_name t x = hd (new_names t [x]);

fun if_library x y = if member (op =) (!mode) "library" then x else y;

fun default_codegen thy defs dep module brack t gr =
  let
    val (u, ts) = strip_comb t;
    fun codegens brack = fold_map (invoke_codegen thy defs dep module brack)
  in (case u of
      Var ((s, i), T) =>
        let
          val (ps, gr') = codegens true ts gr;
          val (_, gr'') = invoke_tycodegen thy defs dep module false T gr'
        in SOME (mk_app brack (str (s ^
           (if i=0 then "" else string_of_int i))) ps, gr'')
        end

    | Free (s, T) =>
        let
          val (ps, gr') = codegens true ts gr;
          val (_, gr'') = invoke_tycodegen thy defs dep module false T gr'
        in SOME (mk_app brack (str s) ps, gr'') end

    | Const (s, T) =>
      (case get_assoc_code thy (s, T) of
         SOME (ms, aux) =>
           let val i = num_args_of ms
           in if length ts < i then
               default_codegen thy defs dep module brack (eta_expand u ts i) gr 
             else
               let
                 val (ts1, ts2) = args_of ms ts;
                 val (ps1, gr1) = codegens false ts1 gr;
                 val (ps2, gr2) = codegens true ts2 gr1;
                 val (ps3, gr3) = codegens false (quotes_of ms) gr2;
                 val (_, gr4) = invoke_tycodegen thy defs dep module false
                   (funpow (length ts) (hd o tl o snd o dest_Type) T) gr3;
                 val (module', suffix) = (case get_defn thy defs s T of
                     NONE => (if_library (thyname_of_const thy s) module, "")
                   | SOME ((U, (module', _)), NONE) =>
                       (if_library module' module, "")
                   | SOME ((U, (module', _)), SOME i) =>
                       (if_library module' module, " def" ^ string_of_int i));
                 val node_id = s ^ suffix;
                 fun p module' = mk_app brack (Pretty.block
                   (pretty_mixfix module module' ms ps1 ps3)) ps2
               in SOME (case try (get_node gr4) node_id of
                   NONE => (case get_aux_code aux of
                       [] => (p module, gr4)
                     | xs => (p module', add_edge (node_id, dep) (new_node
                         (node_id, (NONE, module', cat_lines xs ^ "\n")) gr4)))
                 | SOME (_, module'', _) =>
                     (p module'', add_edge (node_id, dep) gr4))
               end
           end
       | NONE => (case get_defn thy defs s T of
           NONE => NONE
         | SOME ((U, (thyname, thm)), k) => (case prep_prim_def thy thm
            of SOME (_, (_, (args, rhs))) => let
               val module' = if_library thyname module;
               val suffix = (case k of NONE => "" | SOME i => " def" ^ string_of_int i);
               val node_id = s ^ suffix;
               val ((ps, def_id), gr') = gr |> codegens true ts
                 ||>> mk_const_id module' (s ^ suffix);
               val p = mk_app brack (str (mk_qual_id module def_id)) ps
             in SOME (case try (get_node gr') node_id of
                 NONE =>
                   let
                     val _ = message ("expanding definition of " ^ s);
                     val (Ts, _) = strip_type U;
                     val (args', rhs') =
                       if not (null args) orelse null Ts then (args, rhs) else
                         let val v = Free (new_name rhs "x", hd Ts)
                         in ([v], betapply (rhs, v)) end;
                     val (p', gr1) = invoke_codegen thy defs node_id module' false
                       rhs' (add_edge (node_id, dep)
                          (new_node (node_id, (NONE, "", "")) gr'));
                     val (xs, gr2) = codegens false args' gr1;
                     val (_, gr3) = invoke_tycodegen thy defs dep module false T gr2;
                     val (ty, gr4) = invoke_tycodegen thy defs node_id module' false U gr3;
                   in (p, map_node node_id (K (NONE, module', string_of
                       (Pretty.block (separate (Pretty.brk 1)
                         (if null args' then
                            [str ("val " ^ snd def_id ^ " :"), ty]
                          else str ("fun " ^ snd def_id) :: xs) @
                        [str " =", Pretty.brk 1, p', str ";"])) ^ "\n\n")) gr4)
                   end
               | SOME _ => (p, add_edge (node_id, dep) gr'))
             end
             | NONE => NONE)))

    | Abs _ =>
      let
        val (bs, Ts) = ListPair.unzip (strip_abs_vars u);
        val t = strip_abs_body u
        val bs' = new_names t bs;
        val (ps, gr1) = codegens true ts gr;
        val (p, gr2) = invoke_codegen thy defs dep module false
          (subst_bounds (map Free (rev (bs' ~~ Ts)), t)) gr1;
      in
        SOME (mk_app brack (Pretty.block (str "(" :: pretty_fn bs' p @
          [str ")"])) ps, gr2)
      end

    | _ => NONE)
  end;

fun default_tycodegen thy defs dep module brack (TVar ((s, i), _)) gr =
      SOME (str (s ^ (if i = 0 then "" else string_of_int i)), gr)
  | default_tycodegen thy defs dep module brack (TFree (s, _)) gr =
      SOME (str s, gr)
  | default_tycodegen thy defs dep module brack (Type (s, Ts)) gr =
      (case AList.lookup (op =) ((#types o CodegenData.get) thy) s of
         NONE => NONE
       | SOME (ms, aux) =>
           let
             val (ps, gr') = fold_map
               (invoke_tycodegen thy defs dep module false)
               (fst (args_of ms Ts)) gr;
             val (qs, gr'') = fold_map
               (invoke_tycodegen thy defs dep module false)
               (quotes_of ms) gr';
             val module' = if_library (thyname_of_type thy s) module;
             val node_id = s ^ " (type)";
             fun p module' = Pretty.block (pretty_mixfix module module' ms ps qs)
           in SOME (case try (get_node gr'') node_id of
               NONE => (case get_aux_code aux of
                   [] => (p module', gr'')
                 | xs => (p module', snd (mk_type_id module' s
                       (add_edge (node_id, dep) (new_node (node_id,
                         (NONE, module', cat_lines xs ^ "\n")) gr'')))))
             | SOME (_, module'', _) =>
                 (p module'', add_edge (node_id, dep) gr''))
           end);

fun mk_tuple [p] = p
  | mk_tuple ps = Pretty.block (str "(" ::
      List.concat (separate [str ",", Pretty.brk 1] (map single ps)) @
        [str ")"]);

fun mk_let bindings body =
  Pretty.blk (0, [str "let", Pretty.brk 1,
    Pretty.blk (0, separate Pretty.fbrk (map (fn (pat, rhs) =>
      Pretty.block [str "val ", pat, str " =", Pretty.brk 1,
      rhs, str ";"]) bindings)),
    Pretty.brk 1, str "in", Pretty.brk 1, body,
    Pretty.brk 1, str "end"]);

fun mk_struct name s = "structure " ^ name ^ " =\nstruct\n\n" ^ s ^ "end;\n";

fun add_to_module name s = AList.map_entry (op =) (name : string) (suffix s);

fun output_code gr module xs =
  let
    val code = map_filter (fn s =>
      let val c as (_, module', _) = Graph.get_node gr s
      in if module = "" orelse module = module' then SOME (s, c) else NONE end)
        (rev (Graph.all_preds gr xs));
    fun string_of_cycle (a :: b :: cs) =
          let val SOME (x, y) = get_first (fn (x, (_, a', _)) =>
            if a = a' then Option.map (pair x)
              (find_first ((fn (_, b', _) => b' = b) o Graph.get_node gr)
                (Graph.imm_succs gr x))
            else NONE) code
          in x ^ " called by " ^ y ^ "\n" ^ string_of_cycle (b :: cs) end
      | string_of_cycle _ = ""
  in
    if module = "" then
      let
        val modules = distinct (op =) (map (#2 o snd) code);
        val mod_gr = fold_rev Graph.add_edge_acyclic
          (maps (fn (s, (_, module, _)) => map (pair module)
            (filter_out (fn s => s = module) (map (#2 o Graph.get_node gr)
              (Graph.imm_succs gr s)))) code)
          (fold_rev (Graph.new_node o rpair ()) modules Graph.empty);
        val modules' =
          rev (Graph.all_preds mod_gr (map (#2 o Graph.get_node gr) xs))
      in
        List.foldl (fn ((_, (_, module, s)), ms) => add_to_module module s ms)
          (map (rpair "") modules') code
      end handle Graph.CYCLES (cs :: _) =>
        error ("Cyclic dependency of modules:\n" ^ commas cs ^
          "\n" ^ string_of_cycle cs)
    else [(module, implode (map (#3 o snd) code))]
  end;

fun gen_generate_code prep_term thy modules module xs =
  let
    val _ = (module <> "" orelse
        member (op =) (!mode) "library" andalso forall (fn (s, _) => s = "") xs)
      orelse error "missing module name";
    val graphs = get_modules thy;
    val defs = mk_deftab thy;
    val gr = new_node ("<Top>", (NONE, module, ""))
      (List.foldl (fn ((gr, (tab1, tab2)), (gr', (tab1', tab2'))) =>
        (Graph.merge (fn ((_, module, _), (_, module', _)) =>
           module = module') (gr, gr'),
         (merge_nametabs (tab1, tab1'), merge_nametabs (tab2, tab2')))) emptygr
           (map (fn s => case Symtab.lookup graphs s of
                NONE => error ("Undefined code module: " ^ s)
              | SOME gr => gr) modules))
      handle Graph.DUP k => error ("Duplicate code for " ^ k);
    fun expand (t as Abs _) = t
      | expand t = (case fastype_of t of
          Type ("fun", [T, U]) => Abs ("x", T, t $ Bound 0) | _ => t);
    val (ps, gr') = fold_map (fn (s, t) => fn gr => apfst (pair s)
      (invoke_codegen thy defs "<Top>" module false t gr))
        (map (apsnd (expand o preprocess_term thy o prep_term thy)) xs) gr;
    val code = map_filter
      (fn ("", _) => NONE
        | (s', p) => SOME (string_of (Pretty.block
          [str ("val " ^ s' ^ " ="), Pretty.brk 1, p, str ";"]))) ps;
    val code' = space_implode "\n\n" code ^ "\n\n";
    val code'' =
      map_filter (fn (name, s) =>
          if member (op =) (!mode) "library" andalso name = module andalso null code
          then NONE
          else SOME (name, mk_struct name s))
        ((if null code then I
          else add_to_module module code')
           (output_code (fst gr') (if_library "" module) ["<Top>"]))
  in
    (code'', del_nodes ["<Top>"] gr')
  end;

val generate_code_i = gen_generate_code Sign.cert_term;
val generate_code = gen_generate_code OldGoals.read_term;


(**** Reflection ****)

val strip_tname = implode o tl o explode;

fun pretty_list xs = Pretty.block (str "[" ::
  flat (separate [str ",", Pretty.brk 1] (map single xs)) @
  [str "]"]);

fun mk_type p (TVar ((s, i), _)) = str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "T")
  | mk_type p (TFree (s, _)) = str (strip_tname s ^ "T")
  | mk_type p (Type (s, Ts)) = (if p then parens else I) (Pretty.block
      [str "Type", Pretty.brk 1, str ("(\"" ^ s ^ "\","),
       Pretty.brk 1, pretty_list (map (mk_type false) Ts), str ")"]);

fun mk_term_of gr module p (TVar ((s, i), _)) = str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "F")
  | mk_term_of gr module p (TFree (s, _)) = str (strip_tname s ^ "F")
  | mk_term_of gr module p (Type (s, Ts)) = (if p then parens else I)
      (Pretty.block (separate (Pretty.brk 1)
        (str (mk_qual_id module
          (get_type_id' (fn s' => "term_of_" ^ s') gr s)) ::
        maps (fn T =>
          [mk_term_of gr module true T, mk_type true T]) Ts)));


(**** Test data generators ****)

fun mk_gen gr module p xs a (TVar ((s, i), _)) = str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "G")
  | mk_gen gr module p xs a (TFree (s, _)) = str (strip_tname s ^ "G")
  | mk_gen gr module p xs a (Type (tyc as (s, Ts))) = (if p then parens else I)
      (Pretty.block (separate (Pretty.brk 1)
        (str (mk_qual_id module (get_type_id' (fn s' => "gen_" ^ s') gr s) ^
          (if member (op =) xs s then "'" else "")) ::
         (case tyc of
            ("fun", [T, U]) =>
              [mk_term_of gr module true T, mk_type true T,
               mk_gen gr module true xs a U, mk_type true U]
          | _ => maps (fn T =>
              [mk_gen gr module true xs a T, mk_type true T]) Ts) @
         (if member (op =) xs s then [str a] else []))));

val test_fn : (int -> term list option) ref = ref (fn _ => NONE);

fun test_term ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val (code, gr) = setmp mode ["term_of", "test"]
      (generate_code_i thy [] "Generated") [("testf", t)];
    val Ts = map snd (fst (strip_abs t));
    val args = map_index (fn (i, T) => ("arg" ^ string_of_int i, T)) Ts;
    val s = "structure TestTerm =\nstruct\n\n" ^
      cat_lines (map snd code) ^
      "\nopen Generated;\n\n" ^ string_of
        (Pretty.block [str "val () = Codegen.test_fn :=",
          Pretty.brk 1, str ("(fn i =>"), Pretty.brk 1,
          mk_let (map (fn (s, T) =>
              (mk_tuple [str s, str (s ^ "_t")],
               Pretty.block [mk_gen gr "Generated" false [] "" T, Pretty.brk 1,
                 str "i"])) args)
            (Pretty.block [str "if ",
              mk_app false (str "testf") (map (str o fst) args),
              Pretty.brk 1, str "then NONE",
              Pretty.brk 1, str "else ",
              Pretty.block [str "SOME ", Pretty.block (str "[" ::
                Pretty.commas (map (fn (s, _) => str (s ^ "_t ()")) args) @
                  [str "]"])]]),
          str ");"]) ^
      "\n\nend;\n";
    val _ = ML_Context.eval_in (SOME ctxt) false Position.none s;
  in ! test_fn end;



(**** Evaluator for terms ****)

val eval_result = ref (fn () => Bound 0);

fun eval_term thy t =
  let
    val ctxt = ProofContext.init thy;
    val e =
      let
        val _ = (null (Term.add_tvars t []) andalso null (Term.add_tfrees t [])) orelse
          error "Term to be evaluated contains type variables";
        val _ = (null (Term.add_vars t []) andalso null (Term.add_frees t [])) orelse
          error "Term to be evaluated contains variables";
        val (code, gr) = setmp mode ["term_of"]
          (generate_code_i thy [] "Generated")
          [("result", Abs ("x", TFree ("'a", []), t))];
        val s = "structure EvalTerm =\nstruct\n\n" ^
          cat_lines (map snd code) ^
          "\nopen Generated;\n\n" ^ string_of
            (Pretty.block [str "val () = Codegen.eval_result := (fn () =>",
              Pretty.brk 1,
              mk_app false (mk_term_of gr "Generated" false (fastype_of t))
                [str "(result ())"],
              str ");"]) ^
          "\n\nend;\n";
        val _ = NAMED_CRITICAL "codegen" (fn () =>
          ML_Context.eval_in (SOME ctxt) false Position.none s);
      in !eval_result end;
  in e () end;

val (_, evaluation_conv) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (Binding.name "evaluation", fn ct =>
    let
      val thy = Thm.theory_of_cterm ct;
      val t = Thm.term_of ct;
    in Thm.cterm_of thy (Logic.mk_equals (t, eval_term thy t)) end)));


(**** Interface ****)

fun parse_mixfix rd s =
  (case Scan.finite Symbol.stopper (Scan.repeat
     (   $$ "_" >> K Arg
      || $$ "?" >> K Ignore
      || $$ "\\<module>" >> K Module
      || $$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length)
      || $$ "{" |-- $$ "*" |-- Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.is_regular
            || Scan.unless ($$ "*" -- $$ "}") (Scan.one Symbol.is_regular)) --|
         $$ "*" --| $$ "}" >> (Quote o rd o implode)
      || Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.is_regular
            || Scan.unless ($$ "_" || $$ "?" || $$ "\\<module>" || $$ "/" || $$ "{" |-- $$ "*")
                 (Scan.one Symbol.is_regular)) >> (Pretty o str o implode)))
       (Symbol.explode s) of
     (p, []) => p
   | _ => error ("Malformed annotation: " ^ quote s));


structure P = OuterParse and K = OuterKeyword;

val _ = List.app OuterKeyword.keyword ["attach", "file", "contains"];

fun strip_whitespace s = implode (fst (take_suffix (fn c => c = "\n" orelse c = " ")
  (snd (take_prefix (fn c => c = "\n" orelse c = " ") (explode s))))) ^ "\n";

val parse_attach = Scan.repeat (P.$$$ "attach" |--
  Scan.optional (P.$$$ "(" |-- P.xname --| P.$$$ ")") "" --
    (P.verbatim >> strip_whitespace));

val _ =
  OuterSyntax.command "types_code"
  "associate types with target language types" K.thy_decl
    (Scan.repeat1 (P.xname --| P.$$$ "(" -- P.string --| P.$$$ ")" -- parse_attach) >>
     (fn xs => Toplevel.theory (fn thy => fold (assoc_type o
       (fn ((name, mfx), aux) => (name, (parse_mixfix
         (Syntax.read_typ_global thy) mfx, aux)))) xs thy)));

val _ =
  OuterSyntax.command "consts_code"
  "associate constants with target language code" K.thy_decl
    (Scan.repeat1
       (P.term --|
        P.$$$ "(" -- P.string --| P.$$$ ")" -- parse_attach) >>
     (fn xs => Toplevel.theory (fn thy => fold (assoc_const o
       (fn ((const, mfx), aux) =>
         (const, (parse_mixfix (Syntax.read_term_global thy) mfx, aux)))) xs thy)));

fun parse_code lib =
  Scan.optional (P.$$$ "(" |-- P.enum "," P.xname --| P.$$$ ")") (!mode) --
  (if lib then Scan.optional P.name "" else P.name) --
  Scan.option (P.$$$ "file" |-- P.name) --
  (if lib then Scan.succeed []
   else Scan.optional (P.$$$ "imports" |-- Scan.repeat1 P.name) []) --|
  P.$$$ "contains" --
  (   Scan.repeat1 (P.name --| P.$$$ "=" -- P.term)
   || Scan.repeat1 (P.term >> pair "")) >>
  (fn ((((mode', module), opt_fname), modules), xs) => Toplevel.theory (fn thy =>
    let
      val mode'' = (if lib then insert (op =) "library" else I) (remove (op =) "library" mode');
      val (code, gr) = setmp mode mode'' (generate_code thy modules module) xs;
      val thy' = thy |> Context.theory_map (ML_Context.exec (fn () =>
        (case opt_fname of
          NONE => ML_Context.eval false Position.none (cat_lines (map snd code))
        | SOME fname =>
            if lib then app (fn (name, s) => File.write
                (Path.append (Path.explode fname) (Path.basic (name ^ ".ML"))) s)
              (("ROOT", implode (map (fn (name, _) =>
                  "use \"" ^ name ^ ".ML\";\n") code)) :: code)
            else File.write (Path.explode fname) (snd (hd code)))));
    in
      if lib then thy'
      else map_modules (Symtab.update (module, gr)) thy'
    end));

val setup = add_codegen "default" default_codegen
  #> add_tycodegen "default" default_tycodegen
  #> add_preprocessor unfold_preprocessor;

val _ =
  OuterSyntax.command "code_library"
    "generates code for terms (one structure for each theory)" K.thy_decl
    (parse_code true);

val _ =
  OuterSyntax.command "code_module"
    "generates code for terms (single structure, incremental)" K.thy_decl
    (parse_code false);

end;
