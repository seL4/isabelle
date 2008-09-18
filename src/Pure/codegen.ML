(*  Title:      Pure/codegen.ML
    ID:         $Id$
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
    codegr * term -> codegr * Pretty.T
  val invoke_tycodegen: theory -> deftab -> string -> string -> bool ->
    codegr * typ -> codegr * Pretty.T
  val mk_id: string -> string
  val mk_qual_id: string -> string * string -> string
  val mk_const_id: string -> string -> codegr -> codegr * (string * string)
  val get_const_id: string -> codegr -> string * string
  val mk_type_id: string -> string -> codegr -> codegr * (string * string)
  val get_type_id: string -> codegr -> string * string
  val thyname_of_type: theory -> string -> string
  val thyname_of_const: theory -> string -> string
  val rename_terms: term list -> term list
  val rename_term: term -> term
  val new_names: term -> string list -> string list
  val new_name: term -> string -> string
  val if_library: 'a -> 'a -> 'a
  val get_defn: theory -> deftab -> string -> typ ->
    ((typ * (string * (term list * term))) * int option) option
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
  val test_fn: (int -> (string * term) list option) ref
  val test_term: theory -> bool -> int -> int -> term -> (string * term) list option
  val auto_quickcheck: bool ref
  val auto_quickcheck_time_limit: int ref
  val eval_result: (unit -> term) ref
  val eval_term: theory -> term -> term
  val evaluation_conv: cterm -> thm
  val parse_mixfix: (string -> 'a) -> string -> 'a mixfix list
  val quotes_of: 'a mixfix list -> 'a list
  val num_args_of: 'a mixfix list -> int
  val replace_quotes: 'b list -> 'a mixfix list -> 'b mixfix list
  val mk_deftab: theory -> deftab
  val add_unfold: thm -> theory -> theory

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
      (term list *    (* parameters *)
       term)))        (* right-hand side *)
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
  codegr ->    (* code dependency graph *)
  string ->    (* node name of caller (for recording dependencies) *)
  string ->    (* module name of caller (for modular code generation) *)
  bool ->      (* whether to parenthesize generated expression *)
  'a ->        (* item to generate code from *)
  (codegr * Pretty.T) option;

(* parameters for random testing *)

type test_params =
  {size: int, iterations: int, default_type: typ option};

fun merge_test_params
  {size = size1, iterations = iterations1, default_type = default_type1}
  {size = size2, iterations = iterations2, default_type = default_type2} =
  {size = Int.max (size1, size2),
   iterations = Int.max (iterations1, iterations2),
   default_type = case default_type1 of
       NONE => default_type2
     | _ => default_type1};

val default_test_params : test_params =
  {size = 10, iterations = 100, default_type = NONE};

fun set_size size ({iterations, default_type, ...} : test_params) =
  {size = size, iterations = iterations, default_type = default_type};

fun set_iterations iterations ({size, default_type, ...} : test_params) =
  {size = size, iterations = iterations, default_type = default_type};

fun set_default_type s thy ({size, iterations, ...} : test_params) =
  {size = size, iterations = iterations,
   default_type = SOME (Syntax.read_typ_global thy s)};


(* theory data *)

structure CodegenData = TheoryDataFun
(
  type T =
    {codegens : (string * term codegen) list,
     tycodegens : (string * typ codegen) list,
     consts : ((string * typ) * (term mixfix list * (string * string) list)) list,
     types : (string * (typ mixfix list * (string * string) list)) list,
     preprocs: (stamp * (theory -> thm list -> thm list)) list,
     modules: codegr Symtab.table,
     test_params: test_params};

  val empty =
    {codegens = [], tycodegens = [], consts = [], types = [],
     preprocs = [], modules = Symtab.empty, test_params = default_test_params};
  val copy = I;
  val extend = I;

  fun merge _
    ({codegens = codegens1, tycodegens = tycodegens1,
      consts = consts1, types = types1,
      preprocs = preprocs1, modules = modules1, test_params = test_params1} : T,
     {codegens = codegens2, tycodegens = tycodegens2,
      consts = consts2, types = types2,
      preprocs = preprocs2, modules = modules2, test_params = test_params2}) =
    {codegens = AList.merge (op =) (K true) (codegens1, codegens2),
     tycodegens = AList.merge (op =) (K true) (tycodegens1, tycodegens2),
     consts = AList.merge (op =) (K true) (consts1, consts2),
     types = AList.merge (op =) (K true) (types1, types2),
     preprocs = AList.merge (op =) (K true) (preprocs1, preprocs2),
     modules = Symtab.merge (K true) (modules1, modules2),
     test_params = merge_test_params test_params1 test_params2};
);

fun print_codegens thy =
  let val {codegens, tycodegens, ...} = CodegenData.get thy in
    Pretty.writeln (Pretty.chunks
      [Pretty.strs ("term code generators:" :: map fst codegens),
       Pretty.strs ("type code generators:" :: map fst tycodegens)])
  end;



(**** access parameters for random testing ****)

fun get_test_params thy = #test_params (CodegenData.get thy);

fun map_test_params f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
    CodegenData.get thy;
  in CodegenData.put {codegens = codegens, tycodegens = tycodegens,
    consts = consts, types = types, preprocs = preprocs,
    modules = modules, test_params = f test_params} thy
  end;


(**** access modules ****)

fun get_modules thy = #modules (CodegenData.get thy);

fun map_modules f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
    CodegenData.get thy;
  in CodegenData.put {codegens = codegens, tycodegens = tycodegens,
    consts = consts, types = types, preprocs = preprocs,
    modules = f modules, test_params = test_params} thy
  end;


(**** add new code generators to theory ****)

fun add_codegen name f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
    CodegenData.get thy
  in (case AList.lookup (op =) codegens name of
      NONE => CodegenData.put {codegens = (name, f) :: codegens,
        tycodegens = tycodegens, consts = consts, types = types,
        preprocs = preprocs, modules = modules,
        test_params = test_params} thy
    | SOME _ => error ("Code generator " ^ name ^ " already declared"))
  end;

fun add_tycodegen name f thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
    CodegenData.get thy
  in (case AList.lookup (op =) tycodegens name of
      NONE => CodegenData.put {tycodegens = (name, f) :: tycodegens,
        codegens = codegens, consts = consts, types = types,
        preprocs = preprocs, modules = modules,
        test_params = test_params} thy
    | SOME _ => error ("Code generator " ^ name ^ " already declared"))
  end;


(**** preprocessors ****)

fun add_preprocessor p thy =
  let val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
    CodegenData.get thy
  in CodegenData.put {tycodegens = tycodegens,
    codegens = codegens, consts = consts, types = types,
    preprocs = (stamp (), p) :: preprocs,
    modules = modules, test_params = test_params} thy
  end;

fun preprocess thy =
  let val {preprocs, ...} = CodegenData.get thy
  in fold (fn (_, f) => f thy) preprocs end;

fun preprocess_term thy t =
  let
    val x = Free (Name.variant (add_term_names (t, [])) "x", fastype_of t);
    (* fake definition *)
    val eq = setmp quick_and_dirty true (SkipProof.make_thm thy)
      (Logic.mk_equals (x, t));
    fun err () = error "preprocess_term: bad preprocessor"
  in case map prop_of (preprocess thy [eq]) of
      [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
    | _ => err ()
  end;

fun add_unfold eqn =
  let
    val thy = Thm.theory_of_thm eqn;
    val ctxt = ProofContext.init thy;
    val eqn' = LocalDefs.meta_rewrite_rule ctxt eqn;
    val names = term_consts (fst (Logic.dest_equals (prop_of eqn')));
    fun prep thy = map (fn th =>
      let val prop = prop_of th
      in
        if forall (fn name => exists_Const (equal name o fst) prop) names
        then rewrite_rule [eqn'] (Thm.transfer thy th)
        else th
      end)
  in add_preprocessor prep end;


(**** associate constants with target language code ****)

fun gen_assoc_const prep_const (raw_const, syn) thy =
  let
    val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
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
        modules = modules, test_params = test_params} thy
    | SOME _ => error ("Constant " ^ cname ^ " already associated with code")
  end;

val assoc_const_i = gen_assoc_const (K I);
val assoc_const = gen_assoc_const Code_Unit.read_bare_const;


(**** associate types with target language types ****)

fun assoc_type (s, syn) thy =
  let
    val {codegens, tycodegens, consts, types, preprocs, modules, test_params} =
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
            preprocs = preprocs, modules = modules, test_params = test_params} thy
        | SOME _ => error ("Type " ^ tc ^ " already associated with code"))
    | _ => error ("Not a type constructor: " ^ s)
  end;

fun get_assoc_type thy = AList.lookup (op =) ((#types o CodegenData.get) thy);


(**** make valid ML identifiers ****)

fun is_ascii_letdig x = Symbol.is_ascii_letter x orelse
  Symbol.is_ascii_digit x orelse Symbol.is_ascii_quasi x;

fun dest_sym s = (case split_last (snd (take_prefix (equal "\\") (explode s))) of
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
    val s' = space_implode "_" (maps (check_str o Symbol.explode) (NameSpace.explode s))
  in
    if Symbol.is_ascii_letter (hd (explode s')) then s' else "id_" ^ s'
  end;

fun mk_long_id (p as (tab, used)) module s =
  let
    fun find_name [] = sys_error "mk_long_id"
      | find_name (ys :: yss) =
          let
            val s' = NameSpace.implode ys
            val s'' = NameSpace.append module s'
          in case Symtab.lookup used s'' of
              NONE => ((module, s'),
                (Symtab.update_new (s, (module, s')) tab,
                 Symtab.update_new (s'', ()) used))
            | SOME _ => find_name yss
          end
  in case Symtab.lookup tab s of
      NONE => find_name (Library.suffixes1 (NameSpace.explode s))
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
  in ((gr, (tab1', tab2)), (module, s'')) end;

fun get_const_id cname (gr, (tab1, tab2)) =
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
  in ((gr, (tab1, tab2')), (module, s'')) end;

fun get_type_id tyname (gr, (tab1, tab2)) =
  case Symtab.lookup (fst tab2) tyname of
    NONE => error ("get_type_id: no such type: " ^ quote tyname)
  | SOME (module, s) =>
      let
        val s' = mk_id s;
        val s'' = if ML_Syntax.is_reserved s' then s' ^ "_type" else s'
      in (module, s'') end;

fun get_type_id' f tyname tab = apsnd f (get_type_id tyname tab);

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
    val names = List.foldr add_term_names
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
  Type.raw_instance (T1, Logic.legacy_varifyT T2);

fun get_assoc_code thy (s, T) = Option.map snd (find_first (fn ((s', T'), _) =>
  s = s' andalso is_instance T T') (#consts (CodegenData.get thy)));

fun get_aux_code xs = map_filter (fn (m, code) =>
  if m = "" orelse member (op =) (!mode) m then SOME code else NONE) xs;

fun mk_deftab thy =
  let
    val axmss = map (fn thy' => (Context.theory_name thy', Theory.axiom_table thy'))
      (thy :: Theory.ancestors_of thy);
    fun prep_def def = (case preprocess thy [def] of
      [def'] => prop_of def' | _ => error "mk_deftab: bad preprocessor");
    fun dest t =
      let
        val (lhs, rhs) = Logic.dest_equals t;
        val (c, args) = strip_comb lhs;
        val (s, T) = dest_Const c
      in if forall is_Var args then SOME (s, (T, (args, rhs))) else NONE
      end handle TERM _ => NONE;
    fun add_def thyname (name, t) = (case dest t of
        NONE => I
      | SOME _ => (case dest (prep_def (Thm.get_axiom_i thy name)) of
          NONE => I
        | SOME (s, (T, (args, rhs))) => Symtab.map_default (s, [])
            (cons (T, (thyname, split_last (rename_terms (args @ [rhs])))))))
  in
    fold (fn (thyname, axms) => Symtab.fold (add_def thyname) axms) axmss Symtab.empty
  end;

fun get_defn thy defs s T = (case Symtab.lookup defs s of
    NONE => NONE
  | SOME ds =>
      let val i = find_index (is_instance T o fst) ds
      in if i >= 0 then
          SOME (List.nth (ds, i), if length ds = 1 then NONE else SOME i)
        else NONE
      end);


(**** invoke suitable code generator for term / type ****)

fun codegen_error (gr, _) dep s =
  error (s ^ "\nrequired by:\n" ^ commas (Graph.all_succs gr [dep]));

fun invoke_codegen thy defs dep module brack (gr, t) = (case get_first
   (fn (_, f) => f thy defs gr dep module brack t) (#codegens (CodegenData.get thy)) of
      NONE => codegen_error gr dep ("Unable to generate code for term:\n" ^
        Syntax.string_of_term_global thy t)
    | SOME x => x);

fun invoke_tycodegen thy defs dep module brack (gr, T) = (case get_first
   (fn (_, f) => f thy defs gr dep module brack T) (#tycodegens (CodegenData.get thy)) of
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
  (map (fst o fst o dest_Var) (term_vars t) union
    add_term_names (t, ML_Syntax.reserved_names)) (map mk_id xs);

fun new_name t x = hd (new_names t [x]);

fun if_library x y = if member (op =) (!mode) "library" then x else y;

fun default_codegen thy defs gr dep module brack t =
  let
    val (u, ts) = strip_comb t;
    fun codegens brack = foldl_map (invoke_codegen thy defs dep module brack)
  in (case u of
      Var ((s, i), T) =>
        let
          val (gr', ps) = codegens true (gr, ts);
          val (gr'', _) = invoke_tycodegen thy defs dep module false (gr', T)
        in SOME (gr'', mk_app brack (str (s ^
           (if i=0 then "" else string_of_int i))) ps)
        end

    | Free (s, T) =>
        let
          val (gr', ps) = codegens true (gr, ts);
          val (gr'', _) = invoke_tycodegen thy defs dep module false (gr', T)
        in SOME (gr'', mk_app brack (str s) ps) end

    | Const (s, T) =>
      (case get_assoc_code thy (s, T) of
         SOME (ms, aux) =>
           let val i = num_args_of ms
           in if length ts < i then
               default_codegen thy defs gr dep module brack (eta_expand u ts i)
             else
               let
                 val (ts1, ts2) = args_of ms ts;
                 val (gr1, ps1) = codegens false (gr, ts1);
                 val (gr2, ps2) = codegens true (gr1, ts2);
                 val (gr3, ps3) = codegens false (gr2, quotes_of ms);
                 val (gr4, _) = invoke_tycodegen thy defs dep module false
                   (gr3, funpow (length ts) (hd o tl o snd o dest_Type) T);
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
                       [] => (gr4, p module)
                     | xs => (add_edge (node_id, dep) (new_node
                         (node_id, (NONE, module', cat_lines xs ^ "\n")) gr4),
                           p module'))
                 | SOME (_, module'', _) =>
                     (add_edge (node_id, dep) gr4, p module''))
               end
           end
       | NONE => (case get_defn thy defs s T of
           NONE => NONE
         | SOME ((U, (thyname, (args, rhs))), k) =>
             let
               val module' = if_library thyname module;
               val suffix = (case k of NONE => "" | SOME i => " def" ^ string_of_int i);
               val node_id = s ^ suffix;
               val (gr', (ps, def_id)) = codegens true (gr, ts) |>>>
                 mk_const_id module' (s ^ suffix);
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
                     val (gr1, p') = invoke_codegen thy defs node_id module' false
                       (add_edge (node_id, dep)
                          (new_node (node_id, (NONE, "", "")) gr'), rhs');
                     val (gr2, xs) = codegens false (gr1, args');
                     val (gr3, _) = invoke_tycodegen thy defs dep module false (gr2, T);
                     val (gr4, ty) = invoke_tycodegen thy defs node_id module' false (gr3, U);
                   in (map_node node_id (K (NONE, module', string_of
                       (Pretty.block (separate (Pretty.brk 1)
                         (if null args' then
                            [str ("val " ^ snd def_id ^ " :"), ty]
                          else str ("fun " ^ snd def_id) :: xs) @
                        [str " =", Pretty.brk 1, p', str ";"])) ^ "\n\n")) gr4,
                     p)
                   end
               | SOME _ => (add_edge (node_id, dep) gr', p))
             end))

    | Abs _ =>
      let
        val (bs, Ts) = ListPair.unzip (strip_abs_vars u);
        val t = strip_abs_body u
        val bs' = new_names t bs;
        val (gr1, ps) = codegens true (gr, ts);
        val (gr2, p) = invoke_codegen thy defs dep module false
          (gr1, subst_bounds (map Free (rev (bs' ~~ Ts)), t));
      in
        SOME (gr2, mk_app brack (Pretty.block (str "(" :: pretty_fn bs' p @
          [str ")"])) ps)
      end

    | _ => NONE)
  end;

fun default_tycodegen thy defs gr dep module brack (TVar ((s, i), _)) =
      SOME (gr, str (s ^ (if i = 0 then "" else string_of_int i)))
  | default_tycodegen thy defs gr dep module brack (TFree (s, _)) =
      SOME (gr, str s)
  | default_tycodegen thy defs gr dep module brack (Type (s, Ts)) =
      (case AList.lookup (op =) ((#types o CodegenData.get) thy) s of
         NONE => NONE
       | SOME (ms, aux) =>
           let
             val (gr', ps) = foldl_map
               (invoke_tycodegen thy defs dep module false)
               (gr, fst (args_of ms Ts));
             val (gr'', qs) = foldl_map
               (invoke_tycodegen thy defs dep module false)
               (gr', quotes_of ms);
             val module' = if_library (thyname_of_type thy s) module;
             val node_id = s ^ " (type)";
             fun p module' = Pretty.block (pretty_mixfix module module' ms ps qs)
           in SOME (case try (get_node gr'') node_id of
               NONE => (case get_aux_code aux of
                   [] => (gr'', p module')
                 | xs => (fst (mk_type_id module' s
                       (add_edge (node_id, dep) (new_node (node_id,
                         (NONE, module', cat_lines xs ^ "\n")) gr''))),
                     p module'))
             | SOME (_, module'', _) =>
                 (add_edge (node_id, dep) gr'', p module''))
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
              (find_first (equal b o #2 o Graph.get_node gr)
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
            (filter_out (equal module) (map (#2 o Graph.get_node gr)
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
        member (op =) (!mode) "library" andalso forall (equal "" o fst) xs)
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
    val (gr', ps) = foldl_map (fn (gr, (s, t)) => apsnd (pair s)
      (invoke_codegen thy defs "<Top>" module false (gr, t)))
        (gr, map (apsnd (expand o preprocess_term thy o prep_term thy)) xs);
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
          (get_type_id' (fn s' => "term_of_" ^ s') s gr)) ::
        maps (fn T =>
          [mk_term_of gr module true T, mk_type true T]) Ts)));


(**** Test data generators ****)

fun mk_gen gr module p xs a (TVar ((s, i), _)) = str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "G")
  | mk_gen gr module p xs a (TFree (s, _)) = str (strip_tname s ^ "G")
  | mk_gen gr module p xs a (Type (tyc as (s, Ts))) = (if p then parens else I)
      (Pretty.block (separate (Pretty.brk 1)
        (str (mk_qual_id module (get_type_id' (fn s' => "gen_" ^ s') s gr) ^
          (if member (op =) xs s then "'" else "")) ::
         (case tyc of
            ("fun", [T, U]) =>
              [mk_term_of gr module true T, mk_type true T,
               mk_gen gr module true xs a U, mk_type true U]
          | _ => maps (fn T =>
              [mk_gen gr module true xs a T, mk_type true T]) Ts) @
         (if member (op =) xs s then [str a] else []))));

val test_fn : (int -> (string * term) list option) ref = ref (fn _ => NONE);

fun test_term thy quiet sz i t =
  let
    val ctxt = ProofContext.init thy;
    val _ = (null (term_tvars t) andalso null (term_tfrees t)) orelse
      error "Term to be tested contains type variables";
    val _ = null (term_vars t) orelse
      error "Term to be tested contains schematic variables";
    val frees = map dest_Free (term_frees t);
    val frees' = frees ~~
      map (fn i => "arg" ^ string_of_int i) (1 upto length frees);
    val (code, gr) = setmp mode ["term_of", "test"]
      (generate_code_i thy [] "Generated") [("testf", list_abs_free (frees, t))];
    val s = "structure TestTerm =\nstruct\n\n" ^
      cat_lines (map snd code) ^
      "\nopen Generated;\n\n" ^ string_of
        (Pretty.block [str "val () = Codegen.test_fn :=",
          Pretty.brk 1, str ("(fn i =>"), Pretty.brk 1,
          mk_let (map (fn ((s, T), s') =>
              (mk_tuple [str s', str (s' ^ "_t")],
               Pretty.block [mk_gen gr "Generated" false [] "" T, Pretty.brk 1,
                 str "i"])) frees')
            (Pretty.block [str "if ",
              mk_app false (str "testf") (map (str o snd) frees'),
              Pretty.brk 1, str "then NONE",
              Pretty.brk 1, str "else ",
              Pretty.block [str "SOME ", Pretty.block (str "[" ::
                flat (separate [str ",", Pretty.brk 1]
                  (map (fn ((s, T), s') => [Pretty.block
                    [str ("(" ^ quote (Symbol.escape s) ^ ","), Pretty.brk 1,
                     str (s' ^ "_t ())")]]) frees')) @
                  [str "]"])]]),
          str ");"]) ^
      "\n\nend;\n";
    val _ = ML_Context.eval_in (SOME ctxt) false Position.none s;
    fun iter f k = if k > i then NONE
      else (case (f () handle Match =>
          (if quiet then ()
           else warning "Exception Match raised in generated code"; NONE)) of
        NONE => iter f (k+1) | SOME x => SOME x);
    fun test k = if k > sz then NONE
      else (if quiet then () else priority ("Test data size: " ^ string_of_int k);
        case iter (fn () => !test_fn k) 1 of
          NONE => test (k+1) | SOME x => SOME x);
  in test 0 end;

fun test_goal quiet ({size, iterations, default_type}, tvinsts) i assms state =
  let
    val thy = Proof.theory_of state;
    fun strip (Const ("all", _) $ Abs (_, _, t)) = strip t
      | strip t = t;
    val (_, (_, st)) = Proof.get_goal state;
    val (gi, frees) = Logic.goal_params (prop_of st) i;
    val gi' = ObjectLogic.atomize_term thy (map_types
      (map_type_tfree (fn p as (s, S) =>
        let val T = the_default (the_default (TFree p) default_type)
          (AList.lookup (op =) tvinsts s)
        in if Sign.of_sort thy (T, S) then T
          else error ("Type " ^ Syntax.string_of_typ_global thy T ^
            " to be substituted for variable " ^
            Syntax.string_of_typ_global thy (TFree p) ^ "\ndoes not have sort " ^
            Syntax.string_of_sort_global thy S)
        end))
      (Logic.list_implies (assms, subst_bounds (frees, strip gi))));
  in test_term thy quiet size iterations gi' end;

fun pretty_counterex ctxt NONE = Pretty.str "No counterexamples found."
  | pretty_counterex ctxt (SOME cex) =
      Pretty.chunks (Pretty.str "Counterexample found:\n" ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) cex);

val auto_quickcheck = ref false;
val auto_quickcheck_time_limit = ref 5000;

fun test_goal' int state =
  let
    val ctxt = Proof.context_of state;
    val assms = map term_of (Assumption.assms_of ctxt);
    val params = get_test_params (Proof.theory_of state);
    fun test () =
      let
        val res = TimeLimit.timeLimit (Time.fromMilliseconds (!auto_quickcheck_time_limit))
          (try (test_goal true (params, []) 1 assms)) state;
      in
        case res of
          NONE => state
        | SOME NONE => state
        | SOME cex => Proof.goal_message (fn () => Pretty.chunks [Pretty.str "",
            Pretty.mark Markup.hilite (pretty_counterex ctxt cex)]) state
      end handle TimeLimit.TimeOut => (warning "Auto quickcheck: timeout."; state);
  in
    if int andalso !auto_quickcheck andalso not (!Toplevel.quiet)
    then test ()
    else state
  end;


(**** Evaluator for terms ****)

val eval_result = ref (fn () => Bound 0);

fun eval_term thy t =
  let
    val ctxt = ProofContext.init thy;
    val e =
      let
        val _ = (null (term_tvars t) andalso null (term_tfrees t)) orelse
          error "Term to be evaluated contains type variables";
        val _ = (null (term_vars t) andalso null (term_frees t)) orelse
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
  (Thm.add_oracle ("evaluation", fn ct =>
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

fun strip_whitespace s = implode (fst (take_suffix (equal "\n" orf equal " ")
  (snd (take_prefix (equal "\n" orf equal " ") (explode s))))) ^ "\n";

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
         (const, (parse_mixfix (OldGoals.read_term thy) mfx, aux)))) xs thy)));

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
  #> Value.add_evaluator ("SML", eval_term o ProofContext.theory_of)
  #> Code.add_attribute ("unfold", Scan.succeed (Thm.declaration_attribute
       (fn thm => Context.mapping (add_unfold thm #> Code.add_inline thm) I)));

val _ = Context.>> (Specification.add_theorem_hook test_goal');

val _ =
  OuterSyntax.command "code_library"
    "generates code for terms (one structure for each theory)" K.thy_decl
    (parse_code true);

val _ =
  OuterSyntax.command "code_module"
    "generates code for terms (single structure, incremental)" K.thy_decl
    (parse_code false);

val params =
  [("size", P.nat >> (K o set_size)),
   ("iterations", P.nat >> (K o set_iterations)),
   ("default_type", P.typ >> set_default_type)];

val parse_test_params = P.short_ident :|-- (fn s =>
  P.$$$ "=" |-- (AList.lookup (op =) params s |> the_default Scan.fail));

fun parse_tyinst xs =
  (P.type_ident --| P.$$$ "=" -- P.typ >> (fn (v, s) => fn thy =>
    fn (x, ys) => (x, (v, Syntax.read_typ_global thy s) :: ys))) xs;

val _ =
  OuterSyntax.command "quickcheck_params" "set parameters for random testing" K.thy_decl
    (P.$$$ "[" |-- P.list1 parse_test_params --| P.$$$ "]" >>
      (fn fs => Toplevel.theory (fn thy =>
         map_test_params (Library.apply (map (fn f => f thy) fs)) thy)));

val _ =
  OuterSyntax.command "quickcheck" "try to find counterexample for subgoal" K.diag
  (Scan.option (P.$$$ "[" |-- P.list1
    (   parse_test_params >> (fn f => fn thy => apfst (f thy))
     || parse_tyinst) --| P.$$$ "]") -- Scan.optional P.nat 1 >>
    (fn (ps, g) => Toplevel.keep (fn st => Toplevel.proof_of st |>
      test_goal false (Library.apply (the_default []
          (Option.map (map (fn f => f (Toplevel.theory_of st))) ps))
        (get_test_params (Toplevel.theory_of st), [])) g [] |>
      pretty_counterex (Toplevel.context_of st) |> Pretty.writeln)));

end;

val auto_quickcheck = Codegen.auto_quickcheck;
val auto_quickcheck_time_limit = Codegen.auto_quickcheck_time_limit;

