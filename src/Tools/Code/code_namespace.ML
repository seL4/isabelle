(*  Title:      Tools/Code/code_namespace.ML
    Author:     Florian Haftmann, TU Muenchen

Mastering target language namespaces.
*)

signature CODE_NAMESPACE =
sig
  val variant_case_insensitive: string -> Name.context -> string * Name.context

  datatype export = Private | Opaque | Public
  val is_public: export -> bool
  val not_private: export -> bool
  val join_exports: export list -> export

  type flat_program
  val flat_program: Proof.context
    -> { module_prefix: string, module_name: string,
    reserved: Name.context, identifiers: Code_Printer.identifiers, empty_nsp: 'a,
    namify_stmt: Code_Thingol.stmt -> string -> 'a -> string * 'a,
    modify_stmt: Code_Thingol.stmt -> Code_Thingol.stmt option }
      -> Code_Symbol.T list -> Code_Thingol.program
      -> { deresolver: string -> Code_Symbol.T -> string,
           flat_program: flat_program }

  datatype ('a, 'b) node =
      Dummy
    | Stmt of export * 'a
    | Module of ('b * (string * ('a, 'b) node) Code_Symbol.Graph.T)
  type ('a, 'b) hierarchical_program
  val hierarchical_program: Proof.context
    -> { module_name: string,
    reserved: Name.context, identifiers: Code_Printer.identifiers,
    empty_nsp: 'c, namify_module: string -> 'c -> string * 'c,
    namify_stmt: Code_Thingol.stmt -> string -> 'c -> string * 'c,
    cyclic_modules: bool,
    class_transitive: bool, class_relation_public: bool,
    empty_data: 'b, memorize_data: Code_Symbol.T -> 'b -> 'b,
    modify_stmts: (Code_Symbol.T * (export * Code_Thingol.stmt)) list -> (export * 'a) option list }
      -> Code_Symbol.T list -> Code_Thingol.program
      -> { deresolver: string list -> Code_Symbol.T -> string,
           hierarchical_program: ('a, 'b) hierarchical_program }
  val print_hierarchical: { print_module: string list -> string -> 'b -> 'c list -> 'c,
    print_stmt: string list -> Code_Symbol.T * (export * 'a) -> 'c,
    lift_markup: (Pretty.T -> Pretty.T) -> 'c -> 'c }
      -> ('a, 'b) hierarchical_program -> 'c list
end;

structure Code_Namespace : CODE_NAMESPACE =
struct

(** name handling on case-insensitive file systems **)

fun restore_for cs =
  if forall Symbol.is_ascii_upper cs then map Symbol.to_ascii_upper
  else if Symbol.is_ascii_upper (nth cs 0) then nth_map 0 Symbol.to_ascii_upper
  else I;

fun variant_case_insensitive s ctxt =
  let
    val cs = Symbol.explode s;
    val s_lower = implode (map Symbol.to_ascii_lower cs);
    val restore = implode o restore_for cs o Symbol.explode;
  in
    ctxt
    |> Name.variant s_lower
    |>> restore
  end;


(** export **)

datatype export = Private | Opaque | Public;

fun is_public Public = true
  | is_public _ = false;

fun not_private Public = true
  | not_private Opaque = true
  | not_private _ = false;

fun mark_export Public _ = Public
  | mark_export _ Public = Public
  | mark_export Opaque _ = Opaque
  | mark_export _ Opaque = Opaque
  | mark_export _ _ = Private;

fun join_exports exports = fold mark_export exports Private;

fun dependent_exports { program = program, class_transitive = class_transitive } =
  let
    fun is_datatype_or_class (Code_Symbol.Type_Constructor _) = true
      | is_datatype_or_class (Code_Symbol.Type_Class _) = true
      | is_datatype_or_class _ = false;
    fun is_relevant (Code_Symbol.Class_Relation _) = true
      | is_relevant sym = is_datatype_or_class sym;
    val proto_gr = Code_Symbol.Graph.restrict is_relevant program;
    val gr =
      proto_gr
      |> Code_Symbol.Graph.fold
          (fn (sym, (_, (_, deps))) =>
            if is_relevant sym
            then I
            else
              Code_Symbol.Graph.new_node (sym, Code_Thingol.NoStmt)
              #> Code_Symbol.Graph.Keys.fold
               (fn sym' =>
                if is_relevant sym'
                then Code_Symbol.Graph.add_edge (sym, sym')
                else I) deps) program
      |> class_transitive ?
          Code_Symbol.Graph.fold (fn (sym as Code_Symbol.Type_Class _, _) =>
            fold (curry Code_Symbol.Graph.add_edge sym)
              ((remove (op =) sym o Code_Symbol.Graph.all_succs proto_gr) [sym]) | _ => I) proto_gr
    fun deps_of sym =
      let
        val succs = Code_Symbol.Graph.Keys.dest o Code_Symbol.Graph.imm_succs gr;
        val deps1 = succs sym;
        val deps2 = [] |> fold (union (op =)) (map succs deps1) |> subtract (op =) deps1
      in (deps1, deps2) end;
  in
    { is_datatype_or_class = is_datatype_or_class,
      deps_of = deps_of }
  end;

fun mark_exports_aux { program = program, prefix_of = prefix_of, map_export = map_export,
    is_datatype_or_class = is_datatype_or_class, deps_of = deps_of,
    class_relation_public = class_relation_public } prefix sym =
  let
    val export = (if is_datatype_or_class sym then Opaque else Public);
    val (dependent_export1, dependent_export2) =
      case Code_Symbol.Graph.get_node program sym of
          Code_Thingol.Fun _ => (SOME Opaque, NONE)
        | Code_Thingol.Classinst _ => (SOME Opaque, NONE)
        | Code_Thingol.Datatypecons _ => (SOME Public, SOME Opaque)
        | Code_Thingol.Classparam _ => (SOME Public, SOME Opaque)
        | Code_Thingol.Class _ => (SOME Opaque, NONE)
        | Code_Thingol.Classrel _ =>
           (if class_relation_public
            then (SOME Public, SOME Opaque)
            else (SOME Opaque, NONE))
        | _ => (NONE, NONE);
    val dependent_exports =
      case dependent_export1 of
        SOME export1 => (case dependent_export2 of
          SOME export2 =>
            let
              val (deps1, deps2) = deps_of sym
            in map (rpair export1) deps1 @ map (rpair export2) deps2 end
        | NONE => map (rpair export1) (fst (deps_of sym)))
      | NONE => [];
  in 
    map_export prefix sym (mark_export export)
    #> fold (fn (sym, export) => map_export (prefix_of sym) sym (mark_export export))
      dependent_exports
  end;

fun mark_exports { program = program, prefix_of = prefix_of, map_export = map_export,
    class_transitive = class_transitive, class_relation_public = class_relation_public } =
  let
    val { is_datatype_or_class, deps_of } =
      dependent_exports { program = program, class_transitive = class_transitive };
  in
    mark_exports_aux { program = program, prefix_of = prefix_of, map_export = map_export,
      is_datatype_or_class = is_datatype_or_class, deps_of = deps_of,
      class_relation_public = class_relation_public }
  end;


(** fundamental module name hierarchy **)

fun module_fragments' { identifiers, reserved } name =
  case Code_Symbol.lookup_module_data identifiers name of
      SOME (fragments, _) => fragments
    | NONE => map (fn fragment => fst (Name.variant fragment reserved)) (Long_Name.explode name);

fun module_fragments { module_name, identifiers, reserved } =
  if module_name = ""
  then module_fragments' { identifiers = identifiers, reserved = reserved }
  else K (Long_Name.explode module_name);

fun build_module_namespace ctxt enforce_upper { module_prefix, module_name, identifiers, reserved } program =
  let
    val module_names = Code_Symbol.Graph.fold (insert (op =) o Code_Symbol.default_prefix ctxt o fst) program [];
    val module_fragments' = module_fragments
      { module_name = module_name, identifiers = identifiers, reserved = reserved };
    val adjust_case = if enforce_upper then map (Name.enforce_case true) else I;
  in
    fold (fn name => Symtab.update (name, adjust_case (Long_Name.explode module_prefix @ module_fragments' name)))
      module_names Symtab.empty
  end;

fun prep_symbol ctxt { module_namespace, force_module, identifiers } sym =
  case Code_Symbol.lookup identifiers sym of
      NONE => ((the o Symtab.lookup module_namespace o Code_Symbol.default_prefix ctxt) sym,
        Code_Symbol.default_base sym)
    | SOME prefix_name => if null force_module then prefix_name
        else (force_module, snd prefix_name);

fun has_priority identifiers = is_some o Code_Symbol.lookup identifiers;

fun build_proto_program { empty, add_stmt, add_dep } program =
  empty
  |> Code_Symbol.Graph.fold (fn (sym, (stmt, _)) => add_stmt sym stmt) program
  |> Code_Symbol.Graph.fold (fn (sym, (_, (_, syms))) =>
      Code_Symbol.Graph.Keys.fold (add_dep sym) syms) program;

fun prioritize has_priority = uncurry append o List.partition has_priority;


(** flat program structure **)

type flat_program = ((string * (export * Code_Thingol.stmt) option) Code_Symbol.Graph.T * (string * Code_Symbol.T list) list) Graph.T;

fun flat_program ctxt { module_prefix, module_name, reserved,
    identifiers, empty_nsp, namify_stmt, modify_stmt } exports program =
  let

    (* building module name hierarchy *)
    val module_namespace = build_module_namespace ctxt true { module_prefix = module_prefix,
      module_name = module_name, identifiers = identifiers, reserved = reserved } program;
    val prep_sym = prep_symbol ctxt { module_namespace = module_namespace,
      force_module = Long_Name.explode module_name, identifiers = identifiers }
      #>> Long_Name.implode;
    val sym_priority = has_priority identifiers;

    (* distribute statements over hierarchy *)
    val mark_exports = mark_exports { program = program, prefix_of = fst o prep_sym,
      map_export = fn module_name => fn sym =>
        Graph.map_node module_name o apfst o Code_Symbol.Graph.map_node sym o apsnd o apfst,
        class_transitive = false, class_relation_public = false };
    fun add_stmt sym stmt =
      let
        val (module_name, base) = prep_sym sym;
      in
        Graph.default_node (module_name, (Code_Symbol.Graph.empty, []))
        #> (Graph.map_node module_name o apfst)
          (Code_Symbol.Graph.new_node (sym, (base, (if null exports then Public else Private, stmt))))
      end;
    fun add_dep sym sym' =
      let
        val (module_name, _) = prep_sym sym;
        val (module_name', _) = prep_sym sym';
      in if module_name = module_name'
        then (Graph.map_node module_name o apfst) (Code_Symbol.Graph.add_edge (sym, sym'))
        else (Graph.map_node module_name o apsnd)
          (AList.map_default (op =) (module_name', []) (insert (op =) sym'))
          #> mark_exports module_name' sym'
      end;
    val proto_program = build_proto_program
      { empty = Graph.empty, add_stmt = add_stmt, add_dep = add_dep } program
      |> fold (fn sym => mark_exports ((fst o prep_sym) sym) sym) exports;

    (* name declarations and statement modifications *)
    fun declare sym (base, (_, stmt)) (gr, nsp) = 
      let
        val (base', nsp') = namify_stmt stmt base nsp;
        val gr' = (Code_Symbol.Graph.map_node sym o apfst) (K base') gr;
      in (gr', nsp') end;
    fun declarations gr = (gr, empty_nsp)
      |> fold (fn sym => declare sym (Code_Symbol.Graph.get_node gr sym))
          (prioritize sym_priority (Code_Symbol.Graph.keys gr))
      |> fst
      |> Code_Symbol.Graph.map_strong_conn (fn syms_bases_exports_stmts =>
        map snd syms_bases_exports_stmts
        |> (map o apsnd) (fn (export, stmt) => Option.map (pair export) (modify_stmt stmt)));
    val flat_program = proto_program
      |> (Graph.map o K o apfst) declarations;

    (* qualified and unqualified imports, deresolving *)
    fun base_deresolver sym = fst (Code_Symbol.Graph.get_node
      (fst (Graph.get_node flat_program (fst (prep_sym sym)))) sym);
    fun classify_names gr imports =
      let
        val import_tab = maps
          (fn (module_name, syms) => map (rpair module_name) syms) imports;
        val imported_syms = map fst import_tab;
        val here_syms = Code_Symbol.Graph.keys gr;
      in
        Code_Symbol.Table.empty
        |> fold (fn sym => Code_Symbol.Table.update (sym, base_deresolver sym)) here_syms
        |> fold (fn sym => Code_Symbol.Table.update (sym,
            Long_Name.append (the (AList.lookup (op =) import_tab sym))
              (base_deresolver sym))) imported_syms
      end;
    val deresolver_tab = Symtab.make (AList.make
      (uncurry classify_names o Graph.get_node flat_program)
        (Graph.keys flat_program));
    fun deresolver "" sym =
          Long_Name.append (fst (prep_sym sym)) (base_deresolver sym)
      | deresolver module_name sym =
          the (Code_Symbol.Table.lookup (the (Symtab.lookup deresolver_tab module_name)) sym)
          handle Option.Option => error ("Unknown statement name: "
            ^ Code_Symbol.quote ctxt sym);

  in { deresolver = deresolver, flat_program = flat_program } end;


(** hierarchical program structure **)

datatype ('a, 'b) node =
    Dummy
  | Stmt of export * 'a
  | Module of ('b * (string * ('a, 'b) node) Code_Symbol.Graph.T);

type ('a, 'b) hierarchical_program = (string * ('a, 'b) node) Code_Symbol.Graph.T;

fun the_stmt (Stmt (export, stmt)) = (export, stmt);

fun map_module_content f (Module content) = Module (f content);

fun map_module [] = I
  | map_module (name_fragment :: name_fragments) =
      apsnd o Code_Symbol.Graph.map_node (Code_Symbol.Module name_fragment) o apsnd o map_module_content
        o map_module name_fragments;

fun map_module_stmts f_module f_stmts sym_base_nodes =
  let
    val some_modules =
      sym_base_nodes
      |> map (fn (_, (base, Module content)) => SOME (base, content) | _ => NONE)
      |> (burrow_options o map o apsnd) f_module;
    val some_export_stmts =
      sym_base_nodes
      |> map (fn (sym, (base, Stmt export_stmt)) => SOME ((sym, export_stmt), base) | _ => NONE)
      |> (burrow_options o burrow_fst) (fn [] => [] | xs => f_stmts xs)
  in
    map2 (fn SOME (base, content) => (K (base, Module content))
      | NONE => fn SOME (some_export_stmt, base) =>
          (base, case some_export_stmt of SOME export_stmt => Stmt export_stmt | NONE => Dummy))
      some_modules some_export_stmts
  end;

fun hierarchical_program ctxt { module_name, reserved, identifiers, empty_nsp,
      namify_module, namify_stmt, cyclic_modules,
      class_transitive, class_relation_public,
      empty_data, memorize_data, modify_stmts }
      exports program =
  let

    (* building module name hierarchy *)
    val module_namespace = build_module_namespace ctxt false { module_prefix = "",
      module_name = module_name, identifiers = identifiers, reserved = reserved } program;
    val prep_sym = prep_symbol ctxt { module_namespace = module_namespace,
      force_module = Long_Name.explode module_name, identifiers = identifiers }
    val sym_priority = has_priority identifiers;

    (* building empty module hierarchy *)
    val empty_module = (empty_data, Code_Symbol.Graph.empty);
    fun ensure_module name_fragment (data, nodes) =
      if can (Code_Symbol.Graph.get_node nodes) (Code_Symbol.Module name_fragment) then (data, nodes)
      else (data,
        nodes |> Code_Symbol.Graph.new_node (Code_Symbol.Module name_fragment, (name_fragment, Module empty_module)));
    fun allocate_module [] = I
      | allocate_module (name_fragment :: name_fragments) =
          ensure_module name_fragment
          #> (apsnd o Code_Symbol.Graph.map_node (Code_Symbol.Module name_fragment) o apsnd o map_module_content o allocate_module) name_fragments;
    val empty_program =
      empty_module
      |> Symtab.fold (fn (_, fragments) => allocate_module fragments) module_namespace
      |> Code_Symbol.Graph.fold (allocate_module o these o Option.map fst
          o Code_Symbol.lookup identifiers o fst) program;

    (* distribute statements over hierarchy *)
    val mark_exports = mark_exports { program = program, prefix_of = fst o prep_sym,
      map_export = fn name_fragments => fn sym => fn f =>
        (map_module name_fragments o apsnd o Code_Symbol.Graph.map_node sym o apsnd)
          (fn Stmt (export, stmt) => Stmt (f export, stmt)),
      class_transitive = class_transitive, class_relation_public = class_relation_public };
    fun add_stmt sym stmt =
      let
        val (name_fragments, base) = prep_sym sym;
      in
        (map_module name_fragments o apsnd)
          (Code_Symbol.Graph.new_node (sym, (base, Stmt (if null exports then Public else Private, stmt))))
      end;
    fun add_edge_acyclic_error error_msg dep gr =
      Code_Symbol.Graph.add_edge_acyclic dep gr
        handle Code_Symbol.Graph.CYCLES _ => error (error_msg ())
    fun add_dep sym sym' =
      let
        val (name_fragments, _) = prep_sym sym;
        val (name_fragments', _) = prep_sym sym';
        val (name_fragments_common, (diff, diff')) =
          chop_prefix (op =) (name_fragments, name_fragments');
        val is_cross_module = not (null diff andalso null diff');
        val dep = apply2 hd (map Code_Symbol.Module diff @ [sym], map Code_Symbol.Module diff' @ [sym']);
        val add_edge = if is_cross_module andalso not cyclic_modules
          then add_edge_acyclic_error (fn _ => "Dependency "
            ^ Code_Symbol.quote ctxt sym ^ " -> "
            ^ Code_Symbol.quote ctxt sym'
            ^ " would result in module dependency cycle") dep
          else Code_Symbol.Graph.add_edge dep;
      in
        (map_module name_fragments_common o apsnd) add_edge
        #> (if is_cross_module then mark_exports name_fragments' sym' else I)
      end;
    val proto_program = build_proto_program
      { empty = empty_program, add_stmt = add_stmt, add_dep = add_dep } program
      |> fold (fn sym => mark_exports ((fst o prep_sym) sym) sym) exports;

    (* name declarations, data and statement modifications *)
    fun make_declarations nsps (data, nodes) =
      let
        val (module_fragments, stmt_syms) =
          Code_Symbol.Graph.keys nodes
          |> List.partition
              (fn sym => case Code_Symbol.Graph.get_node nodes sym
                of (_, Module _) => true | _ => false)
          |> apply2 (prioritize sym_priority)
        fun declare namify sym (nsps, nodes) =
          let
            val (base, node) = Code_Symbol.Graph.get_node nodes sym;
            val (base', nsps') = namify node base nsps;
            val nodes' = Code_Symbol.Graph.map_node sym (K (base', node)) nodes;
          in (nsps', nodes') end;
        val (nsps', nodes') = (nsps, nodes)
          |> fold (declare (K namify_module)) module_fragments
          |> fold (declare (namify_stmt o snd o the_stmt)) stmt_syms;
        fun modify_stmts' syms_stmts =
          let
            val stmts' = modify_stmts syms_stmts
          in stmts' @ replicate (length syms_stmts - length stmts') NONE end;
        val nodes'' =
          nodes'
          |> Code_Symbol.Graph.map_strong_conn (map_module_stmts (make_declarations nsps') modify_stmts');
        val data' = fold memorize_data stmt_syms data;
      in (data', nodes'') end;
    val (_, hierarchical_program) = make_declarations empty_nsp proto_program;

    (* deresolving *)
    fun deresolver prefix_fragments sym =
      let
        val (name_fragments, _) = prep_sym sym;
        val (_, (_, remainder)) = chop_prefix (op =) (prefix_fragments, name_fragments);
        val nodes = fold (fn name_fragment => fn nodes => case Code_Symbol.Graph.get_node nodes (Code_Symbol.Module name_fragment)
         of (_, Module (_, nodes)) => nodes) name_fragments hierarchical_program;
        val (base', _) = Code_Symbol.Graph.get_node nodes sym;
      in Long_Name.implode (remainder @ [base']) end
        handle Code_Symbol.Graph.UNDEF _ => error ("Unknown statement name: "
          ^ Code_Symbol.quote ctxt sym);

  in { deresolver = deresolver, hierarchical_program = hierarchical_program } end;

fun print_hierarchical { print_module, print_stmt, lift_markup } =
  let
    fun print_node _ (_, Dummy) =
          NONE
      | print_node prefix_fragments (sym, Stmt stmt) =
          SOME (lift_markup (Code_Printer.markup_stmt sym)
            (print_stmt prefix_fragments (sym, stmt)))
      | print_node prefix_fragments (Code_Symbol.Module name_fragment, Module (data, nodes)) =
          let
            val prefix_fragments' = prefix_fragments @ [name_fragment]
          in
            Option.map (print_module prefix_fragments'
              name_fragment data) (print_nodes prefix_fragments' nodes)
          end
    and print_nodes prefix_fragments nodes =
      let
        val xs = (map_filter (fn sym => print_node prefix_fragments
          (sym, snd (Code_Symbol.Graph.get_node nodes sym))) o rev o flat o Code_Symbol.Graph.strong_conn) nodes
      in if null xs then NONE else SOME xs end;
  in these o print_nodes [] end;

end;
