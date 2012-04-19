(*  Title:      Tools/Code/code_namespace.ML
    Author:     Florian Haftmann, TU Muenchen

Mastering target language namespaces.
*)

signature CODE_NAMESPACE =
sig
  type flat_program
  val flat_program: (string -> string) -> { module_alias: string -> string option,
    module_prefix: string, reserved: Name.context, empty_nsp: 'a,
    namify_stmt: Code_Thingol.stmt -> string -> 'a -> string * 'a,
    modify_stmt: Code_Thingol.stmt -> Code_Thingol.stmt option }
      -> Code_Thingol.program
      -> { deresolver: string -> string -> string,
           flat_program: flat_program }

  datatype ('a, 'b) node =
      Dummy
    | Stmt of 'a
    | Module of ('b * (string * ('a, 'b) node) Graph.T)
  type ('a, 'b) hierarchical_program
  val hierarchical_program: (string -> string) -> { module_alias: string -> string option,
    reserved: Name.context, empty_nsp: 'c, namify_module: string -> 'c -> string * 'c,
    namify_stmt: Code_Thingol.stmt -> string -> 'c -> string * 'c,
    cyclic_modules: bool, empty_data: 'b, memorize_data: string -> 'b -> 'b,
    modify_stmts: (string * Code_Thingol.stmt) list -> 'a option list }
      -> Code_Thingol.program
      -> { deresolver: string list -> string -> string,
           hierarchical_program: ('a, 'b) hierarchical_program }
  val print_hierarchical: { print_module: string list -> string -> 'b -> 'c list -> 'c,
    print_stmt: string list -> string * 'a -> 'c,
    lift_markup: (Pretty.T -> Pretty.T) -> 'c -> 'c }
      -> ('a, 'b) hierarchical_program -> 'c list
end;

structure Code_Namespace : CODE_NAMESPACE =
struct

(** building module name hierarchy **)

val dest_name =
  apfst Long_Name.implode o split_last o fst o split_last o Long_Name.explode;

fun build_module_namespace { module_alias, module_prefix, reserved } program =
  let
    fun alias_fragments name = case module_alias name
     of SOME name' => Long_Name.explode name'
      | NONE => map (fn name => fst (Name.variant name reserved)) (Long_Name.explode name);
    val module_names = Graph.fold (insert (op =) o fst o dest_name o fst) program [];
  in
    fold (fn name => Symtab.update (name, Long_Name.explode module_prefix @ alias_fragments name))
      module_names Symtab.empty
  end;


(** flat program structure **)

type flat_program = ((string * Code_Thingol.stmt option) Graph.T * (string * string list) list) Graph.T;

fun flat_program labelled_name { module_alias, module_prefix, reserved,
      empty_nsp, namify_stmt, modify_stmt } program =
  let

    (* building module name hierarchy *)
    val fragments_tab = build_module_namespace { module_alias = module_alias,
      module_prefix = module_prefix, reserved = reserved } program;
    val dest_name = dest_name
      #>> (Long_Name.implode o the o Symtab.lookup fragments_tab);

    (* distribute statements over hierarchy *)
    fun add_stmt name stmt =
      let
        val (module_name, base) = dest_name name;
      in
        Graph.default_node (module_name, (Graph.empty, []))
        #> (Graph.map_node module_name o apfst) (Graph.new_node (name, (base, stmt)))
      end;
    fun add_dependency name name' =
      let
        val (module_name, _) = dest_name name;
        val (module_name', _) = dest_name name';
      in if module_name = module_name'
        then (Graph.map_node module_name o apfst) (Graph.add_edge (name, name'))
        else (Graph.map_node module_name o apsnd) (AList.map_default (op =) (module_name', []) (insert (op =) name'))
      end;
    val proto_program = Graph.empty
      |> Graph.fold (fn (name, (stmt, _)) => add_stmt name stmt) program
      |> Graph.fold (fn (name, (_, (_, names))) =>
          Graph.Keys.fold (add_dependency name) names) program;

    (* name declarations and statement modifications *)
    fun declare name (base, stmt) (gr, nsp) = 
      let
        val (base', nsp') = namify_stmt stmt base nsp;
        val gr' = (Graph.map_node name o apfst) (K base') gr;
      in (gr', nsp') end;
    fun declarations gr = (gr, empty_nsp)
      |> fold (fn name => declare name (Graph.get_node gr name)) (Graph.keys gr) 
      |> fst
      |> (Graph.map o K o apsnd) modify_stmt;
    val flat_program = proto_program
      |> (Graph.map o K o apfst) declarations;

    (* qualified and unqualified imports, deresolving *)
    fun base_deresolver name = fst (Graph.get_node
      (fst (Graph.get_node flat_program (fst (dest_name name)))) name);
    fun classify_names gr imports =
      let
        val import_tab = maps
          (fn (module_name, names) => map (rpair module_name) names) imports;
        val imported_names = map fst import_tab;
        val here_names = Graph.keys gr;
      in
        Symtab.empty
        |> fold (fn name => Symtab.update (name, base_deresolver name)) here_names
        |> fold (fn name => Symtab.update (name,
            Long_Name.append (the (AList.lookup (op =) import_tab name))
              (base_deresolver name))) imported_names
      end;
    val deresolver_tab = Symtab.make (AList.make
      (uncurry classify_names o Graph.get_node flat_program)
        (Graph.keys flat_program));
    fun deresolver "" name =
          Long_Name.append (fst (dest_name name)) (base_deresolver name)
      | deresolver module_name name =
          the (Symtab.lookup (the (Symtab.lookup deresolver_tab module_name)) name)
          handle Option => error ("Unknown statement name: " ^ labelled_name name);

  in { deresolver = deresolver, flat_program = flat_program } end;


(** hierarchical program structure **)

datatype ('a, 'b) node =
    Dummy
  | Stmt of 'a
  | Module of ('b * (string * ('a, 'b) node) Graph.T);

type ('a, 'b) hierarchical_program = (string * ('a, 'b) node) Graph.T;

fun map_module_content f (Module content) = Module (f content);

fun map_module [] = I
  | map_module (name_fragment :: name_fragments) =
      apsnd o Graph.map_node name_fragment o apsnd o map_module_content
        o map_module name_fragments;

fun hierarchical_program labelled_name { module_alias, reserved, empty_nsp,
      namify_module, namify_stmt, cyclic_modules, empty_data, memorize_data, modify_stmts } program =
  let

    (* building module name hierarchy *)
    val fragments_tab = build_module_namespace { module_alias = module_alias,
      module_prefix = "", reserved = reserved } program;
    val dest_name = dest_name #>> (the o Symtab.lookup fragments_tab);

    (* building empty module hierarchy *)
    val empty_module = (empty_data, Graph.empty);
    fun ensure_module name_fragment (data, nodes) =
      if can (Graph.get_node nodes) name_fragment then (data, nodes)
      else (data,
        nodes |> Graph.new_node (name_fragment, (name_fragment, Module empty_module)));
    fun allocate_module [] = I
      | allocate_module (name_fragment :: name_fragments) =
          ensure_module name_fragment
          #> (apsnd o Graph.map_node name_fragment o apsnd o map_module_content o allocate_module) name_fragments;
    val empty_program = Symtab.fold (fn (_, fragments) => allocate_module fragments)
      fragments_tab empty_module;

    (* distribute statements over hierarchy *)
    fun add_stmt name stmt =
      let
        val (name_fragments, base) = dest_name name;
      in
        (map_module name_fragments o apsnd) (Graph.new_node (name, (base, Stmt stmt)))
      end;
    fun add_dependency name name' =
      let
        val (name_fragments, _) = dest_name name;
        val (name_fragments', _) = dest_name name';
        val (name_fragments_common, (diff, diff')) =
          chop_prefix (op =) (name_fragments, name_fragments');
        val is_module = not (null diff andalso null diff');
        val dep = pairself hd (diff @ [name], diff' @ [name']);
        val add_edge = if is_module andalso not cyclic_modules
          then (fn node => Graph.add_edge_acyclic dep node
            handle Graph.CYCLES _ => error ("Dependency "
              ^ quote name ^ " -> " ^ quote name'
              ^ " would result in module dependency cycle"))
          else Graph.add_edge dep
      in (map_module name_fragments_common o apsnd) add_edge end;
    val proto_program = empty_program
      |> Graph.fold (fn (name, (stmt, _)) => add_stmt name stmt) program
      |> Graph.fold (fn (name, (_, (_, names))) =>
          Graph.Keys.fold (add_dependency name) names) program;

    (* name declarations, data and statement modifications *)
    fun make_declarations nsps (data, nodes) =
      let
        val (module_fragments, stmt_names) = List.partition
          (fn name_fragment => case Graph.get_node nodes name_fragment
            of (_, Module _) => true | _ => false) (Graph.keys nodes);
        fun declare namify name (nsps, nodes) =
          let
            val (base, node) = Graph.get_node nodes name;
            val (base', nsps') = namify node base nsps;
            val nodes' = Graph.map_node name (K (base', node)) nodes;
          in (nsps', nodes') end;
        val (nsps', nodes') = (nsps, nodes)
          |> fold (declare (K namify_module)) module_fragments
          |> fold (declare (namify_stmt o (fn Stmt stmt => stmt))) stmt_names;
        fun zip_fillup xs ys = xs ~~ ys @ replicate (length xs - length ys) NONE;
        fun select_names names = case filter (member (op =) stmt_names) names
         of [] => NONE
          | xs => SOME xs;
        val modify_stmts' = AList.make (snd o Graph.get_node nodes)
          #> split_list
          ##> map (fn Stmt stmt => stmt)
          #> (fn (names, stmts) => zip_fillup names (modify_stmts (names ~~ stmts)));
        val stmtss' = (maps modify_stmts' o map_filter select_names o Graph.strong_conn) nodes;
        val nodes'' = Graph.map (fn name => apsnd (fn Module content => Module (make_declarations nsps' content)
            | _ => case AList.lookup (op =) stmtss' name of SOME (SOME stmt) => Stmt stmt | _ => Dummy)) nodes';
        val data' = fold memorize_data stmt_names data;
      in (data', nodes'') end;
    val (_, hierarchical_program) = make_declarations empty_nsp proto_program;

    (* deresolving *)
    fun deresolver prefix_fragments name =
      let
        val (name_fragments, _) = dest_name name;
        val (_, (_, remainder)) = chop_prefix (op =) (prefix_fragments, name_fragments);
        val nodes = fold (fn name_fragment => fn nodes => case Graph.get_node nodes name_fragment
         of (_, Module (_, nodes)) => nodes) name_fragments hierarchical_program;
        val (base', _) = Graph.get_node nodes name;
      in Long_Name.implode (remainder @ [base']) end
        handle Graph.UNDEF _ => error ("Unknown statement name: " ^ labelled_name name);

  in { deresolver = deresolver, hierarchical_program = hierarchical_program } end;

fun print_hierarchical { print_module, print_stmt, lift_markup } =
  let
    fun print_node _ (_, Dummy) =
          NONE
      | print_node prefix_fragments (name, Stmt stmt) =
          SOME (lift_markup (Code_Printer.markup_stmt name)
            (print_stmt prefix_fragments (name, stmt)))
      | print_node prefix_fragments (name_fragment, Module (data, nodes)) =
          let
            val prefix_fragments' = prefix_fragments @ [name_fragment]
          in
            Option.map (print_module prefix_fragments'
              name_fragment data) (print_nodes prefix_fragments' nodes)
          end
    and print_nodes prefix_fragments nodes =
      let
        val xs = (map_filter (fn name => print_node prefix_fragments
          (name, snd (Graph.get_node nodes name))) o rev o flat o Graph.strong_conn) nodes
      in if null xs then NONE else SOME xs end;
  in these o print_nodes [] end;

end;