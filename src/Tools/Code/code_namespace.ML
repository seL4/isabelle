(*  Title:      Tools/Code/code_namespace.ML
    Author:     Florian Haftmann, TU Muenchen

Mastering target language namespaces.
*)

signature CODE_NAMESPACE =
sig
  datatype ('a, 'b) node =
      Dummy
    | Stmt of 'a
    | Module of ('b * (string * ('a, 'b) node) Graph.T);
  val hierarchical_program: (string -> string) -> { module_alias: string -> string option,
    reserved: Name.context, empty_nsp: 'c, namify_module: string -> 'c -> string * 'c,
    namify_stmt: Code_Thingol.stmt -> string -> 'c -> string * 'c,
    cyclic_modules: bool, empty_data: 'b, memorize_data: string -> 'b -> 'b,
    modify_stmts: Code_Thingol.stmt list -> 'a option list }
      -> Code_Thingol.program
      -> { deresolver: string list -> string -> string,
           hierarchical_program: (string * ('a, 'b) node) Graph.T }
end;

structure Code_Namespace : CODE_NAMESPACE =
struct

(* hierarchical program structure *)

datatype ('a, 'b) node =
    Dummy
  | Stmt of 'a
  | Module of ('b * (string * ('a, 'b) node) Graph.T);

fun map_module_content f (Module content) = Module (f content);

fun map_module [] = I
  | map_module (name_fragment :: name_fragments) =
      apsnd o Graph.map_node name_fragment o apsnd o map_module_content
        o map_module name_fragments;

fun hierarchical_program labelled_name { module_alias, reserved, empty_nsp,
      namify_module, namify_stmt, cyclic_modules, empty_data, memorize_data, modify_stmts } program =
  let

    (* building module name hierarchy *)
    fun alias_fragments name = case module_alias name
     of SOME name' => Long_Name.explode name'
      | NONE => map (fn name => fst (yield_singleton Name.variants name reserved))
          (Long_Name.explode name);
    val module_names = Graph.fold (insert (op =) o fst o Code_Printer.dest_name o fst) program [];
    val fragments_tab = fold (fn name => Symtab.update
      (name, alias_fragments name)) module_names Symtab.empty;
    val dest_name = Code_Printer.dest_name #>> (the o Symtab.lookup fragments_tab);

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
        val (name_fragments, base) = dest_name name;
        val (name_fragments', base') = dest_name name';
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
      |> Graph.fold (fn (name, (_, (_, names))) => fold (add_dependency name) names) program;

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
        val modify_stmts' = filter (member (op =) stmt_names)
          #> AList.make (snd o Graph.get_node nodes)
          #> split_list
          ##> map (fn Stmt stmt => stmt)
          ##> modify_stmts
          #> op ~~;
        val stmtss' = maps modify_stmts' (Graph.strong_conn nodes);
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

end;