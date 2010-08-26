(*  Title:      Tools/Code/code_scala.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for Scala.
*)

signature CODE_SCALA =
sig
  val target: string
  val setup: theory -> theory
end;

structure Code_Scala : CODE_SCALA =
struct

val target = "Scala";

open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;


(** Scala serializer **)

fun print_scala_stmt labelled_name syntax_tyco syntax_const reserved
    args_num is_singleton_constr deresolve =
  let
    val deresolve_base = Long_Name.base_name o deresolve;
    fun lookup_tyvar tyvars = lookup_var tyvars o first_upper;
    fun intro_tyvars vs = intro_vars (map (first_upper o fst) vs);
    fun print_tyco_expr tyvars fxy (tyco, tys) = applify "[" "]"
          (print_typ tyvars NOBR) fxy ((str o deresolve) tyco) tys
    and print_typ tyvars fxy (tyco `%% tys) = (case syntax_tyco tyco
         of NONE => print_tyco_expr tyvars fxy (tyco, tys)
          | SOME (i, print) => print (print_typ tyvars) fxy tys)
      | print_typ tyvars fxy (ITyVar v) = (str o lookup_tyvar tyvars) v;
    fun print_dicttyp tyvars (class, ty) = print_tyco_expr tyvars NOBR (class, [ty]);
    fun print_tupled_typ tyvars ([], ty) =
          print_typ tyvars NOBR ty
      | print_tupled_typ tyvars ([ty1], ty2) =
          concat [print_typ tyvars BR ty1, str "=>", print_typ tyvars NOBR ty2]
      | print_tupled_typ tyvars (tys, ty) =
          concat [enum "," "(" ")" (map (print_typ tyvars NOBR) tys),
            str "=>", print_typ tyvars NOBR ty];
    fun constraint p1 p2 = Pretty.block [p1, str ":", Pretty.brk 1, p2];
    fun print_var vars NONE = str "_"
      | print_var vars (SOME v) = (str o lookup_var vars) v
    fun print_term tyvars is_pat some_thm vars fxy (IConst c) =
          print_app tyvars is_pat some_thm vars fxy (c, [])
      | print_term tyvars is_pat some_thm vars fxy (t as (t1 `$ t2)) =
          (case Code_Thingol.unfold_const_app t
           of SOME app => print_app tyvars is_pat some_thm vars fxy app
            | _ => applify "(" ")" (print_term tyvars is_pat some_thm vars NOBR) fxy
                (print_term tyvars is_pat some_thm vars BR t1) [t2])
      | print_term tyvars is_pat some_thm vars fxy (IVar v) =
          print_var vars v
      | print_term tyvars is_pat some_thm vars fxy ((v, ty) `|=> t) =
          let
            val vars' = intro_vars (the_list v) vars;
          in
            concat [
              enclose "(" ")" [constraint (print_var vars' v) (print_typ tyvars NOBR ty)],
              str "=>",
              print_term tyvars false some_thm vars' NOBR t
            ]
          end 
      | print_term tyvars is_pat some_thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then print_case tyvars some_thm vars fxy cases
                else print_app tyvars is_pat some_thm vars fxy c_ts
            | NONE => print_case tyvars some_thm vars fxy cases)
    and print_app tyvars is_pat some_thm vars fxy
        (app as ((c, ((arg_typs, _), function_typs)), ts)) =
      let
        val k = length ts;
        val arg_typs' = if is_pat orelse
          (is_none (syntax_const c) andalso is_singleton_constr c) then [] else arg_typs;
        val (l, print') = case syntax_const c
         of NONE => (args_num c, fn fxy => fn ts => applify "(" ")"
              (print_term tyvars is_pat some_thm vars NOBR) fxy
                (applify "[" "]" (print_typ tyvars NOBR)
                  NOBR ((str o deresolve) c) arg_typs') ts)
          | SOME (Plain_const_syntax (k, s)) => (k, fn fxy => fn ts => applify "(" ")"
              (print_term tyvars is_pat some_thm vars NOBR) fxy
                (applify "[" "]" (print_typ tyvars NOBR)
                  NOBR (str s) arg_typs') ts)
          | SOME (Complex_const_syntax (k, print)) =>
              (k, fn fxy => fn ts => print (print_term tyvars is_pat some_thm) some_thm vars fxy
                (ts ~~ take k function_typs))
      in if k = l then print' fxy ts
      else if k < l then
        print_term tyvars is_pat some_thm vars fxy (Code_Thingol.eta_expand l app)
      else let
        val (ts1, ts23) = chop l ts;
      in
        Pretty.block (print' BR ts1 :: map (fn t => Pretty.block
          [str ".apply(", print_term tyvars is_pat some_thm vars NOBR t, str ")"]) ts23)
      end end
    and print_bind tyvars some_thm fxy p =
      gen_print_bind (print_term tyvars true) some_thm fxy p
    and print_case tyvars some_thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_match ((IVar NONE, _), t) vars =
                  ((true, print_term tyvars false some_thm vars NOBR t), vars)
              | print_match ((pat, ty), t) vars =
                  vars
                  |> print_bind tyvars some_thm BR pat
                  |>> (fn p => (false, concat [str "val", constraint p (print_typ tyvars NOBR ty),
                      str "=", print_term tyvars false some_thm vars NOBR t]))
            val (seps_ps, vars') = fold_map print_match binds vars;
            val all_seps_ps = seps_ps @ [(true, print_term tyvars false some_thm vars' NOBR body)];
            fun insert_seps [(_, p)] = [p]
              | insert_seps ((_, p) :: (seps_ps as (sep, _) :: _)) =
                  (if sep then Pretty.block [p, str ";"] else p) :: insert_seps seps_ps
          in brackify_block fxy (str "{") (insert_seps all_seps_ps) (str "}")
          end
      | print_case tyvars some_thm vars fxy (((t, ty), clauses as _ :: _), _) =
          let
            fun print_select (pat, body) =
              let
                val (p_pat, vars') = print_bind tyvars some_thm NOBR pat vars;
                val p_body = print_term tyvars false some_thm vars' NOBR body
              in concat [str "case", p_pat, str "=>", p_body] end;
          in brackify_block fxy
            (concat [print_term tyvars false some_thm vars NOBR t, str "match", str "{"])
            (map print_select clauses)
            (str "}") 
          end
      | print_case tyvars some_thm vars fxy ((_, []), _) =
          (brackify fxy o Pretty.breaks o map str) ["error(\"empty case\")"];
    fun print_context tyvars vs name = applify "[" "]"
      (fn (v, sort) => (Pretty.block o map str)
        (lookup_tyvar tyvars v :: maps (fn sort => [": ", deresolve sort]) sort))
          NOBR ((str o deresolve_base) name) vs;
    fun print_defhead tyvars vars name vs params tys ty =
      Pretty.block [str "def ", constraint (applify "(" ")" (fn (param, ty) =>
        constraint ((str o lookup_var vars) param) (print_typ tyvars NOBR ty))
          NOBR (print_context tyvars vs name) (params ~~ tys)) (print_typ tyvars NOBR ty),
            str " ="];
    fun print_def name (vs, ty) [] =
          let
            val (tys, ty') = Code_Thingol.unfold_fun ty;
            val params = Name.invents (snd reserved) "a" (length tys);
            val tyvars = intro_tyvars vs reserved;
            val vars = intro_vars params reserved;
          in
            concat [print_defhead tyvars vars name vs params tys ty',
              str ("error(\"" ^ name ^ "\")")]
          end
      | print_def name (vs, ty) eqs =
          let
            val tycos = fold (fn ((ts, t), _) =>
              fold Code_Thingol.add_tyconames (t :: ts)) eqs [];
            val tyvars = reserved
              |> intro_base_names
                   (is_none o syntax_tyco) deresolve tycos
              |> intro_tyvars vs;
            val simple = case eqs
             of [((ts, _), _)] => forall Code_Thingol.is_IVar ts
              | _ => false;
            val consts = fold Code_Thingol.add_constnames
              (map (snd o fst) eqs) [];
            val vars1 = reserved
              |> intro_base_names
                   (is_none o syntax_const) deresolve consts
            val params = if simple
              then (map (fn IVar (SOME x) => x) o fst o fst o hd) eqs
              else aux_params vars1 (map (fst o fst) eqs);
            val vars2 = intro_vars params vars1;
            val (tys', ty') = Code_Thingol.unfold_fun_n (length params) ty;
            fun print_tuple [p] = p
              | print_tuple ps = enum "," "(" ")" ps;
            fun print_rhs vars' ((_, t), (some_thm, _)) =
              print_term tyvars false some_thm vars' NOBR t;
            fun print_clause (eq as ((ts, _), (some_thm, _))) =
              let
                val vars' = intro_vars ((fold o Code_Thingol.fold_varnames)
                  (insert (op =)) ts []) vars1;
              in
                concat [str "case",
                  print_tuple (map (print_term tyvars true some_thm vars' NOBR) ts),
                  str "=>", print_rhs vars' eq]
              end;
            val head = print_defhead tyvars vars2 name vs params tys' ty';
          in if simple then
            concat [head, print_rhs vars2 (hd eqs)]
          else
            Pretty.block_enclose
              (concat [head, print_tuple (map (str o lookup_var vars2) params),
                str "match", str "{"], str "}")
              (map print_clause eqs)
          end;
    val print_method = str o Library.enclose "`" "`" o space_implode "+"
      o fst o split_last o Long_Name.explode;
    fun print_stmt (name, Code_Thingol.Fun (_, (((vs, ty), raw_eqs), _))) =
          print_def name (vs, ty) (filter (snd o snd) raw_eqs)
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, cos))) =
          let
            val tyvars = intro_tyvars vs reserved;
            fun print_co ((co, _), []) =
                  concat [str "final", str "case", str "object", (str o deresolve_base) co,
                    str "extends", applify "[" "]" I NOBR ((str o deresolve_base) name)
                      (replicate (length vs) (str "Nothing"))]
              | print_co ((co, vs_args), tys) =
                  concat [applify "(" ")"
                    (fn (v, arg) => constraint (str v) (print_typ tyvars NOBR arg)) NOBR
                    (applify "[" "]" (str o lookup_tyvar tyvars) NOBR ((concat o map str)
                      ["final", "case", "class", deresolve_base co]) vs_args)
                    (Name.names (snd reserved) "a" tys),
                    str "extends",
                    applify "[" "]" (str o lookup_tyvar tyvars o fst) NOBR
                      ((str o deresolve_base) name) vs
                  ];
          in
            Pretty.chunks (applify "[" "]" (str o prefix "+" o lookup_tyvar tyvars o fst)
              NOBR ((concat o map str) ["abstract", "sealed", "class", deresolve_base name]) vs
                :: map print_co cos)
          end
      | print_stmt (name, Code_Thingol.Class (_, (v, (super_classes, classparams)))) =
          let
            val tyvars = intro_tyvars [(v, [name])] reserved;
            fun add_typarg s = Pretty.block
              [str s, str "[", (str o lookup_tyvar tyvars) v, str "]"];
            fun print_super_classes [] = NONE
              | print_super_classes classes = SOME (concat (str "extends"
                  :: separate (str "with") (map (add_typarg o deresolve o fst) classes)));
            fun print_classparam_val (classparam, ty) =
              concat [str "val", constraint (print_method classparam)
                ((print_tupled_typ tyvars o Code_Thingol.unfold_fun) ty)];
            fun print_classparam_def (classparam, ty) =
              let
                val (tys, ty) = Code_Thingol.unfold_fun ty;
                val [implicit_name] = Name.invents (snd reserved) (lookup_tyvar tyvars v) 1;
                val proto_vars = intro_vars [implicit_name] reserved;
                val auxs = Name.invents (snd proto_vars) "a" (length tys);
                val vars = intro_vars auxs proto_vars;
              in
                concat [str "def", constraint (Pretty.block [applify "(" ")"
                  (fn (aux, ty) => constraint ((str o lookup_var vars) aux)
                  (print_typ tyvars NOBR ty)) NOBR (add_typarg (deresolve_base classparam))
                  (auxs ~~ tys), str "(implicit ", str implicit_name, str ": ",
                  add_typarg (deresolve name), str ")"]) (print_typ tyvars NOBR ty), str "=",
                  applify "(" ")" (str o lookup_var vars) NOBR
                  (Pretty.block [str implicit_name, str ".", print_method classparam]) auxs]
              end;
          in
            Pretty.chunks (
              (Pretty.block_enclose
                (concat ([str "trait", (add_typarg o deresolve_base) name]
                  @ the_list (print_super_classes super_classes) @ [str "{"]), str "}")
                (map print_classparam_val classparams))
              :: map print_classparam_def classparams
            )
          end
      | print_stmt (name, Code_Thingol.Classinst ((class, (tyco, vs)),
            (super_instances, (classparam_instances, further_classparam_instances)))) =
          let
            val tyvars = intro_tyvars vs reserved;
            val classtyp = (class, tyco `%% map (ITyVar o fst) vs);
            fun print_classparam_instance ((classparam, const as (_, (_, tys))), (thm, _)) =
              let
                val aux_tys = Name.names (snd reserved) "a" tys;
                val auxs = map fst aux_tys;
                val vars = intro_vars auxs reserved;
                val aux_abstr = if null auxs then [] else [enum "," "(" ")"
                  (map (fn (aux, ty) => constraint ((str o lookup_var vars) aux)
                  (print_typ tyvars NOBR ty)) aux_tys), str "=>"];
              in 
                concat ([str "val", print_method classparam, str "="]
                  @ aux_abstr @| print_app tyvars false (SOME thm) vars NOBR
                    (const, map (IVar o SOME) auxs))
              end;
          in
            Pretty.block_enclose (concat [str "implicit def",
              constraint (print_context tyvars vs name) (print_dicttyp tyvars classtyp),
              str "=", str "new", print_dicttyp tyvars classtyp, str "{"], str "}")
                (map print_classparam_instance (classparam_instances @ further_classparam_instances))
          end;
  in print_stmt end;

local

(* hierarchical module name space *)

datatype node =
    Dummy
  | Stmt of Code_Thingol.stmt
  | Module of ((Name.context * Name.context) * Name.context) * (string list * (string * node) Graph.T);

in

fun scala_program_of_program labelled_name module_name reserved raw_module_alias program =
  let

    (* building module name hierarchy *)
    val module_alias = if is_some module_name then K module_name else raw_module_alias;
    fun alias_fragments name = case module_alias name
     of SOME name' => Long_Name.explode name'
      | NONE => map (fn name => fst (yield_singleton Name.variants name reserved))
          (Long_Name.explode name);
    val module_names = Graph.fold (insert (op =) o fst o dest_name o fst) program [];
    val fragments_tab = fold (fn name => Symtab.update
      (name, alias_fragments name)) module_names Symtab.empty;
    val dest_name = Code_Printer.dest_name #>> (the o Symtab.lookup fragments_tab);

    (* building empty module hierarchy *)
    val empty_module = (((reserved, reserved), reserved), ([], Graph.empty));
    fun map_module f (Module content) = Module (f content);
    fun declare_module name_fragement ((nsp_class, nsp_object), nsp_common) =
      let
        val declare = Name.declare name_fragement;
      in ((declare nsp_class, declare nsp_object), declare nsp_common) end;
    fun ensure_module name_fragement (nsps, (implicits, nodes)) =
      if can (Graph.get_node nodes) name_fragement then (nsps, (implicits, nodes))
      else
        (nsps |> declare_module name_fragement, (implicits,
          nodes |> Graph.new_node (name_fragement, (name_fragement, Module empty_module))));
    fun allocate_module [] = I
      | allocate_module (name_fragment :: name_fragments) =
          ensure_module name_fragment
          #> (apsnd o apsnd o Graph.map_node name_fragment o apsnd o map_module o allocate_module) name_fragments;
    val empty_program = Symtab.fold (fn (_, fragments) => allocate_module fragments)
      fragments_tab empty_module;
    fun change_module [] = I
      | change_module (name_fragment :: name_fragments) =
          apsnd o apsnd o Graph.map_node name_fragment o apsnd o map_module
            o change_module name_fragments;

    (* statement declaration *)
    fun namify_class base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_class') = yield_singleton Name.variants base nsp_class
      in (base', ((nsp_class', nsp_object), Name.declare base' nsp_common)) end;
    fun namify_object base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_object') = yield_singleton Name.variants base nsp_object
      in (base', ((nsp_class, nsp_object'), Name.declare base' nsp_common)) end;
    fun namify_common upper base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_common') =
          yield_singleton Name.variants (if upper then first_upper base else base) nsp_common
      in
        (base',
          ((Name.declare base' nsp_class, Name.declare base' nsp_object), nsp_common'))
      end;
    fun declare_stmt name stmt =
      let
        val (name_fragments, base) = dest_name name;
        val namify = case stmt
         of Code_Thingol.Fun _ => namify_object
          | Code_Thingol.Datatype _ => namify_class
          | Code_Thingol.Datatypecons _ => namify_common true
          | Code_Thingol.Class _ => namify_class
          | Code_Thingol.Classrel _ => namify_object
          | Code_Thingol.Classparam _ => namify_object
          | Code_Thingol.Classinst _ => namify_common false;
        val stmt' = case stmt
         of Code_Thingol.Datatypecons _ => Dummy
          | Code_Thingol.Classrel _ => Dummy
          | Code_Thingol.Classparam _ => Dummy
          | _ => Stmt stmt;
        fun is_classinst stmt = case stmt
         of Code_Thingol.Classinst _ => true
          | _ => false;
        val implicit_deps = filter (is_classinst o Graph.get_node program)
          (Graph.imm_succs program name);
        fun declaration (nsps, (implicits, nodes)) =
          let
            val (base', nsps') = namify base nsps;
            val implicits' = union (op =) implicit_deps implicits;
            val nodes' = Graph.new_node (name, (base', stmt')) nodes;
          in (nsps', (implicits', nodes')) end;
      in change_module name_fragments declaration end;

    (* dependencies *)
    fun add_dependency name name' =
      let
        val (name_fragments, base) = dest_name name;
        val (name_fragments', base') = dest_name name';
        val (name_fragments_common, (diff, diff')) =
          chop_prefix (op =) (name_fragments, name_fragments');
        val dep = if null diff then (name, name') else (hd diff, hd diff')
      in (change_module name_fragments_common o apsnd o apsnd) (Graph.add_edge dep) end;

    (* producing program *)
    val (_, (_, sca_program)) = empty_program
      |> Graph.fold (fn (name, (stmt, _)) => declare_stmt name stmt) program
      |> Graph.fold (fn (name, (_, (_, names))) => fold (add_dependency name) names) program;

    (* deresolving *)
    fun deresolve name =
      let
        val (name_fragments, _) = dest_name name;
        val nodes = fold (fn name_fragement => fn nodes => case Graph.get_node nodes name_fragement
         of (_, Module (_, (_, nodes))) => nodes) name_fragments sca_program;
        val (base', _) = Graph.get_node nodes name;
      in Long_Name.implode (name_fragments @ [base']) end
        handle Graph.UNDEF _ => error ("Unknown statement name: " ^ labelled_name name);

  in (deresolve, sca_program) end;

fun serialize_scala raw_module_name labelled_name
    raw_reserved includes raw_module_alias
    _ syntax_tyco syntax_const (code_of_pretty, code_writeln)
    program stmt_names destination =
  let

    (* generic nonsense *)
    val presentation_stmt_names = Code_Target.stmt_names_of_destination destination;
    val module_name = if null presentation_stmt_names then raw_module_name else SOME "Code";

    (* preprocess program *)
    val reserved = fold (insert (op =) o fst) includes raw_reserved;
    val (deresolve, sca_program) = scala_program_of_program labelled_name
      module_name (Name.make_context reserved) raw_module_alias program;

    (* print statements *)
    fun lookup_constr tyco constr = case Graph.get_node program tyco
     of Code_Thingol.Datatype (_, (_, constrs)) =>
          the (AList.lookup (op = o apsnd fst) constrs constr);
    fun classparams_of_class class = case Graph.get_node program class
     of Code_Thingol.Class (_, (_, (_, classparams))) => classparams;
    fun args_num c = case Graph.get_node program c
     of Code_Thingol.Fun (_, (((_, ty), []), _)) =>
          (length o fst o Code_Thingol.unfold_fun) ty
      | Code_Thingol.Fun (_, ((_, ((ts, _), _) :: _), _)) => length ts
      | Code_Thingol.Datatypecons (_, tyco) => length (lookup_constr tyco c)
      | Code_Thingol.Classparam (_, class) =>
          (length o fst o Code_Thingol.unfold_fun o the o AList.lookup (op =)
            (classparams_of_class class)) c;
    fun is_singleton_constr c = case Graph.get_node program c
     of Code_Thingol.Datatypecons (_, tyco) => null (lookup_constr tyco c)
      | _ => false;
    val print_stmt = print_scala_stmt labelled_name syntax_tyco syntax_const
      (make_vars reserved) args_num is_singleton_constr deresolve;

    (* print nodes *)
    fun print_implicits [] = NONE
      | print_implicits implicits = (SOME o Pretty.block)
          (str "import /*implicits*/" :: Pretty.brk 1 :: Pretty.commas (map (str o deresolve) implicits));
    fun print_module base implicits p = Pretty.chunks2
      ([str ("object " ^ base ^ " {")] @ the_list (print_implicits implicits)
        @ [p, str ("} /* object " ^ base ^ " */")]);
    fun print_node (_, Dummy) = NONE
      | print_node (name, Stmt stmt) = if not (not (null presentation_stmt_names)
          andalso member (op =) presentation_stmt_names name)
          then SOME (print_stmt (name, stmt))
          else NONE
      | print_node (name, Module (_, (implicits, nodes))) = if null presentation_stmt_names
          then case print_nodes nodes
           of NONE => NONE
            | SOME p => SOME (print_module (Long_Name.base_name name) implicits p)
          else print_nodes nodes
    and print_nodes nodes = let
        val ps = map_filter (fn name => print_node (name,
          snd (Graph.get_node nodes name)))
            ((rev o flat o Graph.strong_conn) nodes);
      in if null ps then NONE else SOME (Pretty.chunks2 ps) end;

    (* serialization *)
    val p = Pretty.chunks2 (map (fn (base, p) => print_module base [] p) includes
      @ the_list (print_nodes sca_program));
  in
    Code_Target.mk_serialization target
      (fn NONE => code_writeln | SOME file => File.write file o code_of_pretty)
      (rpair [] o code_of_pretty) p destination
  end;

end; (*local*)

val literals = let
  fun char_scala c = if c = "'" then "\\'"
    else if c = "\"" then "\\\""
    else if c = "\\" then "\\\\"
    else let val k = ord c
    in if k < 32 orelse k > 126 then "\\" ^ radixstring (8, "0", k) else c end
  fun numeral_scala k = if k < 0
    then if k > ~ 2147483647 then "- " ^ string_of_int (~ k)
      else quote ("- " ^ string_of_int (~ k))
    else if k <= 2147483647 then string_of_int k
      else quote (string_of_int k)
in Literals {
  literal_char = Library.enclose "'" "'" o char_scala,
  literal_string = quote o translate_string char_scala,
  literal_numeral = fn k => "BigInt(" ^ numeral_scala k ^ ")",
  literal_positive_numeral = fn k => "Nat.Nat(" ^ numeral_scala k ^ ")",
  literal_alternative_numeral = fn k => "Natural.Nat(" ^ numeral_scala k ^ ")",
  literal_naive_numeral = fn k => "BigInt(" ^ numeral_scala k ^ ")",
  literal_list = fn [] => str "Nil" | ps => Pretty.block [str "List", enum "," "(" ")" ps],
  infix_cons = (6, "::")
} end;


(** Isar setup **)

fun isar_serializer module_name =
  Code_Target.parse_args (Scan.succeed ())
  #> (fn () => serialize_scala module_name);

val setup =
  Code_Target.add_target
    (target, { serializer = isar_serializer, literals = literals,
      check = { env_var = "SCALA_HOME", make_destination = fn p => Path.append p (Path.explode "ROOT.scala"),
        make_command = fn scala_home => fn p => fn _ =>
          "export JAVA_OPTS='-Xms128m -Xmx512m -Xss2m' && "
            ^ Path.implode (Path.append (Path.explode scala_home) (Path.explode "bin/scalac")) ^ " " ^ File.shell_path p } })
  #> Code_Target.add_syntax_tyco target "fun"
     (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
        brackify_infix (1, R) fxy (
          print_typ BR ty1 (*product type vs. tupled arguments!*),
          str "=>",
          print_typ (INFX (1, R)) ty2
        )))
  #> fold (Code_Target.add_reserved target) [
      "abstract", "case", "catch", "class", "def", "do", "else", "extends", "false",
      "final", "finally", "for", "forSome", "if", "implicit", "import", "lazy",
      "match", "new", "null", "object", "override", "package", "private", "protected",
      "requires", "return", "sealed", "super", "this", "throw", "trait", "try",
      "true", "type", "val", "var", "while", "with", "yield"
    ]
  #> fold (Code_Target.add_reserved target) [
      "apply", "error", "BigInt", "Nil", "List"
    ];

end; (*struct*)
