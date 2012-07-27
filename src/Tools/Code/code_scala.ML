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

fun print_scala_stmt tyco_syntax const_syntax reserved
    args_num is_singleton_constr (deresolve, deresolve_full) =
  let
    fun lookup_tyvar tyvars = lookup_var tyvars o first_upper;
    fun intro_tyvars vs = intro_vars (map (first_upper o fst) vs);
    fun print_tyco_expr tyvars fxy (tyco, tys) = applify "[" "]"
          (print_typ tyvars NOBR) fxy ((str o deresolve) tyco) tys
    and print_typ tyvars fxy (tyco `%% tys) = (case tyco_syntax tyco
         of NONE => print_tyco_expr tyvars fxy (tyco, tys)
          | SOME (_, print) => print (print_typ tyvars) fxy tys)
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
    fun print_term tyvars is_pat some_thm vars fxy (IConst const) =
          print_app tyvars is_pat some_thm vars fxy (const, [])
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
      | print_term tyvars is_pat some_thm vars fxy (ICase case_expr) =
          (case Code_Thingol.unfold_const_app (#primitive case_expr)
           of SOME (app as ({ name = c, ... }, _)) => if is_none (const_syntax c)
                then print_case tyvars some_thm vars fxy case_expr
                else print_app tyvars is_pat some_thm vars fxy app
            | NONE => print_case tyvars some_thm vars fxy case_expr)
    and print_app tyvars is_pat some_thm vars fxy
        (app as ({ name = c, typargs, dom, ... }, ts)) =
      let
        val k = length ts;
        val typargs' = if is_pat orelse
          (is_none (const_syntax c) andalso is_singleton_constr c) then [] else typargs;
        val (l, print') = case const_syntax c
         of NONE => (args_num c, fn fxy => fn ts => applify "(" ")"
              (print_term tyvars is_pat some_thm vars NOBR) fxy
                (applify "[" "]" (print_typ tyvars NOBR)
                  NOBR ((str o deresolve) c) typargs') ts)
          | SOME (Plain_const_syntax (k, s)) => (k, fn fxy => fn ts => applify "(" ")"
              (print_term tyvars is_pat some_thm vars NOBR) fxy
                (applify "[" "]" (print_typ tyvars NOBR)
                  NOBR (str s) typargs') ts)
          | SOME (Complex_const_syntax (k, print)) =>
              (k, fn fxy => fn ts => print (print_term tyvars is_pat some_thm) some_thm vars fxy
                (ts ~~ take k dom))
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
    and print_case tyvars some_thm vars fxy { clauses = [], ... } =
          (brackify fxy o Pretty.breaks o map str) ["sys.error(\"empty case\")"]
      | print_case tyvars some_thm vars fxy (case_expr as { clauses = [_], ... }) =
          let
            val (bind :: binds, body) = Code_Thingol.unfold_let (ICase case_expr);
            fun print_match_val ((pat, ty), t) vars =
              vars
              |> print_bind tyvars some_thm BR pat
              |>> (fn p => (false, concat [str "val", constraint p (print_typ tyvars NOBR ty),
                  str "=", print_term tyvars false some_thm vars NOBR t]));
            fun print_match_seq t vars =
              ((true, print_term tyvars false some_thm vars NOBR t), vars);
            fun print_match is_first ((IVar NONE, ty), t) =
                  if Code_Thingol.is_IAbs t andalso is_first
                    then print_match_val ((IVar NONE, ty), t)
                    else print_match_seq t
              | print_match _ ((pat, ty), t) =
                  print_match_val ((pat, ty), t);
            val (seps_ps, vars') =
              vars |> print_match true bind ||>> fold_map (print_match false) binds |>> uncurry cons;
            val all_seps_ps = seps_ps @ [(true, print_term tyvars false some_thm vars' NOBR body)];
            fun insert_seps [(_, p)] = [p]
              | insert_seps ((_, p) :: (seps_ps as (sep, _) :: _)) =
                  (if sep then Pretty.block [p, str ";"] else p) :: insert_seps seps_ps
          in brackify_block fxy (str "{") (insert_seps all_seps_ps) (str "}") end
      | print_case tyvars some_thm vars fxy { term = t, typ = ty, clauses = clauses as _ :: _, ... } =
          let
            fun print_select (pat, body) =
              let
                val (p_pat, vars') = print_bind tyvars some_thm NOBR pat vars;
                val p_body = print_term tyvars false some_thm vars' NOBR body
              in concat [str "case", p_pat, str "=>", p_body] end;
          in
            map print_select clauses
            |> Pretty.block_enclose (concat [print_term tyvars false some_thm vars NOBR t, str "match", str "{"], str "}")
            |> single
            |> enclose "(" ")"
          end;
    fun print_context tyvars vs name = applify "[" "]"
      (fn (v, sort) => (Pretty.block o map str)
        (lookup_tyvar tyvars v :: maps (fn sort => [" : ", deresolve sort]) sort))
          NOBR ((str o deresolve) name) vs;
    fun print_defhead tyvars vars name vs params tys ty =
      Pretty.block [str "def ", constraint (applify "(" ")" (fn (param, ty) =>
        constraint ((str o lookup_var vars) param) (print_typ tyvars NOBR ty))
          NOBR (print_context tyvars vs name) (params ~~ tys)) (print_typ tyvars NOBR ty),
            str " ="];
    fun print_def name (vs, ty) [] =
          let
            val (tys, ty') = Code_Thingol.unfold_fun ty;
            val params = Name.invent (snd reserved) "a" (length tys);
            val tyvars = intro_tyvars vs reserved;
            val vars = intro_vars params reserved;
          in
            concat [print_defhead tyvars vars name vs params tys ty',
              str ("sys.error(\"" ^ name ^ "\")")]
          end
      | print_def name (vs, ty) eqs =
          let
            val tycos = fold (fn ((ts, t), _) =>
              fold Code_Thingol.add_tyconames (t :: ts)) eqs [];
            val tyvars = reserved
              |> intro_base_names
                   (is_none o tyco_syntax) deresolve tycos
              |> intro_tyvars vs;
            val simple = case eqs
             of [((ts, _), _)] => forall Code_Thingol.is_IVar ts
              | _ => false;
            val consts = fold Code_Thingol.add_constnames
              (map (snd o fst) eqs) [];
            val vars1 = reserved
              |> intro_base_names
                   (is_none o const_syntax) deresolve consts
            val params = if simple
              then (map (fn IVar (SOME x) => x) o fst o fst o hd) eqs
              else aux_params vars1 (map (fst o fst) eqs);
            val vars2 = intro_vars params vars1;
            val (tys', ty') = Code_Thingol.unfold_fun_n (length params) ty;
            fun tuplify [p] = p
              | tuplify ps = enum "," "(" ")" ps;
            fun print_rhs vars' ((_, t), (some_thm, _)) =
              print_term tyvars false some_thm vars' NOBR t;
            fun print_clause (eq as ((ts, _), (some_thm, _))) =
              let
                val vars' = intro_vars ((fold o Code_Thingol.fold_varnames)
                  (insert (op =)) ts []) vars1;
              in
                concat [str "case",
                  tuplify (map (print_term tyvars true some_thm vars' NOBR) ts),
                  str "=>", print_rhs vars' eq]
              end;
            val head = print_defhead tyvars vars2 name vs params tys' ty';
          in if simple then
            concat [head, print_rhs vars2 (hd eqs)]
          else
            Pretty.block_enclose
              (concat [head, tuplify (map (str o lookup_var vars2) params),
                str "match", str "{"], str "}")
              (map print_clause eqs)
          end;
    val print_method = str o Library.enclose "`" "`" o deresolve_full;
    fun print_stmt (name, Code_Thingol.Fun (_, (((vs, ty), raw_eqs), _))) =
          print_def name (vs, ty) (filter (snd o snd) raw_eqs)
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, cos))) =
          let
            val tyvars = intro_tyvars (map (rpair []) vs) reserved;
            fun print_co ((co, _), []) =
                  concat [str "final", str "case", str "object", (str o deresolve) co,
                    str "extends", applify "[" "]" I NOBR ((str o deresolve) name)
                      (replicate (length vs) (str "Nothing"))]
              | print_co ((co, vs_args), tys) =
                  concat [applify "(" ")"
                    (fn (v, arg) => constraint (str v) (print_typ tyvars NOBR arg)) NOBR
                    (applify "[" "]" (str o lookup_tyvar tyvars) NOBR ((concat o map str)
                      ["final", "case", "class", deresolve co]) vs_args)
                    (Name.invent_names (snd reserved) "a" tys),
                    str "extends",
                    applify "[" "]" (str o lookup_tyvar tyvars) NOBR
                      ((str o deresolve) name) vs
                  ];
          in
            Pretty.chunks (applify "[" "]" (str o prefix "+" o lookup_tyvar tyvars)
              NOBR ((concat o map str) ["abstract", "sealed", "class", deresolve name]) vs
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
                val [implicit_name] = Name.invent (snd reserved) (lookup_tyvar tyvars v) 1;
                val proto_vars = intro_vars [implicit_name] reserved;
                val auxs = Name.invent (snd proto_vars) "a" (length tys);
                val vars = intro_vars auxs proto_vars;
              in
                concat [str "def", constraint (Pretty.block [applify "(" ")"
                  (fn (aux, ty) => constraint ((str o lookup_var vars) aux)
                  (print_typ tyvars NOBR ty)) NOBR (add_typarg (deresolve classparam))
                  (auxs ~~ tys), str "(implicit ", str implicit_name, str ": ",
                  add_typarg (deresolve name), str ")"]) (print_typ tyvars NOBR ty), str "=",
                  applify "(" ")" (str o lookup_var vars) NOBR
                  (Pretty.block [str implicit_name, str ".", print_method classparam]) auxs]
              end;
          in
            Pretty.chunks (
              (Pretty.block_enclose
                (concat ([str "trait", (add_typarg o deresolve) name]
                  @ the_list (print_super_classes super_classes) @ [str "{"]), str "}")
                (map print_classparam_val classparams))
              :: map print_classparam_def classparams
            )
          end
      | print_stmt (name, Code_Thingol.Classinst
          { class, tyco, vs, inst_params, superinst_params, ... }) =
          let
            val tyvars = intro_tyvars vs reserved;
            val classtyp = (class, tyco `%% map (ITyVar o fst) vs);
            fun print_classparam_instance ((classparam, const as { dom, ... }), (thm, _)) =
              let
                val aux_dom = Name.invent_names (snd reserved) "a" dom;
                val auxs = map fst aux_dom;
                val vars = intro_vars auxs reserved;
                val aux_abstr = if null auxs then [] else [enum "," "(" ")"
                  (map (fn (aux, ty) => constraint ((str o lookup_var vars) aux)
                  (print_typ tyvars NOBR ty)) aux_dom), str "=>"];
              in
                concat ([str "val", print_method classparam, str "="]
                  @ aux_abstr @| print_app tyvars false (SOME thm) vars NOBR
                    (const, map (IVar o SOME) auxs))
              end;
          in
            Pretty.block_enclose (concat [str "implicit def",
              constraint (print_context tyvars vs name) (print_dicttyp tyvars classtyp),
              str "=", str "new", print_dicttyp tyvars classtyp, str "{"], str "}")
                (map print_classparam_instance (inst_params @ superinst_params))
          end;
  in print_stmt end;

fun scala_program_of_program labelled_name reserved module_alias program =
  let
    fun namify_module name_fragment ((nsp_class, nsp_object), nsp_common) =
      let
        val declare = Name.declare name_fragment;
      in (name_fragment, ((declare nsp_class, declare nsp_object), declare nsp_common)) end;
    fun namify_class base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_class') = Name.variant base nsp_class
      in (base', ((nsp_class', nsp_object), Name.declare base' nsp_common)) end;
    fun namify_object base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_object') = Name.variant base nsp_object
      in (base', ((nsp_class, nsp_object'), Name.declare base' nsp_common)) end;
    fun namify_common upper base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_common') =
          Name.variant (if upper then first_upper base else base) nsp_common
      in
        (base',
          ((Name.declare base' nsp_class, Name.declare base' nsp_object), nsp_common'))
      end;
    fun namify_stmt (Code_Thingol.Fun _) = namify_object
      | namify_stmt (Code_Thingol.Datatype _) = namify_class
      | namify_stmt (Code_Thingol.Datatypecons _) = namify_common true
      | namify_stmt (Code_Thingol.Class _) = namify_class
      | namify_stmt (Code_Thingol.Classrel _) = namify_object
      | namify_stmt (Code_Thingol.Classparam _) = namify_object
      | namify_stmt (Code_Thingol.Classinst _) = namify_common false;
    fun memorize_implicits name =
      let
        fun is_classinst stmt = case stmt
         of Code_Thingol.Classinst _ => true
          | _ => false;
        val implicits = filter (is_classinst o Graph.get_node program)
          (Graph.immediate_succs program name);
      in union (op =) implicits end;
    fun modify_stmt (_, Code_Thingol.Fun (_, (_, SOME _))) = NONE
      | modify_stmt (_, Code_Thingol.Datatypecons _) = NONE
      | modify_stmt (_, Code_Thingol.Classrel _) = NONE
      | modify_stmt (_, Code_Thingol.Classparam _) = NONE
      | modify_stmt (_, stmt) = SOME stmt;
  in
    Code_Namespace.hierarchical_program labelled_name
      { module_alias = module_alias, reserved = reserved,
        empty_nsp = ((reserved, reserved), reserved), namify_module = namify_module,
        namify_stmt = namify_stmt, cyclic_modules = true, empty_data = [],
        memorize_data = memorize_implicits, modify_stmts = map modify_stmt } program
  end;

fun serialize_scala { labelled_name, reserved_syms, includes,
    module_alias, class_syntax, tyco_syntax, const_syntax } program =
  let

    (* build program *)
    val { deresolver, hierarchical_program = scala_program } =
      scala_program_of_program labelled_name (Name.make_context reserved_syms) module_alias program;

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
    fun print_stmt prefix_fragments = print_scala_stmt
      tyco_syntax const_syntax (make_vars reserved_syms) args_num
      is_singleton_constr (deresolver prefix_fragments, deresolver []);

    (* print modules *)
    fun print_implicit prefix_fragments implicit =
      let
        val s = deresolver prefix_fragments implicit;
      in if length (Long_Name.explode s) = 1 then NONE else SOME (str s) end;
    fun print_module prefix_fragments base implicits ps = Pretty.chunks2
      ([str ("object " ^ base ^ " {")]
        @ (case map_filter (print_implicit prefix_fragments) implicits
            of [] => [] | implicit_ps => (single o Pretty.block)
            (str "import /*implicits*/" :: Pretty.brk 1 :: commas implicit_ps))
        @ ps @ [str ("} /* object " ^ base ^ " */")]);

    (* serialization *)
    val p = Pretty.chunks2 (map snd includes
      @ Code_Namespace.print_hierarchical {
        print_module = print_module, print_stmt = print_stmt,
        lift_markup = I } scala_program);
    fun write width NONE = writeln o format [] width
      | write width (SOME p) = File.write p o format [] width;
    fun prepare names width p = ([("", format names width p)], try (deresolver []));
  in
    Code_Target.serialization write prepare p
  end;

val serializer : Code_Target.serializer =
  Code_Target.parse_args (Scan.succeed ()) #> K serialize_scala;

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
  literal_positive_numeral = fn k => "Nat(" ^ numeral_scala k ^ ")",
  literal_alternative_numeral = fn k => "Natural(" ^ numeral_scala k ^ ")",
  literal_naive_numeral = fn k => "BigInt(" ^ numeral_scala k ^ ")",
  literal_list = fn [] => str "Nil" | ps => Pretty.block [str "List", enum "," "(" ")" ps],
  infix_cons = (6, "::")
} end;


(** Isar setup **)

val setup =
  Code_Target.add_target
    (target, { serializer = serializer, literals = literals,
      check = { env_var = "SCALA_HOME",
        make_destination = fn p => Path.append p (Path.explode "ROOT.scala"),
        make_command = fn _ =>
          "env JAVA_OPTS='-Xms128m -Xmx512m -Xss2m' \"$SCALA_HOME/bin/scalac\" ROOT.scala" } })
  #> Code_Target.add_tyco_syntax target "fun"
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
      "apply", "sys", "scala", "BigInt", "Nil", "List"
    ];

end; (*struct*)
