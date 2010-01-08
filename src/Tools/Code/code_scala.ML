(*  Author:     Florian Haftmann, TU Muenchen

Serializer for Scala.
*)

signature CODE_SCALA =
sig
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

fun print_scala_stmt labelled_name syntax_tyco syntax_const reserved args_num is_singleton deresolve =
  let
    val deresolve_base = Long_Name.base_name o deresolve;
    fun print_typ tyvars fxy (tycoexpr as tyco `%% tys) = (case syntax_tyco tyco
         of NONE => applify "[" "]" fxy
              ((str o deresolve) tyco) (map (print_typ tyvars NOBR) tys)
          | SOME (i, print) => print (print_typ tyvars) fxy tys)
      | print_typ tyvars fxy (ITyVar v) = (str o lookup_var tyvars) v;
    fun print_typed tyvars p ty =
      Pretty.block [p, str ":", Pretty.brk 1, print_typ tyvars NOBR ty]
    fun print_var vars NONE = str "_"
      | print_var vars (SOME v) = (str o lookup_var vars) v
    fun print_term tyvars is_pat thm vars fxy (IConst c) =
          print_app tyvars is_pat thm vars fxy (c, [])
      | print_term tyvars is_pat thm vars fxy (t as (t1 `$ t2)) =
          (case Code_Thingol.unfold_const_app t
           of SOME app => print_app tyvars is_pat thm vars fxy app
            | _ => applify "(" ")" fxy
                (print_term tyvars is_pat thm vars BR t1)
                [print_term tyvars is_pat thm vars NOBR t2])
      | print_term tyvars is_pat thm vars fxy (IVar v) =
          print_var vars v
      | print_term tyvars is_pat thm vars fxy ((v, ty) `|=> t) =
          let
            val vars' = intro_vars (the_list v) vars;
          in
            concat [
              Pretty.block [str "(", print_typed tyvars (print_var vars' v) ty, str ")"],
              str "=>",
              print_term tyvars false thm vars' NOBR t
            ]
          end 
      | print_term tyvars is_pat thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then print_case tyvars thm vars fxy cases
                else print_app tyvars is_pat thm vars fxy c_ts
            | NONE => print_case tyvars thm vars fxy cases)
    and print_app tyvars is_pat thm vars fxy (app as ((c, ((tys, _), _)), ts)) =
      let
        val k = length ts;
        val l = case syntax_const c of NONE => args_num c | SOME (l, _) => l;
        val tys' = if is_pat orelse
          (is_none (syntax_const c) andalso is_singleton c) then [] else tys;
        val (no_syntax, print') = case syntax_const c
         of NONE => (true, fn ts => applify "(" ")" fxy
              (applify "[" "]" NOBR ((str o deresolve) c) (map (print_typ tyvars NOBR) tys'))
                (map (print_term tyvars is_pat thm vars NOBR) ts))
          | SOME (_, print) => (false, fn ts =>
              print (print_term tyvars is_pat thm) thm vars fxy (ts ~~ take k tys));
      in if k = l then print' ts
      else if k < l then
        print_term tyvars is_pat thm vars fxy (Code_Thingol.eta_expand l app)
      else let
        val (ts1, ts23) = chop l ts;
      in
        Pretty.block (print' ts1 :: map (fn t => Pretty.block
          [str ".apply(", print_term tyvars is_pat thm vars NOBR t, str ")"]) ts23)
      end end
    and print_bind tyvars thm fxy p = gen_print_bind (print_term tyvars true) thm fxy p
    and print_case tyvars thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_match ((pat, ty), t) vars =
              vars
              |> print_bind tyvars thm BR pat
              |>> (fn p => semicolon [Pretty.block [str "val", Pretty.brk 1, p,
                str ":", Pretty.brk 1, print_typ tyvars NOBR ty],
                  str "=", print_term tyvars false thm vars NOBR t])
            val (ps, vars') = fold_map print_match binds vars;
          in
            brackify_block fxy
              (str "{")
              (ps @| print_term tyvars false thm vars' NOBR body)
              (str "}")
          end
      | print_case tyvars thm vars fxy (((t, ty), clauses as _ :: _), _) =
          let
            fun print_select (pat, body) =
              let
                val (p, vars') = print_bind tyvars thm NOBR pat vars;
              in concat [str "case", p, str "=>", print_term tyvars false thm vars' NOBR body] end;
          in brackify_block fxy
            (concat [print_term tyvars false thm vars NOBR t, str "match", str "{"])
            (map print_select clauses)
            (str "}") 
          end
      | print_case tyvars thm vars fxy ((_, []), _) =
          (brackify fxy o Pretty.breaks o map str) ["error(\"empty case\")"];
    fun implicit_arguments tyvars vs vars =
      let
        val implicit_typ_ps = maps (fn (v, sort) => map (fn class => Pretty.block
          [(str o deresolve) class, str "[", (str o lookup_var tyvars) v, str "]"]) sort) vs;
        val implicit_names = Name.invents (snd vars) "a" (length implicit_typ_ps);
        val vars' = intro_vars implicit_names vars;
        val implicit_ps = map2 (fn v => fn p => concat [str (v ^ ":"), p])
          implicit_names implicit_typ_ps;
      in ((implicit_names, implicit_ps), vars') end;
    fun print_defhead tyvars vars p vs params tys implicits ty =
      concat [str "def", print_typed tyvars (applify "(implicit " ")" NOBR
        (applify "(" ")" NOBR
          (applify "[" "]" NOBR p (map (str o lookup_var tyvars o fst) vs))
            (map2 (fn param => fn ty => print_typed tyvars
                ((str o lookup_var vars) param) ty)
              params tys)) implicits) ty, str "="]
    fun print_stmt (name, Code_Thingol.Fun (_, ((vs, ty), raw_eqs))) = (case filter (snd o snd) raw_eqs
         of [] =>
              let
                val (tys, ty') = Code_Thingol.unfold_fun ty;
                val params = Name.invents (snd reserved) "a" (length tys);
                val tyvars = intro_vars (map fst vs) reserved;
                val vars = intro_vars params reserved;
              in
                concat [print_defhead tyvars vars ((str o deresolve) name) vs params tys [] ty',
                  str ("error(\"" ^ name ^ "\")")]
              end
          | eqs =>
              let
                val tycos = fold (fn ((ts, t), (thm, _)) =>
                  fold Code_Thingol.add_tyconames (t :: ts)) eqs [];
                val tyvars = reserved
                  |> intro_base_names
                       (is_none o syntax_tyco) deresolve tycos
                  |> intro_vars (map fst vs);
                val simple = case eqs
                 of [((ts, _), _)] => forall Code_Thingol.is_IVar ts
                  | _ => false;
                val consts = fold Code_Thingol.add_constnames
                  (map (snd o fst) eqs) [];
                val vars1 = reserved
                  |> intro_base_names
                       (is_none o syntax_const) deresolve consts
                val ((_, implicit_ps), vars2) = implicit_arguments tyvars vs vars1;
                val params = if simple then (map (fn IVar (SOME x) => x) o fst o fst o hd) eqs
                  else aux_params vars2 (map (fst o fst) eqs);
                val vars3 = intro_vars params vars2;
                val (tys, ty1) = Code_Thingol.unfold_fun ty;
                val (tys1, tys2) = chop (length params) tys;
                val ty2 = Library.foldr
                  (fn (ty1, ty2) => Code_Thingol.fun_tyco `%% [ty1, ty2]) (tys2, ty1);
                fun print_tuple [p] = p
                  | print_tuple ps = enum "," "(" ")" ps;
                fun print_rhs vars' ((_, t), (thm, _)) = print_term tyvars false thm vars' NOBR t;
                fun print_clause (eq as ((ts, _), (thm, _))) =
                  let
                    val vars' = intro_vars ((fold o Code_Thingol.fold_varnames) (insert (op =)) ts []) vars2;
                  in
                    concat [str "case", print_tuple (map (print_term tyvars true thm vars' NOBR) ts),
                      str "=>", print_rhs vars' eq]
                  end;
                val head = print_defhead tyvars vars3 ((str o deresolve) name) vs params tys1 implicit_ps ty2;
              in if simple then
                concat [head, print_rhs vars3 (hd eqs)]
              else
                Pretty.block_enclose
                  (concat [head, print_tuple (map (str o lookup_var vars3) params),
                    str "match", str "{"], str "}")
                  (map print_clause eqs)
              end)
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, cos))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_co (co, []) =
                  concat [str "final", str "case", str "object", (str o deresolve_base) co,
                    str "extends", applify "[" "]" NOBR ((str o deresolve_base) name)
                      (replicate (length vs) (str "Nothing"))]
              | print_co (co, tys) =
                  let
                    val fields = Name.names (snd reserved) "a" tys;
                    val vars = intro_vars (map fst fields) reserved;
                    fun add_typargs p = applify "[" "]" NOBR p
                      (map (str o lookup_var tyvars o fst) vs);
                  in
                    concat [
                      applify "(" ")" NOBR
                        (add_typargs ((concat o map str) ["final", "case", "class", deresolve_base co]))
                        (map (uncurry (print_typed tyvars) o apfst str) fields),
                      str "extends",
                      add_typargs ((str o deresolve_base) name)
                    ]
                  end
          in
            Pretty.chunks (
              applify "[" "]" NOBR ((concat o map str) ["sealed", "class", deresolve_base name])
                (map (str o prefix "+" o lookup_var tyvars o fst) vs)
              :: map print_co cos
            )
          end
      | print_stmt (name, Code_Thingol.Class (_, (v, (superclasses, classparams)))) =
          let
            val tyvars = intro_vars [v] reserved;
            val vs = [(v, [name])];
            fun add_typarg p = applify "[" "]" NOBR p [(str o lookup_var tyvars) v];
            fun print_superclasses [] = NONE
              | print_superclasses classes = SOME (concat (str "extends"
                  :: separate (str "with") (map (add_typarg o str o deresolve o fst) classes)));
            fun print_tupled_typ ([], ty) =
                  print_typ tyvars NOBR ty
              | print_tupled_typ ([ty1], ty2) =
                  concat [print_typ tyvars BR ty1, str "=>", print_typ tyvars NOBR ty2]
              | print_tupled_typ (tys, ty) =
                  concat [enum "," "(" ")" (map (print_typ tyvars NOBR) tys),
                    str "=>", print_typ tyvars NOBR ty];
            fun print_classparam_val (classparam, ty) =
              concat [str "val", (str o suffix "$:" o deresolve_base) classparam,
                (print_tupled_typ o Code_Thingol.unfold_fun) ty]
            fun print_classparam_def (classparam, ty) =
              let
                val (tys, ty) = Code_Thingol.unfold_fun ty;
                val params = Name.invents (snd reserved) "a" (length tys);
                val vars = intro_vars params reserved;
                val (([implicit], [p_implicit]), vars') = implicit_arguments tyvars vs vars;
                val head = print_defhead tyvars vars' ((str o deresolve) classparam) vs params tys [p_implicit] ty;
              in
                concat [head, applify "(" ")" NOBR
                  (Pretty.block [str implicit, str ".", (str o suffix "$" o deresolve_base) classparam])
                  (map (str o lookup_var vars') params)]
              end;
          in
            Pretty.chunks (
              (Pretty.block_enclose
                (concat ([str "trait", add_typarg ((str o deresolve_base) name)]
                  @ the_list (print_superclasses superclasses) @ [str "{"]), str "}")
                (map print_classparam_val classparams))
              :: map print_classparam_def classparams
            )
          end
      | print_stmt (name, Code_Thingol.Classinst ((class, (tyco, vs)),
            (super_instances, classparam_insts))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            val insttyp = tyco `%% map (ITyVar o fst) vs;
            val p_inst_typ = print_typ tyvars NOBR insttyp;
            fun add_typ_params p = applify "[" "]" NOBR p (map (str o lookup_var tyvars o fst) vs);
            fun add_inst_typ p = Pretty.block [p, str "[", p_inst_typ, str "]"];
            val ((implicit_names, implicit_ps), vars) = implicit_arguments tyvars vs reserved;
            fun print_classparam_inst ((classparam, const as (_, (_, tys))), (thm, _)) =
              let
                val auxs = Name.invents (snd reserved) "a" (length tys);
                val vars = intro_vars auxs reserved;
                val args = if null auxs then [] else
                  [concat [enum "," "(" ")" (map2 (fn aux => fn ty => print_typed tyvars ((str o lookup_var vars) aux) ty)
                    auxs tys), str "=>"]];
              in 
                concat ([str "val", (str o suffix "$" o deresolve_base) classparam,
                  str "="] @ args @ [print_app tyvars false thm vars NOBR (const, map (IVar o SOME) auxs)])
              end;
          in
            Pretty.chunks [
              Pretty.block_enclose
                (concat ([str "trait",
                    add_typ_params ((str o deresolve_base) name),
                    str "extends",
                    Pretty.block [(str o deresolve) class, str "[", p_inst_typ, str "]"]]
                    @ map (fn (_, (_, (superinst, _))) => add_typ_params (str ("with " ^ deresolve superinst)))
                      super_instances @| str "{"), str "}")
                (map (fn p => Pretty.block [str "implicit val arg$", p]) implicit_ps
                  @ map print_classparam_inst classparam_insts),
              concat [str "implicit", str (if null vs then "val" else "def"),
                applify "(implicit " ")" NOBR (applify "[" "]" NOBR
                  ((str o deresolve_base) name) (map (str o lookup_var tyvars o fst) vs))
                    implicit_ps,
                  str "=", str "new", applify "[" "]" NOBR ((str o deresolve_base) name)
                      (map (str o lookup_var tyvars o fst) vs),
                    Pretty.enum ";" "{ " " }" (map (str o (fn v => "val arg$" ^ v ^ " = " ^ v) o lookup_var vars)
                      implicit_names)]
            ]
          end;
  in print_stmt end;

fun scala_program_of_program labelled_name module_name reserved raw_module_alias program =
  let
    val the_module_name = the_default "Program" module_name;
    val module_alias = K (SOME the_module_name);
    val reserved = Name.make_context reserved;
    fun prepare_stmt (name, stmt) (nsps, stmts) =
      let
        val (_, base) = Code_Printer.dest_name name;
        val mk_name_stmt = yield_singleton Name.variants;
        fun add_class ((nsp_class, nsp_object), nsp_common) =
          let
            val (base', nsp_class') = mk_name_stmt base nsp_class
          in (base', ((nsp_class', nsp_object), Name.declare base' nsp_common)) end;
        fun add_object ((nsp_class, nsp_object), nsp_common) =
          let
            val (base', nsp_object') = mk_name_stmt base nsp_object
          in (base', ((nsp_class, nsp_object'), Name.declare base' nsp_common)) end;
        fun add_common upper ((nsp_class, nsp_object), nsp_common) =
          let
            val (base', nsp_common') =
              mk_name_stmt (if upper then first_upper base else base) nsp_common
          in (base', ((Name.declare base' nsp_class, Name.declare base' nsp_object), nsp_common')) end;
        val add_name = case stmt
         of Code_Thingol.Fun _ => add_object
          | Code_Thingol.Datatype _ => add_class
          | Code_Thingol.Datatypecons _ => add_common true
          | Code_Thingol.Class _ => add_class
          | Code_Thingol.Classrel _ => add_object
          | Code_Thingol.Classparam _ => add_object
          | Code_Thingol.Classinst _ => add_common false;
        fun add_stmt base' = case stmt
         of Code_Thingol.Datatypecons _ => cons (name, (base', NONE))
          | Code_Thingol.Classrel _ => cons (name, (base', NONE))
          | Code_Thingol.Classparam _ => cons (name, (base', NONE))
          | _ => cons (name, (base', SOME stmt));
      in
        nsps
        |> add_name
        |-> (fn base' => rpair (add_stmt base' stmts))
      end;
    val (_, sca_program) = fold prepare_stmt (AList.make (fn name => Graph.get_node program name)
      (Graph.strong_conn program |> flat)) (((reserved, reserved), reserved), []);
    fun deresolver name = (fst o the o AList.lookup (op =) sca_program) name
      handle Option => error ("Unknown statement name: " ^ labelled_name name);
  in (deresolver, (the_module_name, sca_program)) end;

fun serialize_scala raw_module_name labelled_name
    raw_reserved includes raw_module_alias
    _ syntax_tyco syntax_const (code_of_pretty, code_writeln) program cs destination =
  let
    val stmt_names = Code_Target.stmt_names_of_destination destination;
    val module_name = if null stmt_names then raw_module_name else SOME "Code";
    val reserved = fold (insert (op =) o fst) includes raw_reserved;
    val (deresolver, (the_module_name, sca_program)) = scala_program_of_program labelled_name
      module_name reserved raw_module_alias program;
    val reserved = make_vars reserved;
    fun args_num c = case Graph.get_node program c
     of Code_Thingol.Fun (_, ((_, ty), [])) => (length o fst o Code_Thingol.unfold_fun) ty
      | Code_Thingol.Fun (_, (_, ((ts, _), _) :: _)) => length ts
      | Code_Thingol.Datatypecons (_, tyco) =>
          let val Code_Thingol.Datatype (_, (_, dtcos)) = Graph.get_node program tyco
          in (length o the o AList.lookup (op =) dtcos) c end
      | Code_Thingol.Classparam (_, class) =>
          let val Code_Thingol.Class (_, (_, (_, classparams))) = Graph.get_node program class
          in (length o fst o Code_Thingol.unfold_fun o the o AList.lookup (op =) classparams) c end;
    fun is_singleton c = case Graph.get_node program c
     of Code_Thingol.Datatypecons (_, tyco) =>
          let val Code_Thingol.Datatype (_, (_, dtcos)) = Graph.get_node program tyco
          in (null o the o AList.lookup (op =) dtcos) c end
      | _ => false;
    val print_stmt = print_scala_stmt labelled_name syntax_tyco syntax_const
      reserved args_num is_singleton deresolver;
    fun print_module name content =
      (name, Pretty.chunks [
        str ("object " ^ name ^ " {"),
        str "",
        content,
        str "",
        str "}"
      ]);
    fun serialize_module the_module_name sca_program =
      let
        val content = Pretty.chunks2 (map_filter
          (fn (name, (_, SOME stmt)) => SOME (print_stmt (name, stmt))
            | (_, (_, NONE)) => NONE) sca_program);
      in print_module the_module_name content end;
    fun check_destination destination =
      (File.check destination; destination);
    fun write_module destination (modlname, content) =
      let
        val filename = case modlname
         of "" => Path.explode "Main.scala"
          | _ => (Path.ext "scala" o Path.explode o implode o separate "/"
                o Long_Name.explode) modlname;
        val pathname = Path.append destination filename;
        val _ = File.mkdir (Path.dir pathname);
      in File.write pathname (code_of_pretty content) end
  in
    Code_Target.mk_serialization target NONE
      (fn NONE => K () o map (code_writeln o snd) | SOME file => K () o map
        (write_module (check_destination file)))
      (rpair [] o cat_lines o map (code_of_pretty o snd))
      (map (uncurry print_module) includes
        @| serialize_module the_module_name sca_program)
      destination
  end;

val literals = let
  fun char_scala c =
    let
      val s = ML_Syntax.print_char c;
    in if s = "'" then "\\'" else s end;
in Literals {
  literal_char = Library.enclose "'" "'" o char_scala,
  literal_string = quote o translate_string char_scala,
  literal_numeral = fn unbounded => fn k => if k >= 0 then string_of_int k
    else Library.enclose "(" ")" (signed_string_of_int k),
  literal_list = fn ps => Pretty.block [str "List", enum "," "(" ")" ps],
  infix_cons = (6, "::")
} end;


(** Isar setup **)

fun isar_seri_scala module_name =
  Code_Target.parse_args (Scan.succeed ())
  #> (fn () => serialize_scala module_name);

val setup =
  Code_Target.add_target (target, (isar_seri_scala, literals))
  #> Code_Target.add_syntax_tyco target "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        print_typ (INFX (1, X)) ty1,
        str "=>",
        print_typ (INFX (1, R)) ty2
      ]))
  #> fold (Code_Target.add_reserved target) [
      "abstract", "case", "catch", "class", "def", "do", "else", "extends", "false",
      "final", "finally", "for", "forSome", "if", "implicit", "import", "lazy",
      "match", "new", "null", "object", "override", "package", "private", "protected",
      "requires", "return", "sealed", "super", "this", "throw", "trait", "try",
      "true", "type", "val", "var", "while", "with"
    ]
  #> fold (Code_Target.add_reserved target) [
      "error", "apply", "List"
    ];

end; (*struct*)
