(*  Title:      Tools/Code/code_scala.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for Scala.
*)

signature CODE_SCALA =
sig
  val target: string
end;

structure Code_Scala : CODE_SCALA =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;

(** Scala serializer **)

val target = "Scala";

val print_scala_string =
  let
    fun chr i = "\\u" ^ align_right "0" 4 (Int.fmt StringCvt.HEX i)
    fun char c = if c = "'" then "\\'"
      else if c = "\"" then "\\\""
      else if c = "\\" then "\\\\"
      else
        let
          val i = ord c
        in
          if i < 32 orelse i > 126
          then chr i
          else if i >= 128
          then error "non-ASCII byte in Scala string literal"
          else c
        end
  in quote o translate_string char end;

datatype scala_stmt = Fun of typscheme * ((iterm list * iterm) * (thm option * bool)) list
  | Datatype of vname list * ((string * vname list) * itype list) list
  | Class of (vname * ((class * class) list * (string * itype) list))
      * (string * { vs: (vname * sort) list,
      inst_params: ((string * (const * int)) * (thm * bool)) list,
      superinst_params: ((string * (const * int)) * (thm * bool)) list }) list;

fun print_scala_stmt tyco_syntax const_syntax reserved
    args_num is_constr (deresolve, deresolve_full) =
  let
    val deresolve_const = deresolve o Constant;
    val deresolve_tyco = deresolve o Type_Constructor;
    val deresolve_class = deresolve o Type_Class;
    fun lookup_tyvar tyvars = lookup_var tyvars o Name.enforce_case true;
    fun intro_tyvars vs = intro_vars (map (Name.enforce_case true o fst) vs);
    fun print_tyco_expr tyvars fxy (sym, tys) = applify "[" "]"
          (print_typ tyvars NOBR) fxy ((str o deresolve) sym) tys
    and print_typ tyvars fxy (tyco `%% tys) = (case tyco_syntax tyco
         of NONE => print_tyco_expr tyvars fxy (Type_Constructor tyco, tys)
          | SOME (_, print) => print (print_typ tyvars) fxy tys)
      | print_typ tyvars fxy (ITyVar v) = (str o lookup_tyvar tyvars) v;
    fun print_dicttyp tyvars (class, ty) = print_tyco_expr tyvars NOBR (Type_Class class, [ty]);
    fun print_tupled_typ tyvars ([], ty) =
          print_typ tyvars NOBR ty
      | print_tupled_typ tyvars ([ty1], ty2) =
          concat [print_typ tyvars BR ty1, str "=>", print_typ tyvars NOBR ty2]
      | print_tupled_typ tyvars (tys, ty) =
          concat [enum "," "(" ")" (map (print_typ tyvars NOBR) tys),
            str "=>", print_typ tyvars NOBR ty];
    fun constraint p1 p2 = Pretty.block [p1, str ":", Pretty.brk 1, p2];
    fun print_var vars NONE = str "_"
      | print_var vars (SOME v) = (str o lookup_var vars) v;
    fun applify_dict tyvars (Dict (_, d)) = applify_plain_dict tyvars d
    and applify_plain_dict tyvars (Dict_Const (inst, dss)) =
          applify_dictss tyvars ((str o deresolve o Class_Instance) inst) dss
      | applify_plain_dict tyvars (Dict_Var { var, class, ... }) =
          Pretty.block [str "implicitly",
            enclose "[" "]" [Pretty.block [(str o deresolve_class) class,
              enclose "[" "]" [(str o lookup_tyvar tyvars) var]]]]
    and applify_dictss tyvars p dss =
      applify "(" ")" (applify_dict tyvars) NOBR p (flat dss)
    fun print_term tyvars is_pat some_thm vars fxy (IConst const) =
          print_app tyvars is_pat some_thm vars fxy (const, [])
      | print_term tyvars is_pat some_thm vars fxy (t as (t1 `$ t2)) =
          (case Code_Thingol.unfold_const_app t
           of SOME app => print_app tyvars is_pat some_thm vars fxy app
            | _ => applify "(" ")" (print_term tyvars is_pat some_thm vars NOBR) fxy
                (print_term tyvars is_pat some_thm vars BR t1) [t2])
      | print_term tyvars is_pat some_thm vars fxy (IVar v) =
          print_var vars v
      | print_term tyvars is_pat some_thm vars fxy (t as _ `|=> _) =
          let
            val (vs_tys, body) = Code_Thingol.unfold_abs t;
            val (ps, vars') = fold_map (print_abs_head tyvars) vs_tys vars;
          in
            brackets (ps @| print_term tyvars false some_thm vars' NOBR body)
          end
      | print_term tyvars is_pat some_thm vars fxy (ICase case_expr) =
          (case Code_Thingol.unfold_const_app (#primitive case_expr)
           of SOME (app as ({ sym = Constant const, ... }, _)) =>
                if is_none (const_syntax const)
                then print_case tyvars some_thm vars fxy case_expr
                else print_app tyvars is_pat some_thm vars fxy app
            | NONE => print_case tyvars some_thm vars fxy case_expr)
    and print_abs_head tyvars (some_v, ty) vars =
           let
             val vars' = intro_vars (the_list some_v) vars;
           in
             (concat [
               enclose "(" ")" [constraint (print_var vars' some_v) (print_typ tyvars NOBR ty)],
               str "=>"
             ], vars')
           end
    and print_app tyvars is_pat some_thm vars fxy
        (app as ({ sym, typargs, dom, dicts, ... }, ts)) =
      let
        val k = length ts;
        val typargs' = if is_pat then [] else typargs;
        val syntax = case sym of
            Constant const => const_syntax const
          | _ => NONE;
        val applify_dicts =
          if is_pat orelse is_some syntax orelse is_constr sym
            orelse Code_Thingol.unambiguous_dictss dicts
          then fn p => K p
          else applify_dictss tyvars;
        val (l, print') = case syntax of
            NONE => (args_num sym, fn fxy => fn ts => applify_dicts
              (gen_applify (is_constr sym) "(" ")"
              (print_term tyvars is_pat some_thm vars NOBR) fxy
                (applify "[" "]" (print_typ tyvars NOBR)
                  NOBR ((str o deresolve) sym) typargs') ts) dicts)
          | SOME (k, Plain_printer s) => (k, fn fxy => fn ts => applify_dicts
              (applify "(" ")"
              (print_term tyvars is_pat some_thm vars NOBR) fxy
                (applify "[" "]" (print_typ tyvars NOBR)
                  NOBR (str s) typargs') ts) dicts)
          | SOME (k, Complex_printer print) =>
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
    fun print_context tyvars vs s = applify "[" "]"
      (fn (v, sort) => (Pretty.block o map str)
        (lookup_tyvar tyvars v :: maps (fn class => [" : ", deresolve_class class]) sort))
          NOBR (str s) vs;
    fun print_defhead tyvars vars const vs params tys ty =
      concat [str "def", constraint (applify "(" ")" (fn (param, ty) =>
        constraint ((str o lookup_var vars) param) (print_typ tyvars NOBR ty))
          NOBR (print_context tyvars vs (deresolve_const const)) (params ~~ tys)) (print_typ tyvars NOBR ty),
            str "="];
    fun print_def const (vs, ty) [] =
          let
            val (tys, ty') = Code_Thingol.unfold_fun ty;
            val params = Name.invent (snd reserved) "a" (length tys);
            val tyvars = intro_tyvars vs reserved;
            val vars = intro_vars params reserved;
          in
            concat [print_defhead tyvars vars const vs params tys ty',
              str ("sys.error(" ^ print_scala_string const ^ ")")]
          end
      | print_def const (vs, ty) eqs =
          let
            val tycos = fold (fn ((ts, t), _) =>
              fold Code_Thingol.add_tyconames (t :: ts)) eqs [];
            val tyvars = reserved
              |> intro_base_names
                   (is_none o tyco_syntax) deresolve_tyco tycos
              |> intro_tyvars vs;
            val simple = case eqs
             of [((ts, _), _)] => forall Code_Thingol.is_IVar ts
              | _ => false;
            val vars1 = reserved
              |> intro_base_names_for (is_none o const_syntax)
                   deresolve (map (snd o fst) eqs);
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
            val head = print_defhead tyvars vars2 const vs params tys' ty';
          in if simple then
            concat [head, print_rhs vars2 (hd eqs)]
          else
            Pretty.block_enclose
              (concat [head, tuplify (map (str o lookup_var vars2) params),
                str "match", str "{"], str "}")
              (map print_clause eqs)
          end;
    val print_method = str o Library.enclose "`" "`" o deresolve_full o Constant;
    fun print_inst class (tyco, { vs, inst_params, superinst_params }) =
      let
        val tyvars = intro_tyvars vs reserved;
        val classtyp = (class, tyco `%% map (ITyVar o fst) vs);
        fun print_classparam_instance ((classparam, (const as { dom, ... }, dom_length)), (thm, _)) =
          let
            val aux_dom = Name.invent_names (snd reserved) "a" dom;
            val auxs = map fst aux_dom;
            val vars = intro_vars auxs reserved;
            val (aux_dom1, aux_dom2) = chop dom_length aux_dom;
            fun abstract_using [] = []
              | abstract_using aux_dom = [enum "," "(" ")"
                  (map (fn (aux, ty) => constraint ((str o lookup_var vars) aux)
                  (print_typ tyvars NOBR ty)) aux_dom), str "=>"];
            val aux_abstr1 = abstract_using aux_dom1;
            val aux_abstr2 = abstract_using aux_dom2;
          in
            concat ([str "val", print_method classparam, str "="]
              @ aux_abstr1 @ aux_abstr2 @| print_app tyvars false (SOME thm) vars NOBR
                (const, map (IVar o SOME) auxs))
          end;
      in
        Pretty.block_enclose (concat [str "implicit def",
          constraint (print_context tyvars vs
            ((Library.enclose "`" "`" o deresolve_full o Class_Instance) (tyco, class)))
          (print_dicttyp tyvars classtyp),
          str "=", str "new", print_dicttyp tyvars classtyp, str "{"], str "}")
            (map print_classparam_instance (inst_params @ superinst_params))
      end;
    fun print_stmt (Constant const, (_, Fun ((vs, ty), raw_eqs))) =
          print_def const (vs, ty) (filter (snd o snd) raw_eqs)
      | print_stmt (Type_Constructor tyco, (_, Datatype (vs, cos))) =
          let
            val tyvars = intro_tyvars (map (rpair []) vs) reserved;
            fun print_co ((co, vs_args), tys) =
              concat [Pretty.block ((applify "[" "]" (str o lookup_tyvar tyvars) NOBR
                (str ("final case class " ^ deresolve_const co)) vs_args)
                @@ enum "," "(" ")" (map (fn (v, arg) => constraint (str v) (print_typ tyvars NOBR arg))
                  (Name.invent_names (snd reserved) "a" tys))),
                str "extends",
                applify "[" "]" (str o lookup_tyvar tyvars) NOBR
                  ((str o deresolve_tyco) tyco) vs
              ];
          in
            Pretty.chunks (applify "[" "]" (str o lookup_tyvar tyvars)
              NOBR (str ("abstract sealed class " ^ deresolve_tyco tyco)) vs
                :: map print_co cos)
          end
      | print_stmt (Type_Class class, (_, Class ((v, (classrels, classparams)), insts))) =
          let
            val tyvars = intro_tyvars [(v, [class])] reserved;
            fun add_typarg s = Pretty.block
              [str s, str "[", (str o lookup_tyvar tyvars) v, str "]"];
            fun print_super_classes [] = NONE
              | print_super_classes classrels = SOME (concat (str "extends"
                  :: separate (str "with") (map (add_typarg o deresolve_class o snd) classrels)));
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
                  (print_typ tyvars NOBR ty)) NOBR (add_typarg (deresolve_const classparam))
                  (auxs ~~ tys), str "(implicit ", str implicit_name, str ": ",
                  add_typarg (deresolve_class class), str ")"]) (print_typ tyvars NOBR ty), str "=",
                  applify "(" ")" (str o lookup_var vars) NOBR
                  (Pretty.block [str implicit_name, str ".", print_method classparam]) auxs]
              end;
          in
            Pretty.chunks (
              (Pretty.block_enclose
                (concat ([str "trait", (add_typarg o deresolve_class) class]
                  @ the_list (print_super_classes classrels) @ [str "{"]), str "}")
                (map print_classparam_val classparams))
              :: map print_classparam_def classparams
              @| Pretty.block_enclose
                (str ("object " ^ deresolve_class class ^ "{"), str "}")
                (map (print_inst class) insts)
            )
          end;
  in print_stmt end;

fun pickup_instances_for_class program =
  let
    val tab =
      Symtab.empty
      |> Code_Symbol.Graph.fold
        (fn (_, (Code_Thingol.Classinst { class, tyco, vs, inst_params, superinst_params, ... }, _)) =>
              Symtab.map_default (class, [])
                (cons (tyco, { vs = vs, inst_params = inst_params, superinst_params = superinst_params }))
           | _ => I) program;
  in Symtab.lookup_list tab end;

fun scala_program_of_program ctxt case_insensitive module_name reserved identifiers exports program =
  let
    val variant = if case_insensitive
      then Code_Namespace.variant_case_insensitive
      else Name.variant;
    fun namify_module name_fragment ((nsp_class, nsp_object), nsp_common) =
      let
        val declare = Name.declare name_fragment;
      in (name_fragment, ((declare nsp_class, declare nsp_object), declare nsp_common)) end;
    fun namify_class base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_class') = variant base nsp_class
      in (base', ((nsp_class', nsp_object), Name.declare base' nsp_common)) end;
    fun namify_object base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_object') = variant base nsp_object
      in (base', ((nsp_class, nsp_object'), Name.declare base' nsp_common)) end;
    fun namify_common base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_common') = variant base nsp_common
      in
        (base', ((Name.declare base' nsp_class, Name.declare base' nsp_object), nsp_common'))
      end;
    fun namify_stmt (Code_Thingol.Fun _) = namify_object
      | namify_stmt (Code_Thingol.Datatype _) = namify_class
      | namify_stmt (Code_Thingol.Datatypecons _) = namify_common
      | namify_stmt (Code_Thingol.Class _) = namify_class
      | namify_stmt (Code_Thingol.Classrel _) = namify_object
      | namify_stmt (Code_Thingol.Classparam _) = namify_object
      | namify_stmt (Code_Thingol.Classinst _) = namify_common;
    val pickup_instances = pickup_instances_for_class program;
    fun modify_stmt (_, (_, Code_Thingol.Fun (_, SOME _))) = NONE
      | modify_stmt (_, (export, Code_Thingol.Fun (x, NONE))) = SOME (export, Fun x)
      | modify_stmt (_, (export, Code_Thingol.Datatype x)) = SOME (export, Datatype x)
      | modify_stmt (_, (_, Code_Thingol.Datatypecons _)) = NONE
      | modify_stmt (Type_Class class, (export, Code_Thingol.Class x)) =
          SOME (export, Class (x, pickup_instances class))
      | modify_stmt (_, (_, Code_Thingol.Classrel _)) = NONE
      | modify_stmt (_, (_, Code_Thingol.Classparam _)) = NONE
      | modify_stmt (_, (_, Code_Thingol.Classinst _)) = NONE
  in
    Code_Namespace.hierarchical_program ctxt
      { module_name = module_name, reserved = reserved, identifiers = identifiers,
        empty_nsp = ((reserved, reserved), reserved), namify_module = namify_module,
        namify_stmt = namify_stmt, cyclic_modules = true,
        class_transitive = true, class_relation_public = false, empty_data = (),
        memorize_data = K I, modify_stmts = map modify_stmt }
      exports program
  end;

fun serialize_scala case_insensitive ctxt { module_name, reserved_syms, identifiers,
    includes, class_syntax, tyco_syntax, const_syntax } program exports =
  let

    (* build program *)
    val { deresolver, hierarchical_program = scala_program } =
      scala_program_of_program ctxt case_insensitive module_name (Name.make_context reserved_syms)
        identifiers exports program;

    (* print statements *)
    fun lookup_constr tyco constr = case Code_Symbol.Graph.get_node program (Type_Constructor tyco)
     of Code_Thingol.Datatype (_, constrs) =>
          the (AList.lookup (op = o apsnd fst) constrs constr);
    fun classparams_of_class class = case Code_Symbol.Graph.get_node program (Type_Class class)
     of Code_Thingol.Class (_, (_, classparams)) => classparams;
    fun args_num (sym as Constant const) = case Code_Symbol.Graph.get_node program sym
     of Code_Thingol.Fun (((_, ty), []), _) =>
          (length o fst o Code_Thingol.unfold_fun) ty
      | Code_Thingol.Fun ((_, ((ts, _), _) :: _), _) => length ts
      | Code_Thingol.Datatypecons tyco => length (lookup_constr tyco const)
      | Code_Thingol.Classparam class =>
          (length o fst o Code_Thingol.unfold_fun o the o AList.lookup (op =)
            (classparams_of_class class)) const;
    fun print_stmt prefix_fragments = print_scala_stmt
      tyco_syntax const_syntax (make_vars reserved_syms) args_num
      (Code_Thingol.is_constr program) (deresolver prefix_fragments, deresolver []);

    (* print modules *)
    fun print_module _ base _ ps = Pretty.chunks2
      (str ("object " ^ base ^ " {")
        :: ps @| str ("} /* object " ^ base ^ " */"));

    (* serialization *)
    val p = Pretty.chunks2 (map snd includes
      @ Code_Namespace.print_hierarchical {
        print_module = print_module, print_stmt = print_stmt,
        lift_markup = I } scala_program);
  in
    (Code_Target.Singleton ("scala", p), try (deresolver []))
  end;

val serializer : Code_Target.serializer =
  Code_Target.parse_args (Scan.optional (Args.$$$ "case_insensitive" >> K true) false
    >> (fn case_insensitive => serialize_scala case_insensitive));

val literals = let
  fun numeral_scala k =
    if ~2147483647 < k andalso k <= 2147483647
    then signed_string_of_int k
    else quote (signed_string_of_int k)
in Literals {
  literal_string = print_scala_string,
  literal_numeral = fn k => "BigInt(" ^ numeral_scala k ^ ")",
  literal_list = fn [] => str "Nil" | ps => Pretty.block [str "List", enum "," "(" ")" ps],
  infix_cons = (6, "::")
} end;


(** Isar setup **)

val _ = Theory.setup
  (Code_Target.add_language
    (target, { serializer = serializer, literals = literals,
      check = { env_var = "SCALA_HOME",
        make_destination = fn p => p + Path.explode "ROOT.scala",
        make_command = fn _ =>
          "isabelle_scala scalac $ISABELLE_SCALAC_OPTIONS ROOT.scala"},
      evaluation_args = Token.explode0 Keyword.empty_keywords "case_insensitive"})
  #> Code_Target.set_printings (Type_Constructor ("fun",
    [(target, SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy (
        print_typ BR ty1 (*product type vs. tupled arguments!*),
        str "=>",
        print_typ (INFX (1, R)) ty2
      )))]))
  #> fold (Code_Target.add_reserved target) [
      "abstract", "case", "catch", "class", "def", "do", "else", "extends", "false",
      "final", "finally", "for", "forSome", "if", "implicit", "import", "lazy",
      "match", "new", "null", "object", "override", "package", "private", "protected",
      "requires", "return", "sealed", "super", "this", "throw", "trait", "try",
      "true", "type", "val", "var", "while", "with", "yield"
    ]
  #> fold (Code_Target.add_reserved target) [
      "apply", "sys", "scala", "BigInt", "Nil", "List"
    ]);

end; (*struct*)
