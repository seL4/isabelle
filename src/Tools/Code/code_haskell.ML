(*  Title:      Tools/Code/code_haskell.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for Haskell.
*)

signature CODE_HASKELL =
sig
  val language_params: string
  val target: string
  val setup: theory -> theory
end;

structure Code_Haskell : CODE_HASKELL =
struct

val target = "Haskell";

val language_extensions =
  ["EmptyDataDecls", "RankNTypes", "ScopedTypeVariables"];

val language_pragma =
  "{-# LANGUAGE " ^ commas language_extensions ^ " #-}";

val language_params =
  space_implode " " (map (prefix "-X") language_extensions);

open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;


(** Haskell serializer **)

fun print_haskell_stmt class_syntax tyco_syntax const_syntax
    reserved deresolve deriving_show =
  let
    fun class_name class = case class_syntax class
     of NONE => deresolve class
      | SOME class => class;
    fun print_typcontext tyvars vs = case maps (fn (v, sort) => map (pair v) sort) vs
     of [] => []
      | constraints => enum "," "(" ")" (
          map (fn (v, class) =>
            str (class_name class ^ " " ^ lookup_var tyvars v)) constraints)
          @@ str " => ";
    fun print_typforall tyvars vs = case map fst vs
     of [] => []
      | vnames => str "forall " :: Pretty.breaks
          (map (str o lookup_var tyvars) vnames) @ str "." @@ Pretty.brk 1;
    fun print_tyco_expr tyvars fxy (tyco, tys) =
      brackify fxy (str tyco :: map (print_typ tyvars BR) tys)
    and print_typ tyvars fxy (tyco `%% tys) = (case tyco_syntax tyco
         of NONE => print_tyco_expr tyvars fxy (deresolve tyco, tys)
          | SOME (_, print) => print (print_typ tyvars) fxy tys)
      | print_typ tyvars fxy (ITyVar v) = (str o lookup_var tyvars) v;
    fun print_typdecl tyvars (tyco, vs) =
      print_tyco_expr tyvars NOBR (tyco, map ITyVar vs);
    fun print_typscheme tyvars (vs, ty) =
      Pretty.block (print_typforall tyvars vs @ print_typcontext tyvars vs @| print_typ tyvars NOBR ty);
    fun print_term tyvars some_thm vars fxy (IConst const) =
          print_app tyvars some_thm vars fxy (const, [])
      | print_term tyvars some_thm vars fxy (t as (t1 `$ t2)) =
          (case Code_Thingol.unfold_const_app t
           of SOME app => print_app tyvars some_thm vars fxy app
            | _ =>
                brackify fxy [
                  print_term tyvars some_thm vars NOBR t1,
                  print_term tyvars some_thm vars BR t2
                ])
      | print_term tyvars some_thm vars fxy (IVar NONE) =
          str "_"
      | print_term tyvars some_thm vars fxy (IVar (SOME v)) =
          (str o lookup_var vars) v
      | print_term tyvars some_thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            val (ps, vars') = fold_map (print_bind tyvars some_thm BR o fst) binds vars;
          in brackets (str "\\" :: ps @ str "->" @@ print_term tyvars some_thm vars' NOBR t') end
      | print_term tyvars some_thm vars fxy (ICase case_expr) =
          (case Code_Thingol.unfold_const_app (#primitive case_expr)
           of SOME (app as ({ name = c, ... }, _)) => if is_none (const_syntax c)
                then print_case tyvars some_thm vars fxy case_expr
                else print_app tyvars some_thm vars fxy app
            | NONE => print_case tyvars some_thm vars fxy case_expr)
    and print_app_expr tyvars some_thm vars ({ name = c, dom, range, annotate, ... }, ts) =
      let
        val ty = Library.foldr (fn (ty1, ty2) => Code_Thingol.fun_tyco `%% [ty1, ty2]) (dom, range)
        val printed_const =
          if annotate then
            brackets [(str o deresolve) c, str "::", print_typ tyvars NOBR ty]
          else
            (str o deresolve) c
      in 
        printed_const :: map (print_term tyvars some_thm vars BR) ts
      end
    and print_app tyvars = gen_print_app (print_app_expr tyvars) (print_term tyvars) const_syntax
    and print_bind tyvars some_thm fxy p = gen_print_bind (print_term tyvars) some_thm fxy p
    and print_case tyvars some_thm vars fxy { clauses = [], ... } =
          (brackify fxy o Pretty.breaks o map str) ["error", "\"empty case\""]
      | print_case tyvars some_thm vars fxy (case_expr as { clauses = [_], ... }) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase case_expr);
            fun print_match ((pat, _), t) vars =
              vars
              |> print_bind tyvars some_thm BR pat
              |>> (fn p => semicolon [p, str "=", print_term tyvars some_thm vars NOBR t])
            val (ps, vars') = fold_map print_match binds vars;
          in brackify_block fxy (str "let {")
            ps
            (concat [str "}", str "in", print_term tyvars some_thm vars' NOBR body])
          end
      | print_case tyvars some_thm vars fxy { term = t, typ = ty, clauses = clauses as _ :: _, ... } =
          let
            fun print_select (pat, body) =
              let
                val (p, vars') = print_bind tyvars some_thm NOBR pat vars;
              in semicolon [p, str "->", print_term tyvars some_thm vars' NOBR body] end;
          in Pretty.block_enclose
            (concat [str "(case", print_term tyvars some_thm vars NOBR t, str "of", str "{"], str "})")
            (map print_select clauses)
          end;
    fun print_stmt (name, Code_Thingol.Fun (_, (((vs, ty), raw_eqs), _))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_err n =
              semicolon (
                (str o deresolve) name
                :: map str (replicate n "_")
                @ str "="
                :: str "error"
                @@ (str o ML_Syntax.print_string
                    o Long_Name.base_name o Long_Name.qualifier) name
              );
            fun print_eqn ((ts, t), (some_thm, _)) =
              let
                val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                val vars = reserved
                  |> intro_base_names
                      (is_none o const_syntax) deresolve consts
                  |> intro_vars ((fold o Code_Thingol.fold_varnames)
                      (insert (op =)) ts []);
              in
                semicolon (
                  (str o deresolve) name
                  :: map (print_term tyvars some_thm vars BR) ts
                  @ str "="
                  @@ print_term tyvars some_thm vars NOBR t
                )
              end;
          in
            Pretty.chunks (
              semicolon [
                (str o suffix " ::" o deresolve) name,
                print_typscheme tyvars (vs, ty)
              ]
              :: (case filter (snd o snd) raw_eqs
               of [] => [print_err ((length o fst o Code_Thingol.unfold_fun) ty)]
                | eqs => map print_eqn eqs)
            )
          end
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, []))) =
          let
            val tyvars = intro_vars vs reserved;
          in
            semicolon [
              str "data",
              print_typdecl tyvars (deresolve name, vs)
            ]
          end
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, [((co, _), [ty])]))) =
          let
            val tyvars = intro_vars vs reserved;
          in
            semicolon (
              str "newtype"
              :: print_typdecl tyvars (deresolve name, vs)
              :: str "="
              :: (str o deresolve) co
              :: print_typ tyvars BR ty
              :: (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, co :: cos))) =
          let
            val tyvars = intro_vars vs reserved;
            fun print_co ((co, _), tys) =
              concat (
                (str o deresolve) co
                :: map (print_typ tyvars BR) tys
              )
          in
            semicolon (
              str "data"
              :: print_typdecl tyvars (deresolve name, vs)
              :: str "="
              :: print_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o print_co) cos
              @ (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | print_stmt (name, Code_Thingol.Class (_, (v, (super_classes, classparams)))) =
          let
            val tyvars = intro_vars [v] reserved;
            fun print_classparam (classparam, ty) =
              semicolon [
                (str o deresolve) classparam,
                str "::",
                print_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                str "class ",
                Pretty.block (print_typcontext tyvars [(v, map fst super_classes)]),
                str (deresolve name ^ " " ^ lookup_var tyvars v),
                str " where {"
              ],
              str "};"
            ) (map print_classparam classparams)
          end
      | print_stmt (_, Code_Thingol.Classinst { class, tyco, vs, inst_params, ... }) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun requires_args classparam = case const_syntax classparam
             of NONE => NONE
              | SOME (Code_Printer.Plain_const_syntax _) => SOME 0
              | SOME (Code_Printer.Complex_const_syntax (k,_ )) => SOME k;
            fun print_classparam_instance ((classparam, const), (thm, _)) =
              case requires_args classparam
               of NONE => semicolon [
                      (str o Long_Name.base_name o deresolve) classparam,
                      str "=",
                      print_app tyvars (SOME thm) reserved NOBR (const, [])
                    ]
                | SOME k =>
                    let
                      val { name = c, dom, range, ... } = const;
                      val (vs, rhs) = (apfst o map) fst
                        (Code_Thingol.unfold_abs (Code_Thingol.eta_expand k (const, [])));
                      val s = if (is_some o const_syntax) c
                        then NONE else (SOME o Long_Name.base_name o deresolve) c;
                      val vars = reserved
                        |> intro_vars (map_filter I (s :: vs));
                      val lhs = IConst { name = classparam, typargs = [],
                        dicts = [], dom = dom, range = range, annotate = false } `$$ map IVar vs;
                        (*dictionaries are not relevant at this late stage,
                          and these consts never need type annotations for disambiguation *)
                    in
                      semicolon [
                        print_term tyvars (SOME thm) vars NOBR lhs,
                        str "=",
                        print_term tyvars (SOME thm) vars NOBR rhs
                      ]
                    end;
          in
            Pretty.block_enclose (
              Pretty.block [
                str "instance ",
                Pretty.block (print_typcontext tyvars vs),
                str (class_name class ^ " "),
                print_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
                str " where {"
              ],
              str "};"
            ) (map print_classparam_instance inst_params)
          end;
  in print_stmt end;

fun haskell_program_of_program labelled_name module_alias module_prefix reserved =
  let
    fun namify_fun upper base (nsp_fun, nsp_typ) =
      let
        val (base', nsp_fun') =
          Name.variant (if upper then first_upper base else base) nsp_fun;
      in (base', (nsp_fun', nsp_typ)) end;
    fun namify_typ base (nsp_fun, nsp_typ) =
      let
        val (base', nsp_typ') = Name.variant (first_upper base) nsp_typ;
      in (base', (nsp_fun, nsp_typ')) end;
    fun namify_stmt (Code_Thingol.Fun (_, (_, SOME _))) = pair
      | namify_stmt (Code_Thingol.Fun _) = namify_fun false
      | namify_stmt (Code_Thingol.Datatype _) = namify_typ
      | namify_stmt (Code_Thingol.Datatypecons _) = namify_fun true
      | namify_stmt (Code_Thingol.Class _) = namify_typ
      | namify_stmt (Code_Thingol.Classrel _) = pair
      | namify_stmt (Code_Thingol.Classparam _) = namify_fun false
      | namify_stmt (Code_Thingol.Classinst _) = pair;
    fun select_stmt (Code_Thingol.Fun (_, (_, SOME _))) = false
      | select_stmt (Code_Thingol.Fun _) = true
      | select_stmt (Code_Thingol.Datatype _) = true
      | select_stmt (Code_Thingol.Datatypecons _) = false
      | select_stmt (Code_Thingol.Class _) = true
      | select_stmt (Code_Thingol.Classrel _) = false
      | select_stmt (Code_Thingol.Classparam _) = false
      | select_stmt (Code_Thingol.Classinst _) = true;
  in
    Code_Namespace.flat_program labelled_name
      { module_alias = module_alias, module_prefix = module_prefix,
        reserved = reserved, empty_nsp = (reserved, reserved), namify_stmt = namify_stmt,
        modify_stmt = fn stmt => if select_stmt stmt then SOME stmt else NONE }
  end;

val prelude_import_operators = [
  "==", "/=", "<", "<=", ">=", ">", "+", "-", "*", "/", "**", ">>=", ">>", "=<<", "&&", "||", "^", "^^", ".", "$", "$!", "++", "!!"
];

val prelude_import_unqualified = [
  "Eq",
  "error",
  "id",
  "return",
  "not",
  "fst", "snd",
  "map", "filter", "concat", "concatMap", "reverse", "zip", "null", "takeWhile", "dropWhile", "all", "any",
  "Integer", "negate", "abs", "divMod",
  "String"
];

val prelude_import_unqualified_constr = [
  ("Bool", ["True", "False"]),
  ("Maybe", ["Nothing", "Just"])
];

fun serialize_haskell module_prefix string_classes { labelled_name, reserved_syms,
    includes, module_alias, class_syntax, tyco_syntax, const_syntax } program =
  let

    (* build program *)
    val reserved = fold (insert (op =) o fst) includes reserved_syms;
    val { deresolver, flat_program = haskell_program } = haskell_program_of_program
      labelled_name module_alias module_prefix (Name.make_context reserved) program;

    (* print statements *)
    fun deriving_show tyco =
      let
        fun deriv _ "fun" = false
          | deriv tycos tyco = not (tyco = Code_Thingol.fun_tyco)
              andalso (member (op =) tycos tyco
              orelse case try (Graph.get_node program) tyco
                of SOME (Code_Thingol.Datatype (_, (_, cs))) => forall (deriv' (tyco :: tycos))
                    (maps snd cs)
                 | NONE => true)
        and deriv' tycos (tyco `%% tys) = deriv tycos tyco
              andalso forall (deriv' tycos) tys
          | deriv' _ (ITyVar _) = true
      in deriv [] tyco end;
    fun print_stmt deresolve = print_haskell_stmt
      class_syntax tyco_syntax const_syntax (make_vars reserved)
      deresolve (if string_classes then deriving_show else K false);

    (* print modules *)
    fun print_module_frame module_name ps =
      (module_name, Pretty.chunks2 (
        str ("module " ^ module_name ^ " where {")
        :: ps
        @| str "}"
      ));
    fun print_qualified_import module_name = semicolon [str "import qualified", str module_name];
    val import_common_ps =
      enclose "import Prelude (" ");" (commas (map str
        (map (Library.enclose "(" ")") prelude_import_operators @ prelude_import_unqualified)
          @ map (fn (tyco, constrs) => (enclose (tyco ^ "(") ")" o commas o map str) constrs) prelude_import_unqualified_constr))
      :: print_qualified_import "Prelude"
      :: map (print_qualified_import o fst) includes;
    fun print_module module_name (gr, imports) =
      let
        val deresolve = deresolver module_name;
        fun print_import module_name = (semicolon o map str) ["import qualified", module_name];
        val import_ps = import_common_ps @ map (print_qualified_import o fst) imports;
        fun print_stmt' name = case Graph.get_node gr name
         of (_, NONE) => NONE
          | (_, SOME stmt) => SOME (markup_stmt name (print_stmt deresolve (name, stmt)));
        val body_ps = map_filter print_stmt' ((flat o rev o Graph.strong_conn) gr);
      in
        print_module_frame module_name
          ((if null import_ps then [] else [Pretty.chunks import_ps]) @ body_ps)
      end;

    (*serialization*)
    fun write_module width (SOME destination) (module_name, content) =
          let
            val _ = File.check_dir destination;
            val filepath = (Path.append destination o Path.ext "hs" o Path.explode o implode
              o separate "/" o Long_Name.explode) module_name;
            val _ = Isabelle_System.mkdirs (Path.dir filepath);
          in
            (File.write filepath o format [] width o Pretty.chunks2)
              [str language_pragma, content]
          end
      | write_module width NONE (_, content) = writeln (format [] width content);
  in
    Code_Target.serialization
      (fn width => fn destination => K () o map (write_module width destination))
      (fn present => fn width => rpair (try (deresolver ""))
        o (map o apsnd) (format present width))
      (map (uncurry print_module_frame o apsnd single) includes
        @ map (fn module_name => print_module module_name (Graph.get_node haskell_program module_name))
          ((flat o rev o Graph.strong_conn) haskell_program))
  end;

val serializer : Code_Target.serializer =
  Code_Target.parse_args (Scan.optional (Args.$$$ "root" -- Args.colon |-- Args.name) ""
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    >> (fn (module_prefix, string_classes) =>
      serialize_haskell module_prefix string_classes));

val literals = let
  fun char_haskell c =
    let
      val s = ML_Syntax.print_char c;
    in if s = "'" then "\\'" else s end;
  fun numeral_haskell k = if k >= 0 then string_of_int k
    else Library.enclose "(" ")" (signed_string_of_int k);
in Literals {
  literal_char = Library.enclose "'" "'" o char_haskell,
  literal_string = quote o translate_string char_haskell,
  literal_numeral = numeral_haskell,
  literal_positive_numeral = numeral_haskell,
  literal_alternative_numeral = numeral_haskell,
  literal_naive_numeral = numeral_haskell,
  literal_list = enum "," "[" "]",
  infix_cons = (5, ":")
} end;


(** optional monad syntax **)

fun pretty_haskell_monad c_bind =
  let
    fun dest_bind t1 t2 = case Code_Thingol.split_pat_abs t2
     of SOME ((pat, ty), t') =>
          SOME ((SOME ((pat, ty), true), t1), t')
      | NONE => NONE;
    fun dest_monad c_bind_name (IConst { name = c, ... } `$ t1 `$ t2) =
          if c = c_bind_name then dest_bind t1 t2
          else NONE
      | dest_monad _ t = case Code_Thingol.split_let t
         of SOME (((pat, ty), tbind), t') =>
              SOME ((SOME ((pat, ty), false), tbind), t')
          | NONE => NONE;
    fun implode_monad c_bind_name = Code_Thingol.unfoldr (dest_monad c_bind_name);
    fun print_monad print_bind print_term (NONE, t) vars =
          (semicolon [print_term vars NOBR t], vars)
      | print_monad print_bind print_term (SOME ((bind, _), true), t) vars = vars
          |> print_bind NOBR bind
          |>> (fn p => semicolon [p, str "<-", print_term vars NOBR t])
      | print_monad print_bind print_term (SOME ((bind, _), false), t) vars = vars
          |> print_bind NOBR bind
          |>> (fn p => semicolon [str "let", str "{", p, str "=", print_term vars NOBR t, str "}"]);
    fun pretty _ [c_bind'] print_term thm vars fxy [(t1, _), (t2, _)] = case dest_bind t1 t2
     of SOME (bind, t') => let
          val (binds, t'') = implode_monad c_bind' t'
          val (ps, vars') = fold_map (print_monad (gen_print_bind (K print_term) thm) print_term)
            (bind :: binds) vars;
        in
          (brackify fxy o single o enclose "do { " " }" o Pretty.breaks)
            (ps @| print_term vars' NOBR t'')
        end
      | NONE => brackify_infix (1, L) fxy
          (print_term vars (INFX (1, L)) t1, str ">>=", print_term vars (INFX (1, X)) t2)
  in (2, ([c_bind], pretty)) end;

fun add_monad target' raw_c_bind thy =
  let
    val c_bind = Code.read_const thy raw_c_bind;
  in if target = target' then
    thy
    |> Code_Target.add_const_syntax target c_bind
        (SOME (Code_Printer.complex_const_syntax (pretty_haskell_monad c_bind)))
  else error "Only Haskell target allows for monad syntax" end;


(** Isar setup **)

val _ =
  Outer_Syntax.command @{command_spec "code_monad"} "define code syntax for monads"
    (Parse.term_group -- Parse.name >> (fn (raw_bind, target) =>
      Toplevel.theory  (add_monad target raw_bind)));

val setup =
  Code_Target.add_target
    (target, { serializer = serializer, literals = literals,
      check = { env_var = "ISABELLE_GHC", make_destination = I,
        make_command = fn module_name =>
          "\"$ISABELLE_GHC\" " ^ language_params  ^ " -odir build -hidir build -stubdir build -e \"\" " ^
            module_name ^ ".hs" } })
  #> Code_Target.add_tyco_syntax target "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy (
        print_typ (INFX (1, X)) ty1,
        str "->",
        print_typ (INFX (1, R)) ty2
      )))
  #> fold (Code_Target.add_reserved target) [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ]
  #> fold (Code_Target.add_reserved target) prelude_import_unqualified
  #> fold (Code_Target.add_reserved target o fst) prelude_import_unqualified_constr
  #> fold (fold (Code_Target.add_reserved target) o snd) prelude_import_unqualified_constr;

end; (*struct*)
