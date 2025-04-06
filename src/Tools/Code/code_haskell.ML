(*  Title:      Tools/Code/code_haskell.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for Haskell.
*)

signature CODE_HASKELL =
sig
  val language_params: string
  val target: string
  val print_numeral: string -> int -> string
end;

structure Code_Haskell : CODE_HASKELL =
struct

val target = "Haskell";

val language_extensions =
  ["EmptyDataDecls", "RankNTypes", "ScopedTypeVariables"];

val language_pragma =
  "{-# LANGUAGE " ^ commas language_extensions ^ " #-}";

val language_params =
  implode_space (map (prefix "-X") language_extensions);

open Basic_Code_Symbol;
open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;


(** Haskell serializer **)

val print_haskell_string =
  quote o translate_string (fn c =>
    if Symbol.is_ascii c then GHC.print_codepoint (ord c)
    else error "non-ASCII byte in Haskell string literal");

fun print_haskell_stmt class_syntax tyco_syntax const_syntax
    reserved deresolve deriving_show =
  let
    val deresolve_const = deresolve o Constant;
    val deresolve_tyco = deresolve o Type_Constructor;
    val deresolve_class = deresolve o Type_Class;
    fun class_name class = case class_syntax class
     of NONE => deresolve_class class
      | SOME class => class;
    fun print_typcontext tyvars vs = case maps (fn (v, sort) => map (pair v) sort) vs
     of [] => []
      | constraints => Pretty.enum "," "(" ")" (
          map (fn (v, class) =>
            Pretty.str (class_name class ^ " " ^ lookup_var tyvars v)) constraints)
          @@ Pretty.str " => ";
    fun print_typforall tyvars vs = case map fst vs
     of [] => []
      | vnames => Pretty.str "forall " :: Pretty.breaks
          (map (Pretty.str o lookup_var tyvars) vnames) @ Pretty.str "." @@ Pretty.brk 1;
    fun print_tyco_expr tyvars fxy (tyco, tys) =
      brackify fxy (Pretty.str tyco :: map (print_typ tyvars BR) tys)
    and print_typ tyvars fxy (tyco `%% tys) = (case tyco_syntax tyco
         of NONE => print_tyco_expr tyvars fxy (deresolve_tyco tyco, tys)
          | SOME (_, print) => print (print_typ tyvars) fxy tys)
      | print_typ tyvars fxy (ITyVar v) = (Pretty.str o lookup_var tyvars) v;
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
          Pretty.str "_"
      | print_term tyvars some_thm vars fxy (IVar (SOME v)) =
          (Pretty.str o lookup_var vars) v
      | print_term tyvars some_thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            val (ps, vars') = fold_map (print_bind tyvars some_thm BR o fst) binds vars;
          in brackets (Pretty.str "\\" :: ps @ Pretty.str "->" @@ print_term tyvars some_thm vars' NOBR t') end
      | print_term tyvars some_thm vars fxy (ICase case_expr) =
          (case Code_Thingol.unfold_const_app (#primitive case_expr)
           of SOME (app as ({ sym = Constant const, ... }, _)) =>
                if is_none (const_syntax const)
                then print_case tyvars some_thm vars fxy case_expr
                else print_app tyvars some_thm vars fxy app
            | NONE => print_case tyvars some_thm vars fxy case_expr)
    and print_app_expr tyvars some_thm vars ({ sym, annotation, ... }, ts) =
      let
        val printed_const =
          case annotation of
            SOME ty => brackets [(Pretty.str o deresolve) sym, Pretty.str "::", print_typ tyvars NOBR ty]
          | NONE => (Pretty.str o deresolve) sym
      in 
        printed_const :: map (print_term tyvars some_thm vars BR) ts
      end
    and print_app tyvars = gen_print_app (print_app_expr tyvars) (print_term tyvars) const_syntax
    and print_bind tyvars some_thm fxy p = gen_print_bind (print_term tyvars) some_thm fxy p
    and print_case tyvars some_thm vars fxy { clauses = [], ... } =
          (brackify fxy o Pretty.breaks o map Pretty.str) ["error", "\"empty case\""]
      | print_case tyvars some_thm vars fxy (case_expr as { clauses = [(IVar _, _)], ... }) =
          let
            val (vs, body) = Code_Thingol.unfold_let_no_pat (ICase case_expr);
            fun print_assignment ((some_v, _), t) vars =
              vars
              |> print_bind tyvars some_thm BR (IVar some_v)
              |>> (fn p => semicolon [p, Pretty.str "=", print_term tyvars some_thm vars NOBR t])
            val (ps, vars') = fold_map print_assignment vs vars;
          in brackify_block fxy (Pretty.str "let {")
            ps
            (concat [Pretty.str "}", Pretty.str "in", print_term tyvars some_thm vars' NOBR body])
          end
      | print_case tyvars some_thm vars fxy { term = t, typ = ty, clauses = clauses as _ :: _, ... } =
          let
            fun print_select (pat, body) =
              let
                val (p, vars') = print_bind tyvars some_thm NOBR pat vars;
              in semicolon [p, Pretty.str "->", print_term tyvars some_thm vars' NOBR body] end;
          in Pretty.block_enclose
            (concat [Pretty.str "(case", print_term tyvars some_thm vars NOBR t, Pretty.str "of", Pretty.str "{"], Pretty.str "})")
            (map print_select clauses)
          end;
    fun print_stmt (Constant const, Code_Thingol.Fun (((vs, ty), raw_eqs), _)) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_err n =
              (semicolon o map Pretty.str) (
                deresolve_const const
                :: replicate n "_"
                @ "="
                :: "error"
                @@ print_haskell_string const
              );
            fun print_eqn ((ts, t), (some_thm, _)) =
              let
                val vars = reserved
                  |> intro_base_names_for (is_none o const_syntax)
                      deresolve (t :: ts)
                  |> intro_vars (build (fold Code_Thingol.add_varnames ts));
              in
                semicolon (
                  (Pretty.str o deresolve_const) const
                  :: map (print_term tyvars some_thm vars BR) ts
                  @ Pretty.str "="
                  @@ print_term tyvars some_thm vars NOBR t
                )
              end;
          in
            Pretty.chunks (
              semicolon [
                (Pretty.str o suffix " ::" o deresolve_const) const,
                print_typscheme tyvars (vs, ty)
              ]
              :: (case filter (snd o snd) raw_eqs
               of [] => [print_err ((length o fst o Code_Thingol.unfold_fun) ty)]
                | eqs => map print_eqn eqs)
            )
          end
      | print_stmt (Type_Constructor tyco, Code_Thingol.Datatype (vs, [])) =
          let
            val tyvars = intro_vars vs reserved;
          in
            semicolon [
              Pretty.str "data",
              print_typdecl tyvars (deresolve_tyco tyco, vs)
            ]
          end
      | print_stmt (Type_Constructor tyco, Code_Thingol.Datatype (vs, [((co, _), [ty])])) =
          let
            val tyvars = intro_vars vs reserved;
          in
            semicolon (
              Pretty.str "newtype"
              :: print_typdecl tyvars (deresolve_tyco tyco, vs)
              :: Pretty.str "="
              :: (Pretty.str o deresolve_const) co
              :: print_typ tyvars BR ty
              :: (if deriving_show tyco then [Pretty.str "deriving (Prelude.Read, Prelude.Show)"] else [])
            )
          end
      | print_stmt (Type_Constructor tyco, Code_Thingol.Datatype (vs, co :: cos)) =
          let
            val tyvars = intro_vars vs reserved;
            fun print_co ((co, _), tys) =
              concat (
                (Pretty.str o deresolve_const) co
                :: map (print_typ tyvars BR) tys
              )
          in
            semicolon (
              Pretty.str "data"
              :: print_typdecl tyvars (deresolve_tyco tyco, vs)
              :: Pretty.str "="
              :: print_co co
              :: map ((fn p => Pretty.block [Pretty.str "| ", p]) o print_co) cos
              @ (if deriving_show tyco then [Pretty.str "deriving (Prelude.Read, Prelude.Show)"] else [])
            )
          end
      | print_stmt (Type_Class class, Code_Thingol.Class (v, (classrels, classparams))) =
          let
            val tyvars = intro_vars [v] reserved;
            fun print_classparam (classparam, ty) =
              semicolon [
                (Pretty.str o deresolve_const) classparam,
                Pretty.str "::",
                print_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                Pretty.str "class ",
                Pretty.block (print_typcontext tyvars [(v, map snd classrels)]),
                Pretty.str (deresolve_class class ^ " " ^ lookup_var tyvars v),
                Pretty.str " where {"
              ],
              Pretty.str "};"
            ) (map print_classparam classparams)
          end
      | print_stmt (_, Code_Thingol.Classinst { class, tyco, vs, inst_params, ... }) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_classparam_instance ((classparam, (const, _)), (thm, _)) =
              case const_syntax classparam of
                NONE => semicolon [
                    (Pretty.str o Long_Name.base_name o deresolve_const) classparam,
                    Pretty.str "=",
                    print_app tyvars (SOME thm) reserved NOBR (const, [])
                  ]
              | SOME (_, Code_Printer.Plain_printer s) => semicolon [
                    (Pretty.str o Long_Name.base_name) s,
                    Pretty.str "=",
                    print_app tyvars (SOME thm) reserved NOBR (const, [])
                  ]
              | SOME (wanted, Code_Printer.Complex_printer _) =>
                  let
                    val { sym = Constant c, dom, range, ... } = const;
                    val ((vs_tys, (ts, _)), _) = Code_Thingol.satisfied_application wanted (const, []);
                    val vs = map fst vs_tys;
                    val rhs = IConst const `$$ ts;
                    val s = if (is_some o const_syntax) c
                      then NONE else (SOME o Long_Name.base_name o deresolve_const) c;
                    val vars = reserved
                      |> intro_vars (map_filter I (s :: vs));
                    val lhs = IConst { sym = Constant classparam, typargs = [],
                      dictss = [], dom = dom, range = range, annotation = NONE } `$$ map IVar vs;
                      (*dictionaries are not relevant in Haskell,
                        and these consts never need type annotations for disambiguation *)
                  in
                    semicolon [
                      print_term tyvars (SOME thm) vars NOBR lhs,
                      Pretty.str "=",
                      print_term tyvars (SOME thm) vars NOBR rhs
                    ]
                  end;
          in
            Pretty.block_enclose (
              Pretty.block [
                Pretty.str "instance ",
                Pretty.block (print_typcontext tyvars vs),
                Pretty.str (class_name class ^ " "),
                print_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
                Pretty.str " where {"
              ],
              Pretty.str "};"
            ) (map print_classparam_instance inst_params)
          end;
  in print_stmt end;

fun haskell_program_of_program ctxt module_prefix module_name reserved identifiers =
  let
    fun namify_fun upper base (nsp_fun, nsp_typ) =
      let
        val (base', nsp_fun') = Name.variant (Name.enforce_case upper base) nsp_fun;
      in (base', (nsp_fun', nsp_typ)) end;
    fun namify_typ base (nsp_fun, nsp_typ) =
      let
        val (base', nsp_typ') = Name.variant (Name.enforce_case true base) nsp_typ;
      in (base', (nsp_fun, nsp_typ')) end;
    fun namify_stmt (Code_Thingol.Fun (_, SOME _)) = pair
      | namify_stmt (Code_Thingol.Fun _) = namify_fun false
      | namify_stmt (Code_Thingol.Datatype _) = namify_typ
      | namify_stmt (Code_Thingol.Datatypecons _) = namify_fun true
      | namify_stmt (Code_Thingol.Class _) = namify_typ
      | namify_stmt (Code_Thingol.Classrel _) = pair
      | namify_stmt (Code_Thingol.Classparam _) = namify_fun false
      | namify_stmt (Code_Thingol.Classinst _) = pair;
    fun select_stmt (Code_Thingol.Fun (_, SOME _)) = false
      | select_stmt (Code_Thingol.Fun _) = true
      | select_stmt (Code_Thingol.Datatype _) = true
      | select_stmt (Code_Thingol.Datatypecons _) = false
      | select_stmt (Code_Thingol.Class _) = true
      | select_stmt (Code_Thingol.Classrel _) = false
      | select_stmt (Code_Thingol.Classparam _) = false
      | select_stmt (Code_Thingol.Classinst _) = true;
  in
    Code_Namespace.flat_program ctxt
      { module_prefix = module_prefix, module_name = module_name, reserved = reserved,
        identifiers = identifiers, empty_nsp = (reserved, reserved), namify_stmt = namify_stmt,
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

val data_bits_import_operators = [
  ".&.", ".|.", ".^."
];

fun serialize_haskell module_prefix string_classes ctxt { module_name,
    reserved_syms, identifiers, includes, class_syntax, tyco_syntax, const_syntax } program exports =
  let

    (* build program *)
    val reserved = fold (insert (op =) o fst) includes reserved_syms;
    val { deresolver, flat_program = haskell_program } = haskell_program_of_program
      ctxt module_prefix module_name (Name.make_context reserved) identifiers exports program;

    (* print statements *)
    fun deriving_show tyco =
      let
        fun deriv _ "fun" = false
          | deriv tycos tyco = member (op =) tycos tyco
              orelse case try (Code_Symbol.Graph.get_node program) (Type_Constructor tyco)
                of SOME (Code_Thingol.Datatype (_, cs)) => forall (deriv' (tyco :: tycos))
                    (maps snd cs)
                 | NONE => true
        and deriv' tycos (tyco `%% tys) = deriv tycos tyco
              andalso forall (deriv' tycos) tys
          | deriv' _ (ITyVar _) = true
      in deriv [] tyco end;
    fun print_stmt deresolve = print_haskell_stmt
      class_syntax tyco_syntax const_syntax (make_vars reserved)
      deresolve (if string_classes then deriving_show else K false);

    (* print modules *)
    fun module_names module_name =
      let
        val (xs, x) = split_last (Long_Name.explode module_name)
      in xs @ [x ^ ".hs"] end
    fun print_module_frame module_name header exports ps =
      (module_names module_name, Pretty.chunks2 (
        header
        @ concat [Pretty.str "module",
          case exports of
            SOME ps => Pretty.block [Pretty.str module_name, Pretty.enclose "(" ")" (Pretty.commas ps)]
          | NONE => Pretty.str module_name,
          Pretty.str "where {"
        ]
        :: ps
        @| Pretty.str "}"
      ));
    fun print_qualified_import module_name =
      semicolon [Pretty.str "import qualified", Pretty.str module_name];
    val import_common_ps =
      Pretty.enclose "import Prelude (" ");" (Pretty.commas (map Pretty.str
        (map (enclose "(" ")") prelude_import_operators @ prelude_import_unqualified)
          @ map (fn (tyco, constrs) => (Pretty.enclose (tyco ^ "(") ")" o Pretty.commas o map Pretty.str) constrs) prelude_import_unqualified_constr))
      :: Pretty.enclose "import Data.Bits (" ");" (Pretty.commas
        (map (Pretty.str o enclose "(" ")") data_bits_import_operators))
      :: print_qualified_import "Prelude"
      :: print_qualified_import "Data.Bits"
      :: map (print_qualified_import o fst) includes;
    fun print_module module_name (gr, imports) =
      let
        val deresolve = deresolver module_name;
        val deresolve_import = SOME o Pretty.str o deresolve;
        val deresolve_import_attached = SOME o Pretty.str o suffix "(..)" o deresolve;
        fun print_import (sym, (_, Code_Thingol.Fun _)) = deresolve_import sym
          | print_import (sym, (Code_Namespace.Public, Code_Thingol.Datatype _)) = deresolve_import_attached sym
          | print_import (sym, (Code_Namespace.Opaque, Code_Thingol.Datatype _)) = deresolve_import sym
          | print_import (sym, (Code_Namespace.Public, Code_Thingol.Class _)) = deresolve_import_attached sym
          | print_import (sym, (Code_Namespace.Opaque, Code_Thingol.Class _)) = deresolve_import sym
          | print_import (sym, (_, Code_Thingol.Classinst _)) = NONE;
        val import_ps = import_common_ps @ map (print_qualified_import o fst) imports;
        fun print_stmt' sym = case Code_Symbol.Graph.get_node gr sym
         of (_, NONE) => NONE
          | (_, SOME (export, stmt)) =>
              SOME (if Code_Namespace.not_private export then print_import (sym, (export, stmt)) else NONE, markup_stmt sym (print_stmt deresolve (sym, stmt)));
        val (export_ps, body_ps) = (flat o rev o Code_Symbol.Graph.strong_conn) gr
          |> map_filter print_stmt'
          |> split_list
          |> apfst (map_filter I);
      in
        print_module_frame module_name [Pretty.str language_pragma] (SOME export_ps)
          ((if null import_ps then [] else [Pretty.chunks import_ps]) @ body_ps)
      end;

  in
    (Code_Target.Hierarchy (map (fn (module_name, content) => ([module_name ^ ".hs"], content)) includes
      @ map (fn module_name => print_module module_name (Graph.get_node haskell_program module_name))
        ((flat o rev o Graph.strong_conn) haskell_program)), try (deresolver ""))
  end;

val serializer : Code_Target.serializer =
  Code_Target.parse_args (Scan.optional (Args.$$$ "root" -- Args.colon |-- Args.name) ""
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    >> (fn (module_prefix, string_classes) =>
      serialize_haskell module_prefix string_classes));

fun print_numeral typ = Library.enclose "(" (" :: " ^ typ ^ ")") o signed_string_of_int;

val literals = Literals {
  literal_string = print_haskell_string,
  literal_numeral = print_numeral "Integer",
  literal_list = Pretty.enum "," "[" "]",
  infix_cons = (5, ":")
};


(** optional monad syntax **)

fun pretty_haskell_monad c_bind =
  let
    fun dest_bind t1 t2 = case Code_Thingol.split_pat_abs t2
     of SOME ((pat, ty), t') =>
          SOME ((SOME ((pat, ty), true), t1), t')
      | NONE => NONE;
    fun dest_monad (IConst { sym = Constant c, ... } `$ t1 `$ t2) =
          if c = c_bind then dest_bind t1 t2
          else NONE
      | dest_monad t = case Code_Thingol.split_let_no_pat t
         of SOME (((some_v, ty), tbind), t') =>
              SOME ((SOME ((IVar some_v, ty), false), tbind), t')
          | NONE => NONE;
    val implode_monad = Code_Thingol.unfoldr dest_monad;
    fun print_monad print_bind print_term (NONE, t) vars =
          (semicolon [print_term vars NOBR t], vars)
      | print_monad print_bind print_term (SOME ((bind, _), true), t) vars = vars
          |> print_bind NOBR bind
          |>> (fn p => semicolon [p, Pretty.str "<-", print_term vars NOBR t])
      | print_monad print_bind print_term (SOME ((bind, _), false), t) vars = vars
          |> print_bind NOBR bind
          |>> (fn p => semicolon [Pretty.str "let", Pretty.str "{", p, Pretty.str "=", print_term vars NOBR t, Pretty.str "}"]);
    fun pretty _ print_term thm vars fxy [(t1, _), (t2, _)] = case dest_bind t1 t2
     of SOME (bind, t') => let
          val (binds, t'') = implode_monad t'
          val (ps, vars') = fold_map (print_monad (gen_print_bind (K print_term) thm) print_term)
            (bind :: binds) vars;
        in
          brackify_block fxy (Pretty.str "do { ")
            (ps @| print_term vars' NOBR t'')
            (Pretty.str " }")
        end
      | NONE => brackify_infix (1, L) fxy
          (print_term vars (INFX (1, L)) t1, Pretty.str ">>=", print_term vars (INFX (1, X)) t2)
  in (2, pretty) end;

fun add_monad target' raw_c_bind thy =
  let
    val c_bind = Code.read_const thy raw_c_bind;
  in
    if target = target' then
      thy
      |> Code_Target.set_printings (Constant (c_bind, [(target,
        SOME (Code_Printer.complex_const_syntax (pretty_haskell_monad c_bind)))]))
    else error "Only Haskell target allows for monad syntax"
  end;


(** Isar setup **)

val _ = Theory.setup
  (Code_Target.add_language
    (target, {serializer = serializer, literals = literals,
      check = { env_var = "ISABELLE_GHC", make_destination = I,
        make_command = fn module_name =>
          "\"$ISABELLE_GHC\" " ^ language_params  ^ " -odir build -hidir build -stubdir build -e \"\" " ^
            module_name ^ ".hs"},
      evaluation_args = []})
  #> Code_Target.set_printings (Type_Constructor ("fun",
    [(target, SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy (
        print_typ (INFX (1, X)) ty1,
        Pretty.str "->",
        print_typ (INFX (1, R)) ty2
      )))]))
  #> fold (Code_Target.add_reserved target) [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ]
  #> fold (Code_Target.add_reserved target) prelude_import_unqualified
  #> fold (Code_Target.add_reserved target o fst) prelude_import_unqualified_constr
  #> fold (fold (Code_Target.add_reserved target) o snd) prelude_import_unqualified_constr);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_monad\<close> "define code syntax for monads"
    (Parse.term -- Parse.name >> (fn (raw_bind, target) =>
      Toplevel.theory (add_monad target raw_bind)));

end; (*struct*)
