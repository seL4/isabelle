(*  Title:      Tools/code/code_haskell.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for Haskell.
*)

signature CODE_HASKELL =
sig
  val setup: theory -> theory
end;

structure Code_Haskell : CODE_HASKELL =
struct

val target = "Haskell";

open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;


(** Haskell serializer **)

fun print_haskell_stmt labelled_name syntax_class syntax_tyco syntax_const
    reserved deresolve contr_classparam_typs deriving_show =
  let
    val deresolve_base = Long_Name.base_name o deresolve;
    fun class_name class = case syntax_class class
     of NONE => deresolve class
      | SOME class => class;
    fun print_typcontext tyvars vs = case maps (fn (v, sort) => map (pair v) sort) vs
     of [] => []
      | classbinds => enum "," "(" ")" (
          map (fn (v, class) =>
            str (class_name class ^ " " ^ lookup_var tyvars v)) classbinds)
          @@ str " => ";
    fun print_typforall tyvars vs = case map fst vs
     of [] => []
      | vnames => str "forall " :: Pretty.breaks
          (map (str o lookup_var tyvars) vnames) @ str "." @@ Pretty.brk 1;
    fun print_tyco_expr tyvars fxy (tyco, tys) =
      brackify fxy (str tyco :: map (print_typ tyvars BR) tys)
    and print_typ tyvars fxy (tycoexpr as tyco `%% tys) = (case syntax_tyco tyco
         of NONE => print_tyco_expr tyvars fxy (deresolve tyco, tys)
          | SOME (i, print) => print (print_typ tyvars) fxy tys)
      | print_typ tyvars fxy (ITyVar v) = (str o lookup_var tyvars) v;
    fun print_typdecl tyvars (vs, tycoexpr) =
      Pretty.block (print_typcontext tyvars vs @| print_tyco_expr tyvars NOBR tycoexpr);
    fun print_typscheme tyvars (vs, ty) =
      Pretty.block (print_typforall tyvars vs @ print_typcontext tyvars vs @| print_typ tyvars NOBR ty);
    fun print_term tyvars thm vars fxy (IConst c) =
          print_app tyvars thm vars fxy (c, [])
      | print_term tyvars thm vars fxy (t as (t1 `$ t2)) =
          (case Code_Thingol.unfold_const_app t
           of SOME app => print_app tyvars thm vars fxy app
            | _ =>
                brackify fxy [
                  print_term tyvars thm vars NOBR t1,
                  print_term tyvars thm vars BR t2
                ])
      | print_term tyvars thm vars fxy (IVar NONE) =
          str "_"
      | print_term tyvars thm vars fxy (IVar (SOME v)) =
          (str o lookup_var vars) v
      | print_term tyvars thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            val (ps, vars') = fold_map (print_bind tyvars thm BR o fst) binds vars;
          in brackets (str "\\" :: ps @ str "->" @@ print_term tyvars thm vars' NOBR t') end
      | print_term tyvars thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then print_case tyvars thm vars fxy cases
                else print_app tyvars thm vars fxy c_ts
            | NONE => print_case tyvars thm vars fxy cases)
    and print_app_expr tyvars thm vars ((c, (_, tys)), ts) = case contr_classparam_typs c
     of [] => (str o deresolve) c :: map (print_term tyvars thm vars BR) ts
      | fingerprint => let
          val ts_fingerprint = ts ~~ take (length ts) fingerprint;
          val needs_annotation = forall (fn (_, NONE) => true | (t, SOME _) =>
            (not o Code_Thingol.locally_monomorphic) t) ts_fingerprint;
          fun print_term_anno (t, NONE) _ = print_term tyvars thm vars BR t
            | print_term_anno (t, SOME _) ty =
                brackets [print_term tyvars thm vars NOBR t, str "::", print_typ tyvars NOBR ty];
        in
          if needs_annotation then
            (str o deresolve) c :: map2 print_term_anno ts_fingerprint (take (length ts) tys)
          else (str o deresolve) c :: map (print_term tyvars thm vars BR) ts
        end
    and print_app tyvars = gen_print_app (print_app_expr tyvars) (print_term tyvars) syntax_const
    and print_bind tyvars thm fxy p = gen_print_bind (print_term tyvars) thm fxy p
    and print_case tyvars thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_match ((pat, ty), t) vars =
              vars
              |> print_bind tyvars thm BR pat
              |>> (fn p => semicolon [p, str "=", print_term tyvars thm vars NOBR t])
            val (ps, vars') = fold_map print_match binds vars;
          in brackify_block fxy (str "let {")
            ps
            (concat [str "}", str "in", print_term tyvars thm vars' NOBR body])
          end
      | print_case tyvars thm vars fxy (((t, ty), clauses as _ :: _), _) =
          let
            fun print_select (pat, body) =
              let
                val (p, vars') = print_bind tyvars thm NOBR pat vars;
              in semicolon [p, str "->", print_term tyvars thm vars' NOBR body] end;
          in brackify_block fxy
            (concat [str "case", print_term tyvars thm vars NOBR t, str "of", str "{"])
            (map print_select clauses)
            (str "}") 
          end
      | print_case tyvars thm vars fxy ((_, []), _) =
          (brackify fxy o Pretty.breaks o map str) ["error", "\"empty case\""];
    fun print_stmt (name, Code_Thingol.Fun (_, ((vs, ty), []))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            val n = (length o fst o Code_Thingol.unfold_fun) ty;
          in
            Pretty.chunks [
              semicolon [
                (str o suffix " ::" o deresolve_base) name,
                print_typscheme tyvars (vs, ty)
              ],
              semicolon (
                (str o deresolve_base) name
                :: map str (replicate n "_")
                @ str "="
                :: str "error"
                @@ (str o ML_Syntax.print_string
                    o Long_Name.base_name o Long_Name.qualifier) name
              )
            ]
          end
      | print_stmt (name, Code_Thingol.Fun (_, ((vs, ty), raw_eqs))) =
          let
            val eqs = filter (snd o snd) raw_eqs;
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_eqn ((ts, t), (thm, _)) =
              let
                val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                val vars = reserved
                  |> intro_base_names
                      (is_none o syntax_const) deresolve consts
                  |> intro_vars ((fold o Code_Thingol.fold_varnames)
                      (insert (op =)) ts []);
              in
                semicolon (
                  (str o deresolve_base) name
                  :: map (print_term tyvars thm vars BR) ts
                  @ str "="
                  @@ print_term tyvars thm vars NOBR t
                )
              end;
          in
            Pretty.chunks (
              semicolon [
                (str o suffix " ::" o deresolve_base) name,
                print_typscheme tyvars (vs, ty)
              ]
              :: map print_eqn eqs
            )
          end
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, []))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
          in
            semicolon [
              str "data",
              print_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
            ]
          end
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, [(co, [ty])]))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
          in
            semicolon (
              str "newtype"
              :: print_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
              :: str "="
              :: (str o deresolve_base) co
              :: print_typ tyvars BR ty
              :: (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | print_stmt (name, Code_Thingol.Datatype (_, (vs, co :: cos))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_co (co, tys) =
              concat (
                (str o deresolve_base) co
                :: map (print_typ tyvars BR) tys
              )
          in
            semicolon (
              str "data"
              :: print_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
              :: str "="
              :: print_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o print_co) cos
              @ (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | print_stmt (name, Code_Thingol.Class (_, (v, (superclasses, classparams)))) =
          let
            val tyvars = intro_vars [v] reserved;
            fun print_classparam (classparam, ty) =
              semicolon [
                (str o deresolve_base) classparam,
                str "::",
                print_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                str "class ",
                Pretty.block (print_typcontext tyvars [(v, map fst superclasses)]),
                str (deresolve_base name ^ " " ^ lookup_var tyvars v),
                str " where {"
              ],
              str "};"
            ) (map print_classparam classparams)
          end
      | print_stmt (_, Code_Thingol.Classinst ((class, (tyco, vs)), (_, classparam_insts))) =
          let
            val tyvars = intro_vars (map fst vs) reserved;
            fun print_instdef ((classparam, c_inst), (thm, _)) = case syntax_const classparam
             of NONE => semicolon [
                    (str o deresolve_base) classparam,
                    str "=",
                    print_app tyvars thm reserved NOBR (c_inst, [])
                  ]
              | SOME (k, pr) =>
                  let
                    val (c_inst_name, (_, tys)) = c_inst;
                    val const = if (is_some o syntax_const) c_inst_name
                      then NONE else (SOME o Long_Name.base_name o deresolve) c_inst_name;
                    val proto_rhs = Code_Thingol.eta_expand k (c_inst, []);
                    val (vs, rhs) = (apfst o map) fst (Code_Thingol.unfold_abs proto_rhs);
                    val vars = reserved
                      |> intro_vars (the_list const)
                      |> intro_vars (map_filter I vs);
                    val lhs = IConst (classparam, (([], []), tys)) `$$ map IVar vs;
                      (*dictionaries are not relevant at this late stage*)
                  in
                    semicolon [
                      print_term tyvars thm vars NOBR lhs,
                      str "=",
                      print_term tyvars thm vars NOBR rhs
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
            ) (map print_instdef classparam_insts)
          end;
  in print_stmt end;

fun haskell_program_of_program labelled_name module_name module_prefix reserved raw_module_alias program =
  let
    val module_alias = if is_some module_name then K module_name else raw_module_alias;
    val reserved = Name.make_context reserved;
    val mk_name_module = mk_name_module reserved module_prefix module_alias program;
    fun add_stmt (name, (stmt, deps)) =
      let
        val (module_name, base) = dest_name name;
        val module_name' = mk_name_module module_name;
        val mk_name_stmt = yield_singleton Name.variants;
        fun add_fun upper (nsp_fun, nsp_typ) =
          let
            val (base', nsp_fun') =
              mk_name_stmt (if upper then first_upper base else base) nsp_fun
          in (base', (nsp_fun', nsp_typ)) end;
        fun add_typ (nsp_fun, nsp_typ) =
          let
            val (base', nsp_typ') = mk_name_stmt (first_upper base) nsp_typ
          in (base', (nsp_fun, nsp_typ')) end;
        val add_name = case stmt
         of Code_Thingol.Fun _ => add_fun false
          | Code_Thingol.Datatype _ => add_typ
          | Code_Thingol.Datatypecons _ => add_fun true
          | Code_Thingol.Class _ => add_typ
          | Code_Thingol.Classrel _ => pair base
          | Code_Thingol.Classparam _ => add_fun false
          | Code_Thingol.Classinst _ => pair base;
        fun add_stmt' base' = case stmt
         of Code_Thingol.Datatypecons _ =>
              cons (name, (Long_Name.append module_name' base', NONE))
          | Code_Thingol.Classrel _ => I
          | Code_Thingol.Classparam _ =>
              cons (name, (Long_Name.append module_name' base', NONE))
          | _ => cons (name, (Long_Name.append module_name' base', SOME stmt));
      in
        Symtab.map_default (module_name', ([], ([], (reserved, reserved))))
              (apfst (fold (insert (op = : string * string -> bool)) deps))
        #> `(fn program => add_name ((snd o snd o the o Symtab.lookup program) module_name'))
        #-> (fn (base', names) =>
              (Symtab.map_entry module_name' o apsnd) (fn (stmts, _) =>
              (add_stmt' base' stmts, names)))
      end;
    val hs_program = fold add_stmt (AList.make (fn name =>
      (Graph.get_node program name, Graph.imm_succs program name))
      (Graph.strong_conn program |> flat)) Symtab.empty;
    fun deresolver name = (fst o the o AList.lookup (op =) ((fst o snd o the
      o Symtab.lookup hs_program) ((mk_name_module o fst o dest_name) name))) name
      handle Option => error ("Unknown statement name: " ^ labelled_name name);
  in (deresolver, hs_program) end;

fun serialize_haskell module_prefix raw_module_name string_classes labelled_name
    raw_reserved includes raw_module_alias
    syntax_class syntax_tyco syntax_const (code_of_pretty, code_writeln) program cs destination =
  let
    val stmt_names = Code_Target.stmt_names_of_destination destination;
    val module_name = if null stmt_names then raw_module_name else SOME "Code";
    val reserved = fold (insert (op =) o fst) includes raw_reserved;
    val (deresolver, hs_program) = haskell_program_of_program labelled_name
      module_name module_prefix reserved raw_module_alias program;
    val contr_classparam_typs = Code_Thingol.contr_classparam_typs program;
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
    val reserved = make_vars reserved;
    fun print_stmt qualified = print_haskell_stmt labelled_name
      syntax_class syntax_tyco syntax_const reserved
      (if qualified then deresolver else Long_Name.base_name o deresolver)
      contr_classparam_typs
      (if string_classes then deriving_show else K false);
    fun print_module name content =
      (name, Pretty.chunks [
        str ("module " ^ name ^ " where {"),
        str "",
        content,
        str "",
        str "}"
      ]);
    fun serialize_module1 (module_name', (deps, (stmts, _))) =
      let
        val stmt_names = map fst stmts;
        val qualified = is_none module_name;
        val imports = subtract (op =) stmt_names deps
          |> distinct (op =)
          |> map_filter (try deresolver)
          |> map Long_Name.qualifier
          |> distinct (op =);
        fun print_import_include (name, _) = str ("import qualified " ^ name ^ ";");
        fun print_import_module name = str ((if qualified
          then "import qualified "
          else "import ") ^ name ^ ";");
        val import_ps = map print_import_include includes @ map print_import_module imports
        val content = Pretty.chunks2 ((if null import_ps then [] else [Pretty.chunks import_ps])
            @ map_filter
              (fn (name, (_, SOME stmt)) => SOME (print_stmt qualified (name, stmt))
                | (_, (_, NONE)) => NONE) stmts
          );
      in print_module module_name' content end;
    fun serialize_module2 (_, (_, (stmts, _))) = Pretty.chunks2 (map_filter
        (fn (name, (_, SOME stmt)) => if null stmt_names
              orelse member (op =) stmt_names name
              then SOME (print_stmt false (name, stmt))
              else NONE
          | (_, (_, NONE)) => NONE) stmts);
    val serialize_module =
      if null stmt_names then serialize_module1 else pair "" o serialize_module2;
    fun check_destination destination =
      (File.check destination; destination);
    fun write_module destination (modlname, content) =
      let
        val filename = case modlname
         of "" => Path.explode "Main.hs"
          | _ => (Path.ext "hs" o Path.explode o implode o separate "/"
                o Long_Name.explode) modlname;
        val pathname = Path.append destination filename;
        val _ = File.mkdir (Path.dir pathname);
      in File.write pathname
        ("{-# OPTIONS_GHC -fglasgow-exts #-}\n\n"
          ^ code_of_pretty content)
      end
  in
    Code_Target.mk_serialization target NONE
      (fn NONE => K () o map (code_writeln o snd) | SOME file => K () o map
        (write_module (check_destination file)))
      (rpair [] o cat_lines o map (code_of_pretty o snd))
      (map (uncurry print_module) includes
        @ map serialize_module (Symtab.dest hs_program))
      destination
  end;

val literals = let
  fun char_haskell c =
    let
      val s = ML_Syntax.print_char c;
    in if s = "'" then "\\'" else s end;
in Literals {
  literal_char = Library.enclose "'" "'" o char_haskell,
  literal_string = quote o translate_string char_haskell,
  literal_numeral = fn unbounded => fn k => if k >= 0 then string_of_int k
    else Library.enclose "(" ")" (signed_string_of_int k),
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
    fun dest_monad c_bind_name (IConst (c, _) `$ t1 `$ t2) =
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
          |>> (fn p => semicolon [str "let", p, str "=", print_term vars NOBR t]);
    fun pretty _ [c_bind'] print_term thm vars fxy [(t1, _), (t2, _)] = case dest_bind t1 t2
     of SOME (bind, t') => let
          val (binds, t'') = implode_monad c_bind' t'
          val (ps, vars') = fold_map (print_monad (gen_print_bind (K print_term) thm) print_term)
            (bind :: binds) vars;
        in
          (brackify fxy o single o enclose "do {" "}" o Pretty.breaks)
            (ps @| print_term vars' NOBR t'')
        end
      | NONE => brackify_infix (1, L) fxy
          [print_term vars (INFX (1, L)) t1, str ">>=", print_term vars (INFX (1, X)) t2]
  in (2, ([c_bind], pretty)) end;

fun add_monad target' raw_c_bind thy =
  let
    val c_bind = Code.read_const thy raw_c_bind;
  in if target = target' then
    thy
    |> Code_Target.add_syntax_const target c_bind
        (SOME (pretty_haskell_monad c_bind))
  else error "Only Haskell target allows for monad syntax" end;


(** Isar setup **)

fun isar_seri_haskell module_name =
  Code_Target.parse_args (Scan.option (Args.$$$ "root" -- Args.colon |-- Args.name)
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    >> (fn (module_prefix, string_classes) =>
      serialize_haskell module_prefix module_name string_classes));

val _ =
  OuterSyntax.command "code_monad" "define code syntax for monads" OuterKeyword.thy_decl (
    OuterParse.term_group -- OuterParse.name >> (fn (raw_bind, target) =>
      Toplevel.theory  (add_monad target raw_bind))
  );

val setup =
  Code_Target.add_target (target, (isar_seri_haskell, literals))
  #> Code_Target.add_syntax_tyco target "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        print_typ (INFX (1, X)) ty1,
        str "->",
        print_typ (INFX (1, R)) ty2
      ]))
  #> fold (Code_Target.add_reserved target) [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ]
  #> fold (Code_Target.add_reserved target) [
      "Prelude", "Main", "Bool", "Maybe", "Either", "Ordering", "Char", "String", "Int",
      "Integer", "Float", "Double", "Rational", "IO", "Eq", "Ord", "Enum", "Bounded",
      "Num", "Real", "Integral", "Fractional", "Floating", "RealFloat", "Monad", "Functor",
      "AlreadyExists", "ArithException", "ArrayException", "AssertionFailed", "AsyncException",
      "BlockedOnDeadMVar", "Deadlock", "Denormal", "DivideByZero", "DotNetException", "DynException",
      "Dynamic", "EOF", "EQ", "EmptyRec", "ErrorCall", "ExitException", "ExitFailure",
      "ExitSuccess", "False", "GT", "HeapOverflow",
      "IOError", "IOException", "IllegalOperation",
      "IndexOutOfBounds", "Just", "Key", "LT", "Left", "LossOfPrecision", "NoMethodError",
      "NoSuchThing", "NonTermination", "Nothing", "Obj", "OtherError", "Overflow",
      "PatternMatchFail", "PermissionDenied", "ProtocolError", "RecConError", "RecSelError",
      "RecUpdError", "ResourceBusy", "ResourceExhausted", "Right", "StackOverflow",
      "ThreadKilled", "True", "TyCon", "TypeRep", "UndefinedElement", "Underflow",
      "UnsupportedOperation", "UserError", "abs", "absReal", "acos", "acosh", "all",
      "and", "any", "appendFile", "asTypeOf", "asciiTab", "asin", "asinh", "atan",
      "atan2", "atanh", "basicIORun", "blockIO", "boundedEnumFrom", "boundedEnumFromThen",
      "boundedEnumFromThenTo", "boundedEnumFromTo", "boundedPred", "boundedSucc", "break",
      "catch", "catchException", "ceiling", "compare", "concat", "concatMap", "const",
      "cos", "cosh", "curry", "cycle", "decodeFloat", "denominator", "div", "divMod",
      "doubleToRatio", "doubleToRational", "drop", "dropWhile", "either", "elem",
      "emptyRec", "encodeFloat", "enumFrom", "enumFromThen", "enumFromThenTo",
      "enumFromTo", "error", "even", "exp", "exponent", "fail", "filter", "flip",
      "floatDigits", "floatProperFraction", "floatRadix", "floatRange", "floatToRational",
      "floor", "fmap", "foldl", "foldl'", "foldl1", "foldr", "foldr1", "fromDouble",
      "fromEnum", "fromEnum_0", "fromInt", "fromInteger", "fromIntegral", "fromObj",
      "fromRational", "fst", "gcd", "getChar", "getContents", "getLine", "head",
      "id", "inRange", "index", "init", "intToRatio", "interact", "ioError", "isAlpha",
      "isAlphaNum", "isDenormalized", "isDigit", "isHexDigit", "isIEEE", "isInfinite",
      "isLower", "isNaN", "isNegativeZero", "isOctDigit", "isSpace", "isUpper", "iterate", "iterate'",
      "last", "lcm", "length", "lex", "lexDigits", "lexLitChar", "lexmatch", "lines", "log",
      "logBase", "lookup", "loop", "map", "mapM", "mapM_", "max", "maxBound", "maximum",
      "maybe", "min", "minBound", "minimum", "mod", "negate", "nonnull", "not", "notElem",
      "null", "numerator", "numericEnumFrom", "numericEnumFromThen", "numericEnumFromThenTo",
      "numericEnumFromTo", "odd", "or", "otherwise", "pi", "pred", 
      "print", "product", "properFraction", "protectEsc", "putChar", "putStr", "putStrLn",
      "quot", "quotRem", "range", "rangeSize", "rationalToDouble", "rationalToFloat",
      "rationalToRealFloat", "read", "readDec", "readField", "readFieldName", "readFile",
      "readFloat", "readHex", "readIO", "readInt", "readList", "readLitChar", "readLn",
      "readOct", "readParen", "readSigned", "reads", "readsPrec", "realFloatToRational",
      "realToFrac", "recip", "reduce", "rem", "repeat", "replicate", "return", "reverse",
      "round", "scaleFloat", "scanl", "scanl1", "scanr", "scanr1", "seq", "sequence",
      "sequence_", "show", "showChar", "showException", "showField", "showList",
      "showLitChar", "showParen", "showString", "shows", "showsPrec", "significand",
      "signum", "signumReal", "sin", "sinh", "snd", "span", "splitAt", "sqrt", "subtract",
      "succ", "sum", "tail", "take", "takeWhile", "takeWhile1", "tan", "tanh", "threadToIOResult",
      "throw", "toEnum", "toInt", "toInteger", "toObj", "toRational", "truncate", "uncurry",
      "undefined", "unlines", "unsafeCoerce", "unsafeIndex", "unsafeRangeSize", "until", "unwords",
      "unzip", "unzip3", "userError", "words", "writeFile", "zip", "zip3", "zipWith", "zipWith3"
    ] (*due to weird handling of ':', we can't do anything else than to import *all* prelude symbols*);

end; (*struct*)
