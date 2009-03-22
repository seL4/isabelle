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

fun pr_haskell_bind pr_term =
  let
    fun pr_bind ((NONE, NONE), _) = str "_"
      | pr_bind ((SOME v, NONE), _) = str v
      | pr_bind ((NONE, SOME p), _) = p
      | pr_bind ((SOME v, SOME p), _) = brackets [str v, str "@", p];
  in gen_pr_bind pr_bind pr_term end;

fun pr_haskell_stmt naming labelled_name syntax_class syntax_tyco syntax_const
    init_syms deresolve is_cons contr_classparam_typs deriving_show =
  let
    val deresolve_base = Long_Name.base_name o deresolve;
    fun class_name class = case syntax_class class
     of NONE => deresolve class
      | SOME class => class;
    fun pr_typcontext tyvars vs = case maps (fn (v, sort) => map (pair v) sort) vs
     of [] => []
      | classbinds => Pretty.enum "," "(" ")" (
          map (fn (v, class) =>
            str (class_name class ^ " " ^ Code_Printer.lookup_var tyvars v)) classbinds)
          @@ str " => ";
    fun pr_typforall tyvars vs = case map fst vs
     of [] => []
      | vnames => str "forall " :: Pretty.breaks
          (map (str o Code_Printer.lookup_var tyvars) vnames) @ str "." @@ Pretty.brk 1;
    fun pr_tycoexpr tyvars fxy (tyco, tys) =
      brackify fxy (str tyco :: map (pr_typ tyvars BR) tys)
    and pr_typ tyvars fxy (tycoexpr as tyco `%% tys) = (case syntax_tyco tyco
         of NONE => pr_tycoexpr tyvars fxy (deresolve tyco, tys)
          | SOME (i, pr) => pr (pr_typ tyvars) fxy tys)
      | pr_typ tyvars fxy (ITyVar v) = (str o Code_Printer.lookup_var tyvars) v;
    fun pr_typdecl tyvars (vs, tycoexpr) =
      Pretty.block (pr_typcontext tyvars vs @| pr_tycoexpr tyvars NOBR tycoexpr);
    fun pr_typscheme tyvars (vs, ty) =
      Pretty.block (pr_typforall tyvars vs @ pr_typcontext tyvars vs @| pr_typ tyvars NOBR ty);
    fun pr_term tyvars thm vars fxy (IConst c) =
          pr_app tyvars thm vars fxy (c, [])
      | pr_term tyvars thm vars fxy (t as (t1 `$ t2)) =
          (case Code_Thingol.unfold_const_app t
           of SOME app => pr_app tyvars thm vars fxy app
            | _ =>
                brackify fxy [
                  pr_term tyvars thm vars NOBR t1,
                  pr_term tyvars thm vars BR t2
                ])
      | pr_term tyvars thm vars fxy (IVar v) =
          (str o Code_Printer.lookup_var vars) v
      | pr_term tyvars thm vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = Code_Thingol.unfold_abs t;
            fun pr ((v, pat), ty) = pr_bind tyvars thm BR ((SOME v, pat), ty);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (str "\\" :: ps @ str "->" @@ pr_term tyvars thm vars' NOBR t') end
      | pr_term tyvars thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then pr_case tyvars thm vars fxy cases
                else pr_app tyvars thm vars fxy c_ts
            | NONE => pr_case tyvars thm vars fxy cases)
    and pr_app' tyvars thm vars ((c, (_, tys)), ts) = case contr_classparam_typs c
     of [] => (str o deresolve) c :: map (pr_term tyvars thm vars BR) ts
      | fingerprint => let
          val ts_fingerprint = ts ~~ curry Library.take (length ts) fingerprint;
          val needs_annotation = forall (fn (_, NONE) => true | (t, SOME _) =>
            (not o Code_Thingol.locally_monomorphic) t) ts_fingerprint;
          fun pr_term_anno (t, NONE) _ = pr_term tyvars thm vars BR t
            | pr_term_anno (t, SOME _) ty =
                brackets [pr_term tyvars thm vars NOBR t, str "::", pr_typ tyvars NOBR ty];
        in
          if needs_annotation then
            (str o deresolve) c :: map2 pr_term_anno ts_fingerprint (curry Library.take (length ts) tys)
          else (str o deresolve) c :: map (pr_term tyvars thm vars BR) ts
        end
    and pr_app tyvars = gen_pr_app (pr_app' tyvars) (pr_term tyvars) syntax_const naming
    and pr_bind tyvars = pr_haskell_bind (pr_term tyvars)
    and pr_case tyvars thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind tyvars thm BR ((NONE, SOME pat), ty)
              |>> (fn p => semicolon [p, str "=", pr_term tyvars thm vars NOBR t])
            val (ps, vars') = fold_map pr binds vars;
          in
            Pretty.block_enclose (
              str "let {",
              concat [str "}", str "in", pr_term tyvars thm vars' NOBR body]
            ) ps
          end
      | pr_case tyvars thm vars fxy (((t, ty), clauses as _ :: _), _) =
          let
            fun pr (pat, body) =
              let
                val (p, vars') = pr_bind tyvars thm NOBR ((NONE, SOME pat), ty) vars;
              in semicolon [p, str "->", pr_term tyvars thm vars' NOBR body] end;
          in
            Pretty.block_enclose (
              concat [str "(case", pr_term tyvars thm vars NOBR t, str "of", str "{"],
              str "})"
            ) (map pr clauses)
          end
      | pr_case tyvars thm vars fxy ((_, []), _) = str "error \"empty case\"";
    fun pr_stmt (name, Code_Thingol.Fun (_, ((vs, ty), []))) =
          let
            val tyvars = Code_Printer.intro_vars (map fst vs) init_syms;
            val n = (length o fst o Code_Thingol.unfold_fun) ty;
          in
            Pretty.chunks [
              Pretty.block [
                (str o suffix " ::" o deresolve_base) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty),
                str ";"
              ],
              concat (
                (str o deresolve_base) name
                :: map str (replicate n "_")
                @ str "="
                :: str "error"
                @@ (str o (fn s => s ^ ";") o ML_Syntax.print_string
                    o Long_Name.base_name o Long_Name.qualifier) name
              )
            ]
          end
      | pr_stmt (name, Code_Thingol.Fun (_, ((vs, ty), raw_eqs))) =
          let
            val eqs = filter (snd o snd) raw_eqs;
            val tyvars = Code_Printer.intro_vars (map fst vs) init_syms;
            fun pr_eq ((ts, t), (thm, _)) =
              let
                val consts = map_filter
                  (fn c => if (is_some o syntax_const) c
                    then NONE else (SOME o Long_Name.base_name o deresolve) c)
                    ((fold o Code_Thingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = init_syms
                  |> Code_Printer.intro_vars consts
                  |> Code_Printer.intro_vars ((fold o Code_Thingol.fold_unbound_varnames)
                       (insert (op =)) ts []);
              in
                semicolon (
                  (str o deresolve_base) name
                  :: map (pr_term tyvars thm vars BR) ts
                  @ str "="
                  @@ pr_term tyvars thm vars NOBR t
                )
              end;
          in
            Pretty.chunks (
              Pretty.block [
                (str o suffix " ::" o deresolve_base) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty),
                str ";"
              ]
              :: map pr_eq eqs
            )
          end
      | pr_stmt (name, Code_Thingol.Datatype (_, (vs, []))) =
          let
            val tyvars = Code_Printer.intro_vars (map fst vs) init_syms;
          in
            semicolon [
              str "data",
              pr_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
            ]
          end
      | pr_stmt (name, Code_Thingol.Datatype (_, (vs, [(co, [ty])]))) =
          let
            val tyvars = Code_Printer.intro_vars (map fst vs) init_syms;
          in
            semicolon (
              str "newtype"
              :: pr_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
              :: str "="
              :: (str o deresolve_base) co
              :: pr_typ tyvars BR ty
              :: (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_stmt (name, Code_Thingol.Datatype (_, (vs, co :: cos))) =
          let
            val tyvars = Code_Printer.intro_vars (map fst vs) init_syms;
            fun pr_co (co, tys) =
              concat (
                (str o deresolve_base) co
                :: map (pr_typ tyvars BR) tys
              )
          in
            semicolon (
              str "data"
              :: pr_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
              :: str "="
              :: pr_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o pr_co) cos
              @ (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_stmt (name, Code_Thingol.Class (_, (v, (superclasses, classparams)))) =
          let
            val tyvars = Code_Printer.intro_vars [v] init_syms;
            fun pr_classparam (classparam, ty) =
              semicolon [
                (str o deresolve_base) classparam,
                str "::",
                pr_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                str "class ",
                Pretty.block (pr_typcontext tyvars [(v, map fst superclasses)]),
                str (deresolve_base name ^ " " ^ Code_Printer.lookup_var tyvars v),
                str " where {"
              ],
              str "};"
            ) (map pr_classparam classparams)
          end
      | pr_stmt (_, Code_Thingol.Classinst ((class, (tyco, vs)), (_, classparam_insts))) =
          let
            val split_abs_pure = (fn (v, _) `|-> t => SOME (v, t) | _ => NONE);
            val unfold_abs_pure = Code_Thingol.unfoldr split_abs_pure;
            val tyvars = Code_Printer.intro_vars (map fst vs) init_syms;
            fun pr_instdef ((classparam, c_inst), (thm, _)) = case syntax_const classparam
             of NONE => semicolon [
                    (str o deresolve_base) classparam,
                    str "=",
                    pr_app tyvars thm init_syms NOBR (c_inst, [])
                  ]
              | SOME (k, pr) =>
                  let
                    val (c_inst_name, (_, tys)) = c_inst;
                    val const = if (is_some o syntax_const) c_inst_name
                      then NONE else (SOME o Long_Name.base_name o deresolve) c_inst_name;
                    val proto_rhs = Code_Thingol.eta_expand k (c_inst, []);
                    val (vs, rhs) = unfold_abs_pure proto_rhs;
                    val vars = init_syms
                      |> Code_Printer.intro_vars (the_list const)
                      |> Code_Printer.intro_vars vs;
                    val lhs = IConst (classparam, ([], tys)) `$$ map IVar vs;
                      (*dictionaries are not relevant at this late stage*)
                  in
                    semicolon [
                      pr_term tyvars thm vars NOBR lhs,
                      str "=",
                      pr_term tyvars thm vars NOBR rhs
                    ]
                  end;
          in
            Pretty.block_enclose (
              Pretty.block [
                str "instance ",
                Pretty.block (pr_typcontext tyvars vs),
                str (class_name class ^ " "),
                pr_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
                str " where {"
              ],
              str "};"
            ) (map pr_instdef classparam_insts)
          end;
  in pr_stmt end;

fun haskell_program_of_program labelled_name module_name module_prefix reserved_names raw_module_alias program =
  let
    val module_alias = if is_some module_name then K module_name else raw_module_alias;
    val reserved_names = Name.make_context reserved_names;
    val mk_name_module = Code_Printer.mk_name_module reserved_names module_prefix module_alias program;
    fun add_stmt (name, (stmt, deps)) =
      let
        val (module_name, base) = Code_Printer.dest_name name;
        val module_name' = mk_name_module module_name;
        val mk_name_stmt = yield_singleton Name.variants;
        fun add_fun upper (nsp_fun, nsp_typ) =
          let
            val (base', nsp_fun') =
              mk_name_stmt (if upper then Code_Printer.first_upper base else base) nsp_fun
          in (base', (nsp_fun', nsp_typ)) end;
        fun add_typ (nsp_fun, nsp_typ) =
          let
            val (base', nsp_typ') = mk_name_stmt (Code_Printer.first_upper base) nsp_typ
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
        Symtab.map_default (module_name', ([], ([], (reserved_names, reserved_names))))
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
      o Symtab.lookup hs_program) ((mk_name_module o fst o Code_Printer.dest_name) name))) name
      handle Option => error ("Unknown statement name: " ^ labelled_name name);
  in (deresolver, hs_program) end;

fun serialize_haskell module_prefix raw_module_name string_classes labelled_name
    raw_reserved_names includes raw_module_alias
    syntax_class syntax_tyco syntax_const naming program cs destination =
  let
    val stmt_names = Code_Target.stmt_names_of_destination destination;
    val module_name = if null stmt_names then raw_module_name else SOME "Code";
    val reserved_names = fold (insert (op =) o fst) includes raw_reserved_names;
    val (deresolver, hs_program) = haskell_program_of_program labelled_name
      module_name module_prefix reserved_names raw_module_alias program;
    val is_cons = Code_Thingol.is_cons program;
    val contr_classparam_typs = Code_Thingol.contr_classparam_typs program;
    fun deriving_show tyco =
      let
        fun deriv _ "fun" = false
          | deriv tycos tyco = member (op =) tycos tyco orelse
              case try (Graph.get_node program) tyco
                of SOME (Code_Thingol.Datatype (_, (_, cs))) => forall (deriv' (tyco :: tycos))
                    (maps snd cs)
                 | NONE => true
        and deriv' tycos (tyco `%% tys) = deriv tycos tyco
              andalso forall (deriv' tycos) tys
          | deriv' _ (ITyVar _) = true
      in deriv [] tyco end;
    val reserved_names = Code_Printer.make_vars reserved_names;
    fun pr_stmt qualified = pr_haskell_stmt naming labelled_name
      syntax_class syntax_tyco syntax_const reserved_names
      (if qualified then deresolver else Long_Name.base_name o deresolver)
      is_cons contr_classparam_typs
      (if string_classes then deriving_show else K false);
    fun pr_module name content =
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
        val deps' = subtract (op =) stmt_names deps
          |> distinct (op =)
          |> map_filter (try deresolver);
        val qualified = is_none module_name andalso
          map deresolver stmt_names @ deps'
          |> map Long_Name.base_name
          |> has_duplicates (op =);
        val imports = deps'
          |> map Long_Name.qualifier
          |> distinct (op =);
        fun pr_import_include (name, _) = str ("import qualified " ^ name ^ ";");
        val pr_import_module = str o (if qualified
          then prefix "import qualified "
          else prefix "import ") o suffix ";";
        val content = Pretty.chunks (
            map pr_import_include includes
            @ map pr_import_module imports
            @ str ""
            :: separate (str "") (map_filter
              (fn (name, (_, SOME stmt)) => SOME (pr_stmt qualified (name, stmt))
                | (_, (_, NONE)) => NONE) stmts)
          )
      in pr_module module_name' content end;
    fun serialize_module2 (_, (_, (stmts, _))) = Pretty.chunks (
      separate (str "") (map_filter
        (fn (name, (_, SOME stmt)) => if null stmt_names
              orelse member (op =) stmt_names name
              then SOME (pr_stmt false (name, stmt))
              else NONE
          | (_, (_, NONE)) => NONE) stmts));
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
          ^ Code_Target.code_of_pretty content)
      end
  in
    Code_Target.mk_serialization target NONE
      (fn NONE => K () o map (Code_Target.code_writeln o snd) | SOME file => K () o map
        (write_module (check_destination file)))
      (rpair [] o cat_lines o map (Code_Target.code_of_pretty o snd))
      (map (uncurry pr_module) includes
        @ map serialize_module (Symtab.dest hs_program))
      destination
  end;

val literals = let
  fun char_haskell c =
    let
      val s = ML_Syntax.print_char c;
    in if s = "'" then "\\'" else s end;
in Literals {
  literal_char = enclose "'" "'" o char_haskell,
  literal_string = quote o translate_string char_haskell,
  literal_numeral = fn unbounded => fn k => if k >= 0 then string_of_int k
    else enclose "(" ")" (signed_string_of_int k),
  literal_list = Pretty.enum "," "[" "]",
  infix_cons = (5, ":")
} end;


(** optional monad syntax **)

fun pretty_haskell_monad c_bind =
  let
    fun dest_bind t1 t2 = case Code_Thingol.split_abs t2
     of SOME (((v, pat), ty), t') =>
          SOME ((SOME (((SOME v, pat), ty), true), t1), t')
      | NONE => NONE;
    fun dest_monad c_bind_name (IConst (c, _) `$ t1 `$ t2) =
          if c = c_bind_name then dest_bind t1 t2
          else NONE
      | dest_monad _ t = case Code_Thingol.split_let t
         of SOME (((pat, ty), tbind), t') =>
              SOME ((SOME (((NONE, SOME pat), ty), false), tbind), t')
          | NONE => NONE;
    fun implode_monad c_bind_name = Code_Thingol.unfoldr (dest_monad c_bind_name);
    fun pr_monad pr_bind pr (NONE, t) vars =
          (semicolon [pr vars NOBR t], vars)
      | pr_monad pr_bind pr (SOME (bind, true), t) vars = vars
          |> pr_bind NOBR bind
          |>> (fn p => semicolon [p, str "<-", pr vars NOBR t])
      | pr_monad pr_bind pr (SOME (bind, false), t) vars = vars
          |> pr_bind NOBR bind
          |>> (fn p => semicolon [str "let", p, str "=", pr vars NOBR t]);
    fun pretty pr naming thm vars fxy [(t1, _), (t2, _)] = case dest_bind t1 t2
     of SOME (bind, t') => let
          val (binds, t'') = implode_monad ((the o Code_Thingol.lookup_const naming) c_bind) t'
          val (ps, vars') = fold_map (pr_monad (pr_haskell_bind (K pr) thm) pr) (bind :: binds) vars;
        in (brackify fxy o single o Pretty.enclose "do {" "}" o Pretty.breaks) (ps @| pr vars' NOBR t'') end
      | NONE => brackify_infix (1, L) fxy
          [pr vars (INFX (1, L)) t1, str ">>=", pr vars (INFX (1, X)) t2]
  in (2, pretty) end;

fun add_monad target' raw_c_bind thy =
  let
    val c_bind = Code_Unit.read_const thy raw_c_bind;
  in if target = target' then
    thy
    |> Code_Target.add_syntax_const target c_bind
        (SOME (pretty_haskell_monad c_bind))
  else error "Only Haskell target allows for monad syntax" end;


(** Isar setup **)

fun isar_seri_haskell module =
  Code_Target.parse_args (Scan.option (Args.$$$ "root" -- Args.colon |-- Args.name)
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    >> (fn (module_prefix, string_classes) =>
      serialize_haskell module_prefix module string_classes));

val _ =
  OuterSyntax.command "code_monad" "define code syntax for monads" OuterKeyword.thy_decl (
    OuterParse.term_group -- OuterParse.name >> (fn (raw_bind, target) =>
      Toplevel.theory  (add_monad target raw_bind))
  );

val setup =
  Code_Target.add_target (target, (isar_seri_haskell, literals))
  #> Code_Target.add_syntax_tyco target "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
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
