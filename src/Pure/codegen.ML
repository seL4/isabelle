(*  Title:      Pure/codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Generic code generator.
*)

signature CODEGEN =
sig
  val quiet_mode : bool ref
  val message : string -> unit
  val mode : string list ref
  val margin : int ref

  datatype 'a mixfix =
      Arg
    | Ignore
    | Pretty of Pretty.T
    | Quote of 'a;

  type 'a codegen

  val add_codegen: string -> term codegen -> theory -> theory
  val add_tycodegen: string -> typ codegen -> theory -> theory
  val add_attribute: string -> (Args.T list -> theory attribute * Args.T list) -> theory -> theory
  val add_preprocessor: (theory -> thm list -> thm list) -> theory -> theory
  val preprocess: theory -> thm list -> thm list
  val print_codegens: theory -> unit
  val generate_code: theory -> (string * string) list -> string
  val generate_code_i: theory -> (string * term) list -> string
  val assoc_consts: (xstring * string option * term mixfix list) list -> theory -> theory
  val assoc_consts_i: (xstring * typ option * term mixfix list) list -> theory -> theory
  val assoc_types: (xstring * typ mixfix list) list -> theory -> theory
  val get_assoc_code: theory -> string -> typ -> term mixfix list option
  val get_assoc_type: theory -> string -> typ mixfix list option
  val invoke_codegen: theory -> string -> bool ->
    (exn option * string) Graph.T * term -> (exn option * string) Graph.T * Pretty.T
  val invoke_tycodegen: theory -> string -> bool ->
    (exn option * string) Graph.T * typ -> (exn option * string) Graph.T * Pretty.T
  val mk_id: string -> string
  val mk_const_id: Sign.sg -> string -> string
  val mk_type_id: Sign.sg -> string -> string
  val rename_term: term -> term
  val new_names: term -> string list -> string list
  val new_name: term -> string -> string
  val get_defn: theory -> string -> typ -> ((term list * term) * int option) option
  val is_instance: theory -> typ -> typ -> bool
  val parens: Pretty.T -> Pretty.T
  val mk_app: bool -> Pretty.T -> Pretty.T list -> Pretty.T
  val eta_expand: term -> term list -> int -> term
  val strip_tname: string -> string
  val mk_type: bool -> typ -> Pretty.T
  val mk_term_of: Sign.sg -> bool -> typ -> Pretty.T
  val mk_gen: Sign.sg -> bool -> string list -> string -> typ -> Pretty.T
  val test_fn: (int -> (string * term) list option) ref
  val test_term: theory -> int -> int -> term -> (string * term) list option
  val parse_mixfix: (string -> 'a) -> string -> 'a mixfix list
end;

structure Codegen : CODEGEN =
struct

val quiet_mode = ref true;
fun message s = if !quiet_mode then () else writeln s;

val mode = ref ([] : string list);

val margin = ref 80;

(**** Mixfix syntax ****)

datatype 'a mixfix =
    Arg
  | Ignore
  | Pretty of Pretty.T
  | Quote of 'a;

fun is_arg Arg = true
  | is_arg Ignore = true
  | is_arg _ = false;

fun quotes_of [] = []
  | quotes_of (Quote q :: ms) = q :: quotes_of ms
  | quotes_of (_ :: ms) = quotes_of ms;

fun args_of [] xs = ([], xs)
  | args_of (Arg :: ms) (x :: xs) = apfst (cons x) (args_of ms xs)
  | args_of (Ignore :: ms) (_ :: xs) = args_of ms xs
  | args_of (_ :: ms) xs = args_of ms xs;

fun num_args x = length (List.filter is_arg x);


(**** theory data ****)

(* type of code generators *)

type 'a codegen = theory -> (exn option * string) Graph.T ->
  string -> bool -> 'a -> ((exn option * string) Graph.T * Pretty.T) option;

(* parameters for random testing *)

type test_params =
  {size: int, iterations: int, default_type: typ option};

fun merge_test_params
  {size = size1, iterations = iterations1, default_type = default_type1}
  {size = size2, iterations = iterations2, default_type = default_type2} =
  {size = Int.max (size1, size2),
   iterations = Int.max (iterations1, iterations2),
   default_type = case default_type1 of
       NONE => default_type2
     | _ => default_type1};

val default_test_params : test_params =
  {size = 10, iterations = 100, default_type = NONE};

fun set_size size ({iterations, default_type, ...} : test_params) =
  {size = size, iterations = iterations, default_type = default_type};

fun set_iterations iterations ({size, default_type, ...} : test_params) =
  {size = size, iterations = iterations, default_type = default_type};

fun set_default_type s sg ({size, iterations, ...} : test_params) =
  {size = size, iterations = iterations,
   default_type = SOME (typ_of (read_ctyp sg s))};

(* data kind 'Pure/codegen' *)
 
structure CodegenArgs =
struct
  val name = "Pure/codegen";
  type T =
    {codegens : (string * term codegen) list,
     tycodegens : (string * typ codegen) list,
     consts : ((string * typ) * term mixfix list) list,
     types : (string * typ mixfix list) list,
     attrs: (string * (Args.T list -> theory attribute * Args.T list)) list,
     preprocs: (stamp * (theory -> thm list -> thm list)) list,
     test_params: test_params};

  val empty =
    {codegens = [], tycodegens = [], consts = [], types = [], attrs = [],
     preprocs = [], test_params = default_test_params};
  val copy = I;
  val prep_ext = I;

  fun merge
    ({codegens = codegens1, tycodegens = tycodegens1,
      consts = consts1, types = types1, attrs = attrs1,
      preprocs = preprocs1, test_params = test_params1},
     {codegens = codegens2, tycodegens = tycodegens2,
      consts = consts2, types = types2, attrs = attrs2,
      preprocs = preprocs2, test_params = test_params2}) =
    {codegens = merge_alists' codegens1 codegens2,
     tycodegens = merge_alists' tycodegens1 tycodegens2,
     consts = merge_alists consts1 consts2,
     types = merge_alists types1 types2,
     attrs = merge_alists attrs1 attrs2,
     preprocs = merge_alists' preprocs1 preprocs2,
     test_params = merge_test_params test_params1 test_params2};

  fun print sg ({codegens, tycodegens, ...} : T) =
    Pretty.writeln (Pretty.chunks
      [Pretty.strs ("term code generators:" :: map fst codegens),
       Pretty.strs ("type code generators:" :: map fst tycodegens)]);
end;

structure CodegenData = TheoryDataFun(CodegenArgs);
val _ = Context.add_setup [CodegenData.init];
val print_codegens = CodegenData.print;


(**** access parameters for random testing ****)

fun get_test_params thy = #test_params (CodegenData.get thy);

fun map_test_params f thy =
  let val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
    CodegenData.get thy;
  in CodegenData.put {codegens = codegens, tycodegens = tycodegens,
    consts = consts, types = types, attrs = attrs, preprocs = preprocs,
    test_params = f test_params} thy
  end;


(**** add new code generators to theory ****)

fun add_codegen name f thy =
  let val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
    CodegenData.get thy
  in (case assoc (codegens, name) of
      NONE => CodegenData.put {codegens = (name, f) :: codegens,
        tycodegens = tycodegens, consts = consts, types = types,
        attrs = attrs, preprocs = preprocs, test_params = test_params} thy
    | SOME _ => error ("Code generator " ^ name ^ " already declared"))
  end;

fun add_tycodegen name f thy =
  let val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
    CodegenData.get thy
  in (case assoc (tycodegens, name) of
      NONE => CodegenData.put {tycodegens = (name, f) :: tycodegens,
        codegens = codegens, consts = consts, types = types,
        attrs = attrs, preprocs = preprocs, test_params = test_params} thy
    | SOME _ => error ("Code generator " ^ name ^ " already declared"))
  end;


(**** code attribute ****)

fun add_attribute name att thy =
  let val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
    CodegenData.get thy
  in (case assoc (attrs, name) of
      NONE => CodegenData.put {tycodegens = tycodegens,
        codegens = codegens, consts = consts, types = types,
        attrs = if name = "" then attrs @ [(name, att)] else (name, att) :: attrs,
        preprocs = preprocs,
        test_params = test_params} thy
    | SOME _ => error ("Code attribute " ^ name ^ " already declared"))
  end;

fun mk_parser (a, p) = (if a = "" then Scan.succeed "" else Args.$$$ a) |-- p;

val code_attr =
  Attrib.syntax (Scan.peek (fn thy => foldr op || Scan.fail (map mk_parser
    (#attrs (CodegenData.get thy)))));

val _ = Context.add_setup
 [Attrib.add_attributes
  [("code", (code_attr, K Attrib.undef_local_attribute),
     "declare theorems for code generation")]];


(**** preprocessors ****)

fun add_preprocessor p thy =
  let val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
    CodegenData.get thy
  in CodegenData.put {tycodegens = tycodegens,
    codegens = codegens, consts = consts, types = types,
    attrs = attrs, preprocs = (stamp (), p) :: preprocs,
    test_params = test_params} thy
  end;

fun preprocess thy ths =
  let val {preprocs, ...} = CodegenData.get thy
  in Library.foldl (fn (ths, (_, f)) => f thy ths) (ths, preprocs) end;

fun unfold_attr (thy, eqn) =
  let
    val (name, _) = dest_Const (head_of
      (fst (Logic.dest_equals (prop_of eqn))));
    fun prep thy = map (fn th =>
      if name mem term_consts (prop_of th) then
        rewrite_rule [eqn] (Thm.transfer thy th)
      else th)
  in (add_preprocessor prep thy, eqn) end;

val _ = Context.add_setup [add_attribute "unfold" (Scan.succeed unfold_attr)];


(**** associate constants with target language code ****)

fun gen_assoc_consts prep_type xs thy = Library.foldl (fn (thy, (s, tyopt, syn)) =>
  let
    val sg = sign_of thy;
    val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
      CodegenData.get thy;
    val cname = Sign.intern_const sg s;
  in
    (case Sign.const_type sg cname of
       SOME T =>
         let val T' = (case tyopt of
                NONE => T
              | SOME ty =>
                  let val U = prep_type sg ty
                  in if Sign.typ_instance sg (U, T) then U
                    else error ("Illegal type constraint for constant " ^ cname)
                  end)
         in (case assoc (consts, (cname, T')) of
             NONE => CodegenData.put {codegens = codegens,
               tycodegens = tycodegens,
               consts = ((cname, T'), syn) :: consts,
               types = types, attrs = attrs, preprocs = preprocs,
               test_params = test_params} thy
           | SOME _ => error ("Constant " ^ cname ^ " already associated with code"))
         end
     | _ => error ("Not a constant: " ^ s))
  end) (thy, xs);

val assoc_consts_i = gen_assoc_consts (K I);
val assoc_consts = gen_assoc_consts (fn sg => typ_of o read_ctyp sg);


(**** associate types with target language types ****)

fun assoc_types xs thy = Library.foldl (fn (thy, (s, syn)) =>
  let
    val {codegens, tycodegens, consts, types, attrs, preprocs, test_params} =
      CodegenData.get thy;
    val tc = Sign.intern_tycon (sign_of thy) s
  in
    (case assoc (types, tc) of
       NONE => CodegenData.put {codegens = codegens,
         tycodegens = tycodegens, consts = consts,
         types = (tc, syn) :: types, attrs = attrs,
         preprocs = preprocs, test_params = test_params} thy
     | SOME _ => error ("Type " ^ tc ^ " already associated with code"))
  end) (thy, xs);

fun get_assoc_type thy s = assoc (#types (CodegenData.get thy), s);


(**** make valid ML identifiers ****)

fun is_ascii_letdig x = Symbol.is_ascii_letter x orelse
  Symbol.is_ascii_digit x orelse Symbol.is_ascii_quasi x;

fun dest_sym s = (case split_last (snd (take_prefix (equal "\\") (explode s))) of
    ("<" :: "^" :: xs, ">") => (true, implode xs)
  | ("<" :: xs, ">") => (false, implode xs)
  | _ => sys_error "dest_sym");
  
fun mk_id s = if s = "" then "" else
  let
    fun check_str [] = []
      | check_str xs = (case take_prefix is_ascii_letdig xs of
          ([], " " :: zs) => check_str zs
        | ([], z :: zs) =>
          if size z = 1 then string_of_int (ord z) :: check_str zs
          else (case dest_sym z of
              (true, "isub") => check_str zs
            | (true, "isup") => "" :: check_str zs
            | (ctrl, s') => (if ctrl then "ctrl_" ^ s' else s') :: check_str zs)
        | (ys, zs) => implode ys :: check_str zs);
    val s' = space_implode "_"
      (List.concat (map (check_str o Symbol.explode) (NameSpace.unpack s)))
  in
    if Symbol.is_ascii_letter (hd (explode s')) then s' else "id_" ^ s'
  end;

fun mk_const_id sg s =
  let val s' = mk_id (Sign.extern sg Sign.constK s)
  in if s' mem ThmDatabase.ml_reserved then s' ^ "_const" else s' end;

fun mk_type_id sg s =
  let val s' = mk_id (Sign.extern sg Sign.typeK s)
  in if s' mem ThmDatabase.ml_reserved then s' ^ "_type" else s' end;

fun rename_terms ts =
  let
    val names = foldr add_term_names
      (map (fst o fst) (Drule.vars_of_terms ts)) ts;
    val reserved = names inter ThmDatabase.ml_reserved;
    val (illegal, alt_names) = split_list (List.mapPartial (fn s =>
      let val s' = mk_id s in if s = s' then NONE else SOME (s, s') end) names)
    val ps = (reserved @ illegal) ~~
      variantlist (map (suffix "'") reserved @ alt_names, names);

    fun rename_id s = getOpt (assoc (ps, s), s);

    fun rename (Var ((a, i), T)) = Var ((rename_id a, i), T)
      | rename (Free (a, T)) = Free (rename_id a, T)
      | rename (Abs (s, T, t)) = Abs (s, T, rename t)
      | rename (t $ u) = rename t $ rename u
      | rename t = t;
  in
    map rename ts
  end;

val rename_term = hd o rename_terms o single;


(**** retrieve definition of constant ****)

fun is_instance thy T1 T2 =
  Sign.typ_instance (sign_of thy) (T1, Type.varifyT T2);

fun get_assoc_code thy s T = Option.map snd (find_first (fn ((s', T'), _) =>
  s = s' andalso is_instance thy T T') (#consts (CodegenData.get thy)));

fun get_defn thy s T =
  let
    val axms = Theory.all_axioms_of thy;
    fun prep_def def = (case preprocess thy [def] of
      [def'] => prop_of def' | _ => error "get_defn: bad preprocessor");
    fun dest t =
      let
        val (lhs, rhs) = Logic.dest_equals t;
        val (c, args) = strip_comb lhs;
        val (s', T') = dest_Const c
      in if s = s' then SOME (T', (args, rhs)) else NONE
      end handle TERM _ => NONE;
    val defs = List.mapPartial (fn (name, t) => Option.map (pair name) (dest t)) axms;
    val i = find_index (is_instance thy T o fst o snd) defs
  in
    if i >= 0 then
      let val (name, (T', (args, _))) = List.nth (defs, i)
      in case dest (prep_def (Thm.get_axiom thy name)) of
          NONE => NONE
        | SOME (T'', p as (args', rhs)) =>
            if T' = T'' andalso args = args' then
              SOME (split_last (rename_terms (args @ [rhs])),
                if length defs = 1 then NONE else SOME i)
            else NONE
      end
    else NONE
  end;


(**** invoke suitable code generator for term / type ****)

fun invoke_codegen thy dep brack (gr, t) = (case get_first
   (fn (_, f) => f thy gr dep brack t) (#codegens (CodegenData.get thy)) of
      NONE => error ("Unable to generate code for term:\n" ^
        Sign.string_of_term (sign_of thy) t ^ "\nrequired by:\n" ^
        commas (Graph.all_succs gr [dep]))
    | SOME x => x);

fun invoke_tycodegen thy dep brack (gr, T) = (case get_first
   (fn (_, f) => f thy gr dep brack T) (#tycodegens (CodegenData.get thy)) of
      NONE => error ("Unable to generate code for type:\n" ^
        Sign.string_of_typ (sign_of thy) T ^ "\nrequired by:\n" ^
        commas (Graph.all_succs gr [dep]))
    | SOME x => x);


(**** code generator for mixfix expressions ****)

fun parens p = Pretty.block [Pretty.str "(", p, Pretty.str ")"];

fun pretty_fn [] p = [p]
  | pretty_fn (x::xs) p = Pretty.str ("fn " ^ x ^ " =>") ::
      Pretty.brk 1 :: pretty_fn xs p;

fun pretty_mixfix [] [] _ = []
  | pretty_mixfix (Arg :: ms) (p :: ps) qs = p :: pretty_mixfix ms ps qs
  | pretty_mixfix (Ignore :: ms) ps qs = pretty_mixfix ms ps qs
  | pretty_mixfix (Pretty p :: ms) ps qs = p :: pretty_mixfix ms ps qs
  | pretty_mixfix (Quote _ :: ms) ps (q :: qs) = q :: pretty_mixfix ms ps qs;


(**** default code generators ****)

fun eta_expand t ts i =
  let
    val (Ts, _) = strip_type (fastype_of t);
    val j = i - length ts
  in
    foldr (fn (T, t) => Abs ("x", T, t))
      (list_comb (t, ts @ map Bound (j-1 downto 0))) (Library.take (j, Ts))
  end;

fun mk_app _ p [] = p
  | mk_app brack p ps = if brack then
       Pretty.block (Pretty.str "(" ::
         separate (Pretty.brk 1) (p :: ps) @ [Pretty.str ")"])
     else Pretty.block (separate (Pretty.brk 1) (p :: ps));

fun new_names t xs = variantlist (map mk_id xs,
  map (fst o fst o dest_Var) (term_vars t) union
  add_term_names (t, ThmDatabase.ml_reserved));

fun new_name t x = hd (new_names t [x]);

fun default_codegen thy gr dep brack t =
  let
    val (u, ts) = strip_comb t;
    fun codegens brack = foldl_map (invoke_codegen thy dep brack)
  in (case u of
      Var ((s, i), T) =>
        let
          val (gr', ps) = codegens true (gr, ts);
          val (gr'', _) = invoke_tycodegen thy dep false (gr', T)
        in SOME (gr'', mk_app brack (Pretty.str (s ^
           (if i=0 then "" else string_of_int i))) ps)
        end

    | Free (s, T) =>
        let
          val (gr', ps) = codegens true (gr, ts);
          val (gr'', _) = invoke_tycodegen thy dep false (gr', T)
        in SOME (gr'', mk_app brack (Pretty.str s) ps) end

    | Const (s, T) =>
      (case get_assoc_code thy s T of
         SOME ms =>
           let val i = num_args ms
           in if length ts < i then
               default_codegen thy gr dep brack (eta_expand u ts i)
             else
               let
                 val (ts1, ts2) = args_of ms ts;
                 val (gr1, ps1) = codegens false (gr, ts1);
                 val (gr2, ps2) = codegens true (gr1, ts2);
                 val (gr3, ps3) = codegens false (gr2, quotes_of ms);
               in
                 SOME (gr3, mk_app brack (Pretty.block (pretty_mixfix ms ps1 ps3)) ps2)
               end
           end
       | NONE => (case get_defn thy s T of
           NONE => NONE
         | SOME ((args, rhs), k) =>
             let
               val id = mk_const_id (sign_of thy) s ^ (case k of
                 NONE => "" | SOME i => "_def" ^ string_of_int i);
               val (gr', ps) = codegens true (gr, ts);
             in
               SOME (Graph.add_edge (id, dep) gr' handle Graph.UNDEF _ =>
                 let
                   val _ = message ("expanding definition of " ^ s);
                   val (Ts, _) = strip_type T;
                   val (args', rhs') =
                     if not (null args) orelse null Ts then (args, rhs) else
                       let val v = Free (new_name rhs "x", hd Ts)
                       in ([v], betapply (rhs, v)) end;
                   val (gr1, p) = invoke_codegen thy id false
                     (Graph.add_edge (id, dep)
                        (Graph.new_node (id, (NONE, "")) gr'), rhs');
                   val (gr2, xs) = codegens false (gr1, args');
                   val (gr3, ty) = invoke_tycodegen thy id false (gr2, T);
                 in Graph.map_node id (K (NONE, Pretty.string_of (Pretty.block
                   (separate (Pretty.brk 1) (if null args' then
                       [Pretty.str ("val " ^ id ^ " :"), ty]
                     else Pretty.str ("fun " ^ id) :: xs) @
                    [Pretty.str " =", Pretty.brk 1, p, Pretty.str ";"])) ^ "\n\n")) gr3
                 end, mk_app brack (Pretty.str id) ps)
             end))

    | Abs _ =>
      let
        val (bs, Ts) = ListPair.unzip (strip_abs_vars u);
        val t = strip_abs_body u
        val bs' = new_names t bs;
        val (gr1, ps) = codegens true (gr, ts);
        val (gr2, p) = invoke_codegen thy dep false
          (gr1, subst_bounds (map Free (rev (bs' ~~ Ts)), t));
      in
        SOME (gr2, mk_app brack (Pretty.block (Pretty.str "(" :: pretty_fn bs' p @
          [Pretty.str ")"])) ps)
      end

    | _ => NONE)
  end;

fun default_tycodegen thy gr dep brack (TVar ((s, i), _)) =
      SOME (gr, Pretty.str (s ^ (if i = 0 then "" else string_of_int i)))
  | default_tycodegen thy gr dep brack (TFree (s, _)) = SOME (gr, Pretty.str s)
  | default_tycodegen thy gr dep brack (Type (s, Ts)) =
      (case assoc (#types (CodegenData.get thy), s) of
         NONE => NONE
       | SOME ms =>
           let
             val (gr', ps) = foldl_map
               (invoke_tycodegen thy dep false) (gr, fst (args_of ms Ts));
             val (gr'', qs) = foldl_map
               (invoke_tycodegen thy dep false) (gr', quotes_of ms)
           in SOME (gr'', Pretty.block (pretty_mixfix ms ps qs)) end);

val _ = Context.add_setup
 [add_codegen "default" default_codegen,
  add_tycodegen "default" default_tycodegen];


fun output_code gr xs = implode (map (snd o Graph.get_node gr)
  (rev (Graph.all_preds gr xs)));

fun gen_generate_code prep_term thy =
  setmp print_mode [] (Pretty.setmp_margin (!margin) (fn xs =>
  let
    val sg = sign_of thy;
    val gr = Graph.new_node ("<Top>", (NONE, "")) Graph.empty;
    val (gr', ps) = foldl_map (fn (gr, (s, t)) => apsnd (pair s)
      (invoke_codegen thy "<Top>" false (gr, t)))
        (gr, map (apsnd (prep_term sg)) xs)
    val code =
      "structure Generated =\nstruct\n\n" ^
      output_code gr' ["<Top>"] ^
      space_implode "\n\n" (map (fn (s', p) => Pretty.string_of (Pretty.block
        [Pretty.str ("val " ^ s' ^ " ="), Pretty.brk 1, p, Pretty.str ";"])) ps) ^
      "\n\nend;\n\nopen Generated;\n";
  in code end));

val generate_code_i = gen_generate_code (K I);
val generate_code = gen_generate_code
  (fn sg => term_of o read_cterm sg o rpair TypeInfer.logicT);


(**** Reflection ****)

val strip_tname = implode o tl o explode;

fun pretty_list xs = Pretty.block (Pretty.str "[" ::
  List.concat (separate [Pretty.str ",", Pretty.brk 1] (map single xs)) @
  [Pretty.str "]"]);

fun mk_type p (TVar ((s, i), _)) = Pretty.str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "T")
  | mk_type p (TFree (s, _)) = Pretty.str (strip_tname s ^ "T")
  | mk_type p (Type (s, Ts)) = (if p then parens else I) (Pretty.block
      [Pretty.str "Type", Pretty.brk 1, Pretty.str ("(\"" ^ s ^ "\","),
       Pretty.brk 1, pretty_list (map (mk_type false) Ts), Pretty.str ")"]);

fun mk_term_of sg p (TVar ((s, i), _)) = Pretty.str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "F")
  | mk_term_of sg p (TFree (s, _)) = Pretty.str (strip_tname s ^ "F")
  | mk_term_of sg p (Type (s, Ts)) = (if p then parens else I) (Pretty.block
      (separate (Pretty.brk 1) (Pretty.str ("term_of_" ^ mk_type_id sg s) ::
        List.concat (map (fn T => [mk_term_of sg true T, mk_type true T]) Ts))));


(**** Test data generators ****)

fun mk_gen sg p xs a (TVar ((s, i), _)) = Pretty.str
      (strip_tname s ^ (if i = 0 then "" else string_of_int i) ^ "G")
  | mk_gen sg p xs a (TFree (s, _)) = Pretty.str (strip_tname s ^ "G")
  | mk_gen sg p xs a (Type (s, Ts)) = (if p then parens else I) (Pretty.block
      (separate (Pretty.brk 1) (Pretty.str ("gen_" ^ mk_type_id sg s ^
        (if s mem xs then "'" else "")) :: map (mk_gen sg true xs a) Ts @
        (if s mem xs then [Pretty.str a] else []))));

val test_fn : (int -> (string * term) list option) ref = ref (fn _ => NONE);

fun test_term thy sz i = setmp print_mode [] (fn t =>
  let
    val _ = assert (null (term_tvars t) andalso null (term_tfrees t))
      "Term to be tested contains type variables";
    val _ = assert (null (term_vars t))
      "Term to be tested contains schematic variables";
    val sg = sign_of thy;
    val frees = map dest_Free (term_frees t);
    val szname = variant (map fst frees) "i";
    val s = "structure TestTerm =\nstruct\n\n" ^
      setmp mode ["term_of", "test"] (generate_code_i thy)
        [("testf", list_abs_free (frees, t))] ^
      "\n" ^ Pretty.string_of
        (Pretty.block [Pretty.str "val () = Codegen.test_fn :=",
          Pretty.brk 1, Pretty.str ("(fn " ^ szname ^ " =>"), Pretty.brk 1,
          Pretty.blk (0, [Pretty.str "let", Pretty.brk 1,
            Pretty.blk (0, separate Pretty.fbrk (map (fn (s, T) =>
              Pretty.block [Pretty.str ("val " ^ mk_id s ^ " ="), Pretty.brk 1,
              mk_gen sg false [] "" T, Pretty.brk 1,
              Pretty.str (szname ^ ";")]) frees)),
            Pretty.brk 1, Pretty.str "in", Pretty.brk 1,
            Pretty.block [Pretty.str "if ",
              mk_app false (Pretty.str "testf") (map (Pretty.str o mk_id o fst) frees),
              Pretty.brk 1, Pretty.str "then NONE",
              Pretty.brk 1, Pretty.str "else ",
              Pretty.block [Pretty.str "SOME ", Pretty.block (Pretty.str "[" ::
                List.concat (separate [Pretty.str ",", Pretty.brk 1]
                  (map (fn (s, T) => [Pretty.block
                    [Pretty.str ("(" ^ Library.quote (Symbol.escape s) ^ ","), Pretty.brk 1,
                     mk_app false (mk_term_of sg false T)
                       [Pretty.str (mk_id s)], Pretty.str ")"]]) frees)) @
                  [Pretty.str "]"])]],
            Pretty.brk 1, Pretty.str "end"]), Pretty.str ");"]) ^
      "\n\nend;\n";
    val _ = use_text Context.ml_output false s;
    fun iter f k = if k > i then NONE
      else (case (f () handle Match =>
          (warning "Exception Match raised in generated code"; NONE)) of
        NONE => iter f (k+1) | SOME x => SOME x);
    fun test k = if k > sz then NONE
      else (priority ("Test data size: " ^ string_of_int k);
        case iter (fn () => !test_fn k) 1 of
          NONE => test (k+1) | SOME x => SOME x);
  in test 0 end);

fun test_goal ({size, iterations, default_type}, tvinsts) i st =
  let
    val sg = Toplevel.sign_of st;
    fun strip (Const ("all", _) $ Abs (_, _, t)) = strip t
      | strip t = t;
    val (gi, frees) = Logic.goal_params
      (prop_of (snd (snd (Proof.get_goal (Toplevel.proof_of st))))) i;
    val gi' = ObjectLogic.atomize_term sg (map_term_types
      (map_type_tfree (fn p as (s, _) => getOpt (assoc (tvinsts, s),
        getOpt (default_type,TFree p)))) (subst_bounds (frees, strip gi)));
  in case test_term (Toplevel.theory_of st) size iterations gi' of
      NONE => writeln "No counterexamples found."
    | SOME cex => writeln ("Counterexample found:\n" ^
        Pretty.string_of (Pretty.chunks (map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1,
            Sign.pretty_term sg t]) cex)))
  end;


(**** Interface ****)

val str = setmp print_mode [] Pretty.str;

fun parse_mixfix rd s =
  (case Scan.finite Symbol.stopper (Scan.repeat
     (   $$ "_" >> K Arg
      || $$ "?" >> K Ignore
      || $$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length)
      || $$ "{" |-- $$ "*" |-- Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.not_eof
            || Scan.unless ($$ "*" -- $$ "}") (Scan.one Symbol.not_eof)) --|
         $$ "*" --| $$ "}" >> (Quote o rd o implode)
      || Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.not_eof
            || Scan.unless ($$ "_" || $$ "?" || $$ "/" || $$ "{" |-- $$ "*")
                 (Scan.one Symbol.not_eof)) >> (Pretty o str o implode)))
       (Symbol.explode s) of
     (p, []) => p
   | _ => error ("Malformed annotation: " ^ quote s));

val _ = Context.add_setup
  [assoc_types [("fun", parse_mixfix (K dummyT) "(_ ->/ _)")]];


structure P = OuterParse and K = OuterSyntax.Keyword;

val assoc_typeP =
  OuterSyntax.command "types_code"
  "associate types with target language types" K.thy_decl
    (Scan.repeat1 (P.xname --| P.$$$ "(" -- P.string --| P.$$$ ")") >>
     (fn xs => Toplevel.theory (fn thy => assoc_types
       (map (fn (name, mfx) => (name, parse_mixfix
         (typ_of o read_ctyp (sign_of thy)) mfx)) xs) thy)));

val assoc_constP =
  OuterSyntax.command "consts_code"
  "associate constants with target language code" K.thy_decl
    (Scan.repeat1
       (P.xname -- (Scan.option (P.$$$ "::" |-- P.typ)) --|
        P.$$$ "(" -- P.string --| P.$$$ ")") >>
     (fn xs => Toplevel.theory (fn thy => assoc_consts
       (map (fn ((name, optype), mfx) => (name, optype, parse_mixfix
         (term_of o read_cterm (sign_of thy) o rpair TypeInfer.logicT) mfx))
           xs) thy)));

val generate_codeP =
  OuterSyntax.command "generate_code" "generates code for terms" K.thy_decl
    (Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") --
     Scan.optional (P.$$$ "[" |-- P.enum "," P.xname --| P.$$$ "]") (!mode) --
     Scan.repeat1 (P.name --| P.$$$ "=" -- P.term) >>
     (fn ((opt_fname, mode'), xs) => Toplevel.theory (fn thy =>
        ((case opt_fname of
            NONE => use_text Context.ml_output false
          | SOME fname => File.write (Path.unpack fname))
              (setmp mode mode' (generate_code thy) xs); thy))));

val params =
  [("size", P.nat >> (K o set_size)),
   ("iterations", P.nat >> (K o set_iterations)),
   ("default_type", P.typ >> set_default_type)];

val parse_test_params = P.short_ident :-- (fn s =>
  P.$$$ "=" |-- getOpt (assoc (params, s), Scan.fail)) >> snd;

fun parse_tyinst xs =
  (P.type_ident --| P.$$$ "=" -- P.typ >> (fn (v, s) => fn sg =>
    fn (x, ys) => (x, (v, typ_of (read_ctyp sg s)) :: ys))) xs;

fun app [] x = x
  | app (f :: fs) x = app fs (f x);

val test_paramsP =
  OuterSyntax.command "quickcheck_params" "set parameters for random testing" K.thy_decl
    (P.$$$ "[" |-- P.list1 parse_test_params --| P.$$$ "]" >>
      (fn fs => Toplevel.theory (fn thy =>
         map_test_params (app (map (fn f => f (sign_of thy)) fs)) thy)));

val testP =
  OuterSyntax.command "quickcheck" "try to find counterexample for subgoal" K.diag
  (Scan.option (P.$$$ "[" |-- P.list1
    (   parse_test_params >> (fn f => fn sg => apfst (f sg))
     || parse_tyinst) --| P.$$$ "]") -- Scan.optional P.nat 1 >>
    (fn (ps, g) => Toplevel.keep (fn st =>
      test_goal (app (getOpt (Option.map
          (map (fn f => f (Toplevel.sign_of st))) ps, []))
        (get_test_params (Toplevel.theory_of st), [])) g st)));

val _ = OuterSyntax.add_parsers
  [assoc_typeP, assoc_constP, generate_codeP, test_paramsP, testP];

end;
