(*  Title:      Pure/codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Generic code generator.
*)

signature CODEGEN =
sig
  val quiet_mode : bool ref
  val message : string -> unit

  datatype mixfix =
      Arg
    | Ignore
    | Pretty of Pretty.T
    | Term of term;

  val add_codegen: string ->
    (theory -> (exn option * string) Graph.T -> string -> bool -> term ->
    ((exn option * string) Graph.T * Pretty.T) option) -> theory -> theory
  val print_codegens: theory -> unit
  val generate_code: theory -> (string * string) list -> string
  val generate_code_i: theory -> (string * term) list -> string
  val assoc_consts: (xstring * string option * mixfix list) list -> theory -> theory
  val assoc_consts_i: (xstring * typ option * mixfix list) list -> theory -> theory
  val assoc_types: (xstring * string) list -> theory -> theory
  val get_assoc_code: theory -> string -> typ -> mixfix list option
  val get_assoc_types: theory -> (string * string) list
  val invoke_codegen: theory -> (exn option * string) Graph.T ->
    string -> bool -> term -> (exn option * string) Graph.T * Pretty.T
  val mk_const_id: Sign.sg -> string -> string
  val mk_type_id: Sign.sg -> string -> string
  val rename_term: term -> term
  val get_defn: theory -> string -> typ -> ((term list * term) * int option) option
  val is_instance: theory -> typ -> typ -> bool
  val parens: Pretty.T -> Pretty.T
  val mk_app: bool -> Pretty.T -> Pretty.T list -> Pretty.T
  val eta_expand: term -> term list -> int -> term
  val parsers: OuterSyntax.parser list
  val setup: (theory -> theory) list
end;

structure Codegen : CODEGEN =
struct

val quiet_mode = ref true;
fun message s = if !quiet_mode then () else writeln s;

(**** Mixfix syntax ****)

datatype mixfix =
    Arg
  | Ignore
  | Pretty of Pretty.T
  | Term of term;

fun is_arg Arg = true
  | is_arg Ignore = true
  | is_arg _ = false;

fun terms_of [] = []
  | terms_of (Term t :: ms) = t :: terms_of ms
  | terms_of (_ :: ms) = terms_of ms;

val num_args = length o filter is_arg;


(**** theory data ****)

(* data kind 'Pure/codegen' *)

structure CodegenArgs =
struct
  val name = "Pure/codegen";
  type T =
    {codegens : (string * (theory -> (exn option * string) Graph.T -> string ->
       bool -> term -> ((exn option * string) Graph.T * Pretty.T) option)) list,
     consts : ((string * typ) * mixfix list) list,
     types : (string * string) list};

  val empty = {codegens = [], consts = [], types = []};
  val copy = I;
  val prep_ext = I;

  fun merge ({codegens = codegens1, consts = consts1, types = types1},
             {codegens = codegens2, consts = consts2, types = types2}) =
    {codegens = rev (merge_alists (rev codegens1) (rev codegens2)),
     consts   = merge_alists consts1 consts2,
     types    = merge_alists types1 types2};

  fun print sg (cs:T) = Pretty.writeln
    (Pretty.strs ("code generators:" :: map fst (#codegens cs)));
end;

structure CodegenData = TheoryDataFun(CodegenArgs);
val print_codegens = CodegenData.print;


(**** add new code generator to theory ****)

fun add_codegen name f thy =
  let val {codegens, consts, types} = CodegenData.get thy
  in (case assoc (codegens, name) of
      None => CodegenData.put {codegens = (name, f)::codegens,
        consts = consts, types = types} thy
    | Some _ => error ("Code generator " ^ name ^ " already declared"))
  end;


(**** associate constants with target language code ****)

fun gen_assoc_consts prep_type xs thy = foldl (fn (thy, (s, tyopt, syn)) =>
  let
    val sg = sign_of thy;
    val {codegens, consts, types} = CodegenData.get thy;
    val cname = Sign.intern_const sg s;
  in
    (case Sign.const_type sg cname of
       Some T =>
         let val T' = (case tyopt of
                None => T
              | Some ty =>
                  let val U = prep_type sg ty
                  in if Type.typ_instance (Sign.tsig_of sg, U, T) then U
                    else error ("Illegal type constraint for constant " ^ cname)
                  end)
         in (case assoc (consts, (cname, T')) of
             None => CodegenData.put {codegens = codegens,
               consts = ((cname, T'), syn) :: consts, types = types} thy
           | Some _ => error ("Constant " ^ cname ^ " already associated with code"))
         end
     | _ => error ("Not a constant: " ^ s))
  end) (thy, xs);

val assoc_consts_i = gen_assoc_consts (K I);
val assoc_consts = gen_assoc_consts (fn sg => typ_of o read_ctyp sg);

(**** associate types with target language types ****)

fun assoc_types xs thy = foldl (fn (thy, (s, syn)) =>
  let
    val {codegens, consts, types} = CodegenData.get thy;
    val tc = Sign.intern_tycon (sign_of thy) s
  in
    (case assoc (types, tc) of
       None => CodegenData.put {codegens = codegens, consts = consts,
         types = (tc, syn) :: types} thy
     | Some _ => error ("Type " ^ tc ^ " already associated with code"))
  end) (thy, xs);

fun get_assoc_types thy = #types (CodegenData.get thy);


(**** retrieve definition of constant ****)

fun is_instance thy T1 T2 =
  Type.typ_instance (Sign.tsig_of (sign_of thy), T1, Type.varifyT T2);

fun get_assoc_code thy s T = apsome snd (find_first (fn ((s', T'), _) =>
  s = s' andalso is_instance thy T T') (#consts (CodegenData.get thy)));

fun get_defn thy s T =
  let
    val axms = flat (map (Symtab.dest o #axioms o Theory.rep_theory)
      (thy :: Theory.ancestors_of thy));
    val defs = mapfilter (fn (_, t) =>
      (let
         val (lhs, rhs) = Logic.dest_equals t;
         val (c, args) = strip_comb lhs;
         val (s', T') = dest_Const c
       in if s=s' then Some (T', (args, rhs)) else None end) handle TERM _ =>
         None) axms;
    val i = find_index (is_instance thy T o fst) defs
  in
    if i>=0 then Some (snd (nth_elem (i, defs)),
      if length defs = 1 then None else Some i)
    else None
  end;


(**** make valid ML identifiers ****)

fun gen_mk_id kind rename sg s =
  let
    val (xs as x::_) = explode (rename (space_implode "_"
      (NameSpace.unpack (Sign.cond_extern sg kind s))));
    fun check_str [] = ""
      | check_str (x::xs) =
          (if Symbol.is_letter x orelse Symbol.is_digit x orelse x="_" then x
           else "_" ^ string_of_int (ord x)) ^ check_str xs
  in
    (if not (Symbol.is_letter x) then "id" else "") ^ check_str xs
  end;

val mk_const_id = gen_mk_id Sign.constK I;
val mk_type_id = gen_mk_id Sign.typeK
  (fn s => if s mem ThmDatabase.ml_reserved then s ^ "_type" else s);

fun rename_term t =
  let
    val names = add_term_names (t, map (fst o fst o dest_Var) (term_vars t));
    val clash = names inter ThmDatabase.ml_reserved;
    val ps = clash ~~ variantlist (clash, names);

    fun rename (Var ((a, i), T)) = Var ((if_none (assoc (ps, a)) a, i), T)
      | rename (Free (a, T)) = Free (if_none (assoc (ps, a)) a, T)
      | rename (Abs (s, T, t)) = Abs (s, T, rename t)
      | rename (t $ u) = rename t $ rename u
      | rename t = t;
  in
    rename t
  end;


(**** invoke suitable code generator for term t ****)

fun invoke_codegen thy gr dep brack t = (case get_first
   (fn (_, f) => f thy gr dep brack t) (#codegens (CodegenData.get thy)) of
      None => error ("Unable to generate code for term:\n" ^
        Sign.string_of_term (sign_of thy) t ^ "\nrequired by:\n" ^
        commas (Graph.all_succs gr [dep]))
    | Some x => x)


(**** code generator for mixfix expressions ****)

fun parens p = Pretty.block [Pretty.str "(", p, Pretty.str ")"];

fun pretty_fn [] p = [p]
  | pretty_fn (x::xs) p = Pretty.str ("fn " ^ x ^ " =>") ::
      Pretty.brk 1 :: pretty_fn xs p;

fun pretty_mixfix [] [] _ = []
  | pretty_mixfix (Arg :: ms) (p :: ps) qs = p :: pretty_mixfix ms ps qs
  | pretty_mixfix (Ignore :: ms) (p :: ps) qs = pretty_mixfix ms ps qs
  | pretty_mixfix (Pretty p :: ms) ps qs = p :: pretty_mixfix ms ps qs
  | pretty_mixfix (Term _ :: ms) ps (q :: qs) = q :: pretty_mixfix ms ps qs;


(**** default code generator ****)

fun eta_expand t ts i =
  let
    val (Ts, _) = strip_type (fastype_of t);
    val j = i - length ts
  in
    foldr (fn (T, t) => Abs ("x", T, t))
      (take (j, Ts), list_comb (t, ts @ map Bound (j-1 downto 0)))
  end;

fun mk_app _ p [] = p
  | mk_app brack p ps = if brack then
       Pretty.block (Pretty.str "(" ::
         separate (Pretty.brk 1) (p :: ps) @ [Pretty.str ")"])
     else Pretty.block (separate (Pretty.brk 1) (p :: ps));

fun new_names t xs = variantlist (xs,
  map (fst o fst o dest_Var) (term_vars t) union
  add_term_names (t, ThmDatabase.ml_reserved));

fun new_name t x = hd (new_names t [x]);

fun default_codegen thy gr dep brack t =
  let
    val (u, ts) = strip_comb t;
    fun mapcode brack' gr ts = foldl_map
      (fn (gr, t) => invoke_codegen thy gr dep brack' t) (gr, ts)

  in (case u of
      Var ((s, i), _) =>
        let val (gr', ps) = mapcode true gr ts
        in Some (gr', mk_app brack (Pretty.str (s ^
           (if i=0 then "" else string_of_int i))) ps)
        end

    | Free (s, _) =>
        let val (gr', ps) = mapcode true gr ts
        in Some (gr', mk_app brack (Pretty.str s) ps) end

    | Const (s, T) =>
      (case get_assoc_code thy s T of
         Some ms =>
           let val i = num_args ms
           in if length ts < i then
               default_codegen thy gr dep brack (eta_expand u ts i)
             else
               let
                 val ts1 = take (i, ts);
                 val ts2 = drop (i, ts);
                 val (gr1, ps1) = mapcode false gr ts1;
                 val (gr2, ps2) = mapcode true gr1 ts2;
                 val (gr3, ps3) = mapcode false gr2 (terms_of ms);
               in
                 Some (gr3, mk_app brack (Pretty.block (pretty_mixfix ms ps1 ps3)) ps2)
               end
           end
       | None => (case get_defn thy s T of
           None => None
         | Some ((args, rhs), k) =>
             let
               val id = mk_const_id (sign_of thy) s ^ (case k of
                 None => "" | Some i => "_def" ^ string_of_int i);
               val (gr', ps) = mapcode true gr ts;
             in
               Some (Graph.add_edge (id, dep) gr' handle Graph.UNDEF _ =>
                 let
                   val _ = message ("expanding definition of " ^ s);
                   val (Ts, _) = strip_type T;
                   val (args', rhs') =
                     if not (null args) orelse null Ts then (args, rhs) else
                       let val v = Free (new_name rhs "x", hd Ts)
                       in ([v], betapply (rhs, v)) end;
                   val (gr1, p) = invoke_codegen thy (Graph.add_edge (id, dep)
                     (Graph.new_node (id, (None, "")) gr')) id false rhs';
                   val (gr2, xs) = mapcode false gr1 args';
                 in Graph.map_node id (K (None, Pretty.string_of (Pretty.block
                   (Pretty.str (if null args' then "val " else "fun ") ::
                    separate (Pretty.brk 1) (Pretty.str id :: xs) @
                    [Pretty.str " =", Pretty.brk 1, p, Pretty.str ";"])) ^ "\n\n")) gr2
                 end, mk_app brack (Pretty.str id) ps)
             end))

    | Abs _ =>
      let
        val (bs, Ts) = ListPair.unzip (strip_abs_vars u);
        val t = strip_abs_body u
        val bs' = new_names t bs;
        val (gr1, ps) = mapcode true gr ts;
        val (gr2, p) = invoke_codegen thy gr1 dep false
          (subst_bounds (map Free (rev (bs' ~~ Ts)), t));
      in
        Some (gr2, mk_app brack (Pretty.block (Pretty.str "(" :: pretty_fn bs' p @
          [Pretty.str ")"])) ps)
      end

    | _ => None)
  end;


fun output_code gr xs = implode (map (snd o Graph.get_node gr)
  (rev (Graph.all_preds gr xs)));

fun gen_generate_code prep_term thy = Pretty.setmp_margin 80 (fn xs =>
  let
    val sg = sign_of thy;
    val gr = Graph.new_node ("<Top>", (None, "")) Graph.empty;
    val (gr', ps) = foldl_map (fn (gr, (s, t)) => apsnd (pair s)
      (invoke_codegen thy gr "<Top>" false t)) (gr, map (apsnd (prep_term sg)) xs)
  in
    "structure Generated =\nstruct\n\n" ^
    output_code gr' ["<Top>"] ^
    space_implode "\n\n" (map (fn (s', p) => Pretty.string_of (Pretty.block
      [Pretty.str ("val " ^ s' ^ " ="), Pretty.brk 1, p, Pretty.str ";"])) ps) ^
    "\n\nend;\n\nopen Generated;\n"
  end);

val generate_code_i = gen_generate_code (K I);
val generate_code = gen_generate_code
  (fn sg => term_of o read_cterm sg o rpair TypeInfer.logicT);

fun parse_mixfix rd s =
  (case Scan.finite Symbol.stopper (Scan.repeat
     (   $$ "_" >> K Arg
      || $$ "?" >> K Ignore
      || $$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length)
      || $$ "{" |-- $$ "*" |-- Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.not_eof
            || Scan.unless ($$ "*" -- $$ "}") (Scan.one Symbol.not_eof)) --|
         $$ "*" --| $$ "}" >> (Term o rd o implode)
      || Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.not_eof
            || Scan.unless ($$ "_" || $$ "?" || $$ "/" || $$ "{" |-- $$ "*")
                 (Scan.one Symbol.not_eof)) >> (Pretty o Pretty.str o implode)))
       (Symbol.explode s) of
     (p, []) => p
   | _ => error ("Malformed annotation: " ^ quote s));

structure P = OuterParse and K = OuterSyntax.Keyword;

val assoc_typeP =
  OuterSyntax.command "types_code"
  "associate types with target language types" K.thy_decl
    (Scan.repeat1 (P.xname --| P.$$$ "(" -- P.string --| P.$$$ ")") >>
     (Toplevel.theory o assoc_types));

val assoc_constP =
  OuterSyntax.command "consts_code"
  "associate constants with target language code" K.thy_decl
    (Scan.repeat1
       (P.xname -- (Scan.option (P.$$$ "::" |-- P.string)) --|
        P.$$$ "(" -- P.string --| P.$$$ ")") >>
     (fn xs => Toplevel.theory (fn thy => assoc_consts
       (map (fn ((name, optype), mfx) => (name, optype, parse_mixfix
         (term_of o read_cterm (sign_of thy) o rpair TypeInfer.logicT) mfx))
           xs) thy)));

val generate_codeP =
  OuterSyntax.command "generate_code" "generates code for terms" K.thy_decl
    (Scan.option (P.$$$ "(" |-- P.string --| P.$$$ ")") --
     Scan.repeat1 (P.name --| P.$$$ "=" -- P.string) >>
     (fn (opt_fname, xs) => Toplevel.theory (fn thy =>
        ((case opt_fname of
            None => use_text Context.ml_output false
          | Some fname => File.write (Path.unpack fname))
              (generate_code thy xs); thy))));

val parsers = [assoc_typeP, assoc_constP, generate_codeP];

val setup = [CodegenData.init, add_codegen "default" default_codegen];

end;

OuterSyntax.add_parsers Codegen.parsers;
