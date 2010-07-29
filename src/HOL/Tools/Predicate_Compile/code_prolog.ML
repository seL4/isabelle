(*  Title:      HOL/Tools/Predicate_Compile/code_prolog.ML
    Author:     Lukas Bulwahn, TU Muenchen

Prototype of an code generator for logic programming languages (a.k.a. Prolog)
*)

signature CODE_PROLOG =
sig
  datatype term = Var of string * typ | Cons of string | AppF of string * term list;
  datatype prem = Conj of prem list | NotRel of string * term list | Rel of string * term list | Eq of term * term | NotEq of term * term;
  type clause = ((string * term list) * prem);
  type logic_program = clause list;

  val generate : Proof.context -> string list -> logic_program
  val write_program : logic_program -> string
  val run : logic_program -> string -> string list -> term list

end;

structure Code_Prolog : CODE_PROLOG =
struct

(* general string functions *)

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;

(* internal program representation *)

datatype term = Var of string * typ | Cons of string | AppF of string * term list;

fun string_of_prol_term (Var (s, T)) = "Var " ^ s
  | string_of_prol_term (Cons s) = "Cons " ^ s
  | string_of_prol_term (AppF (f, args)) = f ^ "(" ^ commas (map string_of_prol_term args) ^ ")" 

datatype prem = Conj of prem list | NotRel of string * term list | Rel of string * term list | Eq of term * term | NotEq of term * term;

fun dest_Rel (Rel (c, ts)) = (c, ts)
 
type clause = ((string * term list) * prem);

type logic_program = clause list;

(* translation from introduction rules to internal representation *)

(* assuming no clashing *)
fun translate_const c = Long_Name.base_name c

fun translate_term ctxt t =
  case strip_comb t of
    (Free (v, T), []) => Var (v, T) 
  | (Const (c, _), []) => Cons (translate_const c)
  | (Const (c, _), args) => AppF (translate_const c, map (translate_term ctxt) args)
  | _ => error ("illegal term for translation: " ^ Syntax.string_of_term ctxt t)


fun translate_literal ctxt t =
  case strip_comb t of
    (Const (@{const_name "op ="}, _), [l, r]) => Eq (pairself (translate_term ctxt) (l, r))
  | (Const (c, _), args) => Rel (translate_const c, map (translate_term ctxt) args)
  | _ => error ("illegal literal for translation: " ^ Syntax.string_of_term ctxt t)

fun NegRel_of (Rel lit) = NotRel lit
  | NegRel_of (Eq eq) = NotEq eq
  
fun translate_prem ctxt t =  
    case try HOLogic.dest_not t of
      SOME t => NegRel_of (translate_literal ctxt t)
    | NONE => translate_literal ctxt t

fun translate_intros ctxt gr const =
  let
    val intros = Graph.get_node gr const
    val (intros', ctxt') = Variable.import_terms true (map prop_of intros) ctxt
    fun translate_intro intro =
      let
        val head = HOLogic.dest_Trueprop (Logic.strip_imp_concl intro)
        val prems = map HOLogic.dest_Trueprop (Logic.strip_imp_prems intro) 
        val prems' = Conj (map (translate_prem ctxt') prems)
        val clause = (dest_Rel (translate_literal ctxt' head), prems')
      in clause end
  in map translate_intro intros' end

fun generate ctxt const =
  let 
     fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val gr = Predicate_Compile_Core.intros_graph_of ctxt
    val scc = strong_conn_of gr const
    val _ = tracing (commas (flat scc))
  in
    maps (translate_intros ctxt gr) (flat scc)
  end

(* transform logic program *)

(** ensure groundness of terms before negation **)

fun add_vars (Var x) vs = insert (op =) x vs
  | add_vars (Cons c) vs = vs
  | add_vars (AppF (f, args)) vs = fold add_vars args vs

fun string_of_typ (Type (s, Ts)) = Long_Name.base_name s

fun mk_groundness_prems ts =
  let
    val vars = fold add_vars ts []
    fun mk_ground (v, T) =
      Rel ("ground_" ^ string_of_typ T, [Var (v, T)])
  in
    map mk_ground vars
  end

fun ensure_groundness_prem (NotRel (c, ts)) = Conj (mk_groundness_prems ts @ [NotRel (c, ts)]) 
  | ensure_groundness_prem (NotEq (l, r)) = Conj (mk_groundness_prems [l, r] @ [NotEq (l, r)])
  | ensure_groundness_prem (Conj ps) = Conj (map ensure_groundness_prem ps)
  | ensure_groundness_prem p = p

fun ensure_groundness_before_negation p =
  map (apsnd ensure_groundness_prem) p

(* code printer *)

fun write_term (Var (v, _)) = first_upper v
  | write_term (Cons c) = first_lower c
  | write_term (AppF (f, args)) = first_lower f ^ "(" ^ space_implode ", " (map write_term args) ^ ")" 

fun write_rel (pred, args) =
  pred ^ "(" ^ space_implode ", " (map write_term args) ^ ")" 

fun write_prem (Conj prems) = space_implode ", " (map write_prem prems)
  | write_prem (Rel p) = write_rel p  
  | write_prem (NotRel p) = "not(" ^ write_rel p ^ ")"
  | write_prem (Eq (l, r)) = write_term l ^ " = " ^ write_term r
  | write_prem (NotEq (l, r)) = write_term l ^ " \\= " ^ write_term r

fun write_clause (head, prem) =
  write_rel head ^ (if prem = Conj [] then "." else " :- " ^ write_prem prem ^ ".")

fun write_program p =
  cat_lines (map write_clause p) 

fun query_first rel vnames =
  "eval :- once("  ^ rel ^ "(" ^ space_implode ", " vnames ^ ")),\n" ^
  "writef('" ^ implode (map (fn v => v ^ " = %w\\n") vnames) ^"', [" ^ space_implode ", " vnames ^ "]).\n"

val prelude =
  "#!/usr/bin/swipl -q -t main -f\n\n" ^
  ":- style_check(-singleton).\n\n" ^
  "main :- catch(eval, E, (print_message(error, E), fail)), halt.\n" ^
  "main :- halt(1).\n"

(* parsing prolog solution *)

val scan_atom =
  Scan.repeat (Scan.one (fn s => Symbol.is_ascii_lower s orelse Symbol.is_ascii_quasi s))

val scan_var =
  Scan.repeat (Scan.one
    (fn s => Symbol.is_ascii_upper s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s))

fun dest_Char (Symbol.Char s) = s

val string_of = concat o map (dest_Char o Symbol.decode)

val scan_term =
  scan_atom >> (Cons o string_of) || scan_var >> (Var o rpair dummyT o string_of)

val parse_term = fst o Scan.finite Symbol.stopper
            (Scan.error (!! (fn _ => raise Fail "parsing prolog output failed"))
                            scan_term)
  o explode
  
fun parse_solution sol =
  let
    fun dest_eq s = (tracing s; tracing(commas (space_explode "=" s)); case space_explode "=" s of
        (l :: r :: []) => parse_term (unprefix " " r)
      | _ => raise Fail "unexpected equation in prolog output")
  in
    map dest_eq (fst (split_last (space_explode "\n" sol)))
  end 
  
(* calling external interpreter and getting results *)

fun run p query_rel vnames =
  let
    val cmd = Path.named_root
    val prog = prelude ^ query_first query_rel vnames ^ write_program p
    val prolog_file = File.tmp_path (Path.basic "prolog_file")
    val _ = File.write prolog_file prog
    val (solution, _) = bash_output ("/usr/bin/swipl -f " ^ File.shell_path prolog_file)
    val ts = parse_solution solution
    val _ = tracing (commas (map string_of_prol_term ts)) 
  in
    ts
  end

(* values command *)

fun mk_term (Var (s, T)) = Free (s, T)
  | mk_term (Cons s) = Const (s, dummyT)
  | mk_term (AppF (f, args)) = list_comb (Const (f, dummyT), map mk_term args)
  
fun values ctxt soln t_compr =
  let
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term ctxt t_compr);
    val (body, Ts, fp) = HOLogic.strip_psplits split;
    val output_names = Name.variant_list (Term.add_free_names body [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = map2 (curry Free) output_names (rev Ts)
    val body = subst_bounds (output_frees, body)
    val (pred as Const (name, T), all_args) =
      case strip_comb body of
        (Const (name, T), all_args) => (Const (name, T), all_args)
      | (head, _) => error ("Not a constant: " ^ Syntax.string_of_term ctxt head)
    val vnames =
      case try (map (fst o dest_Free)) all_args of
        SOME vs => vs
      | NONE => error ("Not only free variables in " ^ commas (map (Syntax.string_of_term ctxt) all_args))
    val ts = run (generate ctxt [name]) (translate_const name) (map first_upper vnames)
  in
    HOLogic.mk_tuple (map mk_term ts)
  end

fun values_cmd print_modes soln raw_t state =
  let
    val ctxt = Toplevel.context_of state
    val t = Syntax.read_term ctxt raw_t
    val t' = values ctxt soln t
    val ty' = Term.type_of t'
    val ctxt' = Variable.auto_fixes t' ctxt
    val p = Print_Mode.with_modes print_modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;


(* renewing the values command for Prolog queries *)

val opt_print_modes =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.xname --| Parse.$$$ ")")) [];

val _ = Outer_Syntax.improper_command "values" "enumerate and print comprehensions" Keyword.diag
  (opt_print_modes -- Scan.optional Parse.nat ~1 -- Parse.term
   >> (fn ((print_modes, soln), t) => Toplevel.keep
        (values_cmd print_modes soln t)));

end;
