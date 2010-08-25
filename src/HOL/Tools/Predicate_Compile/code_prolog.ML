(*  Title:      HOL/Tools/Predicate_Compile/code_prolog.ML
    Author:     Lukas Bulwahn, TU Muenchen

Prototype of an code generator for logic programming languages (a.k.a. Prolog)
*)

signature CODE_PROLOG =
sig
  type code_options = {ensure_groundness : bool}
  val options : code_options ref

  datatype arith_op = Plus | Minus
  datatype prol_term = Var of string | Cons of string | AppF of string * prol_term list
    | Number of int | ArithOp of arith_op * prol_term list;
  datatype prem = Conj of prem list
    | Rel of string * prol_term list | NotRel of string * prol_term list
    | Eq of prol_term * prol_term | NotEq of prol_term * prol_term
    | ArithEq of prol_term * prol_term | NotArithEq of prol_term * prol_term
    | Ground of string * typ;

  type clause = ((string * prol_term list) * prem);
  type logic_program = clause list;
  type constant_table = (string * string) list
    
  val generate : code_options -> Proof.context -> string list -> (logic_program * constant_table)
  val write_program : logic_program -> string
  val run : logic_program -> string -> string list -> int option -> prol_term list list

  val trace : bool Unsynchronized.ref
end;

structure Code_Prolog : CODE_PROLOG =
struct

(* diagnostic tracing *)

val trace = Unsynchronized.ref false

fun tracing s = if !trace then Output.tracing s else () 

(* code generation options *)

type code_options = {ensure_groundness : bool}

val options = Unsynchronized.ref {ensure_groundness = false};

(* general string functions *)

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;

(* internal program representation *)

datatype arith_op = Plus | Minus

datatype prol_term = Var of string | Cons of string | AppF of string * prol_term list
  | Number of int | ArithOp of arith_op * prol_term list;

fun maybe_AppF (c, []) = Cons c
  | maybe_AppF (c, xs) = AppF (c, xs)

fun is_Var (Var _) = true
  | is_Var _ = false

fun is_arith_term (Var _) = true
  | is_arith_term (Number _) = true
  | is_arith_term (ArithOp (_, operands)) = forall is_arith_term operands
  | is_arith_term _ = false

fun string_of_prol_term (Var s) = "Var " ^ s
  | string_of_prol_term (Cons s) = "Cons " ^ s
  | string_of_prol_term (AppF (f, args)) = f ^ "(" ^ commas (map string_of_prol_term args) ^ ")" 
  | string_of_prol_term (Number n) = "Number " ^ string_of_int n

datatype prem = Conj of prem list
  | Rel of string * prol_term list | NotRel of string * prol_term list
  | Eq of prol_term * prol_term | NotEq of prol_term * prol_term
  | ArithEq of prol_term * prol_term | NotArithEq of prol_term * prol_term
  | Ground of string * typ;
  
fun dest_Rel (Rel (c, ts)) = (c, ts)
 
type clause = ((string * prol_term list) * prem);

type logic_program = clause list;

(* translation from introduction rules to internal representation *)

(** constant table **)

type constant_table = (string * string) list

(* assuming no clashing *)
fun mk_constant_table consts =
  AList.make (first_lower o Long_Name.base_name) consts

fun declare_consts consts constant_table =
  fold (fn c => AList.update (op =) (c, first_lower (Long_Name.base_name c))) consts constant_table
  
fun translate_const constant_table c =
  case AList.lookup (op =) constant_table c of
    SOME c' => c'
  | NONE => error ("No such constant: " ^ c)

fun inv_lookup _ [] _ = NONE
  | inv_lookup eq ((key, value)::xs) value' =
      if eq (value', value) then SOME key
      else inv_lookup eq xs value';

fun restore_const constant_table c =
  case inv_lookup (op =) constant_table c of
    SOME c' => c'
  | NONE => error ("No constant corresponding to "  ^ c)

(** translation of terms, literals, premises, and clauses **)

fun translate_arith_const @{const_name "Groups.plus_class.plus"} = SOME Plus
  | translate_arith_const @{const_name "Groups.minus_class.minus"} = SOME Minus
  | translate_arith_const _ = NONE

fun translate_term ctxt constant_table t =
  case try HOLogic.dest_number t of
    SOME (@{typ "int"}, n) => Number n
  | NONE =>
      (case strip_comb t of
        (Free (v, T), []) => Var v 
      | (Const (c, _), []) => Cons (translate_const constant_table c)
      | (Const (c, _), args) =>
        (case translate_arith_const c of
          SOME aop => ArithOp (aop, map (translate_term ctxt constant_table) args)
        | NONE =>                                                             
            AppF (translate_const constant_table c, map (translate_term ctxt constant_table) args))
      | _ => error ("illegal term for translation: " ^ Syntax.string_of_term ctxt t))

fun translate_literal ctxt constant_table t =
  case strip_comb t of
    (Const (@{const_name "op ="}, _), [l, r]) =>
      let
        val l' = translate_term ctxt constant_table l
        val r' = translate_term ctxt constant_table r
      in
        (if is_Var l' andalso is_arith_term r' andalso not (is_Var r') then ArithEq else Eq) (l', r')
      end
  | (Const (c, _), args) =>
      Rel (translate_const constant_table c, map (translate_term ctxt constant_table) args)
  | _ => error ("illegal literal for translation: " ^ Syntax.string_of_term ctxt t)

fun NegRel_of (Rel lit) = NotRel lit
  | NegRel_of (Eq eq) = NotEq eq
  | NegRel_of (ArithEq eq) = NotArithEq eq

fun mk_groundness_prems t = map Ground (Term.add_frees t [])
  
fun translate_prem options ctxt constant_table t =  
    case try HOLogic.dest_not t of
      SOME t =>
        if #ensure_groundness options then
          Conj (mk_groundness_prems t @ [NegRel_of (translate_literal ctxt constant_table t)])
        else
          NegRel_of (translate_literal ctxt constant_table t)
    | NONE => translate_literal ctxt constant_table t
    
fun imp_prems_conv cv ct =
  case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv) (imp_prems_conv cv) ct
  | _ => Conv.all_conv ct

fun Trueprop_conv cv ct =
  case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct  
  | _ => raise Fail "Trueprop_conv"

fun preprocess_intro thy rule =
  Conv.fconv_rule
    (imp_prems_conv
      (Trueprop_conv (Conv.try_conv (Conv.rewr_conv @{thm Predicate.eq_is_eq}))))
    (Thm.transfer thy rule)

fun translate_intros options ctxt gr const constant_table =
  let
    val intros = map (preprocess_intro (ProofContext.theory_of ctxt)) (Graph.get_node gr const)
    val (intros', ctxt') = Variable.import_terms true (map prop_of intros) ctxt
    val constant_table' = declare_consts (fold Term.add_const_names intros' []) constant_table
    fun translate_intro intro =
      let
        val head = HOLogic.dest_Trueprop (Logic.strip_imp_concl intro)
        val prems = map HOLogic.dest_Trueprop (Logic.strip_imp_prems intro)
        val prems' = Conj (map (translate_prem options ctxt' constant_table') prems)
        val clause = (dest_Rel (translate_literal ctxt' constant_table' head), prems')
      in clause end
  in (map translate_intro intros', constant_table') end

fun generate options ctxt const =
  let 
     fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val gr = Predicate_Compile_Core.intros_graph_of ctxt
    val scc = strong_conn_of gr const
    val constant_table = mk_constant_table (flat scc)
  in
    apfst flat (fold_map (translate_intros options ctxt gr) (flat scc) constant_table)
  end
  
(* add implementation for ground predicates *)

fun add_ground_typ (Conj prems) = fold add_ground_typ prems
  | add_ground_typ (Ground (_, T)) = insert (op =) T
  | add_ground_typ _ = I

fun mk_relname (Type (Tcon, Targs)) =
  first_lower (Long_Name.base_name Tcon) ^ space_implode "_" (map mk_relname Targs)
  | mk_relname _ = raise Fail "unexpected type"

(* This is copied from "pat_completeness.ML" *)
fun inst_constrs_of thy (T as Type (name, _)) =
  map (fn (Cn,CT) =>
    Envir.subst_term_types (Sign.typ_match thy (body_type CT, T) Vartab.empty) (Const (Cn, CT)))
    (the (Datatype.get_constrs thy name))
  | inst_constrs_of thy T = raise TYPE ("inst_constrs_of", [T], [])
  
fun mk_ground_impl ctxt (T as Type (Tcon, Targs)) (seen, constant_table) =
  if member (op =) seen T then ([], (seen, constant_table))
  else
    let
      val rel_name = mk_relname T
      fun mk_impl (Const (constr_name, T)) (seen, constant_table) =
        let
          val constant_table' = declare_consts [constr_name] constant_table
          val (rec_clauses, (seen', constant_table'')) =
            fold_map (mk_ground_impl ctxt) (binder_types T) (seen, constant_table')
          val vars = map (fn i => Var ("x" ^ string_of_int i)) (1 upto (length (binder_types T)))    
          fun mk_prem v T = Rel (mk_relname T, [v])
          val clause =
            ((rel_name, [maybe_AppF (translate_const constant_table'' constr_name, vars)]),
             Conj (map2 mk_prem vars (binder_types T)))
        in
          (clause :: flat rec_clauses, (seen', constant_table''))
        end
      val constrs = inst_constrs_of (ProofContext.theory_of ctxt) T
    in apfst flat (fold_map mk_impl constrs (T :: seen, constant_table)) end
 | mk_ground_impl ctxt T (seen, constant_table) =
   raise Fail ("unexpected type :" ^ Syntax.string_of_typ ctxt T)

fun replace_ground (Conj prems) = Conj (map replace_ground prems)
  | replace_ground (Ground (x, T)) =
    Rel (mk_relname T, [Var x])  
  | replace_ground p = p
  
fun add_ground_predicates ctxt (p, constant_table) =
  let
    val ground_typs = fold (add_ground_typ o snd) p []
    val (grs, (_, constant_table')) = fold_map (mk_ground_impl ctxt) ground_typs ([], constant_table)
    val p' = map (apsnd replace_ground) p
  in
    ((flat grs) @ p', constant_table')
  end
    
(* code printer *)

fun write_arith_op Plus = "+"
  | write_arith_op Minus = "-"

fun write_term (Var v) = first_upper v
  | write_term (Cons c) = c
  | write_term (AppF (f, args)) = f ^ "(" ^ space_implode ", " (map write_term args) ^ ")"
  | write_term (ArithOp (oper, [a1, a2])) = write_term a1 ^ " " ^ write_arith_op oper ^ " " ^ write_term a2
  | write_term (Number n) = string_of_int n

fun write_rel (pred, args) =
  pred ^ "(" ^ space_implode ", " (map write_term args) ^ ")" 

fun write_prem (Conj prems) = space_implode ", " (map write_prem prems)
  | write_prem (Rel p) = write_rel p  
  | write_prem (NotRel p) = "not(" ^ write_rel p ^ ")"
  | write_prem (Eq (l, r)) = write_term l ^ " = " ^ write_term r
  | write_prem (NotEq (l, r)) = write_term l ^ " \\= " ^ write_term r
  | write_prem (ArithEq (l, r)) = write_term l ^ " is " ^ write_term r
  | write_prem (NotArithEq (l, r)) = write_term l ^ " =\\= " ^ write_term r

fun write_clause (head, prem) =
  write_rel head ^ (if prem = Conj [] then "." else " :- " ^ write_prem prem ^ ".")

fun write_program p =
  cat_lines (map write_clause p) 

(** query templates **)

fun query_first rel vnames =
  "eval :- once("  ^ rel ^ "(" ^ space_implode ", " vnames ^ ")),\n" ^
  "writef('" ^ space_implode ";" (map (fn v => v ^ " = %w") vnames) ^
  "\\n', [" ^ space_implode ", " vnames ^ "]).\n"
  
fun query_firstn n rel vnames =
  "eval :- findnsols(" ^ string_of_int n ^ ", (" ^ space_implode ", " vnames ^ "), " ^
    rel ^ "(" ^ space_implode ", " vnames ^ "), Sols), writelist(Sols).\n" ^
    "writelist([]).\n" ^
    "writelist([(" ^ space_implode ", " vnames ^ ")|T]) :- " ^
    "writef('" ^ space_implode ";" (map (fn v => v ^ " = %w") vnames) ^
    "\\n', [" ^ space_implode ", " vnames ^ "]), writelist(T).\n"
  
val prelude =
  "#!/usr/bin/swipl -q -t main -f\n\n" ^
  ":- use_module(library('dialect/ciao/aggregates')).\n" ^
  ":- style_check(-singleton).\n" ^
  ":- style_check(-discontiguous).\n" ^ 	
  ":- style_check(-atom).\n\n" ^
  "main :- catch(eval, E, (print_message(error, E), fail)), halt.\n" ^
  "main :- halt(1).\n"

(* parsing prolog solution *)
val scan_number =
  Scan.many1 Symbol.is_ascii_digit

val scan_atom =
  Scan.many1 (fn s => Symbol.is_ascii_lower s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s)

val scan_var =
  Scan.many1
    (fn s => Symbol.is_ascii_upper s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s)

val scan_ident =
  Scan.repeat (Scan.one
    (fn s => Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s))

fun dest_Char (Symbol.Char s) = s

val string_of = concat o map (dest_Char o Symbol.decode)

val is_atom_ident = forall Symbol.is_ascii_lower

val is_var_ident =
  forall (fn s => Symbol.is_ascii_upper s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s)

fun int_of_symbol_list xs = fold (fn x => fn s => s * 10 + (ord x - ord "0")) xs 0

fun scan_terms xs = (((scan_term --| $$ ",") ::: scan_terms)
  || (scan_term >> single)) xs
and scan_term xs =
  ((scan_number >> (Number o int_of_symbol_list))
  || (scan_var >> (Var o string_of))
  || ((scan_atom -- ($$ "(" |-- scan_terms --| $$ ")"))
    >> (fn (f, ts) => AppF (string_of f, ts)))
  || (scan_atom >> (Cons o string_of))) xs

val parse_term = fst o Scan.finite Symbol.stopper
    (Scan.error (!! (fn _ => raise Fail "parsing prolog output failed")) scan_term)
  o explode
  
fun parse_solutions sol =
  let
    fun dest_eq s = case space_explode "=" s of
        (l :: r :: []) => parse_term (unprefix " " r)
      | _ => raise Fail "unexpected equation in prolog output"
    fun parse_solution s = map dest_eq (space_explode ";" s)
  in
    map parse_solution (fst (split_last (space_explode "\n" sol)))
  end 
  
(* calling external interpreter and getting results *)

fun run p query_rel vnames nsols =
  let
    val cmd = Path.named_root
    val query = case nsols of NONE => query_first | SOME n => query_firstn n 
    val prog = prelude ^ query query_rel vnames ^ write_program p
    val _ = tracing ("Generated prolog program:\n" ^ prog)
    val prolog_file = File.tmp_path (Path.basic "prolog_file")
    val _ = File.write prolog_file prog
    val (solution, _) = bash_output ("/usr/local/bin/swipl -f " ^ File.shell_path prolog_file)
    val _ = tracing ("Prolog returned solution(s):\n" ^ solution)
    val tss = parse_solutions solution
  in
    tss
  end

(* values command *)

fun restore_term ctxt constant_table (Var s, T) = Free (s, T)
  | restore_term ctxt constant_table (Number n, @{typ "int"}) = HOLogic.mk_number @{typ "int"} n
  | restore_term ctxt constant_table (Number n, _) = raise (Fail "unexpected type for number") 
  | restore_term ctxt constant_table (Cons s, T) = Const (restore_const constant_table s, T)
  | restore_term ctxt constant_table (AppF (f, args), T) =
    let
      val thy = ProofContext.theory_of ctxt
      val c = restore_const constant_table f
      val cT = Sign.the_const_type thy c
      val (argsT, resT) = strip_type cT
      val subst = Sign.typ_match thy (resT, T) Vartab.empty
      val argsT' = map (Envir.subst_type subst) argsT
    in
      list_comb (Const (c, Envir.subst_type subst cT),
        map (restore_term ctxt constant_table) (args ~~ argsT'))
    end

fun values ctxt soln t_compr =
  let
    val options = !options
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term ctxt t_compr);
    val (body, Ts, fp) = HOLogic.strip_psplits split;
    val output_names = Name.variant_list (Term.add_free_names body [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = rev (map2 (curry Free) output_names Ts)
    val body = subst_bounds (output_frees, body)
    val (pred as Const (name, T), all_args) =
      case strip_comb body of
        (Const (name, T), all_args) => (Const (name, T), all_args)
      | (head, _) => error ("Not a constant: " ^ Syntax.string_of_term ctxt head)
    val vnames =
      case try (map (fst o dest_Free)) all_args of
        SOME vs => vs
      | NONE => error ("Not only free variables in " ^ commas (map (Syntax.string_of_term ctxt) all_args))
    val _ = tracing "Generating prolog program..."
    val (p, constant_table) = generate options ctxt [name]
      |> (if #ensure_groundness options then add_ground_predicates ctxt else I)
    val _ = tracing "Running prolog program..."
    val tss = run p (translate_const constant_table name) (map first_upper vnames) soln
    val _ = tracing "Restoring terms..."
    val empty = Const("Orderings.bot_class.bot", fastype_of t_compr)
    fun mk_insert x S =
      Const (@{const_name "Set.insert"}, fastype_of x --> fastype_of S --> fastype_of S) $ x $ S 
    fun mk_set_compr in_insert [] xs =
       rev ((Free ("...", fastype_of t_compr)) ::
        (if null in_insert then xs else (fold mk_insert in_insert empty) :: xs))
      | mk_set_compr in_insert (t :: ts) xs =
        let
          val frees = Term.add_frees t []
        in
          if null frees then
            mk_set_compr (t :: in_insert) ts xs
          else
            let
              val uu as (uuN, uuT) = singleton (Variable.variant_frees ctxt [t]) ("uu", fastype_of t)
              val set_compr =
                HOLogic.mk_Collect (uuN, uuT, fold (fn (s, T) => fn t => HOLogic.mk_exists (s, T, t))
                  frees (HOLogic.mk_conj (HOLogic.mk_eq (Free uu, t), @{term "True"})))
            in
              mk_set_compr [] ts
                (set_compr :: (if null in_insert then xs else (fold mk_insert in_insert empty) :: xs))  
            end
        end
  in
      foldl1 (HOLogic.mk_binop @{const_name sup}) (mk_set_compr []
        (map (fn ts => HOLogic.mk_tuple (map (restore_term ctxt constant_table) (ts ~~ Ts))) tss) [])
  end

fun values_cmd print_modes soln raw_t state =
  let
    val ctxt = Toplevel.context_of state
    val t = Syntax.read_term ctxt raw_t
    val t' = values ctxt soln t
    val ty' = Term.type_of t'
    val ctxt' = Variable.auto_fixes t' ctxt
    val _ = tracing "Printing terms..."
    val p = Print_Mode.with_modes print_modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;


(* renewing the values command for Prolog queries *)

val opt_print_modes =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.xname --| Parse.$$$ ")")) [];

val _ = Outer_Syntax.improper_command "values" "enumerate and print comprehensions" Keyword.diag
  (opt_print_modes -- Scan.optional (Parse.nat >> SOME) NONE -- Parse.term
   >> (fn ((print_modes, soln), t) => Toplevel.keep
        (values_cmd print_modes soln t))); (*FIXME does not preserve the previous functionality*)

end;
