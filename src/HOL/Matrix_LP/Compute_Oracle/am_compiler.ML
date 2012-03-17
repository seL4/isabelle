(*  Title:      HOL/Matrix/Compute_Oracle/am_compiler.ML
    Author:     Steven Obua
*)

signature COMPILING_AM = 
sig
  include ABSTRACT_MACHINE

  val set_compiled_rewriter : (term -> term) -> unit
  val list_nth : 'a list * int -> 'a
  val list_map : ('a -> 'b) -> 'a list -> 'b list
end

structure AM_Compiler : COMPILING_AM = struct

val list_nth = List.nth;
val list_map = map;

open AbstractMachine;

val compiled_rewriter = Unsynchronized.ref (NONE:(term -> term)Option.option)

fun set_compiled_rewriter r = (compiled_rewriter := SOME r)

type program = (term -> term)

fun count_patternvars PVar = 1
  | count_patternvars (PConst (_, ps)) =
      List.foldl (fn (p, count) => (count_patternvars p)+count) 0 ps

fun print_rule (p, t) = 
    let
        fun str x = string_of_int x
        fun print_pattern n PVar = (n+1, "x"^(str n))
          | print_pattern n (PConst (c, [])) = (n, "c"^(str c))
          | print_pattern n (PConst (c, args)) = 
            let
                val h = print_pattern n (PConst (c,[]))
            in
                print_pattern_list h args
            end
        and print_pattern_list r [] = r
          | print_pattern_list (n, p) (t::ts) = 
            let
                val (n, t) = print_pattern n t
            in
                print_pattern_list (n, "App ("^p^", "^t^")") ts
            end

        val (n, pattern) = print_pattern 0 p
        val pattern =
            if exists_string Symbol.is_ascii_blank pattern then "(" ^ pattern ^")"
            else pattern
        
        fun print_term d (Var x) = "Var " ^ str x
          | print_term d (Const c) = "c" ^ str c
          | print_term d (App (a,b)) = "App (" ^ print_term d a ^ ", " ^ print_term d b ^ ")"
          | print_term d (Abs c) = "Abs (" ^ print_term (d + 1) c ^ ")"
          | print_term d (Computed c) = print_term d c

        fun listvars n = if n = 0 then "x0" else "x"^(str n)^", "^(listvars (n-1))

        val term = print_term 0 t
        val term =
            if n > 0 then "Closure (["^(listvars (n-1))^"], "^term^")"
            else "Closure ([], "^term^")"
                           
    in
        "  | weak_reduce (false, stack, "^pattern^") = Continue (false, stack, "^term^")"
    end

fun constants_of PVar = []
  | constants_of (PConst (c, ps)) = c :: maps constants_of ps

fun constants_of_term (Var _) = []
  | constants_of_term (Abs m) = constants_of_term m
  | constants_of_term (App (a,b)) = (constants_of_term a)@(constants_of_term b)
  | constants_of_term (Const c) = [c]
  | constants_of_term (Computed c) = constants_of_term c
    
fun load_rules sname name prog = 
    let
        val buffer = Unsynchronized.ref ""
        fun write s = (buffer := (!buffer)^s)
        fun writeln s = (write s; write "\n")
        fun writelist [] = ()
          | writelist (s::ss) = (writeln s; writelist ss)
        fun str i = string_of_int i
        val _ = writelist [
                "structure "^name^" = struct",
                "",
                "datatype term = Dummy | App of term * term | Abs of term | Var of int | Const of int | Closure of term list * term"]
        val constants = distinct (op =) (maps (fn (p, r) => ((constants_of p)@(constants_of_term r))) prog)
        val _ = map (fn x => write (" | c"^(str x))) constants
        val _ = writelist [
                "",
                "datatype stack = SEmpty | SAppL of term * stack | SAppR of term * stack | SAbs of stack",
                "",
                "type state = bool * stack * term",
                "",
                "datatype loopstate = Continue of state | Stop of stack * term",
                "",
                "fun proj_C (Continue s) = s",
                "  | proj_C _ = raise Match",
                "",
                "fun proj_S (Stop s) = s",
                "  | proj_S _ = raise Match",
                "",
                "fun cont (Continue _) = true",
                "  | cont _ = false",
                "",
                "fun do_reduction reduce p =",
                "    let",
                "       val s = Unsynchronized.ref (Continue p)",
                "       val _ = while cont (!s) do (s := reduce (proj_C (!s)))",
                "   in",
                "       proj_S (!s)",
                "   end",
                ""]

        val _ = writelist [
                "fun weak_reduce (false, stack, Closure (e, App (a, b))) = Continue (false, SAppL (Closure (e, b), stack), Closure (e, a))",
                "  | weak_reduce (false, SAppL (b, stack), Closure (e, Abs m)) = Continue (false, stack, Closure (b::e, m))",
                "  | weak_reduce (false, stack, c as Closure (e, Abs m)) = Continue (true, stack, c)",
                "  | weak_reduce (false, stack, Closure (e, Var n)) = Continue (false, stack, case "^sname^".list_nth (e, n) of Dummy => Var n | r => r)",
                "  | weak_reduce (false, stack, Closure (e, c)) = Continue (false, stack, c)"]
        val _ = writelist (map print_rule prog)
        val _ = writelist [
                "  | weak_reduce (false, stack, clos) = Continue (true, stack, clos)",
                "  | weak_reduce (true, SAppR (a, stack), b) = Continue (false, stack, App (a,b))",
                "  | weak_reduce (true, s as (SAppL (b, stack)), a) = Continue (false, SAppR (a, stack), b)",
                "  | weak_reduce (true, stack, c) = Stop (stack, c)",
                "",
                "fun strong_reduce (false, stack, Closure (e, Abs m)) =",
                "    let",
                "        val (stack', wnf) = do_reduction weak_reduce (false, SEmpty, Closure (Dummy::e, m))",
                "    in",
                "        case stack' of",
                "            SEmpty => Continue (false, SAbs stack, wnf)",
                "          | _ => raise ("^sname^".Run \"internal error in strong: weak failed\")",
                "    end",              
                "  | strong_reduce (false, stack, clos as (App (u, v))) = Continue (false, SAppL (v, stack), u)",
                "  | strong_reduce (false, stack, clos) = Continue (true, stack, clos)",
                "  | strong_reduce (true, SAbs stack, m) = Continue (false, stack, Abs m)",
                "  | strong_reduce (true, SAppL (b, stack), a) = Continue (false, SAppR (a, stack), b)",
                "  | strong_reduce (true, SAppR (a, stack), b) = Continue (true, stack, App (a, b))",
                "  | strong_reduce (true, stack, clos) = Stop (stack, clos)",
                ""]
        
        val ic = "(case c of "^(implode (map (fn c => (str c)^" => c"^(str c)^" | ") constants))^" _ => Const c)"                                                       
        val _ = writelist [
                "fun importTerm ("^sname^".Var x) = Var x",
                "  | importTerm ("^sname^".Const c) =  "^ic,
                "  | importTerm ("^sname^".App (a, b)) = App (importTerm a, importTerm b)",
                "  | importTerm ("^sname^".Abs m) = Abs (importTerm m)",
                ""]

        fun ec c = "  | exportTerm c"^(str c)^" = "^sname^".Const "^(str c)
        val _ = writelist [
                "fun exportTerm (Var x) = "^sname^".Var x",
                "  | exportTerm (Const c) = "^sname^".Const c",
                "  | exportTerm (App (a,b)) = "^sname^".App (exportTerm a, exportTerm b)",
                "  | exportTerm (Abs m) = "^sname^".Abs (exportTerm m)",
                "  | exportTerm (Closure (closlist, clos)) = raise ("^sname^".Run \"internal error, cannot export Closure\")",
                "  | exportTerm Dummy = raise ("^sname^".Run \"internal error, cannot export Dummy\")"]
        val _ = writelist (map ec constants)
                
        val _ = writelist [
                "",
                "fun rewrite t = ",
                "    let",
                "      val (stack, wnf) = do_reduction weak_reduce (false, SEmpty, Closure ([], importTerm t))",
                "    in",
                "      case stack of ",
                "           SEmpty => (case do_reduction strong_reduce (false, SEmpty, wnf) of",
                "                          (SEmpty, snf) => exportTerm snf",
                "                        | _ => raise ("^sname^".Run \"internal error in rewrite: strong failed\"))",
                "         | _ => (raise ("^sname^".Run \"internal error in rewrite: weak failed\"))",
                "    end",
                "",
                "val _ = "^sname^".set_compiled_rewriter rewrite",
                "",
                "end;"]

    in
        compiled_rewriter := NONE;      
        use_text ML_Env.local_context (1, "") false (!buffer);
        case !compiled_rewriter of 
            NONE => raise (Compile "cannot communicate with compiled function")
          | SOME r => (compiled_rewriter := NONE; r)
    end 

fun compile eqs = 
    let
        val _ = if exists (fn (a,_,_) => not (null a)) eqs then raise Compile ("cannot deal with guards") else ()
        val eqs = map (fn (_,b,c) => (b,c)) eqs
        fun check (p, r) = if check_freevars (count_patternvars p) r then () else raise Compile ("unbound variables in rule") 
        val _ = map (fn (p, r) => 
                  (check (p, r); 
                   case p of PVar => raise (Compile "pattern is just a variable") | _ => ())) eqs
    in
        load_rules "AM_Compiler" "AM_compiled_code" eqs
    end 

fun run prog t = prog t

end

