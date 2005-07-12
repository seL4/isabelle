(*  Title:      Pure/Tools/am_compiler.ML
    ID:         $Id$
    Author:     Steven Obua
*)

signature COMPILING_AM = 
sig
    include ABSTRACT_MACHINE

    datatype closure = CVar of int | CConst of int
		     | CApp of closure * closure | CAbs of closure | Closure of (closure list) * closure

    val set_compiled_rewriter : (term -> closure) -> unit
end

structure AM_Compiler :> COMPILING_AM = struct

datatype term = Var of int | Const of int | App of term * term | Abs of term

datatype pattern = PVar | PConst of int * (pattern list)

datatype closure = CVar of int | CConst of int
		 | CApp of closure * closure | CAbs of closure | Closure of (closure list) * closure

val compiled_rewriter = ref (NONE:(term -> closure)Option.option)

fun set_compiled_rewriter r = (compiled_rewriter := SOME r)

type program = (term -> term)

datatype stack = SEmpty | SAppL of closure * stack | SAppR of closure * stack | SAbs of stack

exception Compile of string;
exception Run of string;

fun clos_of_term (Var x) = CVar x
  | clos_of_term (Const c) = CConst c
  | clos_of_term (App (u, v)) = CApp (clos_of_term u, clos_of_term v)
  | clos_of_term (Abs u) = CAbs (clos_of_term u)

fun term_of_clos (CVar x) = Var x
  | term_of_clos (CConst c) = Const c
  | term_of_clos (CApp (u, v)) = App (term_of_clos u, term_of_clos v)
  | term_of_clos (CAbs u) = Abs (term_of_clos u)
  | term_of_clos (Closure (e, u)) = raise (Run "internal error: closure in normalized term found")

fun strip_closure args (CApp (a,b)) = strip_closure (b::args) a
  | strip_closure args x = (x, args)

(* Returns true iff at most 0 .. (free-1) occur unbound. therefore check_freevars 0 t iff t is closed *)
fun check_freevars free (Var x) = x < free
  | check_freevars free (Const c) = true
  | check_freevars free (App (u, v)) = check_freevars free u andalso check_freevars free v
  | check_freevars free (Abs m) = check_freevars (free+1) m

fun count_patternvars PVar = 1
  | count_patternvars (PConst (_, ps)) = List.foldl (fn (p, count) => (count_patternvars p)+count) 0 ps

fun print_rule (p, t) = 
    let	
	fun str x = Int.toString x		    
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
	val pattern = if List.exists Char.isSpace (String.explode pattern) then "("^pattern^")" else pattern
	
	fun print_term d (Var x) = (*if x < d then "Var "^(str x) else "x"^(str (n-(x-d)-1))*) "Var "^(str x)
	  | print_term d (Const c) = "c"^(str c)
	  | print_term d (App (a,b)) = "App ("^(print_term d a)^", "^(print_term d b)^")"
	  | print_term d (Abs c) = "Abs ("^(print_term (d+1) c)^")"

	fun listvars n = if n = 0 then "x0" else "x"^(str n)^", "^(listvars (n-1))

	val term = print_term 0 t
	val term = if n > 0 then "Closure (["^(listvars (n-1))^"], "^term^")" else "Closure ([], "^term^")"
			   
    in
	"lookup stack "^pattern^" = weak stack ("^term^")"
    end

fun remove_dups (c::cs) = 
    let val cs = remove_dups cs in
	if (List.exists (fn x => x=c) cs) then cs else c::cs
    end
  | remove_dups [] = []

fun constants_of PVar = []
  | constants_of (PConst (c, ps)) = c::(List.concat (map constants_of ps))

fun constants_of_term (Var _) = []
  | constants_of_term (Abs m) = constants_of_term m
  | constants_of_term (App (a,b)) = (constants_of_term a)@(constants_of_term b)
  | constants_of_term (Const c) = [c]
    
fun load_rules sname name prog = 
    let
	val buffer = ref ""
	fun write s = (buffer := (!buffer)^s)
	fun writeln s = (write s; write "\n")
	fun writelist [] = ()
	  | writelist (s::ss) = (writeln s; writelist ss)
	fun str i = Int.toString i
	val _ = writelist [
		"structure "^name^" = struct",
		"",
		"datatype term = App of term * term | Abs of term | Var of int | Const of int | Closure of term list * term"]
	val constants = remove_dups (List.concat (map (fn (p, r) => ((constants_of p)@(constants_of_term r))) prog))
	val _ = map (fn x => write (" | c"^(str x))) constants
	val _ = writelist [
		"",
		"datatype stack = SEmpty | SAppL of term * stack | SAppR of term * stack | SAbs of stack",
		""]
	val _ = (case prog of
		    r::rs => (writeln ("fun "^(print_rule r)); 
			      map (fn r => writeln("  | "^(print_rule r))) rs; 
			      writeln ("  | lookup stack clos = weak_last stack clos"); ())								
		  | [] => (writeln "fun lookup stack clos = weak_last stack clos"))
	val _ = writelist [
		"and weak stack (Closure (e, App (a, b))) = weak (SAppL (Closure (e, b), stack)) (Closure (e, a))",
		"  | weak (SAppL (b, stack)) (Closure (e, Abs m)) =  weak stack (Closure (b::e, m))",
		"  | weak stack (clos as Closure (_, Abs _)) = weak_last stack clos",
		"  | weak stack (Closure (e, Var n)) = weak stack (List.nth (e, n) handle Subscript => (Var (n-(length e))))",
		"  | weak stack (Closure (e, c)) = weak stack c",
		"  | weak stack clos = lookup stack clos",
		"and weak_last (SAppR (a, stack)) b = weak stack (App(a, b))",
		"  | weak_last (SAppL (b, stack)) a = weak (SAppR (a, stack)) b",
		"  | weak_last stack c = (stack, c)",
		"",
		"fun lift n (v as Var m) = if m < n then v else Var (m+1)",
		"  | lift n (Abs t) = Abs (lift (n+1) t)",
		"  | lift n (App (a,b)) = App (lift n a, lift n b)",
		"  | lift n (Closure (e, a)) = Closure (lift_env n e, lift (n+(length e)) a)",
		"  | lift n c = c",
		"and lift_env n e = map (lift n) e",
		"",
		"fun strong stack (Closure (e, Abs m)) = ",
		"    let",
		"      val (stack', wnf) = weak SEmpty (Closure ((Var 0)::(lift_env 0 e), m))",
		"    in",
		"      case stack' of",
		"           SEmpty => strong (SAbs stack) wnf",
		"         | _ => raise ("^sname^".Run \"internal error in strong: weak failed\")",
		"    end",
		"  | strong stack (clos as (App (u, v))) = strong (SAppL (v, stack)) u",
		"  | strong stack clos = strong_last stack clos",
		"and strong_last (SAbs stack) m = strong stack (Abs m)",
		"  | strong_last (SAppL (b, stack)) a = strong (SAppR (a, stack)) b",
		"  | strong_last (SAppR (a, stack)) b = strong_last stack (App (a, b))",
		"  | strong_last stack clos = (stack, clos)",
		""]
	
	val ic = "(case c of "^(String.concat (map (fn c => (str c)^" => c"^(str c)^" | ") constants))^" _ => Const c)"						  	
	val _ = writelist [
		"fun importTerm ("^sname^".Var x) = Var x",
		"  | importTerm ("^sname^".Const c) =  "^ic,
		"  | importTerm ("^sname^".App (a, b)) = App (importTerm a, importTerm b)",
		"  | importTerm ("^sname^".Abs m) = Abs (importTerm m)",
		""]

	fun ec c = "  | exportTerm c"^(str c)^" = "^sname^".CConst "^(str c)
	val _ = writelist [
		"fun exportTerm (Var x) = "^sname^".CVar x",
		"  | exportTerm (Const c) = "^sname^".CConst c",
		"  | exportTerm (App (a,b)) = "^sname^".CApp (exportTerm a, exportTerm b)",
		"  | exportTerm (Abs m) = "^sname^".CAbs (exportTerm m)",
		"  | exportTerm (Closure (closlist, clos)) = "^sname^".Closure (map exportTerm closlist, exportTerm clos)"]
	val _ = writelist (map ec constants)
		
	val _ = writelist [
		"",
		"fun rewrite t = ",
		"    let",
		"      val (stack, wnf) = weak SEmpty (Closure ([], importTerm t))",
		"    in",
		"      case stack of ",
		"           SEmpty => (case strong SEmpty wnf of",
		"                          (SEmpty, snf) => exportTerm snf",
		"                        | _ => raise ("^sname^".Run \"internal error in rewrite: strong failed\"))",
		"         | _ => (raise ("^sname^".Run \"internal error in rewrite: weak failed\"))",
		"    end",
		"",
		"val _ = "^sname^".set_compiled_rewriter rewrite",
		"",
		"end;"]

	val _ = 
	    let
		val fout = TextIO.openOut "gen_code.ML"
		val _ = TextIO.output (fout, !buffer)
		val _  = TextIO.closeOut fout
	    in
		()
	    end
	    
	val dummy = (fn s => ())		    
    in
	compiled_rewriter := NONE;	
	use_text (dummy, dummy) false (!buffer);
	case !compiled_rewriter of 
	    NONE => raise (Compile "cannot communicate with compiled function")
	  | SOME r => (compiled_rewriter := NONE; fn t => term_of_clos (r t))
    end	

fun compile eqs = 
    let
	val _ = map (fn (p, r) => 
                  (check_freevars (count_patternvars p) r; 
                   case p of PVar => raise (Compile "pattern reduces to a variable") | _ => ())) eqs
    in
	load_rules "AM_Compiler" "AM_compiled_code" eqs
    end	

fun run prog t = (prog t)
			 	  
end

structure AbstractMachine = AM_Compiler
