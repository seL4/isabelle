(*  Title:      Tools/Compute_Oracle/am_interpreter.ML
    ID:         $Id$
    Author:     Steven Obua
*)

structure AM_Interpreter : ABSTRACT_MACHINE = struct

open AbstractMachine;

datatype closure = CDummy | CVar of int | CConst of int
                 | CApp of closure * closure | CAbs of closure
                 | Closure of (closure list) * closure

structure prog_struct = TableFun(type key = int*int val ord = prod_ord int_ord int_ord);

datatype program = Program of ((pattern * closure) list) prog_struct.table

datatype stack = SEmpty | SAppL of closure * stack | SAppR of closure * stack | SAbs of stack

fun clos_of_term (Var x) = CVar x
  | clos_of_term (Const c) = CConst c
  | clos_of_term (App (u, v)) = CApp (clos_of_term u, clos_of_term v)
  | clos_of_term (Abs u) = CAbs (clos_of_term u)

fun term_of_clos (CVar x) = Var x
  | term_of_clos (CConst c) = Const c
  | term_of_clos (CApp (u, v)) = App (term_of_clos u, term_of_clos v)
  | term_of_clos (CAbs u) = Abs (term_of_clos u)
  | term_of_clos (Closure (e, u)) = raise (Run "internal error: closure in normalized term found")
  | term_of_clos CDummy = raise (Run "internal error: dummy in normalized term found")

fun strip_closure args (CApp (a,b)) = strip_closure (b::args) a
  | strip_closure args x = (x, args)

fun len_head_of_closure n (CApp (a,b)) = len_head_of_closure (n+1) a
  | len_head_of_closure n x = (n, x)


(* earlier occurrence of PVar corresponds to higher de Bruijn index *)
fun pattern_match args PVar clos = SOME (clos::args)
  | pattern_match args (PConst (c, patterns)) clos =
    let
        val (f, closargs) = strip_closure [] clos
    in
        case f of
            CConst d =>
            if c = d then
                pattern_match_list args patterns closargs
            else
                NONE
          | _ => NONE
    end
and pattern_match_list args [] [] = SOME args
  | pattern_match_list args (p::ps) (c::cs) =
    (case pattern_match args p c of
        NONE => NONE
      | SOME args => pattern_match_list args ps cs)
  | pattern_match_list _ _ _ = NONE

fun count_patternvars PVar = 1
  | count_patternvars (PConst (_, ps)) = List.foldl (fn (p, count) => (count_patternvars p)+count) 0 ps

fun pattern_key (PConst (c, ps)) = (c, length ps)
  | pattern_key _ = raise (Compile "pattern reduces to variable")

(*Returns true iff at most 0 .. (free-1) occur unbound. therefore
  check_freevars 0 t iff t is closed*)
fun check_freevars free (Var x) = x < free
  | check_freevars free (Const c) = true
  | check_freevars free (App (u, v)) = check_freevars free u andalso check_freevars free v
  | check_freevars free (Abs m) = check_freevars (free+1) m

fun compile eqs =
    let
	val _ = if exists (fn (a,b,c) => not (null a)) eqs then raise Compile ("cannot deal with guards") else ()
	val eqs = map (fn (a,b,c) => (b,c)) eqs
	fun check (p, r) = if check_freevars (count_patternvars p) r then () else raise Compile ("unbound variables in rule") 
        val eqs = map (fn (p, r) => (check (p,r); (pattern_key p, (p, clos_of_term r)))) eqs
	fun merge (k, a) table = prog_struct.update (k, case prog_struct.lookup table k of NONE => [a] | SOME l => a::l) table
	val p = fold merge eqs prog_struct.empty 
    in
        Program p
    end

fun match_rules n [] clos = NONE
  | match_rules n ((p,eq)::rs) clos =
    case pattern_match [] p clos of
        NONE => match_rules (n+1) rs clos
      | SOME args => SOME (Closure (args, eq))

fun match_closure (Program prog) clos =
    case len_head_of_closure 0 clos of
        (len, CConst c) =>
        (case prog_struct.lookup prog (c, len) of
            NONE => NONE
          | SOME rules => match_rules 0 rules clos)
      | _ => NONE


type state = bool * program * stack * closure

datatype loopstate = Continue of state | Stop of stack * closure

fun proj_C (Continue s) = s
  | proj_C _ = raise Match

fun proj_S (Stop s) = s
  | proj_S _ = raise Match

fun cont (Continue _) = true
  | cont _ = false

fun do_reduction reduce p =
    let
	val s = ref (Continue p)
	val _ = while cont (!s) do (s := reduce (proj_C (!s)))
    in
	proj_S (!s)
    end

fun weak_reduce (false, prog, stack, Closure (e, CApp (a, b))) = Continue (false, prog, SAppL (Closure (e, b), stack), Closure (e, a))
  | weak_reduce (false, prog, SAppL (b, stack), Closure (e, CAbs m)) = Continue (false, prog, stack, Closure (b::e, m))
  | weak_reduce (false, prog, stack, Closure (e, CVar n)) = Continue (false, prog, stack, case List.nth (e, n) of CDummy => CVar n | r => r)
  | weak_reduce (false, prog, stack, Closure (e, c as CConst _)) = Continue (false, prog, stack, c)
  | weak_reduce (false, prog, stack, clos) =
    (case match_closure prog clos of
         NONE => Continue (true, prog, stack, clos)
       | SOME r => Continue (false, prog, stack, r))
  | weak_reduce (true, prog, SAppR (a, stack), b) = Continue (false, prog, stack, CApp (a,b))
  | weak_reduce (true, prog, s as (SAppL (b, stack)), a) = Continue (false, prog, SAppR (a, stack), b)
  | weak_reduce (true, prog, stack, c) = Stop (stack, c)

fun strong_reduce (false, prog, stack, Closure (e, CAbs m)) =
    let
        val (stack', wnf) = do_reduction weak_reduce (false, prog, SEmpty, Closure (CDummy::e, m))
    in
        case stack' of
            SEmpty => Continue (false, prog, SAbs stack, wnf)
          | _ => raise (Run "internal error in strong: weak failed")
    end
  | strong_reduce (false, prog, stack, clos as (CApp (u, v))) = Continue (false, prog, SAppL (v, stack), u)
  | strong_reduce (false, prog, stack, clos) = Continue (true, prog, stack, clos)
  | strong_reduce (true, prog, SAbs stack, m) = Continue (false, prog, stack, CAbs m)
  | strong_reduce (true, prog, SAppL (b, stack), a) = Continue (false, prog, SAppR (a, stack), b)
  | strong_reduce (true, prog, SAppR (a, stack), b) = Continue (true, prog, stack, CApp (a, b))
  | strong_reduce (true, prog, stack, clos) = Stop (stack, clos)

fun run prog t =
    let
        val (stack, wnf) = do_reduction weak_reduce (false, prog, SEmpty, Closure ([], clos_of_term t))
    in
        case stack of
            SEmpty => (case do_reduction strong_reduce (false, prog, SEmpty, wnf) of
                           (SEmpty, snf) => term_of_clos snf
                         | _ => raise (Run "internal error in run: strong failed"))
          | _ => raise (Run "internal error in run: weak failed")
    end

fun discard p = ()

end
