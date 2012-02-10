(*  Title:      HOL/Matrix/Compute_Oracle/am_interpreter.ML
    Author:     Steven Obua
*)

signature AM_BARRAS = 
sig
  include ABSTRACT_MACHINE
  val max_reductions : int option Unsynchronized.ref
end

structure AM_Interpreter : AM_BARRAS = struct

open AbstractMachine;

datatype closure = CDummy | CVar of int | CConst of int
                 | CApp of closure * closure | CAbs of closure
                 | Closure of (closure list) * closure

structure prog_struct = Table(type key = int*int val ord = prod_ord int_ord int_ord);

datatype program = Program of ((pattern * closure * (closure*closure) list) list) prog_struct.table

datatype stack = SEmpty | SAppL of closure * stack | SAppR of closure * stack | SAbs of stack

fun clos_of_term (Var x) = CVar x
  | clos_of_term (Const c) = CConst c
  | clos_of_term (App (u, v)) = CApp (clos_of_term u, clos_of_term v)
  | clos_of_term (Abs u) = CAbs (clos_of_term u)
  | clos_of_term (Computed t) = clos_of_term t

fun term_of_clos (CVar x) = Var x
  | term_of_clos (CConst c) = Const c
  | term_of_clos (CApp (u, v)) = App (term_of_clos u, term_of_clos v)
  | term_of_clos (CAbs u) = Abs (term_of_clos u)
  | term_of_clos (Closure _) = raise (Run "internal error: closure in normalized term found")
  | term_of_clos CDummy = raise (Run "internal error: dummy in normalized term found")

fun resolve_closure closures (CVar x) = (case nth closures x of CDummy => CVar x | r => r)
  | resolve_closure closures (CConst c) = CConst c
  | resolve_closure closures (CApp (u, v)) = CApp (resolve_closure closures u, resolve_closure closures v)
  | resolve_closure closures (CAbs u) = CAbs (resolve_closure (CDummy::closures) u)
  | resolve_closure closures (CDummy) = raise (Run "internal error: resolve_closure applied to CDummy")
  | resolve_closure closures (Closure (e, u)) = resolve_closure e u

fun resolve_closure' c = resolve_closure [] c

fun resolve_stack tm SEmpty = tm
  | resolve_stack tm (SAppL (c, s)) = resolve_stack (CApp (tm, resolve_closure' c)) s
  | resolve_stack tm (SAppR (c, s)) = resolve_stack (CApp (resolve_closure' c, tm)) s
  | resolve_stack tm (SAbs s) = resolve_stack (CAbs tm) s

fun resolve (stack, closure) = 
    let
        val _ = writeln "start resolving"
        val t = resolve_stack (resolve_closure' closure) stack
        val _ = writeln "finished resolving"
    in
        t
    end

fun strip_closure args (CApp (a,b)) = strip_closure (b::args) a
  | strip_closure args x = (x, args)

fun len_head_of_closure n (CApp (a, _)) = len_head_of_closure (n+1) a
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
  | check_freevars free (Const _) = true
  | check_freevars free (App (u, v)) = check_freevars free u andalso check_freevars free v
  | check_freevars free (Abs m) = check_freevars (free+1) m
  | check_freevars free (Computed t) = check_freevars free t

fun compile eqs =
    let
        fun check p r = if check_freevars p r then () else raise Compile ("unbound variables in rule") 
        fun check_guard p (Guard (a,b)) = (check p a; check p b) 
        fun clos_of_guard (Guard (a,b)) = (clos_of_term a, clos_of_term b)
        val eqs = map (fn (guards, p, r) => let val pcount = count_patternvars p val _ = map (check_guard pcount) (guards) val _ = check pcount r in 
                                              (pattern_key p, (p, clos_of_term r, map clos_of_guard guards)) end) eqs
        fun merge (k, a) table = prog_struct.update (k, case prog_struct.lookup table k of NONE => [a] | SOME l => a::l) table
        val p = fold merge eqs prog_struct.empty 
    in
        Program p
    end


type state = bool * program * stack * closure

datatype loopstate = Continue of state | Stop of stack * closure

fun proj_C (Continue s) = s
  | proj_C _ = raise Match

exception InterruptedExecution of stack * closure

fun proj_S (Stop s) = s
  | proj_S (Continue (_,_,s,c)) = (s,c)

fun cont (Continue _) = true
  | cont _ = false

val max_reductions = Unsynchronized.ref (NONE : int option)

fun do_reduction reduce p =
    let
        val s = Unsynchronized.ref (Continue p)
        val counter = Unsynchronized.ref 0
        val _ = case !max_reductions of 
                    NONE => while cont (!s) do (s := reduce (proj_C (!s)))
                  | SOME m => while cont (!s) andalso (!counter < m) do (s := reduce (proj_C (!s)); counter := (!counter) + 1)
    in
        case !max_reductions of
            SOME m => if !counter >= m then raise InterruptedExecution (proj_S (!s)) else proj_S (!s)
          | NONE => proj_S (!s)
    end

fun match_rules prog n [] clos = NONE
  | match_rules prog n ((p,eq,guards)::rs) clos =
    case pattern_match [] p clos of
        NONE => match_rules prog (n+1) rs clos
      | SOME args => if forall (guard_checks prog args) guards then SOME (Closure (args, eq)) else match_rules prog (n+1) rs clos
and guard_checks prog args (a,b) = (simp prog (Closure (args, a)) = simp prog (Closure (args, b)))
and match_closure (p as (Program prog)) clos =
    case len_head_of_closure 0 clos of
        (len, CConst c) =>
        (case prog_struct.lookup prog (c, len) of
            NONE => NONE
          | SOME rules => match_rules p 0 rules clos)
      | _ => NONE

and weak_reduce (false, prog, stack, Closure (e, CApp (a, b))) = Continue (false, prog, SAppL (Closure (e, b), stack), Closure (e, a))
  | weak_reduce (false, prog, SAppL (b, stack), Closure (e, CAbs m)) = Continue (false, prog, stack, Closure (b::e, m))
  | weak_reduce (false, prog, stack, Closure (e, CVar n)) = Continue (false, prog, stack, case nth e n of CDummy => CVar n | r => r)
  | weak_reduce (false, prog, stack, Closure (_, c as CConst _)) = Continue (false, prog, stack, c)
  | weak_reduce (false, prog, stack, clos) =
    (case match_closure prog clos of
         NONE => Continue (true, prog, stack, clos)
       | SOME r => Continue (false, prog, stack, r))
  | weak_reduce (true, prog, SAppR (a, stack), b) = Continue (false, prog, stack, CApp (a,b))
  | weak_reduce (true, prog, SAppL (b, stack), a) = Continue (false, prog, SAppR (a, stack), b)
  | weak_reduce (true, prog, stack, c) = Stop (stack, c)

and strong_reduce (false, prog, stack, Closure (e, CAbs m)) =
    (let
         val (stack', wnf) = do_reduction weak_reduce (false, prog, SEmpty, Closure (CDummy::e, m))
     in
         case stack' of
             SEmpty => Continue (false, prog, SAbs stack, wnf)
           | _ => raise (Run "internal error in strong: weak failed")
     end handle InterruptedExecution state => raise InterruptedExecution (stack, resolve state))
  | strong_reduce (false, prog, stack, CApp (u, v)) = Continue (false, prog, SAppL (v, stack), u)
  | strong_reduce (false, prog, stack, clos) = Continue (true, prog, stack, clos)
  | strong_reduce (true, prog, SAbs stack, m) = Continue (false, prog, stack, CAbs m)
  | strong_reduce (true, prog, SAppL (b, stack), a) = Continue (false, prog, SAppR (a, stack), b)
  | strong_reduce (true, prog, SAppR (a, stack), b) = Continue (true, prog, stack, CApp (a, b))
  | strong_reduce (true, prog, stack, clos) = Stop (stack, clos)

and simp prog t =
    (let
         val (stack, wnf) = do_reduction weak_reduce (false, prog, SEmpty, t)
     in
         case stack of
             SEmpty => (case do_reduction strong_reduce (false, prog, SEmpty, wnf) of
                            (SEmpty, snf) => snf
                          | _ => raise (Run "internal error in run: strong failed"))
           | _ => raise (Run "internal error in run: weak failed")
     end handle InterruptedExecution state => resolve state)


fun run prog t =
    (let
         val (stack, wnf) = do_reduction weak_reduce (false, prog, SEmpty, Closure ([], clos_of_term t))
     in
         case stack of
             SEmpty => (case do_reduction strong_reduce (false, prog, SEmpty, wnf) of
                            (SEmpty, snf) => term_of_clos snf
                          | _ => raise (Run "internal error in run: strong failed"))
           | _ => raise (Run "internal error in run: weak failed")
     end handle InterruptedExecution state => term_of_clos (resolve state))

end
