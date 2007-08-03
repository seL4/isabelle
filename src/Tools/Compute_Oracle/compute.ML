(*  Title:      Pure/Tools/compute.ML
    ID:         $Id$
    Author:     Steven Obua
*)

signature COMPUTE = sig

    type computer

    datatype machine = BARRAS | BARRAS_COMPILED | HASKELL | SML

    exception Make of string
    val make : machine -> theory -> thm list -> computer

    exception Compute of string
    val compute : computer -> (int -> string) -> cterm -> term
    val theory_of : computer -> theory
    val hyps_of : computer -> term list
    val shyps_of : computer -> sort list

    val rewrite_param : computer -> (int -> string) -> cterm -> thm
    val rewrite : computer -> cterm -> thm

    val discard : computer -> unit

    val setup : theory -> theory

end

structure Compute :> COMPUTE = struct

datatype machine = BARRAS | BARRAS_COMPILED | HASKELL | SML	 

(* Terms are mapped to integer codes *)
structure Encode :> 
sig
    type encoding
    val empty : encoding
    val insert : term -> encoding -> int * encoding
    val lookup_code : term -> encoding -> int option
    val lookup_term : int -> encoding -> term option					
    val remove_code : int -> encoding -> encoding
    val remove_term : term -> encoding -> encoding
    val fold : ((term * int) -> 'a -> 'a) -> encoding -> 'a -> 'a    
end 
= 
struct

type encoding = int * (int Termtab.table) * (term Inttab.table)

val empty = (0, Termtab.empty, Inttab.empty)

fun insert t (e as (count, term2int, int2term)) = 
    (case Termtab.lookup term2int t of
	 NONE => (count, (count+1, Termtab.update_new (t, count) term2int, Inttab.update_new (count, t) int2term))
       | SOME code => (code, e))

fun lookup_code t (_, term2int, _) = Termtab.lookup term2int t

fun lookup_term c (_, _, int2term) = Inttab.lookup int2term c

fun remove_code c (e as (count, term2int, int2term)) = 
    (case lookup_term c e of NONE => e | SOME t => (count, Termtab.delete t term2int, Inttab.delete c int2term))

fun remove_term t (e as (count, term2int, int2term)) = 
    (case lookup_code t e of NONE => e | SOME c => (count, Termtab.delete t term2int, Inttab.delete c int2term))

fun fold f (_, term2int, _) = Termtab.fold f term2int 

end


exception Make of string;
exception Compute of string;

local
    fun make_constant t ty encoding = 
	let 
	    val (code, encoding) = Encode.insert t encoding 
	in 
	    (encoding, AbstractMachine.Const code)
	end
in

fun remove_types encoding t =
    case t of 
	Var (_, ty) => make_constant t ty encoding
      | Free (_, ty) => make_constant t ty encoding
      | Const (_, ty) => make_constant t ty encoding
      | Abs (_, ty, t') => 
	let val (encoding, t'') = remove_types encoding t' in
	    (encoding, AbstractMachine.Abs t'')
	end
      | a $ b => 
	let
	    val (encoding, a) = remove_types encoding a
	    val (encoding, b) = remove_types encoding b
	in
	    (encoding, AbstractMachine.App (a,b))
	end
      | Bound b => (encoding, AbstractMachine.Var b)
end
    
local
    fun type_of (Free (_, ty)) = ty
      | type_of (Const (_, ty)) = ty
      | type_of (Var (_, ty)) = ty
      | type_of _ = sys_error "infer_types: type_of error"
in
fun infer_types naming encoding =
    let
        fun infer_types _ bounds _ (AbstractMachine.Var v) = (Bound v, List.nth (bounds, v))
	  | infer_types _ bounds _ (AbstractMachine.Const code) = 
	    let
		val c = the (Encode.lookup_term code encoding)
	    in
		(c, type_of c)
	    end
	  | infer_types level bounds _ (AbstractMachine.App (a, b)) = 
	    let
		val (a, aty) = infer_types level bounds NONE a
		val (adom, arange) =
                    case aty of
                        Type ("fun", [dom, range]) => (dom, range)
                      | _ => sys_error "infer_types: function type expected"
                val (b, bty) = infer_types level bounds (SOME adom) b
	    in
		(a $ b, arange)
	    end
          | infer_types level bounds (SOME (ty as Type ("fun", [dom, range]))) (AbstractMachine.Abs m) =
            let
                val (m, _) = infer_types (level+1) (dom::bounds) (SOME range) m
            in
                (Abs (naming level, dom, m), ty)
            end
          | infer_types _ _ NONE (AbstractMachine.Abs m) = sys_error "infer_types: cannot infer type of abstraction"

        fun infer ty term =
            let
                val (term', _) = infer_types 0 [] (SOME ty) term
            in
                term'
            end
    in
        infer
    end
end

datatype prog = 
	 ProgBarras of AM_Interpreter.program 
       | ProgBarrasC of AM_Compiler.program
       | ProgHaskell of AM_GHC.program
       | ProgSML of AM_SML.program

structure Sorttab = TableFun(type key = sort val ord = Term.sort_ord)

datatype computer = Computer of theory_ref * Encode.encoding * term list * unit Sorttab.table * prog

datatype cthm = ComputeThm of term list * sort list * term

fun thm2cthm th = 
    let
	val {hyps, prop, tpairs, shyps, ...} = Thm.rep_thm th
	val _ = if not (null tpairs) then raise Make "theorems may not contain tpairs" else ()
    in
	ComputeThm (hyps, shyps, prop)
    end

fun make machine thy raw_ths =
    let
	fun transfer (x:thm) = Thm.transfer thy x
	val ths = map (thm2cthm o Thm.strip_shyps o transfer) raw_ths

        fun thm2rule (encoding, hyptable, shyptable) th =
            let
		val (ComputeThm (hyps, shyps, prop)) = th
		val hyptable = fold (fn h => Termtab.update (h, ())) hyps hyptable
		val shyptable = fold (fn sh => Sorttab.update (sh, ())) shyps shyptable
		val (prems, prop) = (Logic.strip_imp_prems prop, Logic.strip_imp_concl prop)
                val (a, b) = Logic.dest_equals prop
                  handle TERM _ => raise (Make "theorems must be meta-level equations (with optional guards)")
		val a = Envir.eta_contract a
		val b = Envir.eta_contract b
		val prems = map Envir.eta_contract prems

                val (encoding, left) = remove_types encoding a     
		val (encoding, right) = remove_types encoding b  
                fun remove_types_of_guard encoding g = 
		    (let
			 val (t1, t2) = Logic.dest_equals g 
			 val (encoding, t1) = remove_types encoding t1
			 val (encoding, t2) = remove_types encoding t2
		     in
			 (encoding, AbstractMachine.Guard (t1, t2))
		     end handle TERM _ => raise (Make "guards must be meta-level equations"))
                val (encoding, prems) = fold_rev (fn p => fn (encoding, ps) => let val (e, p) = remove_types_of_guard encoding p in (e, p::ps) end) prems (encoding, [])
                
                fun make_pattern encoding n vars (var as AbstractMachine.Abs _) =
		    raise (Make "no lambda abstractions allowed in pattern")
		  | make_pattern encoding n vars (var as AbstractMachine.Var _) =
		    raise (Make "no bound variables allowed in pattern")
		  | make_pattern encoding n vars (AbstractMachine.Const code) =
		    (case the (Encode.lookup_term code encoding) of
			 Var _ => ((n+1, Inttab.update_new (code, n) vars, AbstractMachine.PVar)
				   handle Inttab.DUP _ => raise (Make "no duplicate variable in pattern allowed"))
		       | _ => (n, vars, AbstractMachine.PConst (code, [])))
                  | make_pattern encoding n vars (AbstractMachine.App (a, b)) =
                    let
                        val (n, vars, pa) = make_pattern encoding n vars a
                        val (n, vars, pb) = make_pattern encoding n vars b
                    in
                        case pa of
                            AbstractMachine.PVar =>
                              raise (Make "patterns may not start with a variable")
                          | AbstractMachine.PConst (c, args) =>
                              (n, vars, AbstractMachine.PConst (c, args@[pb]))
                    end

                (* Principally, a check should be made here to see if the (meta-) hyps contain any of the variables of the rule.
                   As it is, all variables of the rule are schematic, and there are no schematic variables in meta-hyps, therefore
                   this check can be left out. *)

                val (vcount, vars, pattern) = make_pattern encoding 0 Inttab.empty left
                val _ = (case pattern of
                             AbstractMachine.PVar =>
                             raise (Make "patterns may not start with a variable")
                         (*  | AbstractMachine.PConst (_, []) => 
			     (print th; raise (Make "no parameter rewrite found"))*)
			   | _ => ())

                (* finally, provide a function for renaming the
                   pattern bound variables on the right hand side *)

                fun rename level vars (var as AbstractMachine.Var _) = var
		  | rename level vars (c as AbstractMachine.Const code) =
		    (case Inttab.lookup vars code of 
			 NONE => c 
		       | SOME n => AbstractMachine.Var (vcount-n-1+level))
                  | rename level vars (AbstractMachine.App (a, b)) =
                    AbstractMachine.App (rename level vars a, rename level vars b)
                  | rename level vars (AbstractMachine.Abs m) =
                    AbstractMachine.Abs (rename (level+1) vars m)
		    
		fun rename_guard (AbstractMachine.Guard (a,b)) = 
		    AbstractMachine.Guard (rename 0 vars a, rename 0 vars b)
            in
                ((encoding, hyptable, shyptable), (map rename_guard prems, pattern, rename 0 vars right))
            end

        val ((encoding, hyptable, shyptable), rules) =
          fold_rev (fn th => fn (encoding_hyptable, rules) =>
            let
              val (encoding_hyptable, rule) = thm2rule encoding_hyptable th
            in (encoding_hyptable, rule::rules) end)
          ths ((Encode.empty, Termtab.empty, Sorttab.empty), [])

        val prog = 
	    case machine of 
		BARRAS => ProgBarras (AM_Interpreter.compile rules)
	      | BARRAS_COMPILED => ProgBarrasC (AM_Compiler.compile rules)
	      | HASKELL => ProgHaskell (AM_GHC.compile rules)
	      | SML => ProgSML (AM_SML.compile rules)

(*	val _ = print (Encode.fold (fn x => fn s => x::s) encoding [])*)

        fun has_witness s = not (null (Sign.witness_sorts thy [] [s]))

	val shyptable = fold Sorttab.delete (filter has_witness (Sorttab.keys (shyptable))) shyptable

    in Computer (Theory.check_thy thy, encoding, Termtab.keys hyptable, shyptable, prog) end

(*fun timeit f =
    let
	val t1 = Time.toMicroseconds (Time.now ())
	val x = f ()
	val t2 = Time.toMicroseconds (Time.now ())
	val _ = writeln ("### time = "^(Real.toString ((Real.fromLargeInt t2 - Real.fromLargeInt t1)/(1000000.0)))^"s")
    in
	x
    end*)

fun report s f = f () (*writeln s; timeit f*)

fun compute (Computer (rthy, encoding, hyps, shyptable, prog)) naming ct =
    let
	fun run (ProgBarras p) = AM_Interpreter.run p
	  | run (ProgBarrasC p) = AM_Compiler.run p
	  | run (ProgHaskell p) = AM_GHC.run p
	  | run (ProgSML p) = AM_SML.run p	    
        val {t=t, T=ty, thy=ctthy, ...} = rep_cterm ct
        val thy = Theory.merge (Theory.deref rthy, ctthy)
        val (encoding, t) = report "remove_types" (fn () => remove_types encoding t)
        val t = report "run" (fn () => run prog t)
        val t = report "infer_types" (fn () => infer_types naming encoding ty t)
    in
        t
    end

fun discard (Computer (rthy, encoding, hyps, shyptable, prog)) = 
    (case prog of
	 ProgBarras p => AM_Interpreter.discard p
       | ProgBarrasC p => AM_Compiler.discard p
       | ProgHaskell p => AM_GHC.discard p
       | ProgSML p => AM_SML.discard p)

fun theory_of (Computer (rthy, _, _,_,_)) = Theory.deref rthy
fun hyps_of (Computer (_, _, hyps, _, _)) = hyps
fun shyps_of (Computer (_, _, _, shyptable, _)) = Sorttab.keys (shyptable)
fun shyptab_of (Computer (_, _, _, shyptable, _)) = shyptable

fun default_naming i = "v_" ^ Int.toString i

exception Param of computer * (int -> string) * cterm;

fun rewrite_param r n ct =
    let 
	val thy = theory_of_cterm ct 
	val th = timeit (fn () => invoke_oracle_i thy "Compute_Oracle.compute" (thy, Param (r, n, ct)))
	val hyps = map (fn h => assume (cterm_of thy h)) (hyps_of r)
    in
	fold (fn h => fn p => implies_elim p h) hyps th 
    end

(*fun rewrite_param r n ct =
    let	
	val hyps = hyps_of r
	val shyps = shyps_of r
	val thy = theory_of_cterm ct
	val _ = Theory.assert_super (theory_of r) thy
	val t' = timeit (fn () => compute r n ct)
	val eq = Logic.mk_equals (term_of ct, t')
    in
	Thm.unchecked_oracle thy "Compute.compute" (eq, hyps, shyps)
    end*)

fun rewrite r ct = rewrite_param r default_naming ct

(* theory setup *)

fun compute_oracle (thy, Param (r, naming, ct)) =
    let
        val _ = Theory.assert_super (theory_of r) thy
        val t' = compute r naming ct
	val eq = Logic.mk_equals (term_of ct, t')
	val hyps = hyps_of r
	val shyptab = shyptab_of r
	fun delete s shyptab = Sorttab.delete s shyptab handle Sorttab.UNDEF _ => shyptab
	fun delete_term t shyptab = fold delete (Sorts.insert_term t []) shyptab
	val shyps = if Sorttab.is_empty shyptab then [] else Sorttab.keys (fold delete_term (eq::hyps) shyptab)
	val _ = if not (null shyps) then raise Compute ("dangling sort hypotheses: "^(makestring shyps)) else ()
    in
        fold_rev (fn hyp => fn p => Logic.mk_implies (hyp, p)) hyps eq
    end
  | compute_oracle _ = raise Match


val setup = (fn thy => (writeln "install oracle"; Theory.add_oracle ("compute", compute_oracle) thy))

(*val _ = Context.add_setup (Theory.add_oracle ("compute", compute_oracle))*)

end

