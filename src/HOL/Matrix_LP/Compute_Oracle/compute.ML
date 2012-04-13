(*  Title:      HOL/Matrix_LP/Compute_Oracle/compute.ML
    Author:     Steven Obua
*)

signature COMPUTE = sig

    type computer
    type theorem
    type naming = int -> string

    datatype machine = BARRAS | BARRAS_COMPILED | HASKELL | SML

    (* Functions designated with a ! in front of them actually update the computer parameter *)

    exception Make of string
    val make : machine -> theory -> thm list -> computer
    val make_with_cache : machine -> theory -> term list -> thm list -> computer
    val theory_of : computer -> theory
    val hyps_of : computer -> term list
    val shyps_of : computer -> sort list
    (* ! *) val update : computer -> thm list -> unit
    (* ! *) val update_with_cache : computer -> term list -> thm list -> unit
    
    (* ! *) val set_naming : computer -> naming -> unit
    val naming_of : computer -> naming
    
    exception Compute of string    
    val simplify : computer -> theorem -> thm 
    val rewrite : computer -> cterm -> thm 

    val make_theorem : computer -> thm -> string list -> theorem
    (* ! *) val instantiate : computer -> (string * cterm) list -> theorem -> theorem
    (* ! *) val evaluate_prem : computer -> int -> theorem -> theorem
    (* ! *) val modus_ponens : computer -> int -> thm -> theorem -> theorem

end

structure Compute :> COMPUTE = struct

open Report;

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

end

exception Make of string;
exception Compute of string;

local
    fun make_constant t encoding = 
        let 
            val (code, encoding) = Encode.insert t encoding 
        in 
            (encoding, AbstractMachine.Const code)
        end
in

fun remove_types encoding t =
    case t of 
        Var _ => make_constant t encoding
      | Free _ => make_constant t encoding
      | Const _ => make_constant t encoding
      | Abs (_, _, t') => 
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
      | type_of _ = raise Fail "infer_types: type_of error"
in
fun infer_types naming encoding =
    let
        fun infer_types _ bounds _ (AbstractMachine.Var v) = (Bound v, nth bounds v)
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
                      | _ => raise Fail "infer_types: function type expected"
                val (b, _) = infer_types level bounds (SOME adom) b
            in
                (a $ b, arange)
            end
          | infer_types level bounds (SOME (ty as Type ("fun", [dom, range]))) (AbstractMachine.Abs m) =
            let
                val (m, _) = infer_types (level+1) (dom::bounds) (SOME range) m
            in
                (Abs (naming level, dom, m), ty)
            end
          | infer_types _ _ NONE (AbstractMachine.Abs _) =
              raise Fail "infer_types: cannot infer type of abstraction"

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

fun machine_of_prog (ProgBarras _) = BARRAS
  | machine_of_prog (ProgBarrasC _) = BARRAS_COMPILED
  | machine_of_prog (ProgHaskell _) = HASKELL
  | machine_of_prog (ProgSML _) = SML

type naming = int -> string

fun default_naming i = "v_" ^ string_of_int i

datatype computer = Computer of
  (theory_ref * Encode.encoding * term list * unit Sorttab.table * prog * unit Unsynchronized.ref * naming)
    option Unsynchronized.ref

fun theory_of (Computer (Unsynchronized.ref (SOME (rthy,_,_,_,_,_,_)))) = Theory.deref rthy
fun hyps_of (Computer (Unsynchronized.ref (SOME (_,_,hyps,_,_,_,_)))) = hyps
fun shyps_of (Computer (Unsynchronized.ref (SOME (_,_,_,shyptable,_,_,_)))) = Sorttab.keys (shyptable)
fun shyptab_of (Computer (Unsynchronized.ref (SOME (_,_,_,shyptable,_,_,_)))) = shyptable
fun stamp_of (Computer (Unsynchronized.ref (SOME (_,_,_,_,_,stamp,_)))) = stamp
fun prog_of (Computer (Unsynchronized.ref (SOME (_,_,_,_,prog,_,_)))) = prog
fun encoding_of (Computer (Unsynchronized.ref (SOME (_,encoding,_,_,_,_,_)))) = encoding
fun set_encoding (Computer (r as Unsynchronized.ref (SOME (p1,_,p2,p3,p4,p5,p6)))) encoding' = 
    (r := SOME (p1,encoding',p2,p3,p4,p5,p6))
fun naming_of (Computer (Unsynchronized.ref (SOME (_,_,_,_,_,_,n)))) = n
fun set_naming (Computer (r as Unsynchronized.ref (SOME (p1,p2,p3,p4,p5,p6,_)))) naming'= 
    (r := SOME (p1,p2,p3,p4,p5,p6,naming'))

fun ref_of (Computer r) = r

datatype cthm = ComputeThm of term list * sort list * term

fun thm2cthm th = 
    let
        val {hyps, prop, tpairs, shyps, ...} = Thm.rep_thm th
        val _ = if not (null tpairs) then raise Make "theorems may not contain tpairs" else ()
    in
        ComputeThm (hyps, shyps, prop)
    end

fun make_internal machine thy stamp encoding cache_pattern_terms raw_ths =
    let
        fun transfer (x:thm) = Thm.transfer thy x
        val ths = map (thm2cthm o Thm.strip_shyps o transfer) raw_ths

        fun make_pattern encoding n vars (AbstractMachine.Abs _) =
            raise (Make "no lambda abstractions allowed in pattern")
          | make_pattern encoding n vars (AbstractMachine.Var _) =
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

                (* Principally, a check should be made here to see if the (meta-) hyps contain any of the variables of the rule.
                   As it is, all variables of the rule are schematic, and there are no schematic variables in meta-hyps, therefore
                   this check can be left out. *)

                val (vcount, vars, pattern) = make_pattern encoding 0 Inttab.empty left
                val _ = (case pattern of
                             AbstractMachine.PVar =>
                             raise (Make "patterns may not start with a variable")
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
          ths ((encoding, Termtab.empty, Sorttab.empty), [])

        fun make_cache_pattern t (encoding, cache_patterns) =
            let
                val (encoding, a) = remove_types encoding t
                val (_,_,p) = make_pattern encoding 0 Inttab.empty a
            in
                (encoding, p::cache_patterns)
            end
        
        val (encoding, _) = fold_rev make_cache_pattern cache_pattern_terms (encoding, [])

        val prog = 
            case machine of 
                BARRAS => ProgBarras (AM_Interpreter.compile rules)
              | BARRAS_COMPILED => ProgBarrasC (AM_Compiler.compile rules)
              | HASKELL => ProgHaskell (AM_GHC.compile rules)
              | SML => ProgSML (AM_SML.compile rules)

        fun has_witness s = not (null (Sign.witness_sorts thy [] [s]))

        val shyptable = fold Sorttab.delete (filter has_witness (Sorttab.keys (shyptable))) shyptable

    in (Theory.check_thy thy, encoding, Termtab.keys hyptable, shyptable, prog, stamp, default_naming) end

fun make_with_cache machine thy cache_patterns raw_thms =
  Computer (Unsynchronized.ref (SOME (make_internal machine thy (Unsynchronized.ref ()) Encode.empty cache_patterns raw_thms)))

fun make machine thy raw_thms = make_with_cache machine thy [] raw_thms

fun update_with_cache computer cache_patterns raw_thms =
    let 
        val c = make_internal (machine_of_prog (prog_of computer)) (theory_of computer) (stamp_of computer) 
                              (encoding_of computer) cache_patterns raw_thms
        val _ = (ref_of computer) := SOME c     
    in
        ()
    end

fun update computer raw_thms = update_with_cache computer [] raw_thms

fun runprog (ProgBarras p) = AM_Interpreter.run p
  | runprog (ProgBarrasC p) = AM_Compiler.run p
  | runprog (ProgHaskell p) = AM_GHC.run p
  | runprog (ProgSML p) = AM_SML.run p    

(* ------------------------------------------------------------------------------------- *)
(* An oracle for exporting theorems; must only be accessible from inside this structure! *)
(* ------------------------------------------------------------------------------------- *)

fun merge_hyps hyps1 hyps2 = 
let
    fun add hyps tab = fold (fn h => fn tab => Termtab.update (h, ()) tab) hyps tab
in
    Termtab.keys (add hyps2 (add hyps1 Termtab.empty))
end

fun add_shyps shyps tab = fold (fn h => fn tab => Sorttab.update (h, ()) tab) shyps tab

fun merge_shyps shyps1 shyps2 = Sorttab.keys (add_shyps shyps2 (add_shyps shyps1 Sorttab.empty))

val (_, export_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (@{binding compute}, fn (thy, hyps, shyps, prop) =>
    let
        val shyptab = add_shyps shyps Sorttab.empty
        fun delete s shyptab = Sorttab.delete s shyptab handle Sorttab.UNDEF _ => shyptab
        fun delete_term t shyptab = fold delete (Sorts.insert_term t []) shyptab
        fun has_witness s = not (null (Sign.witness_sorts thy [] [s]))
        val shyptab = fold Sorttab.delete (filter has_witness (Sorttab.keys (shyptab))) shyptab
        val shyps = if Sorttab.is_empty shyptab then [] else Sorttab.keys (fold delete_term (prop::hyps) shyptab)
        val _ =
          if not (null shyps) then
            raise Compute ("dangling sort hypotheses: " ^
              commas (map (Syntax.string_of_sort_global thy) shyps))
          else ()
    in
        Thm.cterm_of thy (fold_rev (fn hyp => fn p => Logic.mk_implies (hyp, p)) hyps prop)
    end)));

fun export_thm thy hyps shyps prop =
    let
        val th = export_oracle (thy, hyps, shyps, prop)
        val hyps = map (fn h => Thm.assume (cterm_of thy h)) hyps
    in
        fold (fn h => fn p => Thm.implies_elim p h) hyps th 
    end
        
(* --------- Rewrite ----------- *)

fun rewrite computer ct =
    let
        val thy = Thm.theory_of_cterm ct
        val {t=t',T=ty,...} = rep_cterm ct
        val _ = Theory.assert_super (theory_of computer) thy
        val naming = naming_of computer
        val (encoding, t) = remove_types (encoding_of computer) t'
        val t = runprog (prog_of computer) t
        val t = infer_types naming encoding ty t
        val eq = Logic.mk_equals (t', t)
    in
        export_thm thy (hyps_of computer) (Sorttab.keys (shyptab_of computer)) eq
    end

(* --------- Simplify ------------ *)

datatype prem = EqPrem of AbstractMachine.term * AbstractMachine.term * Term.typ * int 
              | Prem of AbstractMachine.term
datatype theorem = Theorem of theory_ref * unit Unsynchronized.ref * (int * typ) Symtab.table * (AbstractMachine.term option) Inttab.table  
               * prem list * AbstractMachine.term * term list * sort list


exception ParamSimplify of computer * theorem

fun make_theorem computer th vars =
let
    val _ = Theory.assert_super (theory_of computer) (theory_of_thm th)

    val (ComputeThm (hyps, shyps, prop)) = thm2cthm th 

    val encoding = encoding_of computer
 
    (* variables in the theorem are identified upfront *)
    fun collect_vars (Abs (_, _, t)) tab = collect_vars t tab
      | collect_vars (a $ b) tab = collect_vars b (collect_vars a tab)
      | collect_vars (Const _) tab = tab
      | collect_vars (Free _) tab = tab
      | collect_vars (Var ((s, i), ty)) tab = 
            if List.find (fn x => x=s) vars = NONE then 
                tab
            else                
                (case Symtab.lookup tab s of
                     SOME ((s',i'),ty') => 
                     if s' <> s orelse i' <> i orelse ty <> ty' then 
                         raise Compute ("make_theorem: variable name '"^s^"' is not unique")
                     else 
                         tab
                   | NONE => Symtab.update (s, ((s, i), ty)) tab)
    val vartab = collect_vars prop Symtab.empty 
    fun encodevar (s, t as (_, ty)) (encoding, tab) = 
        let
            val (x, encoding) = Encode.insert (Var t) encoding
        in
            (encoding, Symtab.update (s, (x, ty)) tab)
        end
    val (encoding, vartab) = Symtab.fold encodevar vartab (encoding, Symtab.empty)                                                     
    val varsubst = Inttab.make (map (fn (_, (x, _)) => (x, NONE)) (Symtab.dest vartab))

    (* make the premises and the conclusion *)
    fun mk_prem encoding t = 
        (let
             val (a, b) = Logic.dest_equals t
             val ty = type_of a
             val (encoding, a) = remove_types encoding a
             val (encoding, b) = remove_types encoding b
             val (eq, encoding) = Encode.insert (Const ("==", ty --> ty --> @{typ "prop"})) encoding 
         in
             (encoding, EqPrem (a, b, ty, eq))
         end handle TERM _ => let val (encoding, t) = remove_types encoding t in (encoding, Prem t) end)
    val (encoding, prems) = 
        (fold_rev (fn t => fn (encoding, l) => 
            case mk_prem encoding t  of 
                (encoding, t) => (encoding, t::l)) (Logic.strip_imp_prems prop) (encoding, []))
    val (encoding, concl) = remove_types encoding (Logic.strip_imp_concl prop)
    val _ = set_encoding computer encoding
in
    Theorem (Theory.check_thy (theory_of_thm th), stamp_of computer, vartab, varsubst, 
             prems, concl, hyps, shyps)
end
    
fun theory_of_theorem (Theorem (rthy,_,_,_,_,_,_,_)) = Theory.deref rthy
fun update_theory thy (Theorem (_,p0,p1,p2,p3,p4,p5,p6)) =
    Theorem (Theory.check_thy thy,p0,p1,p2,p3,p4,p5,p6)
fun stamp_of_theorem (Theorem (_,s, _, _, _, _, _, _)) = s     
fun vartab_of_theorem (Theorem (_,_,vt,_,_,_,_,_)) = vt
fun varsubst_of_theorem (Theorem (_,_,_,vs,_,_,_,_)) = vs 
fun update_varsubst vs (Theorem (p0,p1,p2,_,p3,p4,p5,p6)) = Theorem (p0,p1,p2,vs,p3,p4,p5,p6)
fun prems_of_theorem (Theorem (_,_,_,_,prems,_,_,_)) = prems
fun update_prems prems (Theorem (p0,p1,p2,p3,_,p4,p5,p6)) = Theorem (p0,p1,p2,p3,prems,p4,p5,p6)
fun concl_of_theorem (Theorem (_,_,_,_,_,concl,_,_)) = concl
fun hyps_of_theorem (Theorem (_,_,_,_,_,_,hyps,_)) = hyps
fun update_hyps hyps (Theorem (p0,p1,p2,p3,p4,p5,_,p6)) = Theorem (p0,p1,p2,p3,p4,p5,hyps,p6)
fun shyps_of_theorem (Theorem (_,_,_,_,_,_,_,shyps)) = shyps
fun update_shyps shyps (Theorem (p0,p1,p2,p3,p4,p5,p6,_)) = Theorem (p0,p1,p2,p3,p4,p5,p6,shyps)

fun check_compatible computer th s = 
    if stamp_of computer <> stamp_of_theorem th then
        raise Compute (s^": computer and theorem are incompatible")
    else ()

fun instantiate computer insts th =
let
    val _ = check_compatible computer th

    val thy = theory_of computer

    val vartab = vartab_of_theorem th

    fun rewrite computer t =
    let  
        val (encoding, t) = remove_types (encoding_of computer) t
        val t = runprog (prog_of computer) t
        val _ = set_encoding computer encoding
    in
        t
    end

    fun assert_varfree vs t = 
        if AbstractMachine.forall_consts (fn x => Inttab.lookup vs x = NONE) t then
            ()
        else
            raise Compute "instantiate: assert_varfree failed"

    fun assert_closed t =
        if AbstractMachine.closed t then
            ()
        else 
            raise Compute "instantiate: not a closed term"

    fun compute_inst (s, ct) vs =
        let
            val _ = Theory.assert_super (theory_of_cterm ct) thy
            val ty = typ_of (ctyp_of_term ct) 
        in          
            (case Symtab.lookup vartab s of 
                 NONE => raise Compute ("instantiate: variable '"^s^"' not found in theorem")
               | SOME (x, ty') => 
                 (case Inttab.lookup vs x of 
                      SOME (SOME _) => raise Compute ("instantiate: variable '"^s^"' has already been instantiated")
                    | SOME NONE => 
                      if ty <> ty' then 
                          raise Compute ("instantiate: wrong type for variable '"^s^"'")
                      else
                          let
                              val t = rewrite computer (term_of ct)
                              val _ = assert_varfree vs t 
                              val _ = assert_closed t
                          in
                              Inttab.update (x, SOME t) vs
                          end
                    | NONE => raise Compute "instantiate: internal error"))
        end

    val vs = fold compute_inst insts (varsubst_of_theorem th)
in
    update_varsubst vs th
end

fun match_aterms subst =
    let 
        exception no_match
        open AbstractMachine
        fun match subst (b as (Const c)) a = 
            if a = b then subst
            else 
                (case Inttab.lookup subst c of 
                     SOME (SOME a') => if a=a' then subst else raise no_match
                   | SOME NONE => if AbstractMachine.closed a then 
                                      Inttab.update (c, SOME a) subst 
                                  else raise no_match
                   | NONE => raise no_match)
          | match subst (b as (Var _)) a = if a=b then subst else raise no_match
          | match subst (App (u, v)) (App (u', v')) = match (match subst u u') v v'
          | match subst (Abs u) (Abs u') = match subst u u'
          | match subst _ _ = raise no_match
    in
        fn b => fn a => (SOME (match subst b a) handle no_match => NONE)
    end

fun apply_subst vars_allowed subst =
    let
        open AbstractMachine
        fun app (t as (Const c)) = 
            (case Inttab.lookup subst c of 
                 NONE => t 
               | SOME (SOME t) => Computed t
               | SOME NONE => if vars_allowed then t else raise Compute "apply_subst: no vars allowed")
          | app (t as (Var _)) = t
          | app (App (u, v)) = App (app u, app v)
          | app (Abs m) = Abs (app m)
    in
        app
    end

fun splicein n l L = List.take (L, n) @ l @ List.drop (L, n+1)

fun evaluate_prem computer prem_no th =
let
    val _ = check_compatible computer th
    val prems = prems_of_theorem th
    val varsubst = varsubst_of_theorem th
    fun run vars_allowed t = 
        runprog (prog_of computer) (apply_subst vars_allowed varsubst t)
in
    case nth prems prem_no of
        Prem _ => raise Compute "evaluate_prem: no equality premise"
      | EqPrem (a, b, ty, _) =>         
        let
            val a' = run false a
            val b' = run true b
        in
            case match_aterms varsubst b' a' of
                NONE => 
                let
                    fun mk s = Syntax.string_of_term_global Pure.thy
                      (infer_types (naming_of computer) (encoding_of computer) ty s)
                    val left = "computed left side: "^(mk a')
                    val right = "computed right side: "^(mk b')
                in
                    raise Compute ("evaluate_prem: cannot assign computed left to right hand side\n"^left^"\n"^right^"\n")
                end
              | SOME varsubst => 
                update_prems (splicein prem_no [] prems) (update_varsubst varsubst th)
        end
end

fun prem2term (Prem t) = t
  | prem2term (EqPrem (a,b,_,eq)) = 
    AbstractMachine.App (AbstractMachine.App (AbstractMachine.Const eq, a), b)

fun modus_ponens computer prem_no th' th = 
let
    val _ = check_compatible computer th
    val thy = 
        let
            val thy1 = theory_of_theorem th
            val thy2 = theory_of_thm th'
        in
            if Theory.subthy (thy1, thy2) then thy2 
            else if Theory.subthy (thy2, thy1) then thy1 else
            raise Compute "modus_ponens: theorems are not compatible with each other"
        end 
    val th' = make_theorem computer th' []
    val varsubst = varsubst_of_theorem th
    fun run vars_allowed t =
        runprog (prog_of computer) (apply_subst vars_allowed varsubst t)
    val prems = prems_of_theorem th
    val prem = run true (prem2term (nth prems prem_no))
    val concl = run false (concl_of_theorem th')    
in
    case match_aterms varsubst prem concl of
        NONE => raise Compute "modus_ponens: conclusion does not match premise"
      | SOME varsubst =>
        let
            val th = update_varsubst varsubst th
            val th = update_prems (splicein prem_no (prems_of_theorem th') prems) th
            val th = update_hyps (merge_hyps (hyps_of_theorem th) (hyps_of_theorem th')) th
            val th = update_shyps (merge_shyps (shyps_of_theorem th) (shyps_of_theorem th')) th
        in
            update_theory thy th
        end
end
                     
fun simplify computer th =
let
    val _ = check_compatible computer th
    val varsubst = varsubst_of_theorem th
    val encoding = encoding_of computer
    val naming = naming_of computer
    fun infer t = infer_types naming encoding @{typ "prop"} t
    fun run t = infer (runprog (prog_of computer) (apply_subst true varsubst t))
    fun runprem p = run (prem2term p)
    val prop = Logic.list_implies (map runprem (prems_of_theorem th), run (concl_of_theorem th))
    val hyps = merge_hyps (hyps_of computer) (hyps_of_theorem th)
    val shyps = merge_shyps (shyps_of_theorem th) (Sorttab.keys (shyptab_of computer))
in
    export_thm (theory_of_theorem th) hyps shyps prop
end

end

