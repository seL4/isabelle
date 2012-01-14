(*  Title:      HOL/Import/shuffler.ML
    Author:     Sebastian Skalberg, TU Muenchen

Package for proving two terms equal by normalizing (hence the
"shuffler" name).  Uses the simplifier for the normalization.
*)

signature Shuffler =
sig
    val debug      : bool Unsynchronized.ref

    val norm_term  : theory -> term -> thm
    val make_equal : theory -> term -> term -> thm option
    val set_prop   : theory -> term -> (string * thm) list -> (string * thm) option

    val find_potential: theory -> term -> (string * thm) list

    val gen_shuffle_tac: Proof.context -> bool -> (string * thm) list -> int -> tactic
    val shuffle_tac: Proof.context -> thm list -> int -> tactic
    val search_tac : Proof.context -> int -> tactic

    val print_shuffles: theory -> unit

    val add_shuffle_rule: thm -> theory -> theory
    val shuffle_attr: attribute

    val setup      : theory -> theory
end

structure Shuffler :> Shuffler =
struct

val debug = Unsynchronized.ref false

fun if_debug f x = if !debug then f x else ()
val message = if_debug writeln

val string_of_thm = Print_Mode.setmp [] Display.string_of_thm_without_context;

structure ShuffleData = Theory_Data
(
  type T = thm list
  val empty = []
  val extend = I
  val merge = Thm.merge_thms
)

fun print_shuffles thy =
  Pretty.writeln (Pretty.big_list "Shuffle theorems:"
    (map (Display.pretty_thm_global thy) (ShuffleData.get thy)))

val weaken =
    let
        val cert = cterm_of Pure.thy
        val P = Free("P",propT)
        val Q = Free("Q",propT)
        val PQ = Logic.mk_implies(P,Q)
        val PPQ = Logic.mk_implies(P,PQ)
        val cP = cert P
        val cQ = cert Q
        val cPQ = cert PQ
        val cPPQ = cert PPQ
        val th1 = Thm.assume cPQ |> implies_intr_list [cPQ,cP]
        val th3 = Thm.assume cP
        val th4 = implies_elim_list (Thm.assume cPPQ) [th3,th3]
                                    |> implies_intr_list [cPPQ,cP]
    in
        Thm.equal_intr th4 th1 |> Drule.export_without_context
    end

val imp_comm =
    let
        val cert = cterm_of Pure.thy
        val P = Free("P",propT)
        val Q = Free("Q",propT)
        val R = Free("R",propT)
        val PQR = Logic.mk_implies(P,Logic.mk_implies(Q,R))
        val QPR = Logic.mk_implies(Q,Logic.mk_implies(P,R))
        val cP = cert P
        val cQ = cert Q
        val cPQR = cert PQR
        val cQPR = cert QPR
        val th1 = implies_elim_list (Thm.assume cPQR) [Thm.assume cP,Thm.assume cQ]
                                    |> implies_intr_list [cPQR,cQ,cP]
        val th2 = implies_elim_list (Thm.assume cQPR) [Thm.assume cQ,Thm.assume cP]
                                    |> implies_intr_list [cQPR,cP,cQ]
    in
        Thm.equal_intr th1 th2 |> Drule.export_without_context
    end

val all_comm =
    let
        val cert = cterm_of Pure.thy
        val xT = TFree("'a",[])
        val yT = TFree("'b",[])
        val x = Free("x",xT)
        val y = Free("y",yT)
        val P = Free("P",xT-->yT-->propT)
        val lhs = Logic.all x (Logic.all y (P $ x $ y))
        val rhs = Logic.all y (Logic.all x (P $ x $ y))
        val cl = cert lhs
        val cr = cert rhs
        val cx = cert x
        val cy = cert y
        val th1 = Thm.assume cr
                         |> forall_elim_list [cy,cx]
                         |> forall_intr_list [cx,cy]
                         |> Thm.implies_intr cr
        val th2 = Thm.assume cl
                         |> forall_elim_list [cx,cy]
                         |> forall_intr_list [cy,cx]
                         |> Thm.implies_intr cl
    in
        Thm.equal_intr th1 th2 |> Drule.export_without_context
    end

val equiv_comm =
    let
        val cert = cterm_of Pure.thy
        val T    = TFree("'a",[])
        val t    = Free("t",T)
        val u    = Free("u",T)
        val ctu  = cert (Logic.mk_equals(t,u))
        val cut  = cert (Logic.mk_equals(u,t))
        val th1  = Thm.assume ctu |> Thm.symmetric |> Thm.implies_intr ctu
        val th2  = Thm.assume cut |> Thm.symmetric |> Thm.implies_intr cut
    in
        Thm.equal_intr th1 th2 |> Drule.export_without_context
    end

(* This simplification procedure rewrites !!x y. P x y
deterministicly, in order for the normalization function, defined
below, to handle nested quantifiers robustly *)

local

exception RESULT of int

fun find_bound n (Bound i) = if i = n then raise RESULT 0
                             else if i = n+1 then raise RESULT 1
                             else ()
  | find_bound n (t $ u) = (find_bound n t; find_bound n u)
  | find_bound n (Abs(_,_,t)) = find_bound (n+1) t
  | find_bound _ _ = ()

fun swap_bound n (Bound i) = if i = n then Bound (n+1)
                             else if i = n+1 then Bound n
                             else Bound i
  | swap_bound n (t $ u) = (swap_bound n t $ swap_bound n u)
  | swap_bound n (Abs(x,xT,t)) = Abs(x,xT,swap_bound (n+1) t)
  | swap_bound n t = t

fun rew_th thy (xv as (x,xT)) (yv as (y,yT)) t =
    let
        val lhs = Logic.list_all ([xv,yv],t)
        val rhs = Logic.list_all ([yv,xv],swap_bound 0 t)
        val rew = Logic.mk_equals (lhs,rhs)
        val init = Thm.trivial (cterm_of thy rew)
    in
        all_comm RS init
    end

fun quant_rewrite thy _ (t as Const("all",T1) $ (Abs(x,xT,Const("all",T2) $ Abs(y,yT,body)))) =
    let
        val res = (find_bound 0 body;2) handle RESULT i => i
    in
        case res of
            0 => SOME (rew_th thy (x,xT) (y,yT) body)
          | 1 => if string_ord(y,x) = LESS
                 then
                     let
                         val newt = Const("all",T1) $ (Abs(y,xT,Const("all",T2) $ Abs(x,yT,body)))
                         val t_th    = Thm.reflexive (cterm_of thy t)
                         val newt_th = Thm.reflexive (cterm_of thy newt)
                     in
                         SOME (Thm.transitive t_th newt_th)
                     end
                 else NONE
          | _ => error "norm_term (quant_rewrite) internal error"
     end
  | quant_rewrite _ _ _ = (warning "quant_rewrite: Unknown lhs"; NONE)

fun freeze_thaw_term t =
    let
        val tvars = Misc_Legacy.term_tvars t
        val tfree_names = Misc_Legacy.add_term_tfree_names(t,[])
        val (type_inst,_) =
            fold (fn (w as (v,_), S) => fn (inst, used) =>
                      let
                          val v' = singleton (Name.variant_list used) v
                      in
                          ((w,TFree(v',S))::inst,v'::used)
                      end)
                  tvars ([], tfree_names)
        val t' = subst_TVars type_inst t
    in
        (t', map (fn (w,TFree(v,S)) => (v,TVar(w,S))
                  | _ => error "Internal error in Shuffler.freeze_thaw") type_inst)
    end

fun inst_tfrees thy [] thm = thm
  | inst_tfrees thy ((name,U)::rest) thm =
    let
        val cU = ctyp_of thy U
        val tfrees = Misc_Legacy.add_term_tfrees (prop_of thm,[])
        val (rens, thm') = Thm.varifyT_global'
    (remove (op = o apsnd fst) name tfrees) thm
        val mid =
            case rens of
                [] => thm'
              | [((_, S), idx)] => Drule.instantiate_normalize
            ([(ctyp_of thy (TVar (idx, S)), cU)], []) thm'
              | _ => error "Shuffler.inst_tfrees internal error"
    in
        inst_tfrees thy rest mid
    end

fun is_Abs (Abs _) = true
  | is_Abs _ = false

fun eta_redex (t $ Bound 0) =
    let
        fun free n (Bound i) = i = n
          | free n (t $ u) = free n t orelse free n u
          | free n (Abs(_,_,t)) = free (n+1) t
          | free n _ = false
    in
        not (free 0 t)
    end
  | eta_redex _ = false

fun eta_contract thy _ origt =
    let
        val (typet,Tinst) = freeze_thaw_term origt
        val (init,thaw) = Drule.legacy_freeze_thaw (Thm.reflexive (cterm_of thy typet))
        val final = inst_tfrees thy Tinst o thaw
        val t = #1 (Logic.dest_equals (prop_of init))
        val _ =
            let
                val lhs = #1 (Logic.dest_equals (prop_of (final init)))
            in
                if not (lhs aconv origt)
                then
                  writeln (cat_lines
                    (["Something is utterly wrong: (orig, lhs, frozen type, t, tinst)",
                      Syntax.string_of_term_global thy origt,
                      Syntax.string_of_term_global thy lhs,
                      Syntax.string_of_term_global thy typet,
                      Syntax.string_of_term_global thy t] @
                      map (fn (n, T) => n ^ ": " ^ Syntax.string_of_typ_global thy T) Tinst))
                else ()
            end
    in
        case t of
            Const("all",_) $ (Abs(x,xT,Const("==",_) $ P $ Q)) =>
            (if eta_redex P andalso eta_redex Q
              then
                  let
                      val cert = cterm_of thy
                      val v = Free (singleton (Name.variant_list (Term.add_free_names t [])) "v", xT)
                      val cv = cert v
                      val ct = cert t
                      val th = (Thm.assume ct)
                                   |> Thm.forall_elim cv
                                   |> Thm.abstract_rule x cv
                      val ext_th = Thm.eta_conversion (cert (Abs(x,xT,P)))
                      val th' = Thm.transitive (Thm.symmetric ext_th) th
                      val cu = cert (prop_of th')
                      val uth = Thm.combination (Thm.assume cu) (Thm.reflexive cv)
                      val uth' = (Thm.beta_conversion false (cert (Abs(x,xT,Q) $ v)))
                                     |> Thm.transitive uth
                                     |> Thm.forall_intr cv
                                     |> Thm.implies_intr cu
                      val rew_th = Thm.equal_intr (th' |> Thm.implies_intr ct) uth'
                      val res = final rew_th
                  in
                       SOME res
                  end
              else NONE)
          | _ => NONE
       end

fun eta_expand thy _ origt =
    let
        val (typet,Tinst) = freeze_thaw_term origt
        val (init,thaw) = Drule.legacy_freeze_thaw (Thm.reflexive (cterm_of thy typet))
        val final = inst_tfrees thy Tinst o thaw
        val t = #1 (Logic.dest_equals (prop_of init))
        val _ =
            let
                val lhs = #1 (Logic.dest_equals (prop_of (final init)))
            in
                if not (lhs aconv origt)
                then
                  writeln (cat_lines
                    (["Something is utterly wrong: (orig, lhs, frozen type, t, tinst)",
                      Syntax.string_of_term_global thy origt,
                      Syntax.string_of_term_global thy lhs,
                      Syntax.string_of_term_global thy typet,
                      Syntax.string_of_term_global thy t] @
                      map (fn (n, T) => n ^ ": " ^ Syntax.string_of_typ_global thy T) Tinst))
                else ()
            end
    in
        case t of
            Const("==",T) $ P $ Q =>
            if is_Abs P orelse is_Abs Q
            then (case domain_type T of
                      Type("fun",[aT,bT]) =>
                      let
                          val cert = cterm_of thy
                          val vname = singleton (Name.variant_list (Term.add_free_names t [])) "v"
                          val v = Free(vname,aT)
                          val cv = cert v
                          val ct = cert t
                          val th1 = (Thm.combination (Thm.assume ct) (Thm.reflexive cv))
                                        |> Thm.forall_intr cv
                                        |> Thm.implies_intr ct
                          val concl = cert (concl_of th1)
                          val th2 = (Thm.assume concl)
                                        |> Thm.forall_elim cv
                                        |> Thm.abstract_rule vname cv
                          val (lhs,rhs) = Logic.dest_equals (prop_of th2)
                          val elhs = Thm.eta_conversion (cert lhs)
                          val erhs = Thm.eta_conversion (cert rhs)
                          val th2' = Thm.transitive
                                         (Thm.transitive (Thm.symmetric elhs) th2)
                                         erhs
                          val res = Thm.equal_intr th1 (th2' |> Thm.implies_intr concl)
                          val res' = final res
                      in
                          SOME res'
                      end
                    | _ => NONE)
            else NONE
          | _ => error ("Bad eta_expand argument" ^ Syntax.string_of_term_global thy t)
    end;

fun mk_tfree s = TFree("'"^s,[])
fun mk_free s t = Free (s,t)
val xT = mk_tfree "a"
val yT = mk_tfree "b"
val x = Free ("x", xT)
val y = Free ("y", yT)
val P  = mk_free "P" (xT-->yT-->propT)
val Q  = mk_free "Q" (xT-->yT)
val R  = mk_free "R" (xT-->yT)
val S  = mk_free "S" xT
val S'  = mk_free "S'" xT
in

fun quant_simproc thy = Simplifier.simproc_global_i
                           thy
                           "Ordered rewriting of nested quantifiers"
                           [Logic.all x (Logic.all y (P $ x $ y))]
                           quant_rewrite
fun eta_expand_simproc thy = Simplifier.simproc_global_i
                         thy
                         "Smart eta-expansion by equivalences"
                         [Logic.mk_equals(Q,R)]
                         eta_expand
fun eta_contract_simproc thy = Simplifier.simproc_global_i
                         thy
                         "Smart handling of eta-contractions"
                         [Logic.all x (Logic.mk_equals (Q $ x, R $ x))]
                         eta_contract
end

(* Disambiguates the names of bound variables in a term, returning t
== t' where all the names of bound variables in t' are unique *)

fun disamb_bound thy t =
    let

        fun F (t $ u,idx) =
            let
                val (t',idx') = F (t,idx)
                val (u',idx'') = F (u,idx')
            in
                (t' $ u',idx'')
            end
          | F (Abs(x,xT,t),idx) =
            let
                val x' = "x" ^ string_of_int idx
                val (t',idx') = F (t,idx+1)
            in
                (Abs(x',xT,t'),idx')
            end
          | F arg = arg
        val (t',_) = F (t,0)
        val ct = cterm_of thy t
        val ct' = cterm_of thy t'
        val res = Thm.transitive (Thm.reflexive ct) (Thm.reflexive ct')
        val _ = message ("disamb_term: " ^ (string_of_thm res))
    in
        res
    end

(* Transforms a term t to some normal form t', returning the theorem t
== t'.  This is originally a help function for make_equal, but might
be handy in its own right, for example for indexing terms. *)

fun norm_term thy t =
    let
        val norms = ShuffleData.get thy
        val ss = Simplifier.global_context thy empty_ss
          addsimps (map (Thm.transfer thy) norms)
          addsimprocs [quant_simproc thy, eta_expand_simproc thy,eta_contract_simproc thy]
        fun chain f th =
            let
                val rhs = Thm.rhs_of th
            in
                Thm.transitive th (f rhs)
            end
        val th =
            t |> disamb_bound thy
              |> chain (Simplifier.full_rewrite ss)
              |> chain Thm.eta_conversion
              |> Thm.strip_shyps
        val _ = message ("norm_term: " ^ (string_of_thm th))
    in
        th
    end


(* Closes a theorem with respect to free and schematic variables (does
not touch type variables, though). *)

fun close_thm th =
    let
        val thy = Thm.theory_of_thm th
        val c = prop_of th
        val vars = Misc_Legacy.add_term_frees (c, Misc_Legacy.add_term_vars(c,[]))
    in
        Drule.forall_intr_list (map (cterm_of thy) vars) th
    end


(* Normalizes a theorem's conclusion using norm_term. *)

fun norm_thm thy th =
    let
        val c = prop_of th
    in
        Thm.equal_elim (norm_term thy c) th
    end

(* make_equal thy t u tries to construct the theorem t == u under the
signature thy.  If it succeeds, SOME (t == u) is returned, otherwise
NONE is returned. *)

fun make_equal thy t u =
    let
        val t_is_t' = norm_term thy t
        val u_is_u' = norm_term thy u
        val th = Thm.transitive t_is_t' (Thm.symmetric u_is_u')
        val _ = message ("make_equal: SOME " ^ (string_of_thm th))
    in
        SOME th
    end
    handle e as THM _ => (message "make_equal: NONE";NONE)

fun match_consts ignore t (* th *) =
    let
        fun add_consts (Const (c, _), cs) =
            if member (op =) ignore c
            then cs
            else insert (op =) c cs
          | add_consts (t $ u, cs) = add_consts (t, add_consts (u, cs))
          | add_consts (Abs (_, _, t), cs) = add_consts (t, cs)
          | add_consts (_, cs) = cs
        val t_consts = add_consts(t,[])
    in
     fn (name,th) =>
        let
            val th_consts = add_consts(prop_of th,[])
        in
            eq_set (op =) (t_consts, th_consts)
        end
    end

val collect_ignored = fold_rev (fn thm => fn cs =>
  let
    val (lhs, rhs) = Logic.dest_equals (prop_of thm);
    val consts_lhs = Term.add_const_names lhs [];
    val consts_rhs = Term.add_const_names rhs [];
    val ignore_lhs = subtract (op =) consts_rhs consts_lhs;
    val ignore_rhs = subtract (op =) consts_lhs consts_rhs;
  in
    fold_rev (insert (op =)) cs (ignore_lhs @ ignore_rhs)
  end)

(* set_prop t thms tries to make a theorem with the proposition t from
one of the theorems thms, by shuffling the propositions around.  If it
succeeds, SOME theorem is returned, otherwise NONE.  *)

fun set_prop thy t =
    let
        val vars = Misc_Legacy.add_term_frees (t, Misc_Legacy.add_term_vars (t,[]))
        val closed_t = fold_rev Logic.all vars t
        val rew_th = norm_term thy closed_t
        val rhs = Thm.rhs_of rew_th

        fun process [] = NONE
          | process ((name,th)::thms) =
            let
                val norm_th = Thm.varifyT_global (norm_thm thy (close_thm (Thm.transfer thy th)))
                val triv_th = Thm.trivial rhs
                val _ = message ("Shuffler.set_prop: Gluing together " ^ (string_of_thm norm_th) ^ " and " ^ (string_of_thm triv_th))
                val mod_th = case Seq.pull (Thm.bicompose false (*true*) (false,norm_th,0) 1 triv_th) of
                                 SOME(th,_) => SOME th
                               | NONE => NONE
            in
                case mod_th of
                    SOME mod_th =>
                    let
                        val closed_th = Thm.equal_elim (Thm.symmetric rew_th) mod_th
                    in
                        message ("Shuffler.set_prop succeeded by " ^ name);
                        SOME (name,forall_elim_list (map (cterm_of thy) vars) closed_th)
                    end
                  | NONE => process thms
            end
            handle e as THM _ => process thms
    in
        fn thms =>
           case process thms of
               res as SOME (name,th) => if (prop_of th) aconv t
                                        then res
                                        else error "Internal error in set_prop"
             | NONE => NONE
    end

fun find_potential thy t =
    let
        val shuffles = ShuffleData.get thy
        val ignored = collect_ignored shuffles []
        val all_thms =
          map (`Thm.get_name_hint) (maps #2 (Facts.dest_static [] (Global_Theory.facts_of thy)))
    in
        filter (match_consts ignored t) all_thms
    end

fun gen_shuffle_tac ctxt search thms = SUBGOAL (fn (t, i) =>
    let
        val thy = Proof_Context.theory_of ctxt
        val set = set_prop thy t
        fun process_tac thms st =
            case set thms of
                SOME (_,th) => Seq.of_list (compose (th,i,st))
              | NONE => Seq.empty
    in
        process_tac thms APPEND
          (if search then process_tac (find_potential thy t) else no_tac)
    end)

fun shuffle_tac ctxt thms =
  gen_shuffle_tac ctxt false (map (pair "") thms);

fun search_tac ctxt =
  gen_shuffle_tac ctxt true (map (pair "premise") (Assumption.all_prems_of ctxt));

fun add_shuffle_rule thm thy =
    let
        val shuffles = ShuffleData.get thy
    in
        if exists (curry Thm.eq_thm thm) shuffles
        then (warning ((string_of_thm thm) ^ " already known to the shuffler");
              thy)
        else ShuffleData.put (thm::shuffles) thy
    end

val shuffle_attr = Thm.declaration_attribute (fn th => Context.mapping (add_shuffle_rule th) I);

val setup =
  Method.setup @{binding shuffle_tac}
    (Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (shuffle_tac ctxt ths)))
    "solve goal by shuffling terms around" #>
  Method.setup @{binding search_tac}
    (Scan.succeed (SIMPLE_METHOD' o search_tac)) "search for suitable theorems" #>
  add_shuffle_rule weaken #>
  add_shuffle_rule equiv_comm #>
  add_shuffle_rule imp_comm #>
  add_shuffle_rule Drule.norm_hhf_eq #>
  add_shuffle_rule Drule.triv_forall_equality #>
  Attrib.setup @{binding shuffle_rule} (Scan.succeed shuffle_attr) "declare rule for shuffler";

end
