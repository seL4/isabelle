(*  Title:      HOL/Matrix/Compute_Oracle/linker.ML
    Author:     Steven Obua

This module solves the problem that the computing oracle does not
instantiate polymorphic rules. By going through the PCompute
interface, all possible instantiations are resolved by compiling new
programs, if necessary. The obvious disadvantage of this approach is
that in the worst case for each new term to be rewritten, a new
program may be compiled.
*)

(*
   Given constants/frees c_1::t_1, c_2::t_2, ...., c_n::t_n,
   and constants/frees d_1::d_1, d_2::s_2, ..., d_m::s_m

   Find all substitutions S such that
   a) the domain of S is tvars (t_1, ..., t_n)
   b) there are indices i_1, ..., i_k, and j_1, ..., j_k with
      1. S (c_i_1::t_i_1) = d_j_1::s_j_1, ..., S (c_i_k::t_i_k) = d_j_k::s_j_k
      2. tvars (t_i_1, ..., t_i_k) = tvars (t_1, ..., t_n)
*)
signature LINKER =
sig
    exception Link of string

    datatype constant = Constant of bool * string * typ
    val constant_of : term -> constant

    type instances
    type subst = Type.tyenv

    val empty : constant list -> instances
    val typ_of_constant : constant -> typ
    val add_instances : theory -> instances -> constant list -> subst list * instances
    val substs_of : instances -> subst list
    val is_polymorphic : constant -> bool
    val distinct_constants : constant list -> constant list
    val collect_consts : term list -> constant list
end

structure Linker : LINKER = struct

exception Link of string;

type subst = Type.tyenv

datatype constant = Constant of bool * string * typ
fun constant_of (Const (name, ty)) = Constant (false, name, ty)
  | constant_of (Free (name, ty)) = Constant (true, name, ty)
  | constant_of _ = raise Link "constant_of"

fun bool_ord (x,y) = if x then (if y then EQUAL else GREATER) else (if y then LESS else EQUAL)
fun constant_ord (Constant (x1,x2,x3), Constant (y1,y2,y3)) = (prod_ord (prod_ord bool_ord fast_string_ord) Term_Ord.typ_ord) (((x1,x2),x3), ((y1,y2),y3))
fun constant_modty_ord (Constant (x1,x2,_), Constant (y1,y2,_)) = (prod_ord bool_ord fast_string_ord) ((x1,x2), (y1,y2))


structure Consttab = Table(type key = constant val ord = constant_ord);
structure ConsttabModTy = Table(type key = constant val ord = constant_modty_ord);

fun typ_of_constant (Constant (_, _, ty)) = ty

val empty_subst = (Vartab.empty : Type.tyenv)

fun merge_subst (A:Type.tyenv) (B:Type.tyenv) =
    SOME (Vartab.fold (fn (v, t) =>
                       fn tab =>
                          (case Vartab.lookup tab v of
                               NONE => Vartab.update (v, t) tab
                             | SOME t' => if t = t' then tab else raise Type.TYPE_MATCH)) A B)
    handle Type.TYPE_MATCH => NONE

fun subst_ord (A:Type.tyenv, B:Type.tyenv) =
    (list_ord (prod_ord Term_Ord.fast_indexname_ord (prod_ord Term_Ord.sort_ord Term_Ord.typ_ord))) (Vartab.dest A, Vartab.dest B)

structure Substtab = Table(type key = Type.tyenv val ord = subst_ord);

fun substtab_union c = Substtab.fold Substtab.update c
fun substtab_unions [] = Substtab.empty
  | substtab_unions [c] = c
  | substtab_unions (c::cs) = substtab_union c (substtab_unions cs)

datatype instances = Instances of unit ConsttabModTy.table * Type.tyenv Consttab.table Consttab.table * constant list list * unit Substtab.table

fun is_polymorphic (Constant (_, _, ty)) = not (null (Term.add_tvarsT ty []))

fun distinct_constants cs =
    Consttab.keys (fold (fn c => Consttab.update (c, ())) cs Consttab.empty)

fun empty cs =
    let
        val cs = distinct_constants (filter is_polymorphic cs)
        val old_cs = cs
(*      fun collect_tvars ty tab = fold (fn v => fn tab => Typtab.update (TVar v, ()) tab) (Misc_Legacy.typ_tvars ty) tab
        val tvars_count = length (Typtab.keys (fold (fn c => fn tab => collect_tvars (typ_of_constant c) tab) cs Typtab.empty))
        fun tvars_of ty = collect_tvars ty Typtab.empty
        val cs = map (fn c => (c, tvars_of (typ_of_constant c))) cs

        fun tyunion A B =
            Typtab.fold
                (fn (v,()) => fn tab => Typtab.update (v, case Typtab.lookup tab v of NONE => 1 | SOME n => n+1) tab)
                A B

        fun is_essential A B =
            Typtab.fold
            (fn (v, ()) => fn essential => essential orelse (case Typtab.lookup B v of NONE => raise Link "is_essential" | SOME n => n=1))
            A false

        fun add_minimal (c', tvs') (tvs, cs) =
            let
                val tvs = tyunion tvs' tvs
                val cs = (c', tvs')::cs
            in
                if forall (fn (c',tvs') => is_essential tvs' tvs) cs then
                    SOME (tvs, cs)
                else
                    NONE
            end

        fun is_spanning (tvs, _) = (length (Typtab.keys tvs) = tvars_count)

        fun generate_minimal_subsets subsets [] = subsets
          | generate_minimal_subsets subsets (c::cs) =
            let
                val subsets' = map_filter (add_minimal c) subsets
            in
                generate_minimal_subsets (subsets@subsets') cs
            end*)

        val minimal_subsets = [old_cs] (*map (fn (tvs, cs) => map fst cs) (filter is_spanning (generate_minimal_subsets [(Typtab.empty, [])] cs))*)

        val constants = Consttab.keys (fold (fold (fn c => Consttab.update (c, ()))) minimal_subsets Consttab.empty)

    in
        Instances (
        fold (fn c => fn tab => ConsttabModTy.update (c, ()) tab) constants ConsttabModTy.empty,
        Consttab.make (map (fn c => (c, Consttab.empty : Type.tyenv Consttab.table)) constants),
        minimal_subsets, Substtab.empty)
    end

local
fun calc ctab substtab [] = substtab
  | calc ctab substtab (c::cs) =
    let
        val csubsts = map snd (Consttab.dest (the (Consttab.lookup ctab c)))
        fun merge_substs substtab subst =
            Substtab.fold (fn (s,_) =>
                           fn tab =>
                              (case merge_subst subst s of NONE => tab | SOME s => Substtab.update (s, ()) tab))
                          substtab Substtab.empty
        val substtab = substtab_unions (map (merge_substs substtab) csubsts)
    in
        calc ctab substtab cs
    end
in
fun calc_substs ctab (cs:constant list) = calc ctab (Substtab.update (empty_subst, ()) Substtab.empty) cs
end

fun add_instances thy (Instances (cfilter, ctab,minsets,substs)) cs =
    let
(*      val _ = writeln (makestring ("add_instances: ", length_cs, length cs, length (Consttab.keys ctab)))*)
        fun calc_instantiations (constant as Constant (free, name, ty)) instantiations =
            Consttab.fold (fn (constant' as Constant (free', name', ty'), insttab) =>
                           fn instantiations =>
                              if free <> free' orelse name <> name' then
                                  instantiations
                              else case Consttab.lookup insttab constant of
                                       SOME _ => instantiations
                                     | NONE => ((constant', (constant, Sign.typ_match thy (ty', ty) empty_subst))::instantiations
                                                handle Type.TYPE_MATCH => instantiations))
                          ctab instantiations
        val instantiations = fold calc_instantiations cs []
        (*val _ = writeln ("instantiations = "^(makestring (length instantiations)))*)
        fun update_ctab (constant', entry) ctab =
            (case Consttab.lookup ctab constant' of
                 NONE => raise Link "internal error: update_ctab"
               | SOME tab => Consttab.update (constant', Consttab.update entry tab) ctab)
        val ctab = fold update_ctab instantiations ctab
        val new_substs = fold (fn minset => fn substs => substtab_union (calc_substs ctab minset) substs)
                              minsets Substtab.empty
        val (added_substs, substs) =
            Substtab.fold (fn (ns, _) =>
                           fn (added, substtab) =>
                              (case Substtab.lookup substs ns of
                                   NONE => (ns::added, Substtab.update (ns, ()) substtab)
                                 | SOME () => (added, substtab)))
                          new_substs ([], substs)
    in
        (added_substs, Instances (cfilter, ctab, minsets, substs))
    end

fun substs_of (Instances (_,_,_,substs)) = Substtab.keys substs


local

fun collect (Var _) tab = tab
  | collect (Bound _) tab = tab
  | collect (a $ b) tab = collect b (collect a tab)
  | collect (Abs (_, _, body)) tab = collect body tab
  | collect t tab = Consttab.update (constant_of t, ()) tab

in
  fun collect_consts tms = Consttab.keys (fold collect tms Consttab.empty)
end

end

signature PCOMPUTE =
sig
    type pcomputer

    val make : Compute.machine -> theory -> thm list -> Linker.constant list -> pcomputer
    val make_with_cache : Compute.machine -> theory -> term list -> thm list -> Linker.constant list -> pcomputer
    
    val add_instances : pcomputer -> Linker.constant list -> bool 
    val add_instances' : pcomputer -> term list -> bool

    val rewrite : pcomputer -> cterm list -> thm list
    val simplify : pcomputer -> Compute.theorem -> thm

    val make_theorem : pcomputer -> thm -> string list -> Compute.theorem
    val instantiate : pcomputer -> (string * cterm) list -> Compute.theorem -> Compute.theorem
    val evaluate_prem : pcomputer -> int -> Compute.theorem -> Compute.theorem
    val modus_ponens : pcomputer -> int -> thm -> Compute.theorem -> Compute.theorem 

end

structure PCompute : PCOMPUTE = struct

exception PCompute of string

datatype theorem = MonoThm of thm | PolyThm of thm * Linker.instances * thm list
datatype pattern = MonoPattern of term | PolyPattern of term * Linker.instances * term list

datatype pcomputer =
  PComputer of theory_ref * Compute.computer * theorem list Unsynchronized.ref *
    pattern list Unsynchronized.ref 

(*fun collect_consts (Var x) = []
  | collect_consts (Bound _) = []
  | collect_consts (a $ b) = (collect_consts a)@(collect_consts b)
  | collect_consts (Abs (_, _, body)) = collect_consts body
  | collect_consts t = [Linker.constant_of t]*)

fun computer_of (PComputer (_,computer,_,_)) = computer

fun collect_consts_of_thm th = 
    let
        val th = prop_of th
        val (prems, th) = (Logic.strip_imp_prems th, Logic.strip_imp_concl th)
        val (left, right) = Logic.dest_equals th
    in
        (Linker.collect_consts [left], Linker.collect_consts (right::prems))
    end

fun create_theorem th =
let
    val (left, right) = collect_consts_of_thm th
    val polycs = filter Linker.is_polymorphic left
    val tytab = fold (fn p => fn tab => fold (fn n => fn tab => Typtab.update (TVar n, ()) tab) (Misc_Legacy.typ_tvars (Linker.typ_of_constant p)) tab) polycs Typtab.empty
    fun check_const (c::cs) cs' =
        let
            val tvars = Misc_Legacy.typ_tvars (Linker.typ_of_constant c)
            val wrong = fold (fn n => fn wrong => wrong orelse is_none (Typtab.lookup tytab (TVar n))) tvars false
        in
            if wrong then raise PCompute "right hand side of theorem contains type variables which do not occur on the left hand side"
            else
                if null (tvars) then
                    check_const cs (c::cs')
                else
                    check_const cs cs'
        end
      | check_const [] cs' = cs'
    val monocs = check_const right []
in
    if null (polycs) then
        (monocs, MonoThm th)
    else
        (monocs, PolyThm (th, Linker.empty polycs, []))
end

fun create_pattern pat = 
let
    val cs = Linker.collect_consts [pat]
    val polycs = filter Linker.is_polymorphic cs
in
    if null (polycs) then
        MonoPattern pat
    else
        PolyPattern (pat, Linker.empty polycs, [])
end
             
fun create_computer machine thy pats ths =
    let
        fun add (MonoThm th) ths = th::ths
          | add (PolyThm (_, _, ths')) ths = ths'@ths
        fun addpat (MonoPattern p) pats = p::pats
          | addpat (PolyPattern (_, _, ps)) pats = ps@pats
        val ths = fold_rev add ths []
        val pats = fold_rev addpat pats []
    in
        Compute.make_with_cache machine thy pats ths
    end

fun update_computer computer pats ths = 
    let
        fun add (MonoThm th) ths = th::ths
          | add (PolyThm (_, _, ths')) ths = ths'@ths
        fun addpat (MonoPattern p) pats = p::pats
          | addpat (PolyPattern (_, _, ps)) pats = ps@pats
        val ths = fold_rev add ths []
        val pats = fold_rev addpat pats []
    in
        Compute.update_with_cache computer pats ths
    end

fun conv_subst thy (subst : Type.tyenv) =
    map (fn (iname, (sort, ty)) => (ctyp_of thy (TVar (iname, sort)), ctyp_of thy ty)) (Vartab.dest subst)

fun add_monos thy monocs pats ths =
    let
        val changed = Unsynchronized.ref false
        fun add monocs (th as (MonoThm _)) = ([], th)
          | add monocs (PolyThm (th, instances, instanceths)) =
            let
                val (newsubsts, instances) = Linker.add_instances thy instances monocs
                val _ = if not (null newsubsts) then changed := true else ()
                val newths = map (fn subst => Thm.instantiate (conv_subst thy subst, []) th) newsubsts
(*              val _ = if not (null newths) then (print ("added new theorems: ", newths); ()) else ()*)
                val newmonos = fold (fn th => fn monos => (snd (collect_consts_of_thm th))@monos) newths []
            in
                (newmonos, PolyThm (th, instances, instanceths@newths))
            end
        fun addpats monocs (pat as (MonoPattern _)) = pat
          | addpats monocs (PolyPattern (p, instances, instancepats)) =
            let
                val (newsubsts, instances) = Linker.add_instances thy instances monocs
                val _ = if not (null newsubsts) then changed := true else ()
                val newpats = map (fn subst => Envir.subst_term_types subst p) newsubsts
            in
                PolyPattern (p, instances, instancepats@newpats)
            end 
        fun step monocs ths =
            fold_rev (fn th =>
                      fn (newmonos, ths) =>
                         let 
                             val (newmonos', th') = add monocs th 
                         in
                             (newmonos'@newmonos, th'::ths)
                         end)
                     ths ([], [])
        fun loop monocs pats ths =
            let 
                val (monocs', ths') = step monocs ths 
                val pats' = map (addpats monocs) pats
            in
                if null (monocs') then
                    (pats', ths')
                else
                    loop monocs' pats' ths'
            end
        val result = loop monocs pats ths
    in
        (!changed, result)
    end

datatype cthm = ComputeThm of term list * sort list * term

fun thm2cthm th =
    let
        val {hyps, prop, shyps, ...} = Thm.rep_thm th
    in
        ComputeThm (hyps, shyps, prop)
    end

val cthm_ord' = prod_ord (prod_ord (list_ord Term_Ord.term_ord) (list_ord Term_Ord.sort_ord)) Term_Ord.term_ord

fun cthm_ord (ComputeThm (h1, sh1, p1), ComputeThm (h2, sh2, p2)) = cthm_ord' (((h1,sh1), p1), ((h2, sh2), p2))

structure CThmtab = Table(type key = cthm val ord = cthm_ord)

fun remove_duplicates ths =
    let
        val counter = Unsynchronized.ref 0
        val tab = Unsynchronized.ref (CThmtab.empty : unit CThmtab.table)
        val thstab = Unsynchronized.ref (Inttab.empty : thm Inttab.table)
        fun update th =
            let
                val key = thm2cthm th
            in
                case CThmtab.lookup (!tab) key of
                    NONE => ((tab := CThmtab.update_new (key, ()) (!tab)); thstab := Inttab.update_new (!counter, th) (!thstab); counter := !counter + 1)
                  | _ => ()
            end
        val _ = map update ths
    in
        map snd (Inttab.dest (!thstab))
    end

fun make_with_cache machine thy pats ths cs =
    let
        val ths = remove_duplicates ths
        val (monocs, ths) = fold_rev (fn th => 
                                      fn (monocs, ths) => 
                                         let val (m, t) = create_theorem th in 
                                             (m@monocs, t::ths)
                                         end)
                                     ths (cs, [])
        val pats = map create_pattern pats
        val (_, (pats, ths)) = add_monos thy monocs pats ths
        val computer = create_computer machine thy pats ths
    in
        PComputer (Theory.check_thy thy, computer, Unsynchronized.ref ths, Unsynchronized.ref pats)
    end

fun make machine thy ths cs = make_with_cache machine thy [] ths cs

fun add_instances (PComputer (thyref, computer, rths, rpats)) cs = 
    let
        val thy = Theory.deref thyref
        val (changed, (pats, ths)) = add_monos thy cs (!rpats) (!rths)
    in
        if changed then
            (update_computer computer pats ths;
             rths := ths;
             rpats := pats;
             true)
        else
            false

    end

fun add_instances' pc ts = add_instances pc (Linker.collect_consts ts)

fun rewrite pc cts =
    let
        val _ = add_instances' pc (map term_of cts)
        val computer = (computer_of pc)
    in
        map (fn ct => Compute.rewrite computer ct) cts
    end

fun simplify pc th = Compute.simplify (computer_of pc) th

fun make_theorem pc th vars = 
    let
        val _ = add_instances' pc [prop_of th]

    in
        Compute.make_theorem (computer_of pc) th vars
    end

fun instantiate pc insts th = 
    let
        val _ = add_instances' pc (map (term_of o snd) insts)
    in
        Compute.instantiate (computer_of pc) insts th
    end

fun evaluate_prem pc prem_no th = Compute.evaluate_prem (computer_of pc) prem_no th

fun modus_ponens pc prem_no th' th =
    let
        val _ = add_instances' pc [prop_of th']
    in
        Compute.modus_ponens (computer_of pc) prem_no th' th
    end    
                                                                                                    

end
