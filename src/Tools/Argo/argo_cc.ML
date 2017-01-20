(*  Title:      Tools/Argo/argo_cc.ML
    Author:     Sascha Boehme
    Author:     Dmitriy Traytel and Matthias Franze, TU Muenchen

Equality reasoning based on congurence closure. It features:

  * congruence closure for any term that participates in equalities
  * support for predicates

These features might be added:

  * caching of explanations while building proofs to obtain shorter proofs
    and faster proof checking
  * propagating relevant merges of equivalence classes to all other theory solvers
  * propagating new relevant negated equalities to all other theory solvers
  * creating lemma "f ~= g | a ~= b | f a = g b" for asserted negated equalities
    between "f a" and "g b" (dynamic ackermannization)

The implementation is inspired by:

  Robert Nieuwenhuis and Albert Oliveras. Fast Congruence Closure and
  Extensions. In Information and Computation, volume 205(4),
  pages 557-580, 2007.

  Harald Ganzinger, George Hagen, Robert Nieuwenhuis, Albert Oliveras,
  Cesare Tinelli. DPLL(T): Fast decision procedures. In Lecture Notes in
  Computer Science, volume 3114, pages 175-188. Springer, 2004.
*)

signature ARGO_CC =
sig
  (* context *)
  type context
  val context: context

  (* enriching the context *)
  val add_atom: Argo_Term.term -> context -> Argo_Lit.literal option * context

  (* main operations *)
  val assume: Argo_Common.literal -> context -> Argo_Lit.literal Argo_Common.implied * context
  val check: context -> Argo_Lit.literal Argo_Common.implied * context
  val explain: Argo_Lit.literal -> context -> (Argo_Cls.clause * context) option
  val add_level: context -> context
  val backtrack: context -> context
end

structure Argo_Cc: ARGO_CC =
struct

(* tables indexed by pairs of terms *)

val term2_ord = prod_ord Argo_Term.term_ord Argo_Term.term_ord

structure Argo_Term2tab = Table(type key = Argo_Term.term * Argo_Term.term val ord = term2_ord)


(* equality certificates *)

(*
  The solver keeps assumed equalities to produce explanations later on.

  A flat equality (lp, (t1, t2)) consists of the assumed literal and its proof
  as well as the terms t1 and t2 that are assumed to be equal. The literal expresses
  the equality t1 = t2.

  A congruence equality (t1, t2) is an equality t1 = t2 where both terms are
  applications (f a) and (g b).

  A symmetric equality eq is a marker for applying the symmetry rule to eq.
*)

datatype eq =
  Flat of Argo_Common.literal * (Argo_Term.term * Argo_Term.term) |
  Cong of Argo_Term.term * Argo_Term.term |
  Symm of eq

fun dest_eq (Flat (_, tp)) = tp
  | dest_eq (Cong tp) = tp
  | dest_eq (Symm eq) = swap (dest_eq eq)

fun symm (Symm eq) = eq
  | symm eq = Symm eq

fun negate (Flat ((lit, p), tp)) = Flat ((Argo_Lit.negate lit, p), tp)
  | negate (Cong tp) = Cong tp
  | negate (Symm eq) = Symm (negate eq)

fun dest_app (Argo_Term.T (_, Argo_Expr.App, [t1, t2])) = (t1, t2)
  | dest_app _ = raise Fail "bad application"


(* context *)

(*
  Each representative keeps track of the yet unimplied atoms in which this any member of
  this representative's equivalence class occurs. An atom is either a list of equalities
  between two terms, a list of predicates or a certificate. The certificate denotes that
  this equivalence class contains already implied predicates, and the literal accompanying
  the certificate specifies the polarity of these predicates.
*)

datatype atoms =
  Eqs of (Argo_Term.term * Argo_Term.term) list |
  Preds of Argo_Term.term list |
  Cert of Argo_Common.literal

(*
  Each representative has an associated ritem that contains the members of the
  equivalence class, the yet unimplied atoms and further information.
*)

type ritem = {
  size: int, (* the size of the equivalence class *)
  class: Argo_Term.term list, (* the equivalence class as a list of distinct terms *)
  occs: Argo_Term.term list, (* a list of all application terms in which members of
    the equivalence class occur either as function or as argument *)
  neqs: (Argo_Term.term * eq) list, (* a list of terms from disjoint equivalence classes,
    for each term of this list there is a certificate of a negated equality that is
    required to explain why the equivalence classes are disjoint *)
  atoms: atoms} (* the atoms of the representative *)

type repr = Argo_Term.term Argo_Termtab.table
type rdata = ritem Argo_Termtab.table
type apps = Argo_Term.term Argo_Term2tab.table
type trace = (Argo_Term.term * eq) Argo_Termtab.table

type context = {
  repr: repr, (* a table mapping terms to their representatives *)
  rdata: rdata, (* a table mapping representatives to their ritems *)
  apps: apps, (* a table mapping a function and an argument to their application *)
  trace: trace, (* the proof forest used to trace assumed and implied equalities *)
  prf: Argo_Proof.context, (* the proof context *)
  back: (repr * rdata * apps * trace) list} (* backtracking information *)

fun mk_context repr rdata apps trace prf back: context =
  {repr=repr, rdata=rdata, apps=apps, trace=trace, prf=prf, back=back}

val context =
  mk_context Argo_Termtab.empty Argo_Termtab.empty Argo_Term2tab.empty Argo_Termtab.empty
    Argo_Proof.cc_context []

fun repr_of repr t = the_default t (Argo_Termtab.lookup repr t)
fun repr_of' ({repr, ...}: context) = repr_of repr
fun put_repr t r = Argo_Termtab.update (t, r)

fun mk_ritem size class occs neqs atoms: ritem =
  {size=size, class=class, occs=occs, neqs=neqs, atoms=atoms}

fun as_ritem t = mk_ritem 1 [t] [] [] (Eqs [])
fun as_pred_ritem t = mk_ritem 1 [t] [] [] (Preds [t])
fun gen_ritem_of mk rdata r = the_default (mk r) (Argo_Termtab.lookup rdata r)
fun ritem_of rdata = gen_ritem_of as_ritem rdata
fun ritem_of_pred rdata = gen_ritem_of as_pred_ritem rdata
fun ritem_of' ({rdata, ...}: context) = ritem_of rdata
fun put_ritem r ri = Argo_Termtab.update (r, ri)

fun add_occ r occ = Argo_Termtab.map_default (r, as_ritem r)
  (fn {size, class, occs, neqs, atoms}: ritem => mk_ritem size class (occ :: occs) neqs atoms)

fun put_atoms atoms ({size, class, occs, neqs, ...}: ritem) = mk_ritem size class occs neqs atoms

fun add_eq_atom r atom = Argo_Termtab.map_default (r, as_ritem r)
  (fn ri as {atoms=Eqs atoms, ...}: ritem => put_atoms (Eqs (atom :: atoms)) ri
    | ri => put_atoms (Eqs [atom]) ri)

fun lookup_app apps tp = Argo_Term2tab.lookup apps tp
fun put_app tp app = Argo_Term2tab.update_new (tp, app)


(* traces for explanations *)

(*
  Assumed and implied equalities are collected in a proof forest for being able to
  produce explanations. For each equivalence class there is one proof tree. The
  equality certificates are oriented towards a root term, that is not necessarily
  the representative of the equivalence class.
*)

(*
  Whenever two equivalence classes are merged due to an equality t1 = t2, the shorter
  of the two paths, either from t1 to its root or t2 to its root, is re-oriented such
  that the relevant ti becomes the new root of its tree. Then, a new edge between ti
  and the other term of the equality t1 = t2 is added to connect the two proof trees.
*)

fun depth_of trace t =
  (case Argo_Termtab.lookup trace t of
    NONE => 0
  | SOME (t', _) => 1 + depth_of trace t')

fun reorient t trace =
  (case Argo_Termtab.lookup trace t of
    NONE => trace
  | SOME (t', eq) => Argo_Termtab.update (t', (t, symm eq)) (reorient t' trace))

fun new_edge from to eq trace = Argo_Termtab.update (from, (to, eq)) (reorient from trace)

fun with_shortest f (t1, t2) eq trace =
  (if depth_of trace t1 <= depth_of trace t2 then f t1 t2 eq else f t2 t1 (symm eq)) trace

fun add_edge eq trace = with_shortest new_edge (dest_eq eq) eq trace

(*
  To produce an explanation that t1 and t2 are equal, the paths to their root are
  extracted from the proof forest. Common ancestors in both paths are dropped.
*)

fun path_to_root trace path t =
  (case Argo_Termtab.lookup trace t of
    NONE => (t, path)
  | SOME (t', _) => path_to_root trace (t :: path) t')

fun drop_common root (t1 :: path1) (t2 :: path2) =
      if Argo_Term.eq_term (t1, t2) then drop_common t1 path1 path2 else root
  | drop_common root _ _ = root

fun common_ancestor trace t1 t2 =
  let val ((root, path1), (_, path2)) = apply2 (path_to_root trace []) (t1, t2)
  in drop_common root path1 path2 end

(*
  The proof of an assumed literal is typically a hypothesis. If the assumed literal is
  already known to be a unit literal, then there is already a proof for it.
*)

fun proof_of (lit, NONE) lits prf =
      (insert Argo_Lit.eq_lit (Argo_Lit.negate lit) lits, Argo_Proof.mk_hyp lit prf)
  | proof_of (_, SOME p) lits prf = (lits, (p, prf))

(*
  The explanation of equality between two terms t1 and t2 is computed based on the
  paths from t1 and t2 to their common ancestor t in the proof forest. For each of
  the two paths, a transitive proof of equality t1 = t and t = t2 is constructed,
  such that t1 = t2 follows by transitivity.
  
  Each edge of the paths denotes an assumed or implied equality. Implied equalities
  might be due to congruences (f a = g b) for which the equalities f = g and a = b
  need to be explained recursively.
*)

fun mk_eq_proof trace t1 t2 lits prf =
  if Argo_Term.eq_term (t1, t2) then (lits, Argo_Proof.mk_refl t1 prf)
  else
    let
      val root = common_ancestor trace t1 t2
      val (lits, (p1, prf)) = trans_proof I I trace t1 root lits prf
      val (lits, (p2, prf)) = trans_proof swap symm trace t2 root lits prf
    in (lits, Argo_Proof.mk_trans p1 p2 prf) end

and trans_proof sw sy trace t root lits prf =
  if Argo_Term.eq_term (t, root) then (lits, Argo_Proof.mk_refl t prf)
  else
    (case Argo_Termtab.lookup trace t of
      NONE => raise Fail "bad trace"
    | SOME (t', eq) => 
        let
          val (lits, (p1, prf)) = proof_step trace (sy eq) lits prf
          val (lits, (p2, prf)) = trans_proof sw sy trace t' root lits prf
        in (lits, uncurry Argo_Proof.mk_trans (sw (p1, p2)) prf) end)

and proof_step _ (Flat (cert, _)) lits prf = proof_of cert lits prf
  | proof_step trace (Cong tp) lits prf =
      let
        val ((t1, t2), (u1, u2)) = apply2 dest_app tp
        val (lits, (p1, prf)) = mk_eq_proof trace t1 u1 lits prf
        val (lits, (p2, prf)) = mk_eq_proof trace t2 u2 lits prf
      in (lits, Argo_Proof.mk_cong p1 p2 prf) end
  | proof_step trace (Symm eq) lits prf =
      proof_step trace eq lits prf ||> uncurry Argo_Proof.mk_symm

(*
  All clauses produced by a theory solver are expected to be a lemma.
  The lemma proof must hence be the last proof step.
*)

fun close_proof lit lits (p, prf) = (lit :: lits, Argo_Proof.mk_lemma [lit] p prf)

(*
  The explanation for the equality of t1 and t2 used the above algorithm.
*)

fun explain_eq lit t1 t2 ({repr, rdata, apps, trace, prf, back}: context) =
  let val (lits, (p, prf)) = mk_eq_proof trace t1 t2 [] prf |-> close_proof lit
  in ((lits, p), mk_context repr rdata apps trace prf back) end

(*
  The explanation that t1 and t2 are distinct uses the negated equality u1 ~= u2 that
  explains why the equivalence class containing t1 and u1 and the equivalence class
  containing t2 and u2 are disjoint. The explanations for t1 = u1 and u2 = t2 are
  constructed using the above algorithm. By transitivity, it follows that t1 ~= t2.  
*)

fun finish_proof (Flat ((lit, _), _)) lits p prf = close_proof lit lits (p, prf)
  | finish_proof (Cong _) _ _ _ = raise Fail "bad equality"
  | finish_proof (Symm eq) lits p prf = Argo_Proof.mk_symm p prf |-> finish_proof eq lits

fun explain_neq eq eq' ({repr, rdata, apps, trace, prf, back}: context) =
  let
    val (t1, t2) = dest_eq eq
    val (u1, u2) = dest_eq eq'

    val (lits, (p, prf)) = proof_step trace eq' [] prf
    val (lits, (p1, prf)) = mk_eq_proof trace t1 u1 lits prf
    val (lits, (p2, prf)) = mk_eq_proof trace u2 t2 lits prf
    val (lits, (p, prf)) = 
      Argo_Proof.mk_trans p p2 prf |-> Argo_Proof.mk_trans p1 |-> finish_proof eq lits
  in ((lits, p), mk_context repr rdata apps trace prf back) end


(* propagating new equalities *)

exception CONFLICT of Argo_Cls.clause * context

(*
  comment missing
*)

fun same_repr repr r (t, _) = Argo_Term.eq_term (r, repr_of repr t)

fun has_atom rdata r eq =
  (case #atoms (ritem_of rdata r) of
    Eqs eqs => member (Argo_Term.eq_term o snd) eqs eq
  | _ => false)

fun add_implied mk_lit repr rdata r neqs (atom as (t, eq)) (eqs, ls) =
  let val r' = repr_of repr t
  in
    if Argo_Term.eq_term (r, r') then (eqs, insert Argo_Lit.eq_lit (mk_lit eq) ls)
    else if exists (same_repr repr r') neqs andalso has_atom rdata r' eq then
      (eqs, Argo_Lit.Neg eq :: ls)
    else (atom :: eqs, ls)
  end

(*
  comment missing
*)

fun copy_occ repr app (eqs, occs, apps) =
  let val rp = apply2 (repr_of repr) (dest_app app)
  in
    (case lookup_app apps rp of
      SOME app' => (Cong (app, app') :: eqs, occs, apps)
    | NONE => (eqs, app :: occs, put_app rp app apps))
  end

(*
  comment missing
*)

fun add_lits (Argo_Lit.Pos _, _) = fold (cons o Argo_Lit.Pos)
  | add_lits (Argo_Lit.Neg _, _) = fold (cons o Argo_Lit.Neg)

fun join_atoms f (Eqs eqs1) (Eqs eqs2) ls = f eqs1 eqs2 ls
  | join_atoms _ (Preds ts1) (Preds ts2) ls = (Preds (union Argo_Term.eq_term ts1 ts2), ls)
  | join_atoms _ (Preds ts) (Cert lp) ls = (Cert lp, add_lits lp ts ls)
  | join_atoms _ (Cert lp) (Preds ts) ls = (Cert lp, add_lits lp ts ls)
  | join_atoms _ (Cert lp) (Cert _) ls = (Cert lp, ls)
  | join_atoms _ _ _ _ = raise Fail "bad atoms"

(*
  comment missing
*)

fun join r1 ri1 r2 ri2 eq (eqs, ls, {repr, rdata, apps, trace, prf, back}: context) =
  let
    val {size=size1, class=class1, occs=occs1, neqs=neqs1, atoms=atoms1}: ritem = ri1
    val {size=size2, class=class2, occs=occs2, neqs=neqs2, atoms=atoms2}: ritem = ri2

    val repr = fold (fn t => put_repr t r1) class2 repr
    val class = fold cons class2 class1
    val (eqs, occs, apps) = fold (copy_occ repr) occs2 (eqs, occs1, apps)
    val trace = add_edge eq trace
    val neqs = AList.merge Argo_Term.eq_term (K true) (neqs1, neqs2)
    fun add r neqs = fold (add_implied Argo_Lit.Pos repr rdata r neqs)
    fun adds eqs1 eqs2 ls = ([], ls) |> add r2 neqs2 eqs1 |> add r1 neqs1 eqs2 |>> Eqs
    val (atoms, ls) = join_atoms adds atoms1 atoms2 ls
    (* TODO: make sure that all implied literals are propagated *)
    val rdata = put_ritem r1 (mk_ritem (size1 + size2) class occs neqs atoms) rdata
  in (eqs, ls, mk_context repr rdata apps trace prf back) end

(*
  comment missing
*)

fun find_neq ({repr, ...}: context) ({neqs, ...}: ritem) r = find_first (same_repr repr r) neqs

fun check_join (r1, r2) (ri1, ri2) eq (ecx as (_, _, cx)) =
  (case find_neq cx ri2 r1 of
    SOME (_, eq') => raise CONFLICT (explain_neq (negate (symm eq)) eq' cx)
  | NONE =>
      (case find_neq cx ri1 r2 of
        SOME (_, eq') => raise CONFLICT (explain_neq (negate eq) eq' cx)
      | NONE => join r1 ri1 r2 ri2 eq ecx))

(*
  comment missing
*)

fun with_max_class f (rp as (r1, r2)) (rip as (ri1: ritem, ri2: ritem)) eq =
  if #size ri1 >= #size ri2 then f rp rip eq else f (r2, r1) (ri2, ri1) (symm eq)

(*
  comment missing
*)

fun propagate ([], ls, cx) = (rev ls, cx)
  | propagate (eq :: eqs, ls, cx) =
      let val rp = apply2 (repr_of' cx) (dest_eq eq)
      in 
        if Argo_Term.eq_term rp then propagate (eqs, ls, cx)
        else propagate (with_max_class check_join rp (apply2 (ritem_of' cx) rp) eq (eqs, ls, cx))
      end

fun without lit (lits, cx) = (Argo_Common.Implied (remove Argo_Lit.eq_lit lit lits), cx)

fun flat_merge (lp as (lit, _)) eq cx = without lit (propagate ([Flat (lp, eq)], [], cx))
  handle CONFLICT (cls, cx) => (Argo_Common.Conflict cls, cx)

(*
  comment missing
*)

fun app_merge app tp (cx as {repr, rdata, apps, trace, prf, back}: context) =
  let val rp as (r1, r2) = apply2 (repr_of repr) tp
  in
    (case lookup_app apps rp of
      SOME app' =>
        (case propagate ([Cong (app, app')], [], cx) of
          ([], cx) => cx
        | _ => raise Fail "bad application merge")
    | NONE =>
        let val rdata = add_occ r1 app (add_occ r2 app rdata)
        in mk_context repr rdata (put_app rp app apps) trace prf back end)
  end

(*
  A negated equality between t1 and t2 is only recorded if t1 and t2 are not already known
  to belong to the same class. In that case, a conflict is raised with an explanation
  why t1 and t2 are equal. Otherwise, the classes of t1 and t2 are marked as disjoint by
  storing the negated equality in the ritems of t1's and t2's representative. All equalities
  between terms of t1's and t2's class are implied as negated equalities. Those equalities
  are found in the ritems of t1's and t2's representative.
*)

fun note_neq eq (r1, r2) (t1, t2) ({repr, rdata, apps, trace, prf, back}: context) =
  let
    val {size=size1, class=class1, occs=occs1, neqs=neqs1, atoms=atoms1}: ritem = ritem_of rdata r1
    val {size=size2, class=class2, occs=occs2, neqs=neqs2, atoms=atoms2}: ritem = ritem_of rdata r2

    fun add r (Eqs eqs) ls = fold (add_implied Argo_Lit.Neg repr rdata r []) eqs ([], ls) |>> Eqs
      | add _ _ _ = raise Fail "bad negated equality between predicates"
    val ((atoms1, atoms2), ls) = [] |> add r2 atoms1 ||>> add r1 atoms2
    val ri1 = mk_ritem size1 class1 occs1 ((t2, eq) :: neqs1) atoms1
    val ri2 = mk_ritem size2 class2 occs2 ((t1, symm eq) :: neqs2) atoms2
  in (ls, mk_context repr (put_ritem r1 ri1 (put_ritem r2 ri2 rdata)) apps trace prf back) end

fun flat_neq (lp as (lit, _)) (tp as (t1, t2)) cx =
  let val rp = apply2 (repr_of' cx) tp
  in
    if Argo_Term.eq_term rp then
      let val (cls, cx) = explain_eq (Argo_Lit.negate lit) t1 t2 cx
      in (Argo_Common.Conflict cls, cx) end
    else without lit (note_neq (Flat (lp, tp)) rp tp cx)
  end


(* declaring atoms *)

(*
  Only a genuinely new equality term t for the equality "t1 = t2" is added. If t1 and t2 belong
  to the same equality class or if the classes of t1 and t2 are known to be disjoint, the
  respective literal is returned together with an unmodified context.
*)

fun add_eq_term t t1 t2 (rp as (r1, r2)) (cx as {repr, rdata, apps, trace, prf, back}: context) =
  if Argo_Term.eq_term rp then (SOME (Argo_Lit.Pos t), cx)
  else if is_some (find_neq cx (ritem_of rdata r1) r2) then (SOME (Argo_Lit.Neg t), cx)
  else
    let val rdata = add_eq_atom r1 (t2, t) (add_eq_atom r2 (t1, t) rdata)
    in (NONE, mk_context repr rdata apps trace prf back) end

(*
  Only a genuinely new predicate t, which is an application "t1 t2", is added.
  If there is a predicate that is known to be congruent to the representatives of t1 and t2,
  and that predicate or its negation has already been assummed, the respective literal of t
  is returned together with an unmodified context.
*)

fun add_pred_term t rp (cx as {repr, rdata, apps, trace, prf, back}: context) =
  (case lookup_app apps rp of
    NONE => (NONE, mk_context repr (put_ritem t (as_pred_ritem t) rdata) apps trace prf back)
  | SOME app =>
      (case `(ritem_of_pred rdata) (repr_of repr app) of
        ({atoms=Cert (Argo_Lit.Pos _, _), ...}: ritem, _) => (SOME (Argo_Lit.Pos t), cx)
      | ({atoms=Cert (Argo_Lit.Neg _, _), ...}: ritem, _) => (SOME (Argo_Lit.Neg t), cx)
      | (ri as {atoms=Preds ts, ...}: ritem, r) =>
          let val rdata = put_ritem r (put_atoms (Preds (t :: ts)) ri) rdata
          in (NONE, mk_context repr rdata apps trace prf back) end
      | ({atoms=Eqs _, ...}: ritem, _) => raise Fail "bad predicate"))

(*
  For each term t that is an application "t1 t2", the reflexive equality t = t1 t2 is added
  to the context. This is required for propagations of congruences.
*)

fun flatten (t as Argo_Term.T (_, Argo_Expr.App, [t1, t2])) cx =
      flatten t1 (flatten t2 (app_merge t (t1, t2) cx))
  | flatten _ cx = cx

(*
  Atoms to be added to the context must either be an equality "t1 = t2" or
  an application "t1 t2" (a predicate). Besides adding the equality or the application,
  reflexive equalities for for all applications in the terms t1 and t2 are added.
*)

fun add_atom (t as Argo_Term.T (_, Argo_Expr.Eq, [t1, t2])) cx =
      add_eq_term t t1 t2 (apply2 (repr_of' cx) (t1, t2)) (flatten t1 (flatten t2 cx))
  | add_atom (t as Argo_Term.T (_, Argo_Expr.App, [t1, t2])) cx =
      let val cx = flatten t1 (flatten t2 (app_merge t (t1, t2) cx))
      in add_pred_term t (apply2 (repr_of' cx) (t1, t2)) cx end
  | add_atom _ cx = (NONE, cx)


(* assuming external knowledge *)

(*
  Assuming a predicate r replaces all predicate atoms of r's ritem with the assumed certificate.
  The predicate atoms are implied, either with positive or with negative polarity based on
  the assumption.

  There must not be a certificate for r since otherwise r would have been assumed before already.
*)

fun assume_pred lit mk_lit cert r ({repr, rdata, apps, trace, prf, back}: context) =
  (case ritem_of_pred rdata r of
    {size, class, occs, neqs, atoms=Preds ts}: ritem =>
      let val rdata = put_ritem r (mk_ritem size class occs neqs cert) rdata
      in without lit (map mk_lit ts, mk_context repr rdata apps trace prf back) end
  | _ => raise Fail "bad predicate assumption")

(*
  Assumed equalities "t1 = t2" are treated as flat equalities between terms t1 and t2.
  If t1 and t2 are applications, congruences are propagated as part of the merge between t1 and t2.
  Negated equalities are handled likewise.

  Assumed predicates do not trigger congruences. Only predicates of the same class are implied.
*)

fun assume (lp as (Argo_Lit.Pos (Argo_Term.T (_, Argo_Expr.Eq, [t1, t2])), _)) cx =
      flat_merge lp (t1, t2) cx
  | assume (lp as (Argo_Lit.Neg (Argo_Term.T (_, Argo_Expr.Eq, [t1, t2])), _)) cx =
      flat_neq lp (t1, t2) cx
  | assume (lp as (lit as Argo_Lit.Pos (t as Argo_Term.T (_, Argo_Expr.App, [_, _])), _)) cx =
      assume_pred lit Argo_Lit.Pos (Cert lp) (repr_of' cx t) cx
  | assume (lp as (lit as Argo_Lit.Neg (t as Argo_Term.T (_, Argo_Expr.App, [_, _])), _)) cx =
      assume_pred lit Argo_Lit.Neg (Cert lp) (repr_of' cx t) cx
  | assume _ cx = (Argo_Common.Implied [], cx)


(* checking for consistency and pending implications *)

(*
  The internal model is always kept consistent. All implications are propagated as soon as
  new information is assumed. Hence, there is nothing to be done here.
*)

fun check cx = (Argo_Common.Implied [], cx)


(* explanations *)

(*
  The explanation for the predicate t, which is an application of t1 and t2, is constructed
  from the explanation of the predicate application "u1 u2" as well as the equalities "u1 = t1"
  and "u2 = t2" which both are constructed from the proof forest. The substitution rule is
  the proof step that concludes "t1 t2" from "u1 u2" and the two equalities "u1 = t1"
  and "u2 = t2".

  The atoms part of the ritem of t's representative must be a certificate of an already
  assumed predicate for otherwise there would be no explanation for t.
*)

fun explain_pred lit t t1 t2 ({repr, rdata, apps, trace, prf, back}: context) =
  (case ritem_of_pred rdata (repr_of repr t) of
    {atoms=Cert (cert as (lit', _)), ...}: ritem =>
      let
        val (u1, u2) = dest_app (Argo_Lit.term_of lit')
        val (lits, (p, prf)) = proof_of cert [] prf
        val (lits, (p1, prf)) = mk_eq_proof trace u1 t1 lits prf
        val (lits, (p2, prf)) = mk_eq_proof trace u2 t2 lits prf
        val (lits, (p, prf)) = Argo_Proof.mk_subst p p1 p2 prf |> close_proof lit lits
      in ((lits, p), mk_context repr rdata apps trace prf back) end
  | _ => raise Fail "no explanation for bad predicate")

(*
  Explanations are produced based on the proof forest that is constructed while assuming new
  information and propagating this among the internal data structures.
  
  For predicates, no distinction between both polarities needs to be done here. The atoms
  part of the relevant ritem knows the assumed polarity.
*)

fun explain (lit as Argo_Lit.Pos (Argo_Term.T (_, Argo_Expr.Eq, [t1, t2]))) cx =
      SOME (explain_eq lit t1 t2 cx)
  | explain (lit as Argo_Lit.Neg (Argo_Term.T (_, Argo_Expr.Eq, [t1, t2]))) cx =
      let val (_, eq) = the (find_neq cx (ritem_of' cx (repr_of' cx t1)) (repr_of' cx t2))
      in SOME (explain_neq (Flat ((lit, NONE), (t1, t2))) eq cx) end
  | explain (lit as (Argo_Lit.Pos (t as Argo_Term.T (_, Argo_Expr.App, [t1, t2])))) cx =
      SOME (explain_pred lit t t1 t2 cx)
  | explain (lit as (Argo_Lit.Neg (t as Argo_Term.T (_, Argo_Expr.App, [t1, t2])))) cx =
      SOME (explain_pred lit t t1 t2 cx)
  | explain _ _ = NONE


(* backtracking *)

(*
  All information that needs to be reconstructed on backtracking is stored on the backtracking
  stack. On backtracking any current information is replaced by what was stored before. No copying
  nor subtle updates are required thanks to immutable data structures.
*)

fun add_level ({repr, rdata, apps, trace, prf, back}: context) =
  mk_context repr rdata apps trace prf ((repr, rdata, apps, trace) :: back)

fun backtrack ({back=[], ...}: context) = raise Empty
  | backtrack ({prf, back=(repr, rdata, apps, trace) :: back, ...}: context) =
      mk_context repr rdata apps trace prf back

end
