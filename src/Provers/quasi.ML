(*  Author:     Oliver Kutter, TU Muenchen

Reasoner for simple transitivity and quasi orders.
*)

(*

The package provides tactics trans_tac and quasi_tac that use
premises of the form

  t = u, t ~= u, t < u and t <= u

to
- either derive a contradiction, in which case the conclusion can be
  any term,
- or prove the concluson, which must be of the form t ~= u, t < u or
  t <= u.

Details:

1. trans_tac:
   Only premises of form t <= u are used and the conclusion must be of
   the same form.  The conclusion is proved, if possible, by a chain of
   transitivity from the assumptions.

2. quasi_tac:
   <= is assumed to be a quasi order and < its strict relative, defined
   as t < u == t <= u & t ~= u.  Again, the conclusion is proved from
   the assumptions.
   Note that the presence of a strict relation is not necessary for
   quasi_tac.  Configure decomp_quasi to ignore < and ~=.  A list of
   required theorems for both situations is given below.
*)

signature LESS_ARITH =
sig
  (* Transitivity of <=
     Note that transitivities for < hold for partial orders only. *)
  val le_trans: thm  (* [| x <= y; y <= z |] ==> x <= z *)

  (* Additional theorem for quasi orders *)
  val le_refl: thm  (* x <= x *)
  val eqD1: thm (* x = y ==> x <= y *)
  val eqD2: thm (* x = y ==> y <= x *)

  (* Additional theorems for premises of the form x < y *)
  val less_reflE: thm  (* x < x ==> P *)
  val less_imp_le : thm (* x < y ==> x <= y *)

  (* Additional theorems for premises of the form x ~= y *)
  val le_neq_trans : thm (* [| x <= y ; x ~= y |] ==> x < y *)
  val neq_le_trans : thm (* [| x ~= y ; x <= y |] ==> x < y *)

  (* Additional theorem for goals of form x ~= y *)
  val less_imp_neq : thm (* x < y ==> x ~= y *)

  (* Analysis of premises and conclusion *)
  (* decomp_x (`x Rel y') should yield SOME (x, Rel, y)
       where Rel is one of "<", "<=", "=" and "~=",
       other relation symbols cause an error message *)
  (* decomp_trans is used by trans_tac, it may only return Rel = "<=" *)
  val decomp_trans: theory -> term -> (term * string * term) option
  (* decomp_quasi is used by quasi_tac *)
  val decomp_quasi: theory -> term -> (term * string * term) option
end;

signature QUASI_TAC =
sig
  val trans_tac: Proof.context -> int -> tactic
  val quasi_tac: Proof.context -> int -> tactic
end;

functor Quasi_Tac(Less: LESS_ARITH): QUASI_TAC =
struct

(* Internal datatype for the proof *)
datatype proof
  = Asm of int
  | Thm of proof list * thm;

exception Cannot;
 (* Internal exception, raised if conclusion cannot be derived from
     assumptions. *)
exception Contr of proof;
  (* Internal exception, raised if contradiction ( x < x ) was derived *)

fun prove asms =
  let fun pr (Asm i) = List.nth (asms, i)
  |       pr (Thm (prfs, thm)) = (map pr prfs) MRS thm
  in pr end;

(* Internal datatype for inequalities *)
datatype less
   = Less  of term * term * proof
   | Le    of term * term * proof
   | NotEq of term * term * proof;

 (* Misc functions for datatype less *)
fun lower (Less (x, _, _)) = x
  | lower (Le (x, _, _)) = x
  | lower (NotEq (x,_,_)) = x;

fun upper (Less (_, y, _)) = y
  | upper (Le (_, y, _)) = y
  | upper (NotEq (_,y,_)) = y;

fun getprf   (Less (_, _, p)) = p
|   getprf   (Le   (_, _, p)) = p
|   getprf   (NotEq (_,_, p)) = p;

(* ************************************************************************ *)
(*                                                                          *)
(* mkasm_trans sign (t, n) :  theory -> (Term.term * int)  -> less          *)
(*                                                                          *)
(* Tuple (t, n) (t an assumption, n its index in the assumptions) is        *)
(* translated to an element of type less.                                   *)
(* Only assumptions of form x <= y are used, all others are ignored         *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkasm_trans sign (t, n) =
  case Less.decomp_trans sign t of
    SOME (x, rel, y) =>
    (case rel of
     "<="  =>  [Le (x, y, Asm n)]
    | _     => error ("trans_tac: unknown relation symbol ``" ^ rel ^
                 "''returned by decomp_trans."))
  | NONE => [];

(* ************************************************************************ *)
(*                                                                          *)
(* mkasm_quasi sign (t, n) : theory -> (Term.term * int) -> less            *)
(*                                                                          *)
(* Tuple (t, n) (t an assumption, n its index in the assumptions) is        *)
(* translated to an element of type less.                                   *)
(* Quasi orders only.                                                       *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkasm_quasi sign (t, n) =
  case Less.decomp_quasi sign t of
    SOME (x, rel, y) => (case rel of
      "<"   => if (x aconv y) then raise Contr (Thm ([Asm n], Less.less_reflE))
               else [Less (x, y, Asm n)]
    | "<="  => [Le (x, y, Asm n)]
    | "="   => [Le (x, y, Thm ([Asm n], Less.eqD1)),
                Le (y, x, Thm ([Asm n], Less.eqD2))]
    | "~="  => if (x aconv y) then
                  raise Contr (Thm ([(Thm ([(Thm ([], Less.le_refl)) ,(Asm n)], Less.le_neq_trans))], Less.less_reflE))
               else [ NotEq (x, y, Asm n),
                      NotEq (y, x,Thm ( [Asm n], thm "not_sym"))]
    | _     => error ("quasi_tac: unknown relation symbol ``" ^ rel ^
                 "''returned by decomp_quasi."))
  | NONE => [];


(* ************************************************************************ *)
(*                                                                          *)
(* mkconcl_trans sign t : theory -> Term.term -> less                       *)
(*                                                                          *)
(* Translates conclusion t to an element of type less.                      *)
(* Only for Conclusions of form x <= y or x < y.                            *)
(*                                                                          *)
(* ************************************************************************ *)


fun mkconcl_trans sign t =
  case Less.decomp_trans sign t of
    SOME (x, rel, y) => (case rel of
     "<="  => (Le (x, y, Asm ~1), Asm 0)
    | _  => raise Cannot)
  | NONE => raise Cannot;


(* ************************************************************************ *)
(*                                                                          *)
(* mkconcl_quasi sign t : theory -> Term.term -> less                       *)
(*                                                                          *)
(* Translates conclusion t to an element of type less.                      *)
(* Quasi orders only.                                                       *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkconcl_quasi sign t =
  case Less.decomp_quasi sign t of
    SOME (x, rel, y) => (case rel of
      "<"   => ([Less (x, y, Asm ~1)], Asm 0)
    | "<="  => ([Le (x, y, Asm ~1)], Asm 0)
    | "~="  => ([NotEq (x,y, Asm ~1)], Asm 0)
    | _  => raise Cannot)
| NONE => raise Cannot;


(* ******************************************************************* *)
(*                                                                     *)
(* mergeLess (less1,less2):  less * less -> less                       *)
(*                                                                     *)
(* Merge to elements of type less according to the following rules     *)
(*                                                                     *)
(* x <= y && y <= z ==> x <= z                                         *)
(* x <= y && x ~= y ==> x < y                                          *)
(* x ~= y && x <= y ==> x < y                                          *)
(*                                                                     *)
(* ******************************************************************* *)

fun mergeLess (Le (x, _, p) , Le (_ , z, q)) =
      Le (x, z, Thm ([p,q] , Less.le_trans))
|   mergeLess (Le (x, z, p) , NotEq (x', z', q)) =
      if (x aconv x' andalso z aconv z' )
       then Less (x, z, Thm ([p,q] , Less.le_neq_trans))
        else error "quasi_tac: internal error le_neq_trans"
|   mergeLess (NotEq (x, z, p) , Le (x' , z', q)) =
      if (x aconv x' andalso z aconv z')
      then Less (x, z, Thm ([p,q] , Less.neq_le_trans))
      else error "quasi_tac: internal error neq_le_trans"
|   mergeLess (_, _) =
      error "quasi_tac: internal error: undefined case";


(* ******************************************************************** *)
(* tr checks for valid transitivity step                                *)
(* ******************************************************************** *)

infix tr;
fun (Le (_, y, _))   tr (Le (x', _, _))   = ( y aconv x' )
  | _ tr _ = false;

(* ******************************************************************* *)
(*                                                                     *)
(* transPath (Lesslist, Less): (less list * less) -> less              *)
(*                                                                     *)
(* If a path represented by a list of elements of type less is found,  *)
(* this needs to be contracted to a single element of type less.       *)
(* Prior to each transitivity step it is checked whether the step is   *)
(* valid.                                                              *)
(*                                                                     *)
(* ******************************************************************* *)

fun transPath ([],lesss) = lesss
|   transPath (x::xs,lesss) =
      if lesss tr x then transPath (xs, mergeLess(lesss,x))
      else error "trans/quasi_tac: internal error transpath";

(* ******************************************************************* *)
(*                                                                     *)
(* less1 subsumes less2 : less -> less -> bool                         *)
(*                                                                     *)
(* subsumes checks whether less1 implies less2                         *)
(*                                                                     *)
(* ******************************************************************* *)

infix subsumes;
fun (Le (x, y, _)) subsumes (Le (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Le _) subsumes (Less _) =
      error "trans/quasi_tac: internal error: Le cannot subsume Less"
  | (NotEq(x,y,_)) subsumes (NotEq(x',y',_)) = x aconv x' andalso y aconv y' orelse x aconv y' andalso y aconv x'
  | _ subsumes _ = false;

(* ******************************************************************* *)
(*                                                                     *)
(* triv_solv less1 : less ->  proof option                     *)
(*                                                                     *)
(* Solves trivial goal x <= x.                                         *)
(*                                                                     *)
(* ******************************************************************* *)

fun triv_solv (Le (x, x', _)) =
    if x aconv x' then  SOME (Thm ([], Less.le_refl))
    else NONE
|   triv_solv _ = NONE;

(* ********************************************************************* *)
(* Graph functions                                                       *)
(* ********************************************************************* *)

(* *********************************************************** *)
(* Functions for constructing graphs                           *)
(* *********************************************************** *)

fun addEdge (v,d,[]) = [(v,d)]
|   addEdge (v,d,((u,dl)::el)) = if v aconv u then ((v,d@dl)::el)
    else (u,dl):: (addEdge(v,d,el));

(* ********************************************************************** *)
(*                                                                        *)
(* mkQuasiGraph constructs from a list of objects of type less a graph g, *)
(* by taking all edges that are candidate for a <=, and a list neqE, by   *)
(* taking all edges that are candiate for a ~=                            *)
(*                                                                        *)
(* ********************************************************************** *)

fun mkQuasiGraph [] = ([],[])
|   mkQuasiGraph lessList =
 let
 fun buildGraphs ([],leG, neqE) = (leG,  neqE)
  |   buildGraphs (l::ls, leG,  neqE) = case l of
       (Less (x,y,p)) =>
         let
          val leEdge  = Le (x,y, Thm ([p], Less.less_imp_le))
          val neqEdges = [ NotEq (x,y, Thm ([p], Less.less_imp_neq)),
                           NotEq (y,x, Thm ( [Thm ([p], Less.less_imp_neq)], thm "not_sym"))]
         in
           buildGraphs (ls, addEdge(y,[],(addEdge (x,[(y,leEdge)],leG))), neqEdges@neqE)
         end
     |  (Le (x,y,p))   => buildGraphs (ls, addEdge(y,[],(addEdge (x,[(y,l)],leG))), neqE)
     | _ =>  buildGraphs (ls, leG,  l::neqE) ;

in buildGraphs (lessList, [],  []) end;

(* ********************************************************************** *)
(*                                                                        *)
(* mkGraph constructs from a list of objects of type less a graph g       *)
(* Used for plain transitivity chain reasoning.                           *)
(*                                                                        *)
(* ********************************************************************** *)

fun mkGraph [] = []
|   mkGraph lessList =
 let
  fun buildGraph ([],g) = g
  |   buildGraph (l::ls, g) =  buildGraph (ls, (addEdge ((lower l),[((upper l),l)],g)))

in buildGraph (lessList, []) end;

(* *********************************************************************** *)
(*                                                                         *)
(* adjacent g u : (''a * 'b list ) list -> ''a -> 'b list                  *)
(*                                                                         *)
(* List of successors of u in graph g                                      *)
(*                                                                         *)
(* *********************************************************************** *)

fun adjacent eq_comp ((v,adj)::el) u =
    if eq_comp (u, v) then adj else adjacent eq_comp el u
|   adjacent _  []  _ = []

(* *********************************************************************** *)
(*                                                                         *)
(* dfs eq_comp g u v:                                                      *)
(* ('a * 'a -> bool) -> ('a  *( 'a * less) list) list ->                   *)
(* 'a -> 'a -> (bool * ('a * less) list)                                   *)
(*                                                                         *)
(* Depth first search of v from u.                                         *)
(* Returns (true, path(u, v)) if successful, otherwise (false, []).        *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs eq_comp g u v =
 let
    val pred = Unsynchronized.ref [];
    val visited = Unsynchronized.ref [];

    fun been_visited v = exists (fn w => eq_comp (w, v)) (!visited)

    fun dfs_visit u' =
    let val _ = visited := u' :: (!visited)

    fun update (x,l) = let val _ = pred := (x,l) ::(!pred) in () end;

    in if been_visited v then ()
    else (app (fn (v',l) => if been_visited v' then () else (
       update (v',l);
       dfs_visit v'; ()) )) (adjacent eq_comp g u')
     end
  in
    dfs_visit u;
    if (been_visited v) then (true, (!pred)) else (false , [])
  end;

(* ************************************************************************ *)
(*                                                                          *)
(* Begin: Quasi Order relevant functions                                    *)
(*                                                                          *)
(*                                                                          *)
(* ************************************************************************ *)

(* ************************************************************************ *)
(*                                                                          *)
(* findPath x y g: Term.term -> Term.term ->                                *)
(*                  (Term.term * (Term.term * less list) list) ->           *)
(*                  (bool, less list)                                       *)
(*                                                                          *)
(*  Searches a path from vertex x to vertex y in Graph g, returns true and  *)
(*  the list of edges forming the path, if a path is found, otherwise false *)
(*  and nil.                                                                *)
(*                                                                          *)
(* ************************************************************************ *)


 fun findPath x y g =
  let
    val (found, tmp) =  dfs (op aconv) g x y ;
    val pred = map snd tmp;

    fun path x y  =
      let
       (* find predecessor u of node v and the edge u -> v *)
       fun lookup v [] = raise Cannot
       |   lookup v (e::es) = if (upper e) aconv v then e else lookup v es;

       (* traverse path backwards and return list of visited edges *)
       fun rev_path v =
        let val l = lookup v pred
            val u = lower l;
        in
           if u aconv x then [l] else (rev_path u) @ [l]
        end
      in rev_path y end;

  in
   if found then (
    if x aconv y then (found,[(Le (x, y, (Thm ([], Less.le_refl))))])
    else (found, (path x y) ))
   else (found,[])
  end;


(* ************************************************************************ *)
(*                                                                          *)
(* findQuasiProof (leqG, neqE) subgoal:                                     *)
(* (Term.term * (Term.term * less list) list) * less list  -> less -> proof *)
(*                                                                          *)
(* Constructs a proof for subgoal by searching a special path in leqG and   *)
(* neqE. Raises Cannot if construction of the proof fails.                  *)
(*                                                                          *)
(* ************************************************************************ *)


(* As the conlusion can be either of form x <= y, x < y or x ~= y we have        *)
(* three cases to deal with. Finding a transitivity path from x to y with label  *)
(* 1. <=                                                                         *)
(*    This is simply done by searching any path from x to y in the graph leG.    *)
(*    The graph leG contains only edges with label <=.                           *)
(*                                                                               *)
(* 2. <                                                                          *)
(*    A path from x to y with label < can be found by searching a path with      *)
(*    label <= from x to y in the graph leG and merging the path x <= y with     *)
(*    a parallel edge x ~= y resp. y ~= x to x < y.                              *)
(*                                                                               *)
(* 3. ~=                                                                         *)
(*   If the conclusion is of form x ~= y, we can find a proof either directly,   *)
(*   if x ~= y or y ~= x are among the assumptions, or by constructing x ~= y if *)
(*   x < y or y < x follows from the assumptions.                                *)

fun findQuasiProof (leG, neqE) subgoal =
  case subgoal of (Le (x,y, _)) => (
   let
    val (xyLefound,xyLePath) = findPath x y leG
   in
    if xyLefound then (
     let
      val Le_x_y = (transPath (tl xyLePath, hd xyLePath))
     in getprf Le_x_y end )
    else raise Cannot
   end )
  | (Less (x,y,_))  => (
   let
    fun findParallelNeq []  = NONE
    |   findParallelNeq (e::es)  =
     if      (x aconv (lower e) andalso y aconv (upper e)) then SOME e
     else if (y aconv (lower e) andalso x aconv (upper e)) then SOME (NotEq (x,y, (Thm ([getprf e], thm "not_sym"))))
     else findParallelNeq es ;
   in
   (* test if there is a edge x ~= y respectivly  y ~= x and     *)
   (* if it possible to find a path x <= y in leG, thus we can conclude x < y *)
    (case findParallelNeq neqE of (SOME e) =>
      let
       val (xyLeFound,xyLePath) = findPath x y leG
      in
       if xyLeFound then (
        let
         val Le_x_y = (transPath (tl xyLePath, hd xyLePath))
         val Less_x_y = mergeLess (e, Le_x_y)
        in getprf Less_x_y end
       ) else raise Cannot
      end
    | _ => raise Cannot)
   end )
 | (NotEq (x,y,_)) =>
  (* First check if a single premiss is sufficient *)
  (case (Library.find_first (fn fact => fact subsumes subgoal) neqE, subgoal) of
    (SOME (NotEq (x, y, p)), NotEq (x', y', _)) =>
      if  (x aconv x' andalso y aconv y') then p
      else Thm ([p], thm "not_sym")
    | _  => raise Cannot
  )


(* ************************************************************************ *)
(*                                                                          *)
(* End: Quasi Order relevant functions                                      *)
(*                                                                          *)
(*                                                                          *)
(* ************************************************************************ *)

(* *********************************************************************** *)
(*                                                                         *)
(* solveLeTrans sign (asms,concl) :                                        *)
(* theory -> less list * Term.term -> proof list                           *)
(*                                                                         *)
(* Solves                                                                  *)
(*                                                                         *)
(* *********************************************************************** *)

fun solveLeTrans sign (asms, concl) =
 let
  val g = mkGraph asms
 in
   let
    val (subgoal, prf) = mkconcl_trans sign concl
    val (found, path) = findPath (lower subgoal) (upper subgoal) g
   in
    if found then [getprf (transPath (tl path, hd path))]
    else raise Cannot
  end
 end;


(* *********************************************************************** *)
(*                                                                         *)
(* solveQuasiOrder sign (asms,concl) :                                     *)
(* theory -> less list * Term.term -> proof list                           *)
(*                                                                         *)
(* Find proof if possible for quasi order.                                 *)
(*                                                                         *)
(* *********************************************************************** *)

fun solveQuasiOrder sign (asms, concl) =
 let
  val (leG, neqE) = mkQuasiGraph asms
 in
   let
   val (subgoals, prf) = mkconcl_quasi sign concl
   fun solve facts less =
       (case triv_solv less of NONE => findQuasiProof (leG, neqE) less
       | SOME prf => prf )
  in   map (solve asms) subgoals end
 end;

(* ************************************************************************ *)
(*                                                                          *)
(* Tactics                                                                  *)
(*                                                                          *)
(*  - trans_tac                                                          *)
(*  - quasi_tac, solves quasi orders                                        *)
(* ************************************************************************ *)


(* trans_tac - solves transitivity chains over <= *)

fun trans_tac ctxt = SUBGOAL (fn (A, n) => fn st =>
 let
  val thy = ProofContext.theory_of ctxt;
  val rfrees = map Free (Term.rename_wrt_term A (Logic.strip_params A));
  val Hs = map (fn H => subst_bounds (rfrees, H)) (Logic.strip_assums_hyp A);
  val C = subst_bounds (rfrees, Logic.strip_assums_concl A);
  val lesss = List.concat (ListPair.map (mkasm_trans thy) (Hs, 0 upto (length Hs - 1)));
  val prfs = solveLeTrans thy (lesss, C);

  val (subgoal, prf) = mkconcl_trans thy C;
 in
  Subgoal.FOCUS (fn {prems, ...} =>
    let val thms = map (prove prems) prfs
    in rtac (prove thms prf) 1 end) ctxt n st
 end
 handle Contr p => Subgoal.FOCUS (fn {prems, ...} => rtac (prove prems p) 1) ctxt n st
  | Cannot  => Seq.empty);


(* quasi_tac - solves quasi orders *)

fun quasi_tac ctxt = SUBGOAL (fn (A, n) => fn st =>
 let
  val thy = ProofContext.theory_of ctxt
  val rfrees = map Free (Term.rename_wrt_term A (Logic.strip_params A));
  val Hs = map (fn H => subst_bounds (rfrees, H)) (Logic.strip_assums_hyp A);
  val C = subst_bounds (rfrees, Logic.strip_assums_concl A);
  val lesss = flat (ListPair.map (mkasm_quasi thy) (Hs, 0 upto (length Hs - 1)));
  val prfs = solveQuasiOrder thy (lesss, C);
  val (subgoals, prf) = mkconcl_quasi thy C;
 in
  Subgoal.FOCUS (fn {prems, ...} =>
    let val thms = map (prove prems) prfs
    in rtac (prove thms prf) 1 end) ctxt n st
 end
 handle Contr p =>
    (Subgoal.FOCUS (fn {prems, ...} => rtac (prove prems p) 1) ctxt n st
      handle Subscript => Seq.empty)
  | Cannot => Seq.empty
  | Subscript => Seq.empty);

end;
