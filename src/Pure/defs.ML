(*  Title:      Pure/General/defs.ML
    ID:         $Id$
    Author:     Steven Obua, TU Muenchen

    Checks if definitions preserve consistency of logic by enforcing
    that there are no cyclic definitions. The algorithm is described in
    "An Algorithm for Determining Definitional Cycles in Higher-Order Logic with Overloading",
    Steven Obua, technical report, to be written :-)
*)

signature DEFS =
sig
  type graph
  val empty: graph
  val declare: string * typ -> graph -> graph
  val define: Pretty.pp -> string * typ -> string -> (string * typ) list -> graph -> graph
  val finalize: string * typ -> graph -> graph
  val merge: Pretty.pp -> graph -> graph -> graph

  val finals : graph -> (typ list) Symtab.table

  (* If set to true then the exceptions CIRCULAR and INFINITE_CHAIN return the full
     chain of definitions that lead to the exception. In the beginning, chain_history
     is initialized with the Isabelle environment variable DEFS_CHAIN_HISTORY. *)
  val set_chain_history : bool -> unit
  val chain_history : unit -> bool

  datatype overloadingstate = Open | Closed | Final

  val overloading_info : graph -> string -> (typ * (string*typ) list * overloadingstate) option
  val fast_overloading_info : graph -> string -> (typ * int * overloadingstate) option
end

structure Defs :> DEFS = struct

type tyenv = Type.tyenv
type edgelabel = (int * typ * typ * (typ * string * string) list)

datatype overloadingstate = Open | Closed | Final

datatype node = Node of
         typ  (* most general type of constant *)
         * defnode Symtab.table
             (* a table of defnodes, each corresponding to 1 definition of the
                constant for a particular type, indexed by axiom name *)
         * (unit Symtab.table) Symtab.table
             (* a table of all back referencing defnodes to this node,
                indexed by node name of the defnodes *)
         * typ list (* a list of all finalized types *)
         * overloadingstate

     and defnode = Defnode of
         typ  (* type of the constant in this particular definition *)
         * (edgelabel list) Symtab.table (* The edges, grouped by nodes. *)

fun getnode graph noderef = the (Symtab.lookup (graph, noderef))
fun get_nodedefs (Node (_, defs, _, _, _)) = defs
fun get_defnode (Node (_, defs, _, _, _)) defname = Symtab.lookup (defs, defname)
fun get_defnode' graph noderef defname =
    Symtab.lookup (get_nodedefs (the (Symtab.lookup (graph, noderef))), defname)

fun table_size table = Symtab.foldl (fn (x, _) => x+1) (0, table)

datatype graphaction = Declare of string * typ
                     | Define of string * typ * string * string * (string * typ) list
                     | Finalize of string * typ

type graph = int * (string Symtab.table) * (graphaction list) * (node Symtab.table)

val CHAIN_HISTORY =
    let
      fun f c = if Char.isSpace c then "" else String.str (Char.toUpper c)
      val env = String.translate f (getenv "DEFS_CHAIN_HISTORY")
    in
      ref (env = "ON" orelse env = "TRUE")
    end

fun set_chain_history b = CHAIN_HISTORY := b
fun chain_history () = !CHAIN_HISTORY

val empty = (0, Symtab.empty, [], Symtab.empty)

exception DEFS of string;
exception CIRCULAR of (typ * string * string) list;
exception INFINITE_CHAIN of (typ * string * string) list;
exception CLASH of string * string * string;
exception FINAL of string * typ;

fun def_err s = raise (DEFS s)

fun no_forwards defs =
    Symtab.foldl
    (fn (closed, (_, Defnode (_, edges))) =>
        if not closed then false else Symtab.is_empty edges)
    (true, defs)

fun checkT' (Type (a, Ts)) = Type (a, map checkT' Ts)
  | checkT' (TFree (a, _)) = TVar ((a, 0), [])        (* FIXME !? *)
  | checkT' (TVar ((a, 0), _)) = TVar ((a, 0), [])
  | checkT' (T as TVar _) = raise TYPE ("Illegal schematic type variable encountered", [T], []);

val checkT = Term.compress_type o checkT';

fun rename ty1 ty2 = Logic.incr_tvar ((maxidx_of_typ ty1)+1) ty2;

fun subst_incr_tvar inc t =
    if (inc > 0) then
      let
        val tv = typ_tvars t
        val t' = Logic.incr_tvar inc t
        fun update_subst (((n,i), _), s) =
            Vartab.update (((n, i), ([], TVar ((n, i+inc), []))), s)
      in
        (t',List.foldl update_subst Vartab.empty tv)
      end
    else
      (t, Vartab.empty)

fun subst s ty = Envir.norm_type s ty

fun subst_history s history = map (fn (ty, cn, dn) => (subst s ty, cn, dn)) history

fun is_instance instance_ty general_ty =
    Type.typ_instance Type.empty_tsig (instance_ty, general_ty)

fun is_instance_r instance_ty general_ty =
    is_instance instance_ty (rename instance_ty general_ty)

fun unify ty1 ty2 =
    SOME (fst (Type.unify Type.empty_tsig (Vartab.empty, 0) (ty1, ty2)))
    handle Type.TUNIFY => NONE

(*
   Unifies ty1 and ty2, renaming ty1 and ty2 so that they have greater indices than max and
   so that they are different. All indices in ty1 and ty2 are supposed to be less than or
   equal to max.
   Returns SOME (max', s1, s2), so that s1(ty1) = s2(ty2) and max' is greater or equal than
   all indices in s1, s2, ty1, ty2.
*)
fun unify_r max ty1 ty2 =
    let
      val max = Int.max(max, 0)
      val max1 = max (* >= maxidx_of_typ ty1 *)
      val max2 = max (* >= maxidx_of_typ ty2 *)
      val max = Int.max(max, Int.max (max1, max2))
      val (ty1, s1) = subst_incr_tvar (max + 1) ty1
      val (ty2, s2) = subst_incr_tvar (max + max1 + 2) ty2
      val max = max + max1 + max2 + 2
      fun merge a b = Vartab.merge (fn _ => false) (a, b)
    in
      case unify ty1 ty2 of
        NONE => NONE
      | SOME s => SOME (max, merge s1 s, merge s2 s)
    end

fun can_be_unified_r ty1 ty2 =
    let
      val ty2 = rename ty1 ty2
    in
      case unify ty1 ty2 of
        NONE => false
      | _ => true
    end

fun can_be_unified ty1 ty2 =
    case unify ty1 ty2 of
      NONE => false
    | _ => true

fun normalize_edge_idx (edge as (maxidx, u1, v1, history)) =
    if maxidx <= 1000000 then edge else
    let

      fun idxlist idx extract_ty inject_ty (tab, max) ts =
          foldr
            (fn (e, ((tab, max), ts)) =>
                let
                  val ((tab, max), ty) = idx (tab, max) (extract_ty e)
                  val e = inject_ty (ty, e)
                in
                  ((tab, max), e::ts)
                end)
            ((tab,max), []) ts

      fun idx (tab,max) (TVar ((a,i),_)) =
          (case Inttab.lookup (tab, i) of
             SOME j => ((tab, max), TVar ((a,j),[]))
           | NONE => ((Inttab.update ((i, max), tab), max+1), TVar ((a,max),[])))
        | idx (tab,max) (Type (t, ts)) =
          let
            val ((tab, max), ts) = idxlist idx I fst (tab, max) ts
          in
            ((tab,max), Type (t, ts))
          end
        | idx (tab, max) ty = ((tab, max), ty)

      val ((tab,max), u1) = idx (Inttab.empty, 0) u1
      val ((tab,max), v1) = idx (tab, max) v1
      val ((tab,max), history) =
          idxlist idx
            (fn (ty,_,_) => ty)
            (fn (ty, (_, s1, s2)) => (ty, s1, s2))
            (tab, max) history
    in
      (max, u1, v1, history)
    end

fun compare_edges (e1 as (maxidx1, u1, v1, history1)) (e2 as (maxidx2, u2, v2, history2)) =
    let
      val t1 = u1 --> v1
      val t2 = Logic.incr_tvar (maxidx1+1) (u2 --> v2)
    in
      if (is_instance t1 t2) then
        (if is_instance t2 t1 then
           SOME (int_ord (length history2, length history1))
         else
           SOME LESS)
      else if (is_instance t2 t1) then
        SOME GREATER
      else
        NONE
    end

fun merge_edges_1 (x, []) = [x]
  | merge_edges_1 (x, (y::ys)) =
    (case compare_edges x y of
       SOME LESS => (y::ys)
     | SOME EQUAL => (y::ys)
     | SOME GREATER => merge_edges_1 (x, ys)
     | NONE => y::(merge_edges_1 (x, ys)))

fun merge_edges xs ys = foldl merge_edges_1 xs ys

fun declare' (g as (cost, axmap, actions, graph)) (cty as (name, ty)) =
    (cost, axmap, (Declare cty)::actions,
     Symtab.update_new ((name, Node (ty, Symtab.empty, Symtab.empty, [], Open)), graph))
    handle Symtab.DUP _ =>
           let
             val (Node (gty, _, _, _, _)) = the (Symtab.lookup(graph, name))
           in
             if is_instance_r ty gty andalso is_instance_r gty ty then
               g
             else
               def_err "constant is already declared with different type"
           end

fun declare'' g (name, ty) = declare' g (name, checkT ty)

val axcounter = ref (IntInf.fromInt 0)
fun newaxname axmap axname =
    let
      val c = !axcounter
      val _ = axcounter := c+1
      val axname' = axname^"_"^(IntInf.toString c)
    in
      (Symtab.update ((axname', axname), axmap), axname')
    end

fun translate_ex axmap x =
    let
      fun translate (ty, nodename, axname) =
          (ty, nodename, the (Symtab.lookup (axmap, axname)))
    in
      case x of
        INFINITE_CHAIN chain => raise (INFINITE_CHAIN (map translate chain))
      | CIRCULAR cycle => raise (CIRCULAR (map translate cycle))
      | _ => raise x
    end

fun define' (cost, axmap, actions, graph) (mainref, ty) axname orig_axname body =
    let
      val mainnode  = (case Symtab.lookup (graph, mainref) of
                         NONE => def_err ("constant "^mainref^" is not declared")
                       | SOME n => n)
      val (Node (gty, defs, backs, finals, _)) = mainnode
      val _ = (if is_instance_r ty gty then ()
               else def_err "type of constant does not match declared type")
      fun check_def (s, Defnode (ty', _)) =
          (if can_be_unified_r ty ty' then
             raise (CLASH (mainref, axname, s))
           else if s = axname then
             def_err "name of axiom is already used for another definition of this constant"
           else false)
      val _ = Symtab.exists check_def defs
      fun check_final finalty =
          (if can_be_unified_r finalty ty then
             raise (FINAL (mainref, finalty))
           else
             true)
      val _ = forall check_final finals

      (* now we know that the only thing that can prevent acceptance of the definition
         is a cyclic dependency *)

      fun insert_edges edges (nodename, links) =
          (if links = [] then
             edges
           else
             let
               val links = map normalize_edge_idx links
             in
               Symtab.update ((nodename,
                               case Symtab.lookup (edges, nodename) of
                                 NONE => links
                               | SOME links' => merge_edges links' links),
                              edges)
             end)

      fun make_edges ((bodyn, bodyty), edges) =
          let
            val bnode =
                (case Symtab.lookup (graph, bodyn) of
                   NONE => def_err "body of constant definition references undeclared constant"
                 | SOME x => x)
            val (Node (general_btyp, bdefs, bbacks, bfinals, closed)) = bnode
          in
            if closed = Final then edges else
            case unify_r 0 bodyty general_btyp of
              NONE => edges
            | SOME (maxidx, sigma1, sigma2) =>
              if exists (is_instance_r bodyty) bfinals then
                edges
              else
                let
                  fun insert_trans_edges ((step1, edges), (nodename, links)) =
                      let
                        val (maxidx1, alpha1, beta1, defname) = step1
                        fun connect (maxidx2, alpha2, beta2, history) =
                            case unify_r (Int.max (maxidx1, maxidx2)) beta1 alpha2 of
                              NONE => NONE
                            | SOME (max, sleft, sright) =>
                              SOME (max, subst sleft alpha1, subst sright beta2,
                                    if !CHAIN_HISTORY then
                                      ((subst sleft beta1, bodyn, defname)::
                                       (subst_history sright history))
                                    else [])
                        val links' = List.mapPartial connect links
                      in
                        (step1, insert_edges edges (nodename, links'))
                      end

                  fun make_edges' ((swallowed, edges),
                                   (def_name, Defnode (def_ty, def_edges))) =
                      if swallowed then
                        (swallowed, edges)
                      else
                        (case unify_r 0 bodyty def_ty of
                           NONE => (swallowed, edges)
                         | SOME (maxidx, sigma1, sigma2) =>
                           (is_instance_r bodyty def_ty,
                            snd (Symtab.foldl insert_trans_edges
                              (((maxidx, subst sigma1 ty, subst sigma2 def_ty, def_name),
                                edges), def_edges))))
                  val (swallowed, edges) = Symtab.foldl make_edges' ((false, edges), bdefs)
                in
                  if swallowed then
                    edges
                  else
                    insert_edges edges
                    (bodyn, [(maxidx, subst sigma1 ty, subst sigma2 general_btyp,[])])
                end
          end

      val edges = foldl make_edges Symtab.empty body

      (* We also have to add the backreferences that this new defnode induces. *)
      fun install_backrefs (graph, (noderef, links)) =
          if links <> [] then
            let
              val (Node (ty, defs, backs, finals, closed)) = getnode graph noderef
              val _ = if closed = Final then
                        sys_error ("install_backrefs: closed node cannot be updated")
                      else ()
              val defnames =
                  (case Symtab.lookup (backs, mainref) of
                     NONE => Symtab.empty
                   | SOME s => s)
              val defnames' = Symtab.update_new ((axname, ()), defnames)
              val backs' = Symtab.update ((mainref,defnames'), backs)
            in
              Symtab.update ((noderef, Node (ty, defs, backs', finals, closed)), graph)
            end
          else
            graph

      val graph = Symtab.foldl install_backrefs (graph, edges)

      val (Node (_, _, backs, _, closed)) = getnode graph mainref
      val closed =
          if closed = Final then sys_error "define: closed node"
          else if closed = Open andalso is_instance_r gty ty then Closed else closed

      val thisDefnode = Defnode (ty, edges)
      val graph = Symtab.update ((mainref, Node (gty, Symtab.update_new
        ((axname, thisDefnode), defs), backs, finals, closed)), graph)

      (* Now we have to check all backreferences to this node and inform them about
         the new defnode. In this section we also check for circularity. *)
      fun update_backrefs ((backs, graph), (noderef, defnames)) =
          let
            fun update_defs ((defnames, graph),(defname, _)) =
                let
                  val (Node (nodety, nodedefs, nodebacks, nodefinals, closed)) =
                      getnode graph noderef
                  val _ = if closed = Final then sys_error "update_defs: closed node" else ()
                  val (Defnode (def_ty, defnode_edges)) =
                      the (Symtab.lookup (nodedefs, defname))
                  val edges = the (Symtab.lookup (defnode_edges, mainref))
                  val refclosed = ref false

                  (* the type of thisDefnode is ty *)
                  fun update (e as (max, alpha, beta, history), (changed, edges)) =
                      case unify_r max beta ty of
                        NONE => (changed, e::edges)
                      | SOME (max', s_beta, s_ty) =>
                        let
                          val alpha' = subst s_beta alpha
                          val ty' = subst s_ty ty
                          val _ =
                              if noderef = mainref andalso defname = axname then
                                (case unify alpha' ty' of
                                   NONE =>
                                   if (is_instance_r ty' alpha') then
                                     raise (INFINITE_CHAIN (
                                            (alpha', mainref, axname)::
                                            (subst_history s_beta history)@
                                            [(ty', mainref, axname)]))
                                   else ()
                                 | SOME s =>
                                   raise (CIRCULAR (
                                          (subst s alpha', mainref, axname)::
                                          (subst_history s (subst_history s_beta history))@
                                          [(subst s ty', mainref, axname)])))
                              else ()
                        in
                          if is_instance_r beta ty then
                            (true, edges)
                          else
                            (changed, e::edges)
                        end

                  val (changed, edges') = foldl update (false, []) edges
                  val defnames' = if edges' = [] then
                                    defnames
                                  else
                                    Symtab.update ((defname, ()), defnames)
                in
                  if changed then
                    let
                      val defnode_edges' =
                          if edges' = [] then
                            Symtab.delete mainref defnode_edges
                          else
                            Symtab.update ((mainref, edges'), defnode_edges)
                      val defnode' = Defnode (def_ty, defnode_edges')
                      val nodedefs' = Symtab.update ((defname, defnode'), nodedefs)
                      val closed = if closed = Closed andalso Symtab.is_empty defnode_edges'
                                      andalso no_forwards nodedefs'
                                   then Final else closed
                      val graph' =
                          Symtab.update
                            ((noderef,
                              Node (nodety, nodedefs', nodebacks, nodefinals, closed)),graph)
                    in
                      (defnames', graph')
                    end
                  else
                    (defnames', graph)
                end

            val (defnames', graph') = Symtab.foldl update_defs
                                                   ((Symtab.empty, graph), defnames)
          in
            if Symtab.is_empty defnames' then
              (backs, graph')
            else
              let
                val backs' = Symtab.update_new ((noderef, defnames'), backs)
              in
                (backs', graph')
              end
          end

      val (backs, graph) = Symtab.foldl update_backrefs ((Symtab.empty, graph), backs)

      (* If a Circular exception is thrown then we never reach this point. *)
      val (Node (gty, defs, _, finals, closed)) = getnode graph mainref
      val closed = if closed = Closed andalso no_forwards defs then Final else closed
      val graph = Symtab.update ((mainref, Node (gty, defs, backs, finals, closed)), graph)
      val actions' = (Define (mainref, ty, axname, orig_axname, body))::actions
    in
      (cost+3, axmap, actions', graph)
    end handle ex => translate_ex axmap ex

fun define'' (g as (cost, axmap, actions, graph)) (mainref, ty) orig_axname body =
    let
      val ty = checkT ty
      fun checkbody (n, t) =
          let
            val (Node (_, _, _,_, closed)) = getnode graph n
          in
            case closed of
              Final => NONE
            | _ => SOME (n, checkT t)
          end
      val body = distinct (List.mapPartial checkbody body)
      val (axmap, axname) = newaxname axmap orig_axname
    in
      define' (cost, axmap, actions, graph) (mainref, ty) axname orig_axname body
    end

fun finalize' (cost, axmap, history, graph) (noderef, ty) =
    case Symtab.lookup (graph, noderef) of
      NONE => def_err ("cannot finalize constant "^noderef^"; it is not declared")
    | SOME (Node (nodety, defs, backs, finals, closed)) =>
      let
        val _ =
            if (not (is_instance_r ty nodety)) then
              def_err ("only type instances of the declared constant "^
                       noderef^" can be finalized")
            else ()
        val _ = Symtab.exists
                  (fn (def_name, Defnode (def_ty, _)) =>
                      if can_be_unified_r ty def_ty then
                        def_err ("cannot finalize constant "^noderef^
                                 "; clash with definition "^def_name)
                      else
                        false)
                  defs

        fun update_finals [] = SOME [ty]
          | update_finals (final_ty::finals) =
            (if is_instance_r ty final_ty then NONE
             else
               case update_finals finals of
                 NONE => NONE
               | (r as SOME finals) =>
                 if (is_instance_r final_ty ty) then
                   r
                 else
                   SOME (final_ty :: finals))
      in
        case update_finals finals of
          NONE => (cost, axmap, history, graph)
        | SOME finals =>
          let
            val closed = if closed = Open andalso is_instance_r nodety ty then
                           Closed else
                         closed
            val graph = Symtab.update ((noderef, Node(nodety, defs, backs, finals, closed)),
                                       graph)

            fun update_backref ((graph, backs), (backrefname, backdefnames)) =
                let
                  fun update_backdef ((graph, defnames), (backdefname, _)) =
                      let
                        val (backnode as Node (backty, backdefs, backbacks,
                                               backfinals, backclosed)) =
                            getnode graph backrefname
                        val (Defnode (def_ty, all_edges)) =
                            the (get_defnode backnode backdefname)

                        val (defnames', all_edges') =
                            case Symtab.lookup (all_edges, noderef) of
                              NONE => sys_error "finalize: corrupt backref"
                            | SOME edges =>
                              let
                                val edges' = List.filter (fn (_, _, beta, _) =>
                                                             not (is_instance_r beta ty)) edges
                              in
                                if edges' = [] then
                                  (defnames, Symtab.delete noderef all_edges)
                                else
                                  (Symtab.update ((backdefname, ()), defnames),
                                   Symtab.update ((noderef, edges'), all_edges))
                              end
                        val defnode' = Defnode (def_ty, all_edges')
                        val backdefs' = Symtab.update ((backdefname, defnode'), backdefs)
                        val backclosed' = if backclosed = Closed andalso
                                             Symtab.is_empty all_edges'
                                             andalso no_forwards backdefs'
                                          then Final else backclosed
                        val backnode' =
                            Node (backty, backdefs', backbacks, backfinals, backclosed')
                      in
                        (Symtab.update ((backrefname, backnode'), graph), defnames')
                      end

                  val (graph', defnames') =
                      Symtab.foldl update_backdef ((graph, Symtab.empty), backdefnames)
                in
                  (graph', if Symtab.is_empty defnames' then backs
                           else Symtab.update ((backrefname, defnames'), backs))
                end
            val (graph', backs') = Symtab.foldl update_backref ((graph, Symtab.empty), backs)
            val Node ( _, defs, _, _, closed) = getnode graph' noderef
            val closed = if closed = Closed andalso no_forwards defs then Final else closed
            val graph' = Symtab.update ((noderef, Node (nodety, defs, backs',
                                                        finals, closed)), graph')
            val history' = (Finalize (noderef, ty)) :: history
          in
            (cost+1, axmap, history', graph')
          end
      end

fun finalize'' g (noderef, ty) = finalize' g (noderef, checkT ty)

fun update_axname ax orig_ax (cost, axmap, history, graph) =
  (cost, Symtab.update ((ax, orig_ax), axmap), history, graph)

fun merge' (Declare cty, g) = declare' g cty
  | merge' (Define (name, ty, axname, orig_axname, body), g as (cost, axmap, history, graph)) =
    (case Symtab.lookup (graph, name) of
       NONE => define' (update_axname axname orig_axname g) (name, ty) axname orig_axname body
     | SOME (Node (_, defs, _, _, _)) =>
       (case Symtab.lookup (defs, axname) of
          NONE => define' (update_axname axname orig_axname g) (name, ty) axname orig_axname body
        | SOME _ => g))
  | merge' (Finalize finals, g) = finalize' g finals

fun merge'' (g1 as (cost1, _, actions1, _)) (g2 as (cost2, _, actions2, _)) =
    if cost1 < cost2 then
      foldr merge' g2 actions1
    else
      foldr merge' g1 actions2

fun finals (_, _, history, graph) =
    Symtab.foldl
      (fn (finals, (name, Node(_, _, _, ftys, _))) =>
          Symtab.update_new ((name, ftys), finals))
      (Symtab.empty, graph)

fun overloading_info (_, axmap, _, graph) c =
    let
      fun translate (ax, Defnode (ty, _)) = (the (Symtab.lookup (axmap, ax)), ty)
    in
      case Symtab.lookup (graph, c) of
        NONE => NONE
      | SOME (Node (ty, defnodes, _, _, state)) =>
        SOME (ty, map translate (Symtab.dest defnodes), state)
    end

fun fast_overloading_info (_, _, _, graph) c =
    let
      fun count (c, _) = c+1
    in
      case Symtab.lookup (graph, c) of
        NONE => NONE
      | SOME (Node (ty, defnodes, _, _, state)) =>
        SOME (ty, Symtab.foldl count (0, defnodes), state)
    end



(** diagnostics **)

fun pretty_const pp (c, T) =
 [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
  Pretty.quote (Pretty.typ pp (Type.freeze_type T))];    (* FIXME zero indexes!? *)

fun pretty_path pp path = fold_rev (fn (T, c, def) =>
  fn [] => [Pretty.block (pretty_const pp (c, T))]
   | prts => Pretty.block (pretty_const pp (c, T) @
      [Pretty.brk 1, Pretty.str ("depends via " ^ quote def ^ " on")]) :: prts) path [];

fun chain_history_msg s =    (* FIXME huh!? *)
  if chain_history () then s ^ ": "
  else s ^ " (set DEFS_CHAIN_HISTORY=ON for full history): ";

fun defs_circular pp path =
  Pretty.str (chain_history_msg "Cyclic dependency of definitions") :: pretty_path pp path
  |> Pretty.chunks |> Pretty.string_of;

fun defs_infinite_chain pp path =
  Pretty.str (chain_history_msg "Infinite chain of definitions") :: pretty_path pp path
  |> Pretty.chunks |> Pretty.string_of;

fun defs_clash def1 def2 = "Type clash in definitions " ^ quote def1 ^ " and " ^ quote def2;

fun defs_final pp const =
  (Pretty.str "Attempt to define final constant" :: Pretty.brk 1 :: pretty_const pp const)
  |> Pretty.block |> Pretty.string_of;


(* external interfaces *)

fun declare const defs =
  if_none (try (declare'' defs) const) defs;

fun define pp const name rhs defs =
  define'' defs const name rhs
    handle DEFS msg => sys_error msg
      | CIRCULAR path => error (defs_circular pp path)
      | INFINITE_CHAIN path => error (defs_infinite_chain pp path)
      | CLASH (_, def1, def2) => error (defs_clash def1 def2)
      | FINAL const => error (defs_final pp const);

fun finalize const defs =
  finalize'' defs const handle DEFS msg => sys_error msg;

fun merge pp defs1 defs2 =
  merge'' defs1 defs2
    handle CIRCULAR namess => error (defs_circular pp namess)
      | INFINITE_CHAIN namess => error (defs_infinite_chain pp namess);

end;

(*

fun tvar name = TVar ((name, 0), [])

val bool = Type ("bool", [])
val int = Type ("int", [])
val lam = Type("lam", [])
val alpha = tvar "'a"
val beta = tvar "'b"
val gamma = tvar "'c"
fun pair a b = Type ("pair", [a,b])
fun prm a = Type ("prm", [a])
val name = Type ("name", [])

val _ = print "make empty"
val g = Defs.empty

val _ = print "declare perm"
val g = Defs.declare g ("perm", prm alpha --> beta --> beta)

val _ = print "declare permF"
val g = Defs.declare g ("permF", prm alpha --> lam --> lam)

val _ = print "define perm (1)"
val g = Defs.define g ("perm", prm alpha --> (beta --> gamma) --> (beta --> gamma)) "perm_fun"
        [("perm", prm alpha --> gamma --> gamma), ("perm", prm alpha --> beta --> beta)]

val _ = print "define permF (1)"
val g = Defs.define g ("permF", prm alpha --> lam --> lam) "permF_app"
        ([("perm", prm alpha --> lam --> lam),
         ("perm", prm alpha --> lam --> lam),
         ("perm", prm alpha --> lam --> lam),
         ("perm", prm alpha --> name --> name)])

val _ = print "define perm (2)"
val g = Defs.define g ("perm", prm alpha --> lam --> lam) "perm_lam"
        [("permF", (prm alpha --> lam --> lam))]

*)
