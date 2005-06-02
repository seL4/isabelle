(*  Title:      Pure/General/defs.ML
    ID:         $Id$
    Author:     Steven Obua, TU Muenchen

    Checks if definitions preserve consistency of logic by enforcing that there are no cyclic definitions.
    The algorithm is described in 
    "Cycle-free Overloading in Isabelle", Steven Obua, technical report, to be written :-)
*)

signature DEFS = sig
    
  type graph
       
  exception DEFS of string
  exception CIRCULAR of (typ * string * string) list
  exception INFINITE_CHAIN of (typ * string * string) list 
  exception FINAL of string * typ
  exception CLASH of string * string * string
                     
  val empty : graph
  val declare : graph -> string * typ -> graph  (* exception DEFS *)
  val define : graph -> string * typ -> string -> (string * typ) list -> graph 
    (* exception DEFS, CIRCULAR, INFINITE_CHAIN, CLASH, FINAL *)
                                                                         
  val finalize : graph -> string * typ -> graph (* exception DEFS *)

  val finals : graph -> (typ list) Symtab.table

  (* the first argument should be the smaller graph *)
  val merge : graph -> graph -> graph (* exception CIRCULAR, INFINITE_CHAIN, CLASH *)

end

structure Defs :> DEFS = struct

type tyenv = Type.tyenv
type edgelabel = (int * typ * typ * (typ * string * string) list)
type noderef = string

datatype node = Node of
         string  (* name of constant *)
         * typ  (* most general type of constant *)
         * defnode Symtab.table  (* a table of defnodes, each corresponding to 1 definition of the 
             constant for a particular type, indexed by axiom name *)
         * backref Symtab.table (* a table of all back references to this node, indexed by node name *)
         * typ list (* a list of all finalized types *)
     
     and defnode = Defnode of
         typ  (* type of the constant in this particular definition *)
         * ((noderef * (string option * edgelabel list) list) Symtab.table) (* The edges, grouped by nodes. *)

and backref = Backref of
    noderef  (* the name of the node that has defnodes which reference a certain node A *)
    * (unit Symtab.table) (* the names of the defnodes that DIRECTLY reference A. *)

fun getnode graph noderef = the (Symtab.lookup (graph, noderef))
fun get_nodename (Node (n, _, _ ,_, _)) = n
fun get_nodedefs (Node (_, _, defs, _, _)) = defs
fun get_defnode (Node (_, _, defs, _, _)) defname = Symtab.lookup (defs, defname)
fun get_defnode' graph noderef defname = Symtab.lookup (get_nodedefs (the (Symtab.lookup (graph, noderef))), defname)
fun get_nodename (Node (n, _, _ , _, _)) = n

datatype graphaction = Declare of string * typ 
		     | Define of string * typ * string * (string * typ) list
		     | Finalize of string * typ

type graph = (graphaction list) * (node Symtab.table)
             
val empty = ([], Symtab.empty)

exception DEFS of string;
exception CIRCULAR of (typ * string * string) list;
exception INFINITE_CHAIN of (typ * string * string) list;
exception CLASH of string * string * string;
exception FINAL of string * typ;

fun def_err s = raise (DEFS s)

fun declare (actions, g) (cty as (name, ty)) =
    ((Declare cty)::actions, 
     Symtab.update_new ((name, Node (name, Type.varifyT(Type.strip_sorts ty), Symtab.empty, Symtab.empty, [])), g))
    handle Symtab.DUP _ => def_err "constant is already declared"

fun rename ty1 ty2 = incr_tvar ((maxidx_of_typ ty1)+1) ty2;  

fun subst_incr_tvar inc t =
    if (inc > 0) then 
      let
	val tv = typ_tvars t
	val t' = incr_tvar inc t
	fun update_subst (((n,i), _), s) =
	    Vartab.update (((n, i), ([], TVar ((n, i+inc), []))), s)
      in
	(t',List.foldl update_subst Vartab.empty tv)
      end	
    else
      (t, Vartab.empty)

(* Rename tys2 so that tys2 and tys1 do not have any variables in common any more.
   As a result, return the renamed tys2' and the substitution that takes tys2 to tys2'. *)
fun subst_rename max1 ty2 =
    let
      val max2 = (maxidx_of_typ ty2)
      val (ty2', s) = subst_incr_tvar (max1 + 1) ty2                
    in
      (ty2', s, max1 + max2 + 1)
    end	       
    
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
   Unifies ty1 and ty2, renaming ty1 and ty2 so that they have greater indices than max and so that they
   are different. All indices in ty1 and ty2 are supposed to be less than or equal to max.
   Returns SOME (max', s1, s2), so that s1(ty1) = s2(ty2) and max' is greater or equal than all 
   indices in s1, s2, ty1, ty2.
*)
fun unify_r max ty1 ty2 = 
    let
      val max =  Int.max(max, 0)
      val max1 = max (* >= maxidx_of_typ ty1 *)
      val max2 = max (* >= maxidx_of_typ ty2 *)
      val max = Int.max(max, Int.max (max1, max2))
      val (ty1, s1) = subst_incr_tvar (max+1) ty1
      val (ty2, s2) = subst_incr_tvar (max+max1+2) ty2
      val max = max+max1+max2+2	
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
           
fun checkT (Type (a, Ts)) = Type (a, map checkT Ts)
  | checkT (TVar ((a, 0), _)) = TVar ((a, 0), [])
  | checkT (TVar ((a, i), _)) = def_err "type is not clean"
  | checkT (TFree (a, _)) = TVar ((a, 0), [])

fun label_ord NONE NONE = EQUAL
  | label_ord NONE (SOME _) = LESS
  | label_ord (SOME _) NONE = GREATER
  | label_ord (SOME l1) (SOME l2) = string_ord (l1,l2)

fun compare_edges (e1 as (maxidx1, u1, v1, history1)) (e2 as (maxidx2, u2, v2, history2)) =
    let
      val t1 = u1 --> v1
      val t2 = u2 --> v2
    in
      if (is_instance_r t1 t2) then
	(if is_instance_r t2 t1 then
	   SOME (int_ord (length history2, length history1))
	 else
	   SOME LESS)
      else if (is_instance_r t2 t1) then
	SOME GREATER
      else
	NONE
    end
    
fun merge_edges_1 (x, []) = []
  | merge_edges_1 (x, (y::ys)) = 
    (case compare_edges x y of
       SOME LESS => (y::ys)
     | SOME EQUAL => (y::ys)
     | SOME GREATER => merge_edges_1 (x, ys)
     | NONE => y::(merge_edges_1 (x, ys)))
    
fun merge_edges xs ys = foldl merge_edges_1 xs ys

fun pack_edges xs = merge_edges [] xs

fun merge_labelled_edges [] es = es
  | merge_labelled_edges es [] = es
  | merge_labelled_edges ((l1,e1)::es1) ((l2,e2)::es2) = 
    (case label_ord l1 l2 of
       LESS => (l1, e1)::(merge_labelled_edges es1 ((l2, e2)::es2))
     | GREATER => (l2, e2)::(merge_labelled_edges ((l1, e1)::es1) es2)
     | EQUAL => (l1, merge_edges e1 e2)::(merge_labelled_edges es1 es2))
    
fun defnode_edges_foldl f a defnode =
    let
      val (Defnode (ty, def_edges)) = defnode
      fun g (b, (_, (n, labelled_edges))) =
	  foldl (fn ((s, edges), b') => 
		    (foldl (fn (e, b'') => f ty n s e b'') b' edges))
		b
		labelled_edges		  		     
    in
      Symtab.foldl g (a, def_edges)
    end	
    
fun define (actions, graph) (name, ty) axname body =
    let
      val ty = checkT ty
      val body = map (fn (n,t) => (n, checkT t)) body		 
      val mainref = name
      val mainnode  = (case Symtab.lookup (graph, mainref) of 
			 NONE => def_err ("constant "^mainref^" is not declared")
		       | SOME n => n)
      val (Node (n, gty, defs, backs, finals)) = mainnode
      val _ = (if is_instance_r ty gty then () else def_err "type of constant does not match declared type")
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
	             
      (* now we know that the only thing that can prevent acceptance of the definition is a cyclic dependency *)

      (* body contains the constants that this constant definition depends on. For each element of body,
         the function make_edges_to calculates a group of edges that connect this constant with 
         the constant that is denoted by the element of the body *)
      fun make_edges_to (bodyn, bodyty) =
	  let
	    val bnode = 
		(case Symtab.lookup (graph, bodyn) of 
		   NONE => def_err "body of constant definition references undeclared constant"
		 | SOME x => x)
	    val (Node (_, general_btyp, bdefs, bbacks, bfinals)) = bnode
	  in
	    case unify_r 0 bodyty general_btyp of
	      NONE => NONE
	    | SOME (maxidx, sigma1, sigma2) => 
	      SOME (
	      let
		(* For each definition of the constant in the body, 
		   check if the definition unifies with the type of the constant in the body. *)	                
                fun make_edges ((swallowed, l),(def_name, Defnode (def_ty, _))) =
		    if swallowed then
		      (swallowed, l)
		    else 
		      (case unify_r 0 bodyty def_ty of
			 NONE => (swallowed, l)
		       | SOME (maxidx, sigma1, sigma2) => 
			 (is_instance_r bodyty def_ty,
			  merge_labelled_edges l [(SOME def_name,[(maxidx, subst sigma1 ty, subst sigma2 def_ty, [])])]))
                val swallowed = exists (is_instance_r bodyty) bfinals
          	val (swallowed, edges) = Symtab.foldl make_edges ((swallowed, []), bdefs)
	      in
		if swallowed then 
		  (bodyn, edges)
		else 
		  (bodyn, [(NONE, [(maxidx, subst sigma1 ty, subst sigma2 general_btyp,[])])]@edges)
	      end)
	  end 
          
      fun update_edges (b as (bodyn, bodyty), edges) =
	  (case make_edges_to b of
	     NONE => edges
	   | SOME m =>
	     (case Symtab.lookup (edges, bodyn) of
		NONE => Symtab.update ((bodyn, m), edges)
	      | SOME (_, es') => 
		let 
		  val (_, es) = m
		  val es = merge_labelled_edges es es'
		in
		  Symtab.update ((bodyn, (bodyn, es)), edges)
		end
	     )
	  )
          
      val edges = foldl update_edges Symtab.empty body
                  
      fun insert_edge edges (nodename, (defname_opt, edge)) = 
	  let
	    val newlink = [(defname_opt, [edge])]
	  in
	    case Symtab.lookup (edges, nodename) of
	      NONE => Symtab.update ((nodename, (nodename, newlink)), edges)		    
	    | SOME (_, links) => 
	      let
		val links' = merge_labelled_edges links newlink
	      in
		Symtab.update ((nodename, (nodename, links')), edges)
	      end
	  end				    
            
      (* We constructed all direct edges that this defnode has. 
         Now we have to construct the transitive hull by going a single step further. *)
          
      val thisDefnode = Defnode (ty, edges)
                        
      fun make_trans_edges _ noderef defname_opt (max1, alpha1, beta1, history1) edges = 
	  case defname_opt of 
	    NONE => edges
	  | SOME defname => 		
	    let
	      val defnode = the (get_defnode' graph noderef defname)
	      fun make_trans_edge _ noderef2 defname_opt2 (max2, alpha2, beta2, history2) edges =
		  case unify_r (Int.max (max1, max2)) beta1 alpha2 of
		    NONE => edges
		  | SOME (max, sleft, sright) =>
		    insert_edge edges (noderef2, 
				       (defname_opt2, 							  
					(max, subst sleft alpha1, subst sright beta2, 
					 (subst_history sleft history1)@
					 ((subst sleft beta1, noderef, defname)::
					  (subst_history sright history2)))))
	    in
	      defnode_edges_foldl make_trans_edge edges defnode
	    end
            
      val edges = defnode_edges_foldl make_trans_edges edges thisDefnode
                  
      val thisDefnode = Defnode (ty, edges)

      (* We also have to add the backreferences that this new defnode induces. *)
	    
      fun hasNONElink ((NONE, _)::_) = true
	| hasNONElink _ = false
	                  
      fun install_backref graph noderef pointingnoderef pointingdefname = 
	  let
	    val (Node (pname, _, _, _, _)) = getnode graph pointingnoderef
	    val (Node (name, ty, defs, backs, finals)) = getnode graph noderef
	  in
	    case Symtab.lookup (backs, pname) of
	      NONE => 
	      let 
		val defnames = Symtab.update ((pointingdefname, ()), Symtab.empty)
		val backs = Symtab.update ((pname, Backref (pointingnoderef, defnames)), backs)
	      in
		Symtab.update ((name, Node (name, ty, defs, backs, finals)), graph) 			
	      end
	    | SOME (Backref (pointingnoderef, defnames)) =>
	      let
		val defnames = Symtab.update_new ((pointingdefname, ()), defnames)
		val backs = Symtab.update ((pname, Backref (pointingnoderef, defnames)), backs)
	      in
		Symtab.update ((name, Node (name, ty, defs, backs, finals)), graph)
	      end
	      handle Symtab.DUP _ => graph
	  end
          
      fun install_backrefs (graph, (_, (noderef, labelled_edges))) =
	  if hasNONElink labelled_edges then
	    install_backref graph noderef mainref axname
	  else 
	    graph
            
      val graph = Symtab.foldl install_backrefs (graph, edges)
                  
      val (Node (_, _, _, backs, _)) = getnode graph mainref
      val graph = Symtab.update ((mainref, Node (n, gty, Symtab.update_new 
        ((axname, thisDefnode), defs), backs, finals)), graph)
		                
      (* Now we have to check all backreferences to this node and inform them about the new defnode. 
	 In this section we also check for circularity. *)
      fun update_backrefs ((backs, newedges), (nodename, Backref (noderef, defnames))) =	    
	  let
	    val node = getnode graph noderef
	    fun update_defs ((defnames, newedges),(defname, _)) =
		let
		  val (Defnode (_, defnode_edges)) = the (get_defnode node defname)
		  val (_, labelled_edges) = the (Symtab.lookup (defnode_edges, n))
						
	          (* the type of thisDefnode is ty *)
		  fun update (e as (max, alpha, beta, history), (none_edges, this_edges)) = 
		      case unify_r max beta ty of
			NONE => (e::none_edges, this_edges)
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
				 | SOME s => raise (CIRCULAR (
						    (subst s alpha', mainref, axname)::
						    (subst_history s (subst_history s_beta history))@
						    [(subst s ty', mainref, axname)])))
			      else ()
			  val edge = (max', alpha', ty', subst_history s_beta history)
			in
			  if is_instance_r beta ty then 
			    (none_edges, edge::this_edges)
			  else
			    (e::none_edges, edge::this_edges)
			end					    			   			    
		in
		  case labelled_edges of 
		    ((NONE, edges)::_) => 
		    let
		      val (none_edges, this_edges) = foldl update ([], []) edges
		      val defnames = if none_edges = [] then defnames else Symtab.update_new ((defname, ()), defnames) 
		    in
		      (defnames, (defname, none_edges, this_edges)::newedges)
		    end			    
		  | _ => sys_error "define: update_defs, internal error, corrupt backrefs"
		end
		    
	    val (defnames, newedges') = Symtab.foldl update_defs ((Symtab.empty, []), defnames)
	  in
	    if Symtab.is_empty defnames then 
	      (backs, (noderef, newedges')::newedges)
	    else
	      let
		val backs = Symtab.update_new ((nodename, Backref (noderef, defnames)), backs)
	      in
		(backs, newedges)
	      end
	  end
	  

      val (backs, newedges) = Symtab.foldl update_backrefs ((Symtab.empty, []), backs)
						 
      (* If a Circular exception is thrown then we never reach this point. *)
      (* Ok, the definition is consistent, let's update this node. *)
      val graph = Symtab.update ((mainref, Node (n, gty, Symtab.update 
        ((axname, thisDefnode), defs), backs, finals)), graph)

      (* Furthermore, update all the other nodes that backreference this node. *)
      fun final_update_backrefs graph noderef defname none_edges this_edges =
	  let
	    val node = getnode graph noderef
	    val (Node (nodename, nodety, defs, backs, finals)) = node
	    val (Defnode (defnode_ty, defnode_edges)) = the (get_defnode node defname)
	    val (_, defnode_links) = the (Symtab.lookup (defnode_edges, n))
                                     
	    fun update edges none_edges this_edges =
		let 
		  val u = merge_labelled_edges edges [(SOME axname, pack_edges this_edges)]
		in
		  if none_edges = [] then
		    u
		  else
		    (NONE, pack_edges none_edges)::u
		end
		
	    val defnode_links' = 
		case defnode_links of 
		  ((NONE, _) :: edges) => update edges none_edges this_edges
		| edges => update edges none_edges this_edges
	    val defnode_edges' = Symtab.update ((n, (mainref, defnode_links')), defnode_edges)
	    val defs' = Symtab.update ((defname, Defnode (defnode_ty, defnode_edges')), defs)
	  in
	    Symtab.update ((nodename, Node (nodename, nodety, defs', backs, finals)), graph)
	  end
          
      val graph = foldl (fn ((noderef, newedges),graph) => foldl (fn ((defname, none_edges, this_edges), graph) =>
        final_update_backrefs graph noderef defname none_edges this_edges) graph newedges) graph newedges		    
                  
    in	    
      ((Define (name, ty, axname, body))::actions, graph)	   
    end 
    
fun finalize (history, graph) (c, ty) = 
    case Symtab.lookup (graph, c) of 
      NONE => def_err ("cannot finalize constant "^c^"; it is not declared")
    | SOME (Node (noderef, nodety, defs, backs, finals)) =>
      let 
	val ty = checkT ty
	val _ = if (not (is_instance_r ty nodety)) then
		  def_err ("only type instances of the declared constant "^c^" can be finalized")
		else ()
	val _ = Symtab.exists (fn (def_name, Defnode (def_ty, _)) =>  
				  if can_be_unified_r ty def_ty then 
				    def_err ("cannot finalize constant "^c^"; clash with definition "^def_name)
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
          NONE => (history, graph)
        | SOME finals => 
	  let
	    val graph = Symtab.update ((noderef, Node(noderef, nodety, defs, backs, finals)), graph)
	                
	    fun update_backref ((graph, backs), (backrefname, Backref (_, backdefnames))) =
		let
		  fun update_backdef ((graph, defnames), (backdefname, _)) = 
	              let 
			val (backnode as Node (_, backty, backdefs, backbacks, backfinals)) = getnode graph backrefname
			val (Defnode (def_ty, all_edges)) = the (get_defnode backnode backdefname)						      
			val (defnames', all_edges') = 
			    case Symtab.lookup (all_edges, noderef) of
			      NONE => sys_error "finalize: corrupt backref"
			    | SOME (_, (NONE, edges)::rest) =>
			      let
				val edges' = List.filter (fn (_, _, beta, _) => not (is_instance_r beta ty)) edges
			      in
				if edges' = [] then 
				  (defnames, Symtab.update ((noderef, (noderef, rest)), all_edges))
				else
				  (Symtab.update ((backdefname, ()), defnames), 
				   Symtab.update ((noderef, (noderef, (NONE, edges')::rest)), all_edges))
			      end
			val defnode' = Defnode (def_ty, all_edges')
			val backnode' = Node (backrefname, backty, Symtab.update ((backdefname, defnode'), backdefs), 
					      backbacks, backfinals)
		      in
			(Symtab.update ((backrefname, backnode'), graph), defnames')			  			  
		      end
	              
		  val (graph', defnames') = Symtab.foldl update_backdef ((graph, Symtab.empty), backdefnames)
		in
		  (graph', if Symtab.is_empty defnames' then backs 
			   else Symtab.update ((backrefname, Backref (backrefname, defnames')), backs))
		end
	    val (graph', backs') = Symtab.foldl update_backref ((graph, Symtab.empty), backs)
	    val Node (_, _, defs, _, _) = getnode graph' noderef
	  in
	    ((Finalize (c, ty)) :: history, Symtab.update ((noderef, Node (noderef, nodety, defs, backs', finals)), graph'))
	  end
      end
      
fun merge' (Declare cty, g) = (declare g cty handle _ => g)
  | merge' (Define (name, ty, axname, body), g as (_, graph)) = 
    (case Symtab.lookup (graph, name) of
       NONE => define g (name, ty) axname body
     | SOME (Node (_, _, defs, _, _)) => 
       (case Symtab.lookup (defs, axname) of
	  NONE => define g (name, ty) axname body
	| SOME _ => g))
  | merge' (Finalize finals, g) = finalize g finals 
                       
fun merge (actions, _) g = foldr merge' g actions
                           
fun finals (history, graph) = 
    Symtab.foldl 
      (fn (finals, (_, Node(name, _, _, _, ftys))) => Symtab.update_new ((name, ftys), finals))  
      (Symtab.empty, graph)

end;
		


(*fun tvar name = TVar ((name, 0), [])

val bool = Type ("bool", [])
val int = Type ("int", [])
val alpha = tvar "'a"
val beta = tvar "'b"
val gamma = tvar "'c"
fun pair a b = Type ("pair", [a,b])

val _ = print "make empty"
val g = Defs.empty 

val _ = print "declare"
val g = Defs.declare g "M" (alpha --> bool)
val g = Defs.declare g "N" (beta --> bool)

val _ = print "define"
val g = Defs.define g "N" (alpha --> bool) "defN" [("M", alpha --> bool)]
val g = Defs.define g "M" (alpha --> bool) "defM" [("N", int --> alpha)]

val g = Defs.declare g "0" alpha
val g = Defs.define g "0" (pair alpha beta) "zp" [("0", alpha), ("0", beta)]*)


