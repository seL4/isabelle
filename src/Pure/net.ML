(*  Title: 	Pure/net.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Discrimination nets: a data structure for indexing items

From the book 
    E. Charniak, C. K. Riesbeck, D. V. McDermott. 
    Artificial Intelligence Programming.
    (Lawrence Erlbaum Associates, 1980).  [Chapter 14]

match_term no longer treats abstractions as wildcards; instead they match 
only wildcards in patterns.  Requires operands to be beta-eta-normal.
*)

signature NET = 
  sig
  type key
  type 'a net
  exception DELETE and INSERT
  val delete: (key list * 'a) * 'a net * ('a*'a -> bool) -> 'a net
  val delete_term:   (term * 'a) * 'a net * ('a*'a -> bool) -> 'a net
  val empty: 'a net
  val insert: (key list * 'a) * 'a net * ('a*'a -> bool) -> 'a net
  val insert_term:   (term * 'a) * 'a net * ('a*'a -> bool) -> 'a net
  val lookup: 'a net * key list -> 'a list
  val match_term: 'a net -> term -> 'a list
  val key_of_term: term -> key list
  val unify_term: 'a net -> term -> 'a list
  val dest: 'a net -> (key list * 'a) list
  val merge: 'a net * 'a net * ('a*'a -> bool) -> 'a net
  end;


structure Net : NET = 
struct

datatype key = CombK | VarK | AtomK of string;

(*Bound variables*)
fun string_of_bound i = "*B*" ^ chr (i div 256) ^ chr (i mod 256);

(*Keys are preorder lists of symbols -- Combinations, Vars, Atoms.
  Any term whose head is a Var is regarded entirely as a Var.
  Abstractions are also regarded as Vars;  this covers eta-conversion
    and "near" eta-conversions such as %x.?P(?f(x)).
*)
fun add_key_of_terms (t, cs) = 
  let fun rands (f$t, cs) = CombK :: rands (f, add_key_of_terms(t, cs))
	| rands (Const(c,_), cs) = AtomK c :: cs
	| rands (Free(c,_),  cs) = AtomK c :: cs
	| rands (Bound i,  cs)   = AtomK (string_of_bound i) :: cs
  in case (head_of t) of
      Var _ => VarK :: cs
    | Abs _ => VarK :: cs
    | _     => rands(t,cs)
  end;

(*convert a term to a list of keys*)
fun key_of_term t = add_key_of_terms (t, []);


(*Trees indexed by key lists: each arc is labelled by a key.
  Each node contains a list of items, and arcs to children.
  Keys in the association list (alist) are stored in ascending order.
  The empty key addresses the entire net.
  Lookup functions preserve order in items stored at same level.
*)
datatype 'a net = Leaf of 'a list
		| Net of {comb: 'a net, 
			  var: 'a net,
			  alist: (string * 'a net) list};

val empty = Leaf[];
val emptynet = Net{comb=empty, var=empty, alist=[]};


(*** Insertion into a discrimination net ***)

exception INSERT;	(*duplicate item in the net*)


(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for items. 
  The empty list of keys generates a Leaf node, others a Net node.
*)
fun insert ((keys,x), net, eq) =
  let fun ins1 ([], Leaf xs) = 
            if gen_mem eq (x,xs) then  raise INSERT  else Leaf(x::xs)
        | ins1 (keys, Leaf[]) = ins1 (keys, emptynet)   (*expand empty...*)
        | ins1 (CombK :: keys, Net{comb,var,alist}) =
	    Net{comb=ins1(keys,comb), var=var, alist=alist}
	| ins1 (VarK :: keys, Net{comb,var,alist}) =
	    Net{comb=comb, var=ins1(keys,var), alist=alist}
	| ins1 (AtomK a :: keys, Net{comb,var,alist}) =
	    let fun newpair net = (a, ins1(keys,net)) 
		fun inslist [] = [newpair empty]
		  | inslist((b: string, netb) :: alist) =
		      if a=b then newpair netb :: alist
		      else if a<b then (*absent, ins1ert in alist*)
			  newpair empty :: (b,netb) :: alist
		      else (*a>b*) (b,netb) :: inslist alist
	    in  Net{comb=comb, var=var, alist= inslist alist}  end
  in  ins1 (keys,net)  end;

fun insert_term ((t,x), net, eq) = insert((key_of_term t, x), net, eq);

(*** Deletion from a discrimination net ***)

exception DELETE;	(*missing item in the net*)

(*Create a new Net node if it would be nonempty*)
fun newnet {comb=Leaf[], var=Leaf[], alist=[]} = empty
  | newnet {comb,var,alist} = Net{comb=comb, var=var, alist=alist};

(*add new (b,net) pair to the alist provided net is nonempty*)
fun conspair((b, Leaf[]), alist) = alist
  | conspair((b, net), alist)    = (b, net) :: alist;

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent.  Collapses the net if possible.
  eq is the equality test for items. *)
fun delete ((keys, x), net, eq) = 
  let fun del1 ([], Leaf xs) =
            if gen_mem eq (x,xs) then Leaf (gen_rem eq (xs,x))
            else raise DELETE
	| del1 (keys, Leaf[]) = raise DELETE
	| del1 (CombK :: keys, Net{comb,var,alist}) =
	    newnet{comb=del1(keys,comb), var=var, alist=alist}
	| del1 (VarK :: keys, Net{comb,var,alist}) =
	    newnet{comb=comb, var=del1(keys,var), alist=alist}
	| del1 (AtomK a :: keys, Net{comb,var,alist}) =
	    let fun newpair net = (a, del1(keys,net)) 
		fun dellist [] = raise DELETE
		  | dellist((b: string, netb) :: alist) =
		      if a=b then conspair(newpair netb, alist)
		      else if a<b then (*absent*) raise DELETE
		      else (*a>b*)  (b,netb) :: dellist alist
	    in  newnet{comb=comb, var=var, alist= dellist alist}  end
  in  del1 (keys,net)  end;

fun delete_term ((t,x), net, eq) = delete((key_of_term t, x), net, eq);

(*** Retrieval functions for discrimination nets ***)

exception OASSOC;

(*Ordered association list lookup*)
fun oassoc ([], a: string) = raise OASSOC
  | oassoc ((b,x)::pairs, a) =
      if b<a then oassoc(pairs,a)
      else if a=b then x
      else raise OASSOC;

(*Return the list of items at the given node, [] if no such node*)
fun lookup (Leaf(xs), []) = xs
  | lookup (Leaf _, _::_) = []	(*non-empty keys and empty net*)
  | lookup (Net{comb,var,alist}, CombK :: keys) = lookup(comb,keys)
  | lookup (Net{comb,var,alist}, VarK :: keys) = lookup(var,keys)
  | lookup (Net{comb,var,alist}, AtomK a :: keys) = 
      lookup(oassoc(alist,a),keys)  handle  OASSOC => [];


(*Skipping a term in a net.  Recursively skip 2 levels if a combination*)
fun net_skip (Leaf _, nets) = nets
  | net_skip (Net{comb,var,alist}, nets) = 
    foldr net_skip 
          (net_skip (comb,[]), 
	   foldr (fn ((_,net), nets) => net::nets) (alist, var::nets));

(** Matching and Unification**)

(*conses the linked net, if present, to nets*)
fun look1 (alist, a) nets =
       oassoc(alist,a) :: nets  handle  OASSOC => nets;

(*Return the nodes accessible from the term (cons them before nets) 
  "unif" signifies retrieval for unification rather than matching.
  Var in net matches any term.
  Abs or Var in object: if "unif", regarded as wildcard, 
                                   else matches only a variable in net.
*)
fun matching unif t (net,nets) =
  let fun rands _ (Leaf _, nets) = nets
	| rands t (Net{comb,alist,...}, nets) =
	    case t of 
		f$t => foldr (matching unif t) (rands f (comb,[]), nets)
	      | Const(c,_) => look1 (alist, c) nets
	      | Free(c,_)  => look1 (alist, c) nets
	      | Bound i    => look1 (alist, string_of_bound i) nets
	      | _      	   => nets
  in 
     case net of
	 Leaf _ => nets
       | Net{var,...} =>
	     case head_of t of
		 Var _ => if unif then net_skip (net,nets)
			  else var::nets	   (*only matches Var in net*)
  (*If "unif" then a var instantiation in the abstraction could allow
    an eta-reduction, so regard the abstraction as a wildcard.*)
	       | Abs _ => if unif then net_skip (net,nets)
			  else var::nets	   (*only a Var can match*)
	       | _ => rands t (net, var::nets)  (*var could match also*)
  end;

fun extract_leaves l = List.concat (map (fn Leaf(xs) => xs) l);

(*return items whose key could match t, WHICH MUST BE BETA-ETA NORMAL*)
fun match_term net t = 
    extract_leaves (matching false t (net,[]));

(*return items whose key could unify with t*)
fun unify_term net t = 
    extract_leaves (matching true t (net,[]));


(** dest **)

fun cons_fst x (xs, y) = (x :: xs, y);

fun dest (Leaf xs) = map (pair []) xs
  | dest (Net {comb, var, alist}) =
      map (cons_fst CombK) (dest comb) @
      map (cons_fst VarK) (dest var) @
      flat (map (fn (a, net) => map (cons_fst (AtomK a)) (dest net)) alist);


(** merge **)

fun add eq (net, keys_x) =
  insert (keys_x, net, eq) handle INSERT => net;

fun merge (net1, net2, eq) =
  foldl (add eq) (net1, dest net2);


end;
