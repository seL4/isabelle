(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      libs/upterm_lib.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    26 Jan 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    generic upterms for lambda calculus  

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


signature UPTERM_LIB = 
sig
       

  (* type for upterms defined in terms of a 't : a downterm type, and 
     'y : types for bound variable in the downterm type *)
  datatype ('t,'y) T =
           abs of string * 'y * (('t,'y) T)
         | appl of 't * (('t,'y) T)
         | appr of 't * (('t,'y) T)
         | root

  (* analysis *)
  val tyenv_of_upterm : ('t,'y) T -> (string * 'y) list
  val tyenv_of_upterm' : ('t,'y) T -> 'y list
  val addr_of_upterm : ('t,'y) T -> int list
  val upsize_of_upterm : ('t,'y) T -> int
  
  (* editing *)
  val map_to_upterm_parts : ('t -> 't2) * ('y -> 'y2)  -> 
														('t,'y) T -> ('t2,'y2) T

  val expand_map_to_upterm_parts : ('t -> 't2 list) * ('y -> 'y2)  -> 
																	 ('t,'y) T -> ('t2,'y2) T list

  val fold_upterm : ('a * 't -> 'a) -> (* left *)
                    ('a * 't -> 'a) ->  (* right *)
                    ('a * (string * 'y) -> 'a) -> (* abs *)
                    ('a * ('t,'y) T) -> 'a (* everything *)

  (* apply one term to another *)
  val apply : ('t,'y) T -> ('t,'y) T -> ('t,'y) T

end;



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure UpTermLib : UPTERM_LIB =
struct 

  (* type for upterms defined in terms of a 't : a downterm type, and 
     'y : types for bound variable in the downterm type *)
  datatype ('t,'y) T =
           abs of string * 'y * ('t,'y) T
         | appl of 't * ('t,'y) T
         | appr of 't * ('t,'y) T
         | root;

  (* get the bound variable names and types for the current foucs *)
  fun tyenv_of_upterm (appl(l,m)) = tyenv_of_upterm m
    | tyenv_of_upterm (appr(r,m)) = tyenv_of_upterm m
    | tyenv_of_upterm (abs(s,ty,m)) = (s, ty) :: (tyenv_of_upterm m)
    | tyenv_of_upterm root = [];

  (* get the bound variable types for the current foucs *)
  fun tyenv_of_upterm' (appl(l,m)) = tyenv_of_upterm' m
    | tyenv_of_upterm' (appr(r,m)) = tyenv_of_upterm' m
    | tyenv_of_upterm' (abs(s,ty,m)) = ty :: (tyenv_of_upterm' m)
    | tyenv_of_upterm' root = [];

  (* an address construction for the upterm, ie if we were at the
     root, address describes how to get to this point. *)
  fun addr_of_upterm1 A root = A
    | addr_of_upterm1 A (appl (l,m)) = addr_of_upterm1 (1::A) m
    | addr_of_upterm1 A (appr (r,m)) = addr_of_upterm1 (2::A) m
    | addr_of_upterm1 A (abs (s,ty,m)) = addr_of_upterm1 (0::A) m;

  fun addr_of_upterm m = addr_of_upterm1 [] m;

  (* the size of the upterm, ie how far to get to root *)
  fun upsize_of_upterm root = 0
    | upsize_of_upterm (appl (l,m)) = (upsize_of_upterm m) + 1
    | upsize_of_upterm (appr (r,m)) = (upsize_of_upterm m) + 1
    | upsize_of_upterm (abs (s,ty,m)) = (upsize_of_upterm m) + 1;

  (* apply an upterm to to another upterm *)
  fun apply x root = x
    | apply x (appl (l,m)) = appl(l, apply x m)
    | apply x (appr (r,m)) = appr(r, apply x m)
    | apply x (abs (s,ty,m)) = abs(s, ty, apply x m);

  (* applies the term function to each term in each part of the upterm *)
  fun map_to_upterm_parts (tf,yf) root = root

    | map_to_upterm_parts (tf,yf) (abs(s,ty,m)) = 
      abs(s,yf ty,map_to_upterm_parts (tf,yf) m)

    | map_to_upterm_parts (tf,yf) (appr(t,m)) = 
      appr (tf t, map_to_upterm_parts (tf,yf) m)

    | map_to_upterm_parts (tf,yf) (appl(t,m)) = 
      appl (tf t, map_to_upterm_parts (tf,yf) m);


  (* applies the term function to each term in each part of the upterm *)
  fun expand_map_to_upterm_parts (tf,yf) root = [root]
    | expand_map_to_upterm_parts (tf,yf) (abs(s,ty,m)) = 
			map (fn x => abs(s,yf ty, x)) 
					(expand_map_to_upterm_parts (tf,yf) m)
    | expand_map_to_upterm_parts (tf,yf) (appr(t,m)) = 
      map appr (IsaPLib.all_pairs 
									(tf t) (expand_map_to_upterm_parts (tf,yf) m))
    | expand_map_to_upterm_parts (tf,yf) (appl(t,m)) = 
      map appl (IsaPLib.all_pairs 
									(tf t) (expand_map_to_upterm_parts (tf,yf) m));

  (* fold along each 't (down term) in the upterm *)
	fun fold_upterm fl fr fa (d, u) = 
      let 
	      fun fold_upterm' (d, root) = d
		      | fold_upterm' (d, abs(s,ty,m)) = fold_upterm' (fa(d,(s,ty)), m)
		      | fold_upterm' (d, appr(t,m)) = fold_upterm' (fr(d,t), m)
		      | fold_upterm' (d, appl(t,m)) = fold_upterm' (fl(d,t), m)
      in fold_upterm' (d,u) end;

end;
