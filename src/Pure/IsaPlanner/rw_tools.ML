(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/rw_tools.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    28 May 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    term related tools used for rewriting

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RWTOOLS =
sig
end;

structure RWTools 
= struct

(* THINKABOUT: don't need this: should be able to generate the paired 
   NsTs directly ? --already implemented as ~~
fun join_lists ([],[]) = []
  | join_lists (x::xs, y::ys) = (x,y) :: (join_lists (xs,ys))
  | join_lists (_, _) = raise ERROR_MESSAGE "join_lists: unequal size lists";
 *)

(* fake free variable names for locally bound variables - these work
as placeholders. *)
fun dest_fake_bound_name n = 
    case (explode n) of 
      (":" :: realchars) => implode realchars
    | _ => n;
fun is_fake_bound_name n = (hd (explode n) = ":");
fun mk_fake_bound_name n = ":" ^ n;



(* fake free variable names for local meta variables - these work
as placeholders. *)
fun dest_fake_fix_name n = 
    case (explode n) of 
      ("@" :: realchars) => implode realchars
    | _ => n;
fun is_fake_fix_name n = (hd (explode n) = "@");
fun mk_fake_fix_name n = "@" ^ n;



(* fake free variable names for meta level bound variables *)
fun dest_fake_all_name n = 
    case (explode n) of 
      ("+" :: realchars) => implode realchars
    | _ => n;
fun is_fake_all_name n = (hd (explode n) = "+");
fun mk_fake_all_name n = "+" ^ n;




(* Ys and Ts not used, Ns are real names of faked local bounds, the
idea is that this will be mapped to free variables thus if a free
variable is a faked local bound then we change it to being a meta
variable so that it can later be instantiated *)
(* FIXME: rename this - avoid the word fix! *)
(* note we are not really "fix"'ing the free, more like making it variable! *)
fun trymkvar_of_fakefree (Ns, Ts) Ys (n,ty) = 
    if (dest_fake_bound_name n) mem Ns then Var((n,0),ty) else Free (n,ty);

(* make a var into a fixed free (ie prefixed with "@") *)
fun mk_fakefixvar Ts ((n,i),ty) = Free(mk_fake_fix_name n, ty);


(* mk_frees_bound: string list -> Term.term -> Term.term *)
(* This function changes free variables to being represented as bound
variables if the free's variable name is in the given list. The debruijn 
index is simply the position in the list *)
(* THINKABOUT: danger of an existing free variable with the same name: fix
this so that name conflict are avoided automatically! In the meantime,
don't have free variables named starting with a ":" *)
fun bounds_of_fakefrees Ys (a $ b) = 
    (bounds_of_fakefrees Ys a) $ (bounds_of_fakefrees Ys b)
  | bounds_of_fakefrees Ys (Abs(n,ty,t)) = 
    Abs(n,ty, bounds_of_fakefrees (n::Ys) t)
  | bounds_of_fakefrees Ys (Free (n,ty)) = 
    let fun try_mk_bound_of_free (i,[]) = Free (n,ty)
          | try_mk_bound_of_free (i,(y::ys)) = 
            if n = y then Bound i else try_mk_bound_of_free (i+1,ys)
    in try_mk_bound_of_free (0,Ys) end
  | bounds_of_fakefrees Ys t = t;


(* map a function f onto each free variables *)
fun map_to_frees f Ys (a $ b) = 
    (map_to_frees f Ys a) $ (map_to_frees f Ys b)
  | map_to_frees f Ys (Abs(n,ty,t)) = 
    Abs(n,ty, map_to_frees f ((n,ty)::Ys) t)
  | map_to_frees f Ys (Free a) = 
    f Ys a
  | map_to_frees f Ys t = t;


(* map a function f onto each meta variable  *)
fun map_to_vars f Ys (a $ b) = 
    (map_to_vars f Ys a) $ (map_to_vars f Ys b)
  | map_to_vars f Ys (Abs(n,ty,t)) = 
    Abs(n,ty, map_to_vars f ((n,ty)::Ys) t)
  | map_to_vars f Ys (Var a) = 
    f Ys a
  | map_to_vars f Ys t = t;

(* map a function f onto each free variables *)
fun map_to_alls f (Const("all",allty) $ Abs(n,ty,t)) = 
    let val (n2,ty2) = f (n,ty) 
    in (Const("all",allty) $ Abs(n2,ty2,map_to_alls f t)) end
  | map_to_alls f x = x;

(* map a function f to each type variable in a term *)
(* implicit arg: term *)
fun map_to_term_tvars f =
    Term.map_term_types (fn TVar(ix,ty) => f (ix,ty) | x => x);



(* what if a param desn't occur in the concl? think about! Note: This
simply fixes meta level univ bound vars as Frees.  At the end, we will
change them back to schematic vars that will then unify
appropriactely, ie with unfake_vars *)
fun fake_concl_of_goal gt i = 
    let 
      val prems = Logic.strip_imp_prems gt
      val sgt = nth_elem (i - 1, prems)

      val tbody = Logic.strip_imp_concl (Term.strip_all_body sgt)
      val tparams = Term.strip_all_vars sgt

      val fakefrees = map (fn (n, ty) => Free(mk_fake_all_name n, ty)) 
                          tparams
    in
      Term.subst_bounds (rev fakefrees,tbody)
    end;

(* what if a param desn't occur in the concl? think about! Note: This
simply fixes meta level univ bound vars as Frees.  At the end, we will
change them back to schematic vars that will then unify
appropriactely, ie with unfake_vars *)
fun fake_goal gt i = 
    let 
      val prems = Logic.strip_imp_prems gt
      val sgt = nth_elem (i - 1, prems)

      val tbody = Term.strip_all_body sgt
      val tparams = Term.strip_all_vars sgt

      val fakefrees = map (fn (n, ty) => Free(mk_fake_all_name n, ty)) 
                          tparams
    in
      Term.subst_bounds (rev fakefrees,tbody)
    end;


(* hand written - for some reason the Isabelle version in drule is broken!
Example? something to do with Bin Yangs examples? 
 *)
fun rename_term_bvars ns (Abs(s,ty,t)) = 
    let val s2opt = Library.find_first (fn (x,y) => s = x) ns
    in case s2opt of 
         None => (Abs(s,ty,rename_term_bvars  ns t))
       | Some (_,s2) => Abs(s2,ty, rename_term_bvars ns t) end
  | rename_term_bvars ns (a$b) = 
    (rename_term_bvars ns a) $ (rename_term_bvars ns b)
  | rename_term_bvars _ x = x;

fun rename_thm_bvars ns th = 
    let val t = Thm.prop_of th 
    in Thm.rename_boundvars t (rename_term_bvars ns t) th end;

(* Finish this to show how it breaks! (raises the exception): 

exception rename_thm_bvars_exp of ((string * string) list * Thm.thm)

    Drule.rename_bvars ns th 
    handle TERM _ => raise rename_thm_bvars_exp (ns, th); 
*)

end;
