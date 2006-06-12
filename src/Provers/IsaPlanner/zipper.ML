(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      Pure/IsaPlanner/zipper.ML
    ID:		$Id$
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    24 Mar 2006
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:
    A notion roughly based on Huet's Zippers for Isabelle terms.
*)   

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* abstract term for no more than pattern matching *)
signature ABSTRACT_TRM = 
sig
type typ   (* types *)
type aname (* abstraction names *)
type fname (* parameter/free variable names *)
type cname (* constant names *)
type vname (* meta variable names *)
type bname (* bound var name *)
datatype term = Const of (cname * typ)
           | Abs of (aname * typ * term)
           | Free of (fname * typ)
           | Var of (vname * typ)
           | Bound of bname
           | $ of term * term;
type T = term;
end;

structure IsabelleTrmWrap : ABSTRACT_TRM= 
struct 
open Term;
type typ   = Term.typ; (* types *)
type aname = string; (* abstraction names *)
type fname = string; (* parameter/free variable names *)
type cname = string; (* constant names *)
type vname = string * int; (* meta variable names *)
type bname = int; (* bound var name *)
type T = term;
end;

(* Concrete version for the Trm structure *)
signature TRM_CTXT_DATA = 
sig

  structure Trm : ABSTRACT_TRM
  datatype dtrm = Abs of Trm.aname * Trm.typ
                | AppL of Trm.T
                | AppR of Trm.T;
  val apply : dtrm -> Trm.T -> Trm.T
  val eq_pos : dtrm * dtrm -> bool
end;

(* A trm context = list of derivatives *)
signature TRM_CTXT =
sig
  structure D : TRM_CTXT_DATA
  type T = D.dtrm list

  val empty : T
  val is_empty : T -> bool

  val eq_path : T * T -> bool

  val add_outerctxt : T -> T -> T

  val apply : T -> D.Trm.T -> D.Trm.T

  val nty_ctxt : T -> (D.Trm.aname * D.Trm.typ) list;
  val ty_ctxt : T -> D.Trm.typ list;

  val depth : T -> int;
  val map : (D.dtrm -> D.dtrm) -> T -> T
  val fold : (D.dtrm -> 'a -> 'a) -> T -> 'a -> 'a

end;

(* A zipper = a term looked at, at a particular point in the term *)
signature ZIPPER =
sig
  structure C : TRM_CTXT
  type T

  val mktop : C.D.Trm.T -> T
  val goto_top : T -> T
  val at_top : T -> bool
  val mk : (C.D.Trm.T * C.T) -> T
  val set_trm : C.D.Trm.T -> T -> T
  val set_ctxt : C.T -> T -> T

  val split : T -> T * C.T
  val add_outerctxt : C.T -> T -> T

  val ctxt : T -> C.T
  val trm : T -> C.D.Trm.T

  val nty_ctxt : T -> (C.D.Trm.aname * C.D.Trm.typ) list;
  val ty_ctxt : T -> C.D.Trm.typ list;

  val depth_of_ctxt : T -> int;
  val map_on_ctxt : (C.D.dtrm -> C.D.dtrm) -> T -> T
  val fold_on_ctxt : (C.D.dtrm -> 'a -> 'a) -> T -> 'a -> 'a

  (* searching through a zipper *)
  datatype zsearch = Here of T | LookIn of T;
  (* lazily search through the zipper *)
  val lzy_search : (T -> zsearch list) -> T -> T Seq.seq
  (* lazy search with folded data *)
  val pf_lzy_search : ('a -> T -> ('a * zsearch list)) 
                      -> 'a -> T -> T Seq.seq
  (* zsearch list is or-choices *)
  val searchfold : ('a -> T -> (('a * zsearch) list)) 
                      -> 'a -> T -> ('a * T) Seq.seq
  (* limit function to the current focus of the zipper, 
     but give function the zipper's context *)
  val limit_pcapply : (C.T -> T -> ('a * T) Seq.seq) 
                      -> T -> ('a * T) Seq.seq
  val limit_apply : (T -> T Seq.seq) -> T -> T Seq.seq
  val limit_capply : (C.T -> T -> T Seq.seq) -> T -> T Seq.seq

  (* moving around zippers with option types *)
  val omove_up : T -> T option
  val omove_up_abs : T -> T option
  val omove_up_app : T -> T option
  val omove_up_left : T -> T option
  val omove_up_right : T -> T option
  val omove_up_left_or_abs : T -> T option
  val omove_up_right_or_abs : T -> T option
  val omove_down_abs : T -> T option
  val omove_down_left : T -> T option
  val omove_down_right : T -> T option
  val omove_down_app : T -> (T * T) option

  (* moving around zippers, raising exceptions *)
  exception move of string * T
  val move_up : T -> T
  val move_up_abs : T -> T
  val move_up_app : T -> T
  val move_up_left : T -> T
  val move_up_right : T -> T
  val move_up_left_or_abs : T -> T
  val move_up_right_or_abs : T -> T
  val move_down_abs : T -> T
  val move_down_left : T -> T
  val move_down_right : T -> T
  val move_down_app : T -> T * T

end;


(* Zipper data for an generic trm *)
functor TrmCtxtDataFUN(Trm : ABSTRACT_TRM) 
: TRM_CTXT_DATA 
= struct
  
  structure Trm = Trm;

  (* a dtrm is, in McBridge-speak, a differentiated term. It represents
  the different ways a term can occur within its datatype constructors *)
  datatype dtrm = Abs of Trm.aname * Trm.typ
                | AppL of Trm.T
                | AppR of Trm.T;

  (* apply a dtrm to a term, ie put the dtrm above it, building context *)
  fun apply (Abs (s,ty)) t = Trm.Abs (s,ty,t)
    | apply (AppL tl) tr = Trm.$ (tl, tr)
    | apply (AppR tr) tl = Trm.$ (tl, tr);

  fun eq_pos (Abs _, Abs _) = true
    | eq_pos (AppL _, AppL _) = true
    | eq_pos (AppR _, AppR _) = true
    | eq_pos _ = false;

end;


(* functor for making term contexts given term data *)
functor TrmCtxtFUN(D : TRM_CTXT_DATA) 
 : TRM_CTXT =
struct 
  structure D = D;

  type T = D.dtrm list;

  val empty = [];
  val is_empty = List.null;

  fun eq_path ([], []) = true
    | eq_path ([], _::_) = false
    | eq_path ( _::_, []) = false
    | eq_path (h::t, h2::t2) = 
      D.eq_pos(h,h2) andalso eq_path (t, t2);

  (* add context to outside of existing context *) 
  fun add_outerctxt ctop cbottom = cbottom @ ctop; 

  (* mkterm : zipper -> trm -> trm *)
  val apply = Library.fold D.apply;
  
  (* named type context *)
  val nty_ctxt = List.foldr (fn (D.Abs nty,ntys) => nty::ntys
                             | (_,ntys) => ntys) [];
  (* type context *)
  val ty_ctxt = List.foldr (fn (D.Abs (_,ty),tys) => ty::tys
                           | (_,tys) => tys) [];

  val depth = length : T -> int;

  val map = List.map : (D.dtrm -> D.dtrm) -> T -> T

  val fold = Library.fold : (D.dtrm -> 'a -> 'a) -> T -> 'a -> 'a;

end;

(* zippers in terms of term contexts *)
functor ZipperFUN(C : TRM_CTXT) 
 : ZIPPER
= struct 

  structure C = C;
  structure D = C.D;
  structure Trm = D.Trm;

  type T = C.D.Trm.T * C.T;

  fun mktop t = (t, C.empty) : T

  val mk = I;
  fun set_trm x = apfst (K x);
  fun set_ctxt x = apsnd (K x);

  fun goto_top (z as (t,c)) = 
      if C.is_empty c then z else (C.apply c t, C.empty);

  fun at_top (_,c) = C.is_empty c;

  fun split (t,c) = ((t,C.empty) : T, c : C.T) 
  fun add_outerctxt c (t,c2) = (t, C.add_outerctxt c c2) : T

  val ctxt = snd;
  val trm = fst;

  fun nty_ctxt x = C.nty_ctxt (ctxt x);
  fun ty_ctxt x = C.ty_ctxt (ctxt x);

  fun depth_of_ctxt x = C.depth (ctxt x);
  fun map_on_ctxt x = apsnd (C.map x);
  fun fold_on_ctxt f = C.fold f o ctxt;

  fun omove_up (t,(d::c)) = SOME (D.apply d t, c)
    | omove_up (z as (_,[])) = NONE;
  fun omove_up_abs (t,((D.Abs(n,ty))::c)) = SOME (Trm.Abs(n,ty,t), c)
    | omove_up_abs z = NONE;
  fun omove_up_app (t,(D.AppL tl)::c) = SOME(Trm.$(tl,t), c)
    | omove_up_app (t,(D.AppR tr)::c) = SOME(Trm.$(t,tr), c)
    | omove_up_app z = NONE;
  fun omove_up_left (t,(D.AppL tl)::c) = SOME(Trm.$(tl,t), c)
    | omove_up_left z = NONE;
  fun omove_up_right (t,(D.AppR tr)::c) = SOME(Trm.$(t,tr), c)
    | omove_up_right _ = NONE;
  fun omove_up_left_or_abs (t,(D.AppL tl)::c) = 
      SOME (Trm.$(tl,t), c)
    | omove_up_left_or_abs (t,(D.Abs (n,ty))::c) = 
      SOME (Trm.Abs(n,ty,t), c)
    | omove_up_left_or_abs z = NONE;
  fun omove_up_right_or_abs (t,(D.Abs (n,ty))::c) = 
      SOME (Trm.Abs(n,ty,t), c) 
    | omove_up_right_or_abs (t,(D.AppR tr)::c) = 
      SOME (Trm.$(t,tr), c)
    | omove_up_right_or_abs _ = NONE;
  fun omove_down_abs (Trm.Abs(s,ty,t),c) = SOME (t,(D.Abs(s,ty))::c)
    | omove_down_abs _ = NONE;
  fun omove_down_left (Trm.$(l,r),c) = SOME (l,(D.AppR r)::c)
    | omove_down_left _ = NONE;
  fun omove_down_right (Trm.$(l,r),c) = SOME (r,(D.AppL l)::c)
    | omove_down_right _ = NONE;
  fun omove_down_app (Trm.$(l,r),c) = 
      SOME ((l,(D.AppR r)::c),(r,(D.AppL l)::c))
    | omove_down_app _ = NONE;

  exception move of string * T
  fun move_up (t,(d::c)) = (D.apply d t, c)
    | move_up (z as (_,[])) = raise move ("move_up",z);
  fun move_up_abs (t,((D.Abs(n,ty))::c)) = (Trm.Abs(n,ty,t), c)
    | move_up_abs z = raise move ("move_up_abs",z);
  fun move_up_app (t,(D.AppL tl)::c) = (Trm.$(tl,t), c)
    | move_up_app (t,(D.AppR tr)::c) = (Trm.$(t,tr), c)
    | move_up_app z = raise move ("move_up_app",z);
  fun move_up_left (t,((D.AppL tl)::c)) = (Trm.$(tl,t), c)
    | move_up_left z = raise move ("move_up_left",z);
  fun move_up_right (t,(D.AppR tr)::c) = (Trm.$(t,tr), c)
    | move_up_right z = raise move ("move_up_right",z);
  fun move_up_left_or_abs (t,(D.AppL tl)::c) = (Trm.$(tl,t), c)
    | move_up_left_or_abs (t,(D.Abs (n,ty))::c) = (Trm.Abs(n,ty,t), c)
    | move_up_left_or_abs z = raise move ("move_up_left_or_abs",z);
  fun move_up_right_or_abs (t,(D.Abs (n,ty))::c) = (Trm.Abs(n,ty,t), c) 
    | move_up_right_or_abs (t,(D.AppR tr)::c) = (Trm.$(t,tr), c)
    | move_up_right_or_abs z = raise move ("move_up_right_or_abs",z);
  fun move_down_abs (Trm.Abs(s,ty,t),c) = (t,(D.Abs(s,ty))::c)
    | move_down_abs z = raise move ("move_down_abs",z);
  fun move_down_left (Trm.$(l,r),c) = (l,(D.AppR r)::c)
    | move_down_left z = raise move ("move_down_left",z);
  fun move_down_right (Trm.$(l,r),c) = (r,(D.AppL l)::c)
    | move_down_right z = raise move ("move_down_right",z);
  fun move_down_app (Trm.$(l,r),c) = 
      ((l,(D.AppR r)::c),(r,(D.AppL l)::c))
    | move_down_app z = raise move ("move_down_app",z);


  (* Note: interpretted as being examined depth first *)
  datatype zsearch = Here of T | LookIn of T;

  fun lzy_search fsearch = 
      let 
        fun lzyl [] () = NONE
          | lzyl ((Here z) :: more) () = SOME(z, Seq.make (lzyl more))
          | lzyl ((LookIn z) :: more) () =
            (case lzy z
              of NONE => NONE
               | SOME (hz,mz) => 
                 SOME (hz, Seq.append (mz, Seq.make (lzyl more))))
        and lzy z = lzyl (fsearch z) ()
      in Seq.make o lzyl o fsearch end;

  (* path folded lazy search - the search list is defined in terms of
  the path passed through: the data a is updated with every zipper
  considered *)
  fun pf_lzy_search fsearch a0 z = 
      let 
        fun lzyl a [] () = NONE
          | lzyl a ((Here z) :: more) () = SOME(z, Seq.make (lzyl a more))
          | lzyl a ((LookIn z) :: more) () =
            (case lzy a z
              of NONE => lzyl a more ()
               | SOME(hz,mz) => SOME(hz,Seq.append(mz,Seq.make(lzyl a more))))
        and lzy a z = 
            let val (a2, slist) = (fsearch a z) in lzyl a2 slist () end

        val (a,slist) = fsearch a0 z
      in Seq.make (lzyl a slist) end;

  (* Note: depth first over zsearch results *)
  fun searchfold fsearch a0 z = 
      let 
        fun lzyl [] () = NONE
          | lzyl ((a, Here z) :: more) () = 
            SOME((a,z), Seq.make (lzyl more))
          | lzyl ((a, LookIn z) :: more) () =
            (case lzyl (fsearch a z) () of 
               NONE => lzyl more ()
             | SOME (z,mz) => SOME (z,Seq.append(mz, Seq.make (lzyl more))))
      in Seq.make (lzyl (fsearch a0 z)) end;


  fun limit_pcapply f z = 
      let val (z2,c) = split z
      in Seq.map (apsnd (add_outerctxt c)) (f c z2) end;
  fun limit_capply (f : C.T -> T -> T Seq.seq) (z : T) = 
      let val ((z2 : T),(c : C.T)) = split z
      in Seq.map (add_outerctxt c) (f c z2) end

  val limit_apply = limit_capply o K;

end;

(* now build these for Isabelle terms *)
structure TrmCtxtData = TrmCtxtDataFUN(IsabelleTrmWrap);
structure TrmCtxt = TrmCtxtFUN(TrmCtxtData);
structure Zipper = ZipperFUN(TrmCtxt);



(* For searching through Zippers below the current focus...
   KEY for naming scheme:    

   td = starting at the top down
   lr = going from left to right
   rl = going from right to left

   bl = starting at the bottom left
   br = starting at the bottom right
   ul = going up then left
   ur = going up then right
   ru = going right then up
   lu = going left then up
*)
signature ZIPPER_SEARCH =
sig
  structure Z : ZIPPER;
  
  val leaves_lr : Z.T -> Z.T Seq.seq
  val leaves_rl : Z.T -> Z.T Seq.seq

  val all_bl_ru : Z.T -> Z.T Seq.seq
  val all_bl_ur : Z.T -> Z.T Seq.seq
  val all_td_lr : Z.T -> Z.T Seq.seq
  val all_td_rl : Z.T -> Z.T Seq.seq
  
end;

functor ZipperSearchFUN(Zipper : ZIPPER) : ZIPPER_SEARCH
= struct

structure Z = Zipper;
structure C = Z.C;
structure D = C.D; 
structure Trm = D.Trm; 

fun sf_leaves_lr z = 
    case Z.trm z 
     of Trm.$ _ => [Z.LookIn (Z.move_down_left z),
                    Z.LookIn (Z.move_down_right z)]
      | Trm.Abs _ => [Z.LookIn (Z.move_down_abs z)]
      | _ => [Z.Here z];
fun sf_leaves_rl z = 
    case Z.trm z 
     of Trm.$ _ => [Z.LookIn (Z.move_down_right z),
                    Z.LookIn (Z.move_down_left z)]
      | Trm.Abs _ => [Z.LookIn (Z.move_down_abs z)]
      | _ => [Z.Here z];
val leaves_lr = Z.lzy_search sf_leaves_lr;
val leaves_rl = Z.lzy_search sf_leaves_rl;


fun sf_all_td_lr z = 
    case Z.trm z 
     of Trm.$ _ => [Z.Here z, Z.LookIn (Z.move_down_left z),
                    Z.LookIn (Z.move_down_right z)]
      | Trm.Abs _ => [Z.Here z, Z.LookIn (Z.move_down_abs z)]
      | _ => [Z.Here z];
fun sf_all_td_rl z = 
    case Z.trm z 
     of Trm.$ _ => [Z.Here z, Z.LookIn (Z.move_down_right z),
                    Z.LookIn (Z.move_down_left z)]
      | Trm.Abs _ => [Z.Here z, Z.LookIn (Z.move_down_abs z)]
      | _ => [Z.Here z];
fun sf_all_bl_ur z = 
    case Z.trm z 
     of Trm.$ _ => [Z.LookIn (Z.move_down_left z), Z.Here z,
                    Z.LookIn (Z.move_down_right z)]
      | Trm.Abs _ => [Z.LookIn (Z.move_down_abs z),
                      Z.Here z]
      | _ => [Z.Here z];
fun sf_all_bl_ru z = 
    case Z.trm z 
     of Trm.$ _ => [Z.LookIn (Z.move_down_left z),
                    Z.LookIn (Z.move_down_right z), Z.Here z]
      | Trm.Abs _ => [Z.LookIn (Z.move_down_abs z), Z.Here z]
      | _ => [Z.Here z];

val all_td_lr = Z.lzy_search sf_all_td_lr;
val all_td_rl = Z.lzy_search sf_all_td_lr;
val all_bl_ur = Z.lzy_search sf_all_bl_ru;
val all_bl_ru = Z.lzy_search sf_all_bl_ur;

end;


structure ZipperSearch = ZipperSearchFUN(Zipper);
