(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      libs/focus_term_lib.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Date:       16 April 2003
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Generic Foucs terms (like Zippers), which allows modification and
    manipulation of term keeping track of how we got to the position
    in the term. We provide a signature for terms, ie any kind of
    lamda calculus with abs and application, and some notion of types
    and naming of abstracted vars. 

    FIXME: at some point in the future make a library to work simply
    with polymorphic upterms - that way if I want to use them without
    the focus part, then I don't need to include all the focus stuff.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(*  to endoce and decode general terms into the type needed by focus
term, this is an easy thing to write, but needs to be done for each
type that is going to be used with focus terms. *)

signature F_ENCODE_TERM_SIG = 
sig

  type term (* type of term to be encoded into TermT for focus term manip *)
  type TypeT (* type annotation for abstractions *)
  type LeafT (* type for other leaf types in term sturcture *)

  (* the type to be encoded into *)
  datatype TermT = $ of TermT * TermT
    | Abs of string * TypeT * TermT
    | lf of LeafT

  (* the encode and decode functions *)
  val fakebounds : string * TypeT -> term -> term
  val encode : term -> TermT
  val decode : TermT -> term

end;



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature FOCUS_TERM_SIG = 
sig
     structure MinTermS : F_ENCODE_TERM_SIG

     exception focus_term_exp of string;
     exception out_of_term_exception of string;

     type Term = MinTermS.TermT;
     type Type = MinTermS.TypeT;

     type UpTerm = (Term,Type) UpTermLib.T;

(*   datatype
       UpTerm =
           abs of string * Type * UpTerm
         | appl of Term * UpTerm
         | appr of Term * UpTerm
         | root *)

     datatype FcTerm = focus of Term * UpTerm

     (* translating *)
     val fcterm_of_term : MinTermS.term -> FcTerm
     val term_of_fcterm : FcTerm -> MinTermS.term

     (* editing/constrution *)
     val enc_appl : (MinTermS.term * UpTerm) -> UpTerm
     val enc_appr : (MinTermS.term * UpTerm) -> UpTerm

     (* upterm creatioin *)
     val upterm_of : FcTerm -> UpTerm
     val add_upterm : UpTerm -> FcTerm -> FcTerm
     val mk_term_of_upterm : (MinTermS.term * UpTerm) -> MinTermS.term
     val mk_termf_of_upterm : UpTerm -> 
            (((string * Type) list) * 
             (MinTermS.term -> MinTermS.term))
     val pure_mk_termf_of_upterm : (MinTermS.term, Type) UpTermLib.T -> 
                                   (((string * Type) list) * 
                                    (MinTermS.term -> MinTermS.term))

     (* focusing, throws exceptions *)
     val focus_bot_left_leaf : FcTerm -> FcTerm
     val focus_left : FcTerm -> FcTerm
     val focus_right : FcTerm -> FcTerm
     val focus_abs : FcTerm -> FcTerm
     val focus_fake_abs : FcTerm -> FcTerm
     val focus_to_top : FcTerm -> FcTerm
     val focus_up : FcTerm -> FcTerm
     val focus_up_right : FcTerm -> FcTerm
     val focus_up_right1 : FcTerm -> FcTerm

     (* optional focus changes *)
     val focus_up_abs : FcTerm -> FcTerm option
     val focus_up_appr : FcTerm -> FcTerm option
     val focus_up_appl : FcTerm -> FcTerm option
     val focus_up_abs_or_appr : FcTerm -> FcTerm option

     val tyenv_of_focus : FcTerm -> (string * Type) list
     val tyenv_of_focus' : FcTerm -> Type list

     (* set/get the focus term *)
     val set_focus_of_fcterm : FcTerm -> MinTermS.term -> FcTerm
     val focus_of_fcterm : FcTerm -> MinTermS.term

     (* leaf navigation *) 
     val leaf_seq_of_fcterm : FcTerm -> FcTerm Seq.seq
     val next_leaf_fcterm : FcTerm -> FcTerm
     val next_leaf_of_fcterm_seq : FcTerm -> FcTerm Seq.seq

     (* analysis *)
     val upsize_of_fcterm : FcTerm -> int
     val pretty_fcterm : FcTerm -> Pretty.T
end;



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* 

   NOTE!!! I think this can be done in a purely functional way with a
   pair of a term (the focus) and a function, that when applied
   unfocuses one level... maybe think about this as it would be a very
   nice generic consrtuction, without the need for encoding/decoding
   strutcures.

*)
functor FocusTermFUN(structure EncodeTerm : F_ENCODE_TERM_SIG)
  : FOCUS_TERM_SIG = 
struct

structure MinTermS = EncodeTerm;

local open MinTermS open UpTermLib in

  type Term = MinTermS.TermT;
  type Type = MinTermS.TypeT;

  exception focus_term_exp of string;
  exception out_of_term_exception of string;

  infix 9 $

  (* datatype to hold a term tree and the path to where you are in the term *)
(*   datatype UpTerm = root
                  | appl of (Term * UpTerm)
                  | appr of (Term * UpTerm)
                  | abs of (string * Type * UpTerm); *)

  type UpTerm = (Term,Type) UpTermLib.T;

  fun enc_appl (t,u) = appl((MinTermS.encode t),u);
  fun enc_appr (t,u) = appr((MinTermS.encode t),u);

  datatype FcTerm = focus of (Term * UpTerm);

  (* the the term of the upterm *)
  fun mk_term_of_upt_aux (t, root) = MinTermS.decode t
    | mk_term_of_upt_aux (t, appl (l,m)) =  mk_term_of_upt_aux(l$t, m)
    | mk_term_of_upt_aux (t, appr (r,m)) =  mk_term_of_upt_aux(t$r, m)
    | mk_term_of_upt_aux (t, abs (s,ty,m)) = mk_term_of_upt_aux(Abs(s,ty,t),m);

  fun mk_term_of_upterm (t, ut) = mk_term_of_upt_aux (MinTermS.encode t, ut);

  (* a function version of the above, given an upterm it returns:
     a function on that given a term puts it in the context of the upterm,
     and a list of bound variables that are in the upterm, added as 
     we go up - so in reverse order from that typiclaly used by top-down
     parsing of terms. *)
  fun mk_termf_of_upt_aux (f, bs, root) = 
      (bs, fn t => MinTermS.decode (f t))
    | mk_termf_of_upt_aux (f, bs, appl (l,m)) =  
      mk_termf_of_upt_aux (fn t => l $ (f t), bs, m)
    | mk_termf_of_upt_aux (f, bs, appr (r,m)) =  
      mk_termf_of_upt_aux (fn t => (f t) $ r, bs, m)
    | mk_termf_of_upt_aux (f, bs, abs (s,ty,m)) = 
      mk_termf_of_upt_aux (fn t => Abs(s,ty,(f t)), (s,ty)::bs, m);

  fun mk_termf_of_upterm ut = mk_termf_of_upt_aux (MinTermS.encode, [], ut);

 
  fun upterm_of (focus(t, u)) = u;

  (* put a new upterm at the start of our current term *)
  fun add_upterm u2 (focus(t, u)) = focus(t, UpTermLib.apply u2 u);


  (* As above but work on the pure originial upterm type *)
  fun pure_mk_termf_of_upterm ut = 
      mk_termf_of_upt_aux 
        (encode, [], (map_to_upterm_parts (encode, I) ut));

  fun fcterm_of_term t = focus(encode t, root);

  fun term_of_fcterm (focus (t, m)) = mk_term_of_upt_aux (t, m);

(*  fun term_of_fcterm (focus (t, root)) = mk_term_of_upt_aux (t, root)
    | term_of_fcterm _ = raise focus_term_exp "term_of_fcterm: something bad has happened here."; *)

  fun focus_of_fcterm (focus(t, _)) = MinTermS.decode t;

  (* replace the focus term with a new term... *)
  fun set_focus_of_fcterm (focus(_, m)) nt = focus(MinTermS.encode nt, m);

  fun focus_left (focus(a $ b, m)) = focus(a, appr(b, m))
    | focus_left (focus(Abs(s,ty,t), m)) = focus_left (focus(t, abs(s,ty,m)))
    | focus_left (focus(l, m)) = raise out_of_term_exception "focus_left";

(* Note: ":" is standard for faked bound vars... see: EQStepTacTermTools *)
  fun focus_fake_abs (focus(Abs(s,ty,t), m)) = 
      let val t' = MinTermS.encode (fakebounds (s,ty) (MinTermS.decode t))
      in focus(t', abs(s,ty,m)) end
    | focus_fake_abs (focus(l, m)) = raise out_of_term_exception "focus_fake_abs";

  fun focus_abs (focus(Abs(s,ty,t), m)) = focus(t, abs(s,ty,m))
    | focus_abs (focus(l, m)) = raise out_of_term_exception "focus_abs";


  fun focus_right (focus(a $ b, m)) = focus(b, appl(a, m))
    | focus_right (focus(Abs(s,ty,t), m)) = focus_right (focus(t, abs(s,ty,m)))
    | focus_right (focus(l, m)) = raise out_of_term_exception "focus_right";

  fun focus_up (focus(t, appl(l,m))) = focus(l$t, m)
    | focus_up (focus(t, appr(r,m))) = focus(t$r, m)
    | focus_up (focus(t, abs(s,ty,m))) = focus_up (focus(Abs(s,ty,t), m))
    | focus_up (focus(t, root)) = raise out_of_term_exception "focus_up";

  fun focus_to_top t = 
    focus_to_top (focus_up t) handle out_of_term_exception _ => t;

  (* focus up until you can move right, and then do so *)
  fun focus_up_right (focus(t, appl(l,m))) = 
      focus_up_right (focus(l$t, m))
    | focus_up_right (focus(t, appr(r,m))) = 
      focus(r, appl(t,m))
    | focus_up_right (focus(t, abs(s,ty,m))) = 
      focus_up_right (focus(Abs(s,ty,t), m))
    | focus_up_right (focus(t, root)) = 
      raise out_of_term_exception "focus_up_right";

  (* as above, but do not move up over a left application *)
  fun focus_up_right1 (focus(t, appl(l,m))) = 
      raise out_of_term_exception "focus_up_right1"
    | focus_up_right1 (focus(t, appr(r,m))) = 
      focus(r, appl(t,m))
    | focus_up_right1 (focus(t, abs(s,ty,m))) = 
      focus_up_right (focus(Abs(s,ty,t), m))
    | focus_up_right1 (focus(t, root)) = 
      raise out_of_term_exception "focus_up_right1";

  (* move focus to the bottom left *)
  fun focus_bot_left_leaf (ft as focus(t, _)) = 
        focus_bot_left_leaf (focus_left ft) 
        handle out_of_term_exception  _=> ft;

  (* focus tools for working directly with the focus representation *)
  fun focus_up_appr (focus(t, appl(l,m))) = NONE
    | focus_up_appr (focus(t, appr(r,m))) = SOME (focus(t$r, m))
    | focus_up_appr (focus(t, abs(s,ty,m))) = NONE
    | focus_up_appr (focus(t, root)) = NONE;

  fun focus_up_appl (focus(t, appl(l,m))) = SOME (focus(l$t, m))
    | focus_up_appl (focus(t, appr(r,m))) = NONE
    | focus_up_appl (focus(t, abs(s,ty,m))) = NONE
    | focus_up_appl (focus(t, root)) = NONE;

  fun focus_up_abs (focus(t, appl(l,m))) = NONE
    | focus_up_abs (focus(t, appr(r,m))) = NONE
    | focus_up_abs (focus(t, abs(s,ty,m))) = 
      SOME (focus_up (focus(Abs(s,ty,t), m)))
    | focus_up_abs (focus(t, root)) = NONE;

  fun focus_up_abs_or_appr (focus(t, appl(l,m))) = NONE
    | focus_up_abs_or_appr (focus(t, appr(r,m))) = SOME (focus(t$r, m))
    | focus_up_abs_or_appr (focus(t, abs(s,ty,m))) = 
      SOME (focus_up (focus(Abs(s,ty,t), m)))
    | focus_up_abs_or_appr (focus(t, root)) = NONE;


  fun tyenv_of_focus (focus(t, u)) = tyenv_of_upterm u;
  fun tyenv_of_focus' (focus(t, u)) = tyenv_of_upterm' u;

  (* return the Term.type of the focus term, computes bound vars type,
     does a quick check only. *)
(*  fun fastype_of_focus (focus(t, m)) = 
       let 
         fun boundtypes_of_upterm (abs(s,ty,m)) = 
         ty::(boundtypes_of_upterm m)
           | boundtypes_of_upterm (appl(t,m)) = 
         boundtypes_of_upterm m
           | boundtypes_of_upterm (appr(t,m)) = 
         boundtypes_of_upterm m
           | boundtypes_of_upterm (root) = []
       in
         fastype_of1 ((boundtypes_of_upterm m), t)
       end; *)

  (* gets the next left hand side term, or throws an exception *)
  fun next_leaf_fcterm ft = focus_bot_left_leaf (focus_up_right ft);

  fun next_leaf_of_fcterm_seq_aux t () = 
    let val nextt = next_leaf_fcterm t
    in 
        SOME (nextt, Seq.make (next_leaf_of_fcterm_seq_aux nextt))
    end handle out_of_term_exception _ => NONE;

  (* sequence of next upterms from start upterm... 
     ie a sequence of all leafs after this one*)
  fun next_leaf_of_fcterm_seq in_t = 
    Seq.make (next_leaf_of_fcterm_seq_aux in_t);

  (* returns a sequence of all leaf up terms from term, ie DFS on 
   leafs of term, ie uses time O(n), n = sizeof term. *)
  fun leaf_seq_of_fcterm in_t = 
    let 
      val botleft = (focus_bot_left_leaf in_t)
    in
      Seq.cons (botleft, (Seq.make (next_leaf_of_fcterm_seq_aux botleft)) )
    end;


  fun upsize_of_fcterm (focus(t, ut)) = upsize_of_upterm ut;

  fun pretty_fcterm ft = Pretty.str "no yet implemented";

end; (* local *)

end; (* functor *)





(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* focus term encoding sturcture for isabelle terms *)
structure EncodeIsaFTerm : F_ENCODE_TERM_SIG = 
struct
  infix 9 $;

  type term = Term.term;

  type TypeT = Term.typ;

  datatype LeafT = lConst of string * Term.typ
     | lVar of ((string * int) * Term.typ)
     | lFree of (string * Term.typ)
     | lBound of int;

  datatype TermT = op $ of TermT * TermT
    | Abs of string * TypeT * TermT
    | lf of LeafT;

  fun fakebounds (s, ty) t = subst_bound (Free(":" ^ s, ty), t);

  fun encode (Term.$(a,b)) = (encode a) $ (encode b)
    | encode (Term.Abs(s,ty,t)) = Abs(s,ty,(encode t))
    | encode (Term.Const(s,ty)) = lf(lConst(s,ty))
    | encode (Term.Var((s,i),ty)) = lf(lVar((s,i),ty))
    | encode (Term.Free(s,ty)) = lf(lFree(s,ty))
    | encode (Term.Bound i) = lf(lBound i);

  fun decode (a $ b) = Term.$(decode a, decode b)
    | decode (Abs(s,ty,t)) = (Term.Abs(s,ty,decode t))
    | decode (lf(lConst(s,ty))) = Term.Const(s,ty)
    | decode (lf(lVar((s,i),ty))) = Term.Var((s,i),ty)
    | decode (lf(lFree(s,ty))) = (Term.Free(s,ty))
    | decode (lf(lBound i)) = (Term.Bound i);

end;

