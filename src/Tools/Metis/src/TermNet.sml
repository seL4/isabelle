(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure TermNet :> TermNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Anonymous variables.                                                      *)
(* ------------------------------------------------------------------------- *)

val anonymousName = Name.fromString "_";
val anonymousVar = Term.Var anonymousName;

(* ------------------------------------------------------------------------- *)
(* Quotient terms.                                                           *)
(* ------------------------------------------------------------------------- *)

datatype qterm =
    Var
  | Fn of NameArity.nameArity * qterm list;

local
  fun cmp [] = EQUAL
    | cmp (q1_q2 :: qs) =
      if Portable.pointerEqual q1_q2 then cmp qs
      else
        case q1_q2 of
          (Var,Var) => EQUAL
        | (Var, Fn _) => LESS
        | (Fn _, Var) => GREATER
        | (Fn f1, Fn f2) => fnCmp f1 f2 qs

  and fnCmp (n1,q1) (n2,q2) qs =
    case NameArity.compare (n1,n2) of
      LESS => LESS
    | EQUAL => cmp (zip q1 q2 @ qs)
    | GREATER => GREATER;
in
  fun compareQterm q1_q2 = cmp [q1_q2];

  fun compareFnQterm (f1,f2) = fnCmp f1 f2 [];
end;

fun equalQterm q1 q2 = compareQterm (q1,q2) = EQUAL;

fun equalFnQterm f1 f2 = compareFnQterm (f1,f2) = EQUAL;

fun termToQterm (Term.Var _) = Var
  | termToQterm (Term.Fn (f,l)) = Fn ((f, length l), map termToQterm l);

local
  fun qm [] = true
    | qm ((Var,_) :: rest) = qm rest
    | qm ((Fn _, Var) :: _) = false
    | qm ((Fn (f,a), Fn (g,b)) :: rest) =
      NameArity.equal f g andalso qm (zip a b @ rest);
in
  fun matchQtermQterm qtm qtm' = qm [(qtm,qtm')];
end;

local
  fun qm [] = true
    | qm ((Var,_) :: rest) = qm rest
    | qm ((Fn _, Term.Var _) :: _) = false
    | qm ((Fn ((f,n),a), Term.Fn (g,b)) :: rest) =
      Name.equal f g andalso n = length b andalso qm (zip a b @ rest);
in
  fun matchQtermTerm qtm tm = qm [(qtm,tm)];
end;

local
  fun qn qsub [] = SOME qsub
    | qn qsub ((Term.Var v, qtm) :: rest) =
      (case NameMap.peek qsub v of
         NONE => qn (NameMap.insert qsub (v,qtm)) rest
       | SOME qtm' => if equalQterm qtm qtm' then qn qsub rest else NONE)
    | qn _ ((Term.Fn _, Var) :: _) = NONE
    | qn qsub ((Term.Fn (f,a), Fn ((g,n),b)) :: rest) =
      if Name.equal f g andalso length a = n then qn qsub (zip a b @ rest)
      else NONE;
in
  fun matchTermQterm qsub tm qtm = qn qsub [(tm,qtm)];
end;

local
  fun qv Var x = x
    | qv x Var = x
    | qv (Fn (f,a)) (Fn (g,b)) =
      let
        val _ = NameArity.equal f g orelse raise Error "TermNet.qv"
      in
        Fn (f, zipWith qv a b)
      end;

  fun qu qsub [] = qsub
    | qu qsub ((Var, _) :: rest) = qu qsub rest
    | qu qsub ((qtm, Term.Var v) :: rest) =
      let
        val qtm =
            case NameMap.peek qsub v of NONE => qtm | SOME qtm' => qv qtm qtm'
      in
        qu (NameMap.insert qsub (v,qtm)) rest
      end
    | qu qsub ((Fn ((f,n),a), Term.Fn (g,b)) :: rest) =
      if Name.equal f g andalso n = length b then qu qsub (zip a b @ rest)
      else raise Error "TermNet.qu";
in
  fun unifyQtermQterm qtm qtm' = total (qv qtm) qtm';

  fun unifyQtermTerm qsub qtm tm = total (qu qsub) [(qtm,tm)];
end;

local
  fun qtermToTerm Var = anonymousVar
    | qtermToTerm (Fn ((f,_),l)) = Term.Fn (f, map qtermToTerm l);
in
  val ppQterm = Print.ppMap qtermToTerm Term.pp;
end;

(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};

datatype 'a net =
    Result of 'a list
  | Single of qterm * 'a net
  | Multiple of 'a net option * 'a net NameArityMap.map;

datatype 'a termNet = Net of parameters * int * (int * (int * 'a) net) option;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun new parm = Net (parm,0,NONE);

local
  fun computeSize (Result l) = length l
    | computeSize (Single (_,n)) = computeSize n
    | computeSize (Multiple (vs,fs)) =
      NameArityMap.foldl
        (fn (_,n,acc) => acc + computeSize n)
        (case vs of SOME n => computeSize n | NONE => 0)
        fs;
in
  fun netSize NONE = NONE
    | netSize (SOME n) = SOME (computeSize n, n);
end;

fun size (Net (_,_,NONE)) = 0
  | size (Net (_, _, SOME (i,_))) = i;

fun null net = size net = 0;

fun singles qtms a = foldr Single a qtms;

local
  fun pre NONE = (0,NONE)
    | pre (SOME (i,n)) = (i, SOME n);

  fun add (Result l) [] (Result l') = Result (l @ l')
    | add a (input1 as qtm :: qtms) (Single (qtm',n)) =
      if equalQterm qtm qtm' then Single (qtm, add a qtms n)
      else add a input1 (add n [qtm'] (Multiple (NONE, NameArityMap.new ())))
    | add a (Var :: qtms) (Multiple (vs,fs)) =
      Multiple (SOME (oadd a qtms vs), fs)
    | add a (Fn (f,l) :: qtms) (Multiple (vs,fs)) =
      let
        val n = NameArityMap.peek fs f
      in
        Multiple (vs, NameArityMap.insert fs (f, oadd a (l @ qtms) n))
      end
    | add _ _ _ = raise Bug "TermNet.insert: Match"

  and oadd a qtms NONE = singles qtms a
    | oadd a qtms (SOME n) = add a qtms n;

  fun ins a qtm (i,n) = SOME (i + 1, oadd (Result [a]) [qtm] n);
in
  fun insert (Net (p,k,n)) (tm,a) =
      Net (p, k + 1, ins (k,a) (termToQterm tm) (pre n))
      handle Error _ => raise Bug "TermNet.insert: should never fail";
end;

fun fromList parm l = foldl (fn (tm_a,n) => insert n tm_a) (new parm) l;

fun filter pred =
    let
      fun filt (Result l) =
          (case List.filter (fn (_,a) => pred a) l of
             [] => NONE
           | l => SOME (Result l))
        | filt (Single (qtm,n)) =
          (case filt n of
             NONE => NONE
           | SOME n => SOME (Single (qtm,n)))
        | filt (Multiple (vs,fs)) =
          let
            val vs = Option.mapPartial filt vs

            val fs = NameArityMap.mapPartial (fn (_,n) => filt n) fs
          in
            if not (Option.isSome vs) andalso NameArityMap.null fs then NONE
            else SOME (Multiple (vs,fs))
          end
    in
      fn net as Net (_,_,NONE) => net
       | Net (p, k, SOME (_,n)) => Net (p, k, netSize (filt n))
    end
    handle Error _ => raise Bug "TermNet.filter: should never fail";

fun toString net = "TermNet[" ^ Int.toString (size net) ^ "]";

(* ------------------------------------------------------------------------- *)
(* Specialized fold operations to support matching and unification.          *)
(* ------------------------------------------------------------------------- *)

local
  fun norm (0 :: ks, (f as (_,n)) :: fs, qtms) =
      let
        val (a,qtms) = revDivide qtms n
      in
        addQterm (Fn (f,a)) (ks,fs,qtms)
      end
    | norm stack = stack

  and addQterm qtm (ks,fs,qtms) =
      let
        val ks = case ks of [] => [] | k :: ks => (k - 1) :: ks
      in
        norm (ks, fs, qtm :: qtms)
      end

  and addFn (f as (_,n)) (ks,fs,qtms) = norm (n :: ks, f :: fs, qtms);
in
  val stackEmpty = ([],[],[]);

  val stackAddQterm = addQterm;

  val stackAddFn = addFn;

  fun stackValue ([],[],[qtm]) = qtm
    | stackValue _ = raise Bug "TermNet.stackValue";
end;

local
  fun fold _ acc [] = acc
    | fold inc acc ((0,stack,net) :: rest) =
      fold inc (inc (stackValue stack, net, acc)) rest
    | fold inc acc ((n, stack, Single (qtm,net)) :: rest) =
      fold inc acc ((n - 1, stackAddQterm qtm stack, net) :: rest)
    | fold inc acc ((n, stack, Multiple (v,fns)) :: rest) =
      let
        val n = n - 1

        val rest =
            case v of
              NONE => rest
            | SOME net => (n, stackAddQterm Var stack, net) :: rest

        fun getFns (f as (_,k), net, x) =
            (k + n, stackAddFn f stack, net) :: x
      in
        fold inc acc (NameArityMap.foldr getFns rest fns)
      end
    | fold _ _ _ = raise Bug "TermNet.foldTerms.fold";
in
  fun foldTerms inc acc net = fold inc acc [(1,stackEmpty,net)];
end;

fun foldEqualTerms pat inc acc =
    let
      fun fold ([],net) = inc (pat,net,acc)
        | fold (pat :: pats, Single (qtm,net)) =
          if equalQterm pat qtm then fold (pats,net) else acc
        | fold (Var :: pats, Multiple (v,_)) =
          (case v of NONE => acc | SOME net => fold (pats,net))
        | fold (Fn (f,a) :: pats, Multiple (_,fns)) =
          (case NameArityMap.peek fns f of
             NONE => acc
           | SOME net => fold (a @ pats, net))
        | fold _ = raise Bug "TermNet.foldEqualTerms.fold";
    in
      fn net => fold ([pat],net)
    end;

local
  fun fold _ acc [] = acc
    | fold inc acc (([],stack,net) :: rest) =
      fold inc (inc (stackValue stack, net, acc)) rest
    | fold inc acc ((Var :: pats, stack, net) :: rest) =
      let
        fun harvest (qtm,n,l) = (pats, stackAddQterm qtm stack, n) :: l
      in
        fold inc acc (foldTerms harvest rest net)
      end
    | fold inc acc ((pat :: pats, stack, Single (qtm,net)) :: rest) =
      (case unifyQtermQterm pat qtm of
         NONE => fold inc acc rest
       | SOME qtm =>
         fold inc acc ((pats, stackAddQterm qtm stack, net) :: rest))
    | fold
        inc acc
        (((pat as Fn (f,a)) :: pats, stack, Multiple (v,fns)) :: rest) =
      let
        val rest =
            case v of
              NONE => rest
            | SOME net => (pats, stackAddQterm pat stack, net) :: rest

        val rest =
            case NameArityMap.peek fns f of
              NONE => rest
            | SOME net => (a @ pats, stackAddFn f stack, net) :: rest
      in
        fold inc acc rest
      end
    | fold _ _ _ = raise Bug "TermNet.foldUnifiableTerms.fold";
in
  fun foldUnifiableTerms pat inc acc net =
      fold inc acc [([pat],stackEmpty,net)];
end;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

local
  fun idwise ((m,_),(n,_)) = Int.compare (m,n);

  fun fifoize ({fifo, ...} : parameters) l = if fifo then sort idwise l else l;
in
  fun finally parm l = map snd (fifoize parm l);
end;

local
  fun mat acc [] = acc
    | mat acc ((Result l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((Single (qtm,n), tm :: tms) :: rest) =
      mat acc (if matchQtermTerm qtm tm then (n,tms) :: rest else rest)
    | mat acc ((Multiple (vs,fs), tm :: tms) :: rest) =
      let
        val rest = case vs of NONE => rest | SOME n => (n,tms) :: rest

        val rest =
            case tm of
              Term.Var _ => rest
            | Term.Fn (f,l) =>
              case NameArityMap.peek fs (f, length l) of
                NONE => rest
              | SOME n => (n, l @ tms) :: rest
      in
        mat acc rest
      end
    | mat _ _ = raise Bug "TermNet.match: Match";
in
  fun match (Net (_,_,NONE)) _ = []
    | match (Net (p, _, SOME (_,n))) tm =
      finally p (mat [] [(n,[tm])])
      handle Error _ => raise Bug "TermNet.match: should never fail";
end;

local
  fun unseenInc qsub v tms (qtm,net,rest) =
      (NameMap.insert qsub (v,qtm), net, tms) :: rest;

  fun seenInc qsub tms (_,net,rest) = (qsub,net,tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, Result l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((qsub, Single (qtm,net), tm :: tms) :: rest) =
      (case matchTermQterm qsub tm qtm of
         NONE => mat acc rest
       | SOME qsub => mat acc ((qsub,net,tms) :: rest))
    | mat acc ((qsub, net as Multiple _, Term.Var v :: tms) :: rest) =
      (case NameMap.peek qsub v of
         NONE => mat acc (foldTerms (unseenInc qsub v tms) rest net)
       | SOME qtm => mat acc (foldEqualTerms qtm (seenInc qsub tms) rest net))
    | mat acc ((qsub, Multiple (_,fns), Term.Fn (f,a) :: tms) :: rest) =
      let
        val rest =
            case NameArityMap.peek fns (f, length a) of
              NONE => rest
            | SOME net => (qsub, net, a @ tms) :: rest
      in
        mat acc rest
      end
    | mat _ _ = raise Bug "TermNet.matched.mat";
in
  fun matched (Net (_,_,NONE)) _ = []
    | matched (Net (parm, _, SOME (_,net))) tm =
      finally parm (mat [] [(NameMap.new (), net, [tm])])
      handle Error _ => raise Bug "TermNet.matched: should never fail";
end;

local
  fun inc qsub v tms (qtm,net,rest) =
      (NameMap.insert qsub (v,qtm), net, tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, Result l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((qsub, Single (qtm,net), tm :: tms) :: rest) =
      (case unifyQtermTerm qsub qtm tm of
         NONE => mat acc rest
       | SOME qsub => mat acc ((qsub,net,tms) :: rest))
    | mat acc ((qsub, net as Multiple _, Term.Var v :: tms) :: rest) =
      (case NameMap.peek qsub v of
         NONE => mat acc (foldTerms (inc qsub v tms) rest net)
       | SOME qtm => mat acc (foldUnifiableTerms qtm (inc qsub v tms) rest net))
    | mat acc ((qsub, Multiple (v,fns), Term.Fn (f,a) :: tms) :: rest) =
      let
        val rest = case v of NONE => rest | SOME net => (qsub,net,tms) :: rest

        val rest =
            case NameArityMap.peek fns (f, length a) of
              NONE => rest
            | SOME net => (qsub, net, a @ tms) :: rest
      in
        mat acc rest
      end
    | mat _ _ = raise Bug "TermNet.unify.mat";
in
  fun unify (Net (_,_,NONE)) _ = []
    | unify (Net (parm, _, SOME (_,net))) tm =
      finally parm (mat [] [(NameMap.new (), net, [tm])])
      handle Error _ => raise Bug "TermNet.unify: should never fail";
end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun inc (qtm, Result l, acc) =
      foldl (fn ((n,a),acc) => (n,(qtm,a)) :: acc) acc l
    | inc _ = raise Bug "TermNet.pp.inc";

  fun toList (Net (_,_,NONE)) = []
    | toList (Net (parm, _, SOME (_,net))) =
      finally parm (foldTerms inc [] net);
in
  fun pp ppA =
      Print.ppMap toList (Print.ppList (Print.ppOp2 " |->" ppQterm ppA));
end;

end
