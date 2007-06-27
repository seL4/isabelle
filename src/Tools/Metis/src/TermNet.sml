(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure TermNet :> TermNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Quotient terms                                                            *)
(* ------------------------------------------------------------------------- *)

datatype qterm = VAR | FN of NameArity.nameArity * qterm list;

fun termToQterm (Term.Var _) = VAR
  | termToQterm (Term.Fn (f,l)) = FN ((f, length l), map termToQterm l);

local
  fun qm [] = true
    | qm ((VAR,_) :: rest) = qm rest
    | qm ((FN _, VAR) :: _) = false
    | qm ((FN (f,a), FN (g,b)) :: rest) = f = g andalso qm (zip a b @ rest);
in
  fun matchQtermQterm qtm qtm' = qm [(qtm,qtm')];
end;

local
  fun qm [] = true
    | qm ((VAR,_) :: rest) = qm rest
    | qm ((FN _, Term.Var _) :: _) = false
    | qm ((FN ((f,n),a), Term.Fn (g,b)) :: rest) =
      f = g andalso n = length b andalso qm (zip a b @ rest);
in
  fun matchQtermTerm qtm tm = qm [(qtm,tm)];
end;

local
  fun qn qsub [] = SOME qsub
    | qn qsub ((Term.Var v, qtm) :: rest) =
      (case NameMap.peek qsub v of
         NONE => qn (NameMap.insert qsub (v,qtm)) rest
       | SOME qtm' => if qtm = qtm' then qn qsub rest else NONE)
    | qn _ ((Term.Fn _, VAR) :: _) = NONE
    | qn qsub ((Term.Fn (f,a), FN ((g,n),b)) :: rest) =
      if f = g andalso length a = n then qn qsub (zip a b @ rest) else NONE;
in
  fun matchTermQterm qsub tm qtm = qn qsub [(tm,qtm)];
end;

local
  fun qv VAR x = x
    | qv x VAR = x
    | qv (FN (f,a)) (FN (g,b)) =
      let
        val _ = f = g orelse raise Error "TermNet.qv"
      in
        FN (f, zipwith qv a b)
      end;

  fun qu qsub [] = qsub
    | qu qsub ((VAR, _) :: rest) = qu qsub rest
    | qu qsub ((qtm, Term.Var v) :: rest) =
      let
        val qtm =
            case NameMap.peek qsub v of NONE => qtm | SOME qtm' => qv qtm qtm'
      in
        qu (NameMap.insert qsub (v,qtm)) rest
      end
    | qu qsub ((FN ((f,n),a), Term.Fn (g,b)) :: rest) =
      if f = g andalso n = length b then qu qsub (zip a b @ rest)
      else raise Error "TermNet.qu";
in
  fun unifyQtermQterm qtm qtm' = total (qv qtm) qtm';

  fun unifyQtermTerm qsub qtm tm = total (qu qsub) [(qtm,tm)];
end;

local
  fun qtermToTerm VAR = Term.Var ""
    | qtermToTerm (FN ((f,_),l)) = Term.Fn (f, map qtermToTerm l);
in
  val ppQterm = Parser.ppMap qtermToTerm Term.pp;
end;

(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};

datatype 'a net =
    RESULT of 'a list
  | SINGLE of qterm * 'a net
  | MULTIPLE of 'a net option * 'a net NameArityMap.map;

datatype 'a termNet = NET of parameters * int * (int * (int * 'a) net) option;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun new parm = NET (parm,0,NONE);

local
  fun computeSize (RESULT l) = length l
    | computeSize (SINGLE (_,n)) = computeSize n
    | computeSize (MULTIPLE (vs,fs)) =
      NameArityMap.foldl
        (fn (_,n,acc) => acc + computeSize n)
        (case vs of SOME n => computeSize n | NONE => 0)
        fs;
in
  fun netSize NONE = NONE
    | netSize (SOME n) = SOME (computeSize n, n);
end;

fun size (NET (_,_,NONE)) = 0
  | size (NET (_, _, SOME (i,_))) = i;

fun null net = size net = 0;

fun singles qtms a = foldr SINGLE a qtms;

local
  fun pre NONE = (0,NONE)
    | pre (SOME (i,n)) = (i, SOME n);

  fun add (RESULT l) [] (RESULT l') = RESULT (l @ l')
    | add a (input1 as qtm :: qtms) (SINGLE (qtm',n)) =
      if qtm = qtm' then SINGLE (qtm, add a qtms n)
      else add a input1 (add n [qtm'] (MULTIPLE (NONE, NameArityMap.new ())))
    | add a (VAR :: qtms) (MULTIPLE (vs,fs)) =
      MULTIPLE (SOME (oadd a qtms vs), fs)
    | add a (FN (f,l) :: qtms) (MULTIPLE (vs,fs)) =
      let
        val n = NameArityMap.peek fs f
      in
        MULTIPLE (vs, NameArityMap.insert fs (f, oadd a (l @ qtms) n))
      end
    | add _ _ _ = raise Bug "TermNet.insert: Match"

  and oadd a qtms NONE = singles qtms a
    | oadd a qtms (SOME n) = add a qtms n;

  fun ins a qtm (i,n) = SOME (i + 1, oadd (RESULT [a]) [qtm] n);
in
  fun insert (NET (p,k,n)) (tm,a) =
      NET (p, k + 1, ins (k,a) (termToQterm tm) (pre n))
      handle Error _ => raise Bug "TermNet.insert: should never fail";
end;

fun fromList parm l = foldl (fn (tm_a,n) => insert n tm_a) (new parm) l;

fun filter pred =
    let
      fun filt (RESULT l) =
          (case List.filter (fn (_,a) => pred a) l of
             [] => NONE
           | l => SOME (RESULT l))
        | filt (SINGLE (qtm,n)) =
          (case filt n of
             NONE => NONE
           | SOME n => SOME (SINGLE (qtm,n)))
        | filt (MULTIPLE (vs,fs)) =
          let
            val vs = Option.mapPartial filt vs

            val fs = NameArityMap.mapPartial (fn (_,n) => filt n) fs
          in
            if not (Option.isSome vs) andalso NameArityMap.null fs then NONE
            else SOME (MULTIPLE (vs,fs))
          end
    in
      fn net as NET (_,_,NONE) => net
       | NET (p, k, SOME (_,n)) => NET (p, k, netSize (filt n))
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
        addQterm (FN (f,a)) (ks,fs,qtms)
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
    | fold inc acc ((n, stack, SINGLE (qtm,net)) :: rest) =
      fold inc acc ((n - 1, stackAddQterm qtm stack, net) :: rest)
    | fold inc acc ((n, stack, MULTIPLE (v,fns)) :: rest) =
      let
        val n = n - 1

        val rest =
            case v of
              NONE => rest
            | SOME net => (n, stackAddQterm VAR stack, net) :: rest

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
        | fold (pat :: pats, SINGLE (qtm,net)) =
          if pat = qtm then fold (pats,net) else acc
        | fold (VAR :: pats, MULTIPLE (v,_)) =
          (case v of NONE => acc | SOME net => fold (pats,net))
        | fold (FN (f,a) :: pats, MULTIPLE (_,fns)) =
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
    | fold inc acc ((VAR :: pats, stack, net) :: rest) =
      let
        fun harvest (qtm,n,l) = (pats, stackAddQterm qtm stack, n) :: l
      in
        fold inc acc (foldTerms harvest rest net)
      end
    | fold inc acc ((pat :: pats, stack, SINGLE (qtm,net)) :: rest) =
      (case unifyQtermQterm pat qtm of
         NONE => fold inc acc rest
       | SOME qtm =>
         fold inc acc ((pats, stackAddQterm qtm stack, net) :: rest))
    | fold
        inc acc
        (((pat as FN (f,a)) :: pats, stack, MULTIPLE (v,fns)) :: rest) =
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
    | mat acc ((RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((SINGLE (qtm,n), tm :: tms) :: rest) =
      mat acc (if matchQtermTerm qtm tm then (n,tms) :: rest else rest)
    | mat acc ((MULTIPLE (vs,fs), tm :: tms) :: rest) =
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
  fun match (NET (_,_,NONE)) _ = []
    | match (NET (p, _, SOME (_,n))) tm =
      finally p (mat [] [(n,[tm])])
      handle Error _ => raise Bug "TermNet.match: should never fail";
end;

local
  fun unseenInc qsub v tms (qtm,net,rest) =
      (NameMap.insert qsub (v,qtm), net, tms) :: rest;

  fun seenInc qsub tms (_,net,rest) = (qsub,net,tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((qsub, SINGLE (qtm,net), tm :: tms) :: rest) =
      (case matchTermQterm qsub tm qtm of
         NONE => mat acc rest
       | SOME qsub => mat acc ((qsub,net,tms) :: rest))
    | mat acc ((qsub, net as MULTIPLE _, Term.Var v :: tms) :: rest) =
      (case NameMap.peek qsub v of
         NONE => mat acc (foldTerms (unseenInc qsub v tms) rest net)
       | SOME qtm => mat acc (foldEqualTerms qtm (seenInc qsub tms) rest net))
    | mat acc ((qsub, MULTIPLE (_,fns), Term.Fn (f,a) :: tms) :: rest) =
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
  fun matched (NET (_,_,NONE)) _ = []
    | matched (NET (parm, _, SOME (_,net))) tm =
      finally parm (mat [] [(NameMap.new (), net, [tm])])
      handle Error _ => raise Bug "TermNet.matched: should never fail";
end;

local
  fun inc qsub v tms (qtm,net,rest) =
      (NameMap.insert qsub (v,qtm), net, tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((qsub, SINGLE (qtm,net), tm :: tms) :: rest) =
      (case unifyQtermTerm qsub qtm tm of
         NONE => mat acc rest
       | SOME qsub => mat acc ((qsub,net,tms) :: rest))
    | mat acc ((qsub, net as MULTIPLE _, Term.Var v :: tms) :: rest) =
      (case NameMap.peek qsub v of
         NONE => mat acc (foldTerms (inc qsub v tms) rest net)
       | SOME qtm => mat acc (foldUnifiableTerms qtm (inc qsub v tms) rest net))
    | mat acc ((qsub, MULTIPLE (v,fns), Term.Fn (f,a) :: tms) :: rest) =
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
  fun unify (NET (_,_,NONE)) _ = []
    | unify (NET (parm, _, SOME (_,net))) tm =
      finally parm (mat [] [(NameMap.new (), net, [tm])])
      handle Error _ => raise Bug "TermNet.unify: should never fail";
end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun inc (qtm, RESULT l, acc) =
      foldl (fn ((n,a),acc) => (n,(qtm,a)) :: acc) acc l
    | inc _ = raise Bug "TermNet.pp.inc";
      
  fun toList (NET (_,_,NONE)) = []
    | toList (NET (parm, _, SOME (_,net))) =
      finally parm (foldTerms inc [] net);
in
  fun pp ppA =
      Parser.ppMap toList (Parser.ppList (Parser.ppBinop " |->" ppQterm ppA));
end;

end
