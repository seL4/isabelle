(*  Title:      Pure/thm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The abstract types "theory" and "thm".
Also "cterm" / "ctyp" (certified terms / typs under a signature).

*)

signature THM =
sig
  structure Envir : ENVIR
  structure Sequence : SEQUENCE
  structure Sign : SIGN
  type cterm
  type ctyp
  type meta_simpset
  type theory
  type thm
  exception THM of string * int * thm list
  exception THEORY of string * theory list
  exception SIMPLIFIER of string * thm
  (*Certified terms/types; previously in sign.ML*)
  val cterm_of: Sign.sg -> term -> cterm
  val ctyp_of: Sign.sg -> typ -> ctyp
  val read_ctyp: Sign.sg -> string -> ctyp
  val read_cterm: Sign.sg -> string * typ -> cterm
  val rep_cterm: cterm -> {T: typ, t: term, sign: Sign.sg, maxidx: int}
  val rep_ctyp: ctyp -> {T: typ, sign: Sign.sg}
  val term_of: cterm -> term
  val typ_of: ctyp -> typ
  val cterm_fun: (term -> term) -> (cterm -> cterm)
  (*End of cterm/ctyp functions*)
  val abstract_rule: string -> cterm -> thm -> thm
  val add_congs: meta_simpset * thm list -> meta_simpset
  val add_prems: meta_simpset * thm list -> meta_simpset
  val add_simps: meta_simpset * thm list -> meta_simpset
  val assume: cterm -> thm
  val assumption: int -> thm -> thm Sequence.seq
  val axioms_of: theory -> (string * thm) list
  val beta_conversion: cterm -> thm
  val bicompose: bool -> bool * thm * int -> int -> thm -> thm Sequence.seq
  val biresolution: bool -> (bool*thm)list -> int -> thm -> thm Sequence.seq
  val combination: thm -> thm -> thm
  val concl_of: thm -> term
  val cprop_of: thm -> cterm
  val del_simps: meta_simpset * thm list -> meta_simpset
  val dest_cimplies: cterm -> cterm*cterm
  val dest_state: thm * int -> (term*term)list * term list * term * term
  val empty_mss: meta_simpset
  val eq_assumption: int -> thm -> thm
  val equal_intr: thm -> thm -> thm
  val equal_elim: thm -> thm -> thm
  val extend_theory: theory -> string
        -> (class * class list) list * sort
           * (string list * int)list
           * (string * string list * string) list
           * (string list * (sort list * class))list
           * (string list * string)list * Sign.Syntax.sext option
        -> (string*string)list -> theory
  val extensional: thm -> thm
  val flexflex_rule: thm -> thm Sequence.seq
  val flexpair_def: thm
  val forall_elim: cterm -> thm -> thm
  val forall_intr: cterm -> thm -> thm
  val freezeT: thm -> thm
  val get_axiom: theory -> string -> thm
  val implies_elim: thm -> thm -> thm
  val implies_intr: cterm -> thm -> thm
  val implies_intr_hyps: thm -> thm
  val instantiate: (indexname*ctyp)list * (cterm*cterm)list
                   -> thm -> thm
  val lift_rule: (thm * int) -> thm -> thm
  val merge_theories: theory * theory -> theory
  val mk_rews_of_mss: meta_simpset -> thm -> thm list
  val mss_of: thm list -> meta_simpset
  val nprems_of: thm -> int
  val parents_of: theory -> theory list
  val prems_of: thm -> term list
  val prems_of_mss: meta_simpset -> thm list
  val pure_thy: theory
  val read_def_cterm :
         Sign.sg * (indexname -> typ option) * (indexname -> sort option) ->
         string * typ -> cterm * (indexname * typ) list
   val reflexive: cterm -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val rep_thm: thm -> {prop: term, hyps: term list, maxidx: int, sign: Sign.sg}
  val rewrite_cterm:
         bool*bool -> meta_simpset -> (meta_simpset -> thm -> thm option)
           -> cterm -> thm
  val set_mk_rews: meta_simpset * (thm -> thm list) -> meta_simpset
  val sign_of: theory -> Sign.sg
  val syn_of: theory -> Sign.Syntax.syntax
  val stamps_of_thm: thm -> string ref list
  val stamps_of_thy: theory -> string ref list
  val symmetric: thm -> thm
  val tpairs_of: thm -> (term*term)list
  val trace_simp: bool ref
  val transitive: thm -> thm -> thm
  val trivial: cterm -> thm
  val varifyT: thm -> thm
end;

functor ThmFun (structure Logic: LOGIC and Unify: UNIFY and Pattern: PATTERN
  and Net:NET sharing type Pattern.type_sig = Unify.Sign.Type.type_sig)(*: THM *) (* FIXME debug *) =
struct

structure Sequence = Unify.Sequence;
structure Envir = Unify.Envir;
structure Sign = Unify.Sign;
structure Type = Sign.Type;
structure Syntax = Sign.Syntax;
structure Symtab = Sign.Symtab;


(** certified types **)

(*certified typs under a signature*)

datatype ctyp = Ctyp of {sign: Sign.sg, T: typ};

fun rep_ctyp (Ctyp args) = args;
fun typ_of (Ctyp {T, ...}) = T;

fun ctyp_of sign T =
  Ctyp {sign = sign, T = Sign.certify_typ sign T};

fun read_ctyp sign s =
  Ctyp {sign = sign, T = Sign.read_typ (sign, K None) s};



(** certified terms **)

(*certified terms under a signature, with checked typ and maxidx of Vars*)

datatype cterm = Cterm of {sign: Sign.sg, t: term, T: typ, maxidx: int};

fun rep_cterm (Cterm args) = args;
fun term_of (Cterm {t, ...}) = t;

(*create a cterm by checking a "raw" term with respect to a signature*)
fun cterm_of sign tm =
  let val (t, T, maxidx) = Sign.certify_term sign tm
  in Cterm {sign = sign, t = t, T = T, maxidx = maxidx}
  end handle TYPE (msg, _, _)
    => raise TERM ("Term not in signature\n" ^ msg, [tm]);

fun cterm_fun f (Cterm {sign, t, ...}) = cterm_of sign (f t);


(*dest_implies for cterms. Note T=prop below*)
fun dest_cimplies (Cterm{sign, T, maxidx, t=Const("==>", _) $ A $ B}) =
       (Cterm{sign=sign, T=T, maxidx=maxidx, t=A},
        Cterm{sign=sign, T=T, maxidx=maxidx, t=B})
  | dest_cimplies ct = raise TERM ("dest_cimplies", [term_of ct]);



(** read cterms **)

(*read term, infer types, certify term*)

fun read_def_cterm (sign, types, sorts) (a, T) =
  let
    val {tsig, const_tab, syn, ...} = Sign.rep_sg sign;
    val showtyp = Sign.string_of_typ sign;
    val showterm = Sign.string_of_term sign;

    fun termerr [] = ""
      | termerr [t] = "\nInvolving this term:\n" ^ showterm t
      | termerr ts = "\nInvolving these terms:\n" ^ cat_lines (map showterm ts);

    val T' = Sign.certify_typ sign T
      handle TYPE (msg, _, _) => error msg;
    val t = Syntax.read syn T' a;
    val (t', tye) = Type.infer_types (tsig, const_tab, types, sorts, T', t)
      handle TYPE (msg, Ts, ts) => error ("Type checking error: " ^ msg ^ "\n"
        ^ cat_lines (map showtyp Ts) ^ termerr ts);
    val ct = cterm_of sign t' handle TERM (msg, _) => error msg;
  in (ct, tye) end;

fun read_cterm sign = #1 o (read_def_cterm (sign, K None, K None));



(**** META-THEOREMS ****)

datatype thm = Thm of
  {sign: Sign.sg, maxidx: int, hyps: term list, prop: term};

fun rep_thm (Thm args) = args;

(*Errors involving theorems*)
exception THM of string * int * thm list;

(*maps object-rule to tpairs *)
fun tpairs_of (Thm{prop,...}) = #1 (Logic.strip_flexpairs prop);

(*maps object-rule to premises *)
fun prems_of (Thm{prop,...}) =
    Logic.strip_imp_prems (Logic.skip_flexpairs prop);

(*counts premises in a rule*)
fun nprems_of (Thm{prop,...}) =
    Logic.count_prems (Logic.skip_flexpairs prop, 0);

(*maps object-rule to conclusion *)
fun concl_of (Thm{prop,...}) = Logic.strip_imp_concl prop;

(*The statement of any Thm is a Cterm*)
fun cprop_of (Thm{sign,maxidx,hyps,prop}) =
        Cterm{sign=sign, maxidx=maxidx, T=propT, t=prop};

(*Stamps associated with a signature*)
val stamps_of_thm = #stamps o Sign.rep_sg o #sign o rep_thm;

(*Theories.  There is one pure theory.
  A theory can be extended.  Two theories can be merged.*)
datatype theory =
    Pure of {sign: Sign.sg}
  | Extend of {sign: Sign.sg,  axioms: thm Symtab.table,  thy: theory}
  | Merge of {sign: Sign.sg,  thy1: theory,  thy2: theory};

(*Errors involving theories*)
exception THEORY of string * theory list;

fun sign_of (Pure {sign}) = sign
  | sign_of (Extend {sign,...}) = sign
  | sign_of (Merge {sign,...}) = sign;

val syn_of = #syn o Sign.rep_sg o sign_of;

(*return the axioms of a theory and its ancestors*)
fun axioms_of (Pure _) = []
  | axioms_of (Extend {axioms, thy, ...}) =
      axioms_of thy @ Symtab.alist_of axioms
  | axioms_of (Merge {thy1, thy2, ...}) = axioms_of thy1 @ axioms_of thy2;

(*return the immediate ancestors -- also distinguishes the kinds of theories*)
fun parents_of (Pure _) = []
  | parents_of (Extend{thy,...}) = [thy]
  | parents_of (Merge{thy1,thy2,...}) = [thy1,thy2];


(*Merge theories of two theorems.  Raise exception if incompatible.
  Prefers (via Sign.merge) the signature of th1.  *)
fun merge_theories(th1,th2) =
  let val Thm{sign=sign1,...} = th1 and Thm{sign=sign2,...} = th2
  in  Sign.merge (sign1,sign2)  end
  handle TERM _ => raise THM("incompatible signatures", 0, [th1,th2]);

(*Stamps associated with a theory*)
val stamps_of_thy = #stamps o Sign.rep_sg o sign_of;


(**** Primitive rules ****)

(* discharge all assumptions t from ts *)
val disch = gen_rem (op aconv);

(*The assumption rule A|-A in a theory  *)
fun assume ct : thm =
  let val {sign, t=prop, T, maxidx} = rep_cterm ct
  in  if T<>propT then
        raise THM("assume: assumptions must have type prop", 0, [])
      else if maxidx <> ~1 then
        raise THM("assume: assumptions may not contain scheme variables",
                  maxidx, [])
      else Thm{sign = sign, maxidx = ~1, hyps = [prop], prop = prop}
  end;

(* Implication introduction
              A |- B
              -------
              A ==> B    *)
fun implies_intr cA (thB as Thm{sign,maxidx,hyps,prop}) : thm =
  let val {sign=signA, t=A, T, maxidx=maxidxA} = rep_cterm cA
  in  if T<>propT then
        raise THM("implies_intr: assumptions must have type prop", 0, [thB])
      else Thm{sign= Sign.merge (sign,signA),  maxidx= max[maxidxA, maxidx],
             hyps= disch(hyps,A),  prop= implies$A$prop}
      handle TERM _ =>
        raise THM("implies_intr: incompatible signatures", 0, [thB])
  end;

(* Implication elimination
        A ==> B       A
        ---------------
                B      *)
fun implies_elim thAB thA : thm =
    let val Thm{maxidx=maxA, hyps=hypsA, prop=propA,...} = thA
        and Thm{sign, maxidx, hyps, prop,...} = thAB;
        fun err(a) = raise THM("implies_elim: "^a, 0, [thAB,thA])
    in  case prop of
            imp$A$B =>
                if imp=implies andalso  A aconv propA
                then  Thm{sign= merge_theories(thAB,thA),
                          maxidx= max[maxA,maxidx],
                          hyps= hypsA union hyps,  (*dups suppressed*)
                          prop= B}
                else err("major premise")
          | _ => err("major premise")
    end;

(* Forall introduction.  The Free or Var x must not be free in the hypotheses.
     A
   ------
   !!x.A       *)
fun forall_intr cx (th as Thm{sign,maxidx,hyps,prop}) =
  let val x = term_of cx;
      fun result(a,T) = Thm{sign= sign, maxidx= maxidx, hyps= hyps,
                            prop= all(T) $ Abs(a, T, abstract_over (x,prop))}
  in  case x of
        Free(a,T) =>
          if exists (apl(x, Logic.occs)) hyps
          then  raise THM("forall_intr: variable free in assumptions", 0, [th])
          else  result(a,T)
      | Var((a,_),T) => result(a,T)
      | _ => raise THM("forall_intr: not a variable", 0, [th])
  end;

(* Forall elimination
              !!x.A
             --------
              A[t/x]     *)
fun forall_elim ct (th as Thm{sign,maxidx,hyps,prop}) : thm =
  let val {sign=signt, t, T, maxidx=maxt} = rep_cterm ct
  in  case prop of
          Const("all",Type("fun",[Type("fun",[qary,_]),_])) $ A =>
            if T<>qary then
                raise THM("forall_elim: type mismatch", 0, [th])
            else Thm{sign= Sign.merge(sign,signt),
                     maxidx= max[maxidx, maxt],
                     hyps= hyps,  prop= betapply(A,t)}
        | _ => raise THM("forall_elim: not quantified", 0, [th])
  end
  handle TERM _ =>
         raise THM("forall_elim: incompatible signatures", 0, [th]);


(*** Equality ***)

(*Definition of the relation =?= *)
val flexpair_def =
  Thm{sign= Sign.pure, hyps= [], maxidx= 0,
      prop= term_of
              (read_cterm Sign.pure
                 ("(?t =?= ?u) == (?t == ?u::?'a::{})", propT))};

(*The reflexivity rule: maps  t   to the theorem   t==t   *)
fun reflexive ct =
  let val {sign, t, T, maxidx} = rep_cterm ct
  in  Thm{sign= sign, hyps= [], maxidx= maxidx, prop= Logic.mk_equals(t,t)}
  end;

(*The symmetry rule
    t==u
    ----
    u==t         *)
fun symmetric (th as Thm{sign,hyps,prop,maxidx}) =
  case prop of
      (eq as Const("==",_)) $ t $ u =>
          Thm{sign=sign, hyps=hyps, maxidx=maxidx, prop= eq$u$t}
    | _ => raise THM("symmetric", 0, [th]);

(*The transitive rule
    t1==u    u==t2
    ------------
        t1==t2      *)
fun transitive th1 th2 =
  let val Thm{maxidx=max1, hyps=hyps1, prop=prop1,...} = th1
      and Thm{maxidx=max2, hyps=hyps2, prop=prop2,...} = th2;
      fun err(msg) = raise THM("transitive: "^msg, 0, [th1,th2])
  in case (prop1,prop2) of
       ((eq as Const("==",_)) $ t1 $ u, Const("==",_) $ u' $ t2) =>
          if not (u aconv u') then err"middle term"  else
              Thm{sign= merge_theories(th1,th2), hyps= hyps1 union hyps2,
                  maxidx= max[max1,max2], prop= eq$t1$t2}
     | _ =>  err"premises"
  end;

(*Beta-conversion: maps (%(x)t)(u) to the theorem  (%(x)t)(u) == t[u/x]   *)
fun beta_conversion ct =
  let val {sign, t, T, maxidx} = rep_cterm ct
  in  case t of
          Abs(_,_,bodt) $ u =>
            Thm{sign= sign,  hyps= [],
                maxidx= maxidx_of_term t,
                prop= Logic.mk_equals(t, subst_bounds([u],bodt))}
        | _ =>  raise THM("beta_conversion: not a redex", 0, [])
  end;

(*The extensionality rule   (proviso: x not free in f, g, or hypotheses)
    f(x) == g(x)
    ------------
       f == g    *)
fun extensional (th as Thm{sign,maxidx,hyps,prop}) =
  case prop of
    (Const("==",_)) $ (f$x) $ (g$y) =>
      let fun err(msg) = raise THM("extensional: "^msg, 0, [th])
      in (if x<>y then err"different variables" else
          case y of
                Free _ =>
                  if exists (apl(y, Logic.occs)) (f::g::hyps)
                  then err"variable free in hyps or functions"    else  ()
              | Var _ =>
                  if Logic.occs(y,f)  orelse  Logic.occs(y,g)
                  then err"variable free in functions"   else  ()
              | _ => err"not a variable");
          Thm{sign=sign, hyps=hyps, maxidx=maxidx,
              prop= Logic.mk_equals(f,g)}
      end
 | _ =>  raise THM("extensional: premise", 0, [th]);

(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.
  The bound variable will be named "a" (since x will be something like x320)
          t == u
    ----------------
      %(x)t == %(x)u     *)
fun abstract_rule a cx (th as Thm{sign,maxidx,hyps,prop}) =
  let val x = term_of cx;
      val (t,u) = Logic.dest_equals prop
            handle TERM _ =>
                raise THM("abstract_rule: premise not an equality", 0, [th])
      fun result T =
            Thm{sign= sign, maxidx= maxidx, hyps= hyps,
                prop= Logic.mk_equals(Abs(a, T, abstract_over (x,t)),
                                      Abs(a, T, abstract_over (x,u)))}
  in  case x of
        Free(_,T) =>
         if exists (apl(x, Logic.occs)) hyps
         then raise THM("abstract_rule: variable free in assumptions", 0, [th])
         else result T
      | Var(_,T) => result T
      | _ => raise THM("abstract_rule: not a variable", 0, [th])
  end;

(*The combination rule
    f==g    t==u
    ------------
     f(t)==g(u)      *)
fun combination th1 th2 =
  let val Thm{maxidx=max1, hyps=hyps1, prop=prop1,...} = th1
      and Thm{maxidx=max2, hyps=hyps2, prop=prop2,...} = th2
  in  case (prop1,prop2)  of
       (Const("==",_) $ f $ g, Const("==",_) $ t $ u) =>
              Thm{sign= merge_theories(th1,th2), hyps= hyps1 union hyps2,
                  maxidx= max[max1,max2], prop= Logic.mk_equals(f$t, g$u)}
     | _ =>  raise THM("combination: premises", 0, [th1,th2])
  end;


(*The equal propositions rule
    A==B    A
    ---------
        B          *)
fun equal_elim th1 th2 =
  let val Thm{maxidx=max1, hyps=hyps1, prop=prop1,...} = th1
      and Thm{maxidx=max2, hyps=hyps2, prop=prop2,...} = th2;
      fun err(msg) = raise THM("equal_elim: "^msg, 0, [th1,th2])
  in  case prop1  of
       Const("==",_) $ A $ B =>
          if not (prop2 aconv A) then err"not equal"  else
              Thm{sign= merge_theories(th1,th2), hyps= hyps1 union hyps2,
                  maxidx= max[max1,max2], prop= B}
     | _ =>  err"major premise"
  end;


(* Equality introduction
    A==>B    B==>A
    -------------
         A==B            *)
fun equal_intr th1 th2 =
let val Thm{maxidx=max1, hyps=hyps1, prop=prop1,...} = th1
    and Thm{maxidx=max2, hyps=hyps2, prop=prop2,...} = th2;
    fun err(msg) = raise THM("equal_intr: "^msg, 0, [th1,th2])
in case (prop1,prop2) of
     (Const("==>",_) $ A $ B, Const("==>",_) $ B' $ A')  =>
        if A aconv A' andalso B aconv B'
        then Thm{sign= merge_theories(th1,th2), hyps= hyps1 union hyps2,
                 maxidx= max[max1,max2], prop= Logic.mk_equals(A,B)}
        else err"not equal"
   | _ =>  err"premises"
end;

(**** Derived rules ****)

(*Discharge all hypotheses (need not verify cterms)
  Repeated hypotheses are discharged only once;  fold cannot do this*)
fun implies_intr_hyps (Thm{sign, maxidx, hyps=A::As, prop}) =
      implies_intr_hyps
            (Thm{sign=sign,  maxidx=maxidx,
                 hyps= disch(As,A),  prop= implies$A$prop})
  | implies_intr_hyps th = th;

(*Smash" unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.
  Resulting sequence may contain multiple elements if the tpairs are
    not all flex-flex. *)
fun flexflex_rule (Thm{sign,maxidx,hyps,prop}) =
  let fun newthm env =
          let val (tpairs,horn) =
                        Logic.strip_flexpairs (Envir.norm_term env prop)
                (*Remove trivial tpairs, of the form t=t*)
              val distpairs = filter (not o op aconv) tpairs
              val newprop = Logic.list_flexpairs(distpairs, horn)
          in  Thm{sign= sign, hyps= hyps,
                  maxidx= maxidx_of_term newprop, prop= newprop}
          end;
      val (tpairs,_) = Logic.strip_flexpairs prop
  in Sequence.maps newthm
            (Unify.smash_unifiers(sign, Envir.empty maxidx, tpairs))
  end;

(*Instantiation of Vars
                      A
             --------------------
              A[t1/v1,....,tn/vn]     *)

(*Check that all the terms are Vars and are distinct*)
fun instl_ok ts = forall is_Var ts andalso null(findrep ts);

(*For instantiate: process pair of cterms, merge theories*)
fun add_ctpair ((ct,cu), (sign,tpairs)) =
  let val {sign=signt, t=t, T= T, ...} = rep_cterm ct
      and {sign=signu, t=u, T= U, ...} = rep_cterm cu
  in  if T=U  then (Sign.merge(sign, Sign.merge(signt, signu)), (t,u)::tpairs)
      else raise TYPE("add_ctpair", [T,U], [t,u])
  end;

fun add_ctyp ((v,ctyp), (sign',vTs)) =
  let val {T,sign} = rep_ctyp ctyp
  in (Sign.merge(sign,sign'), (v,T)::vTs) end;

(*Left-to-right replacements: ctpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms of same type.
  Normalizes the new theorem! *)
fun instantiate (vcTs,ctpairs)  (th as Thm{sign,maxidx,hyps,prop}) =
  let val (newsign,tpairs) = foldr add_ctpair (ctpairs, (sign,[]));
      val (newsign,vTs) = foldr add_ctyp (vcTs, (newsign,[]));
      val newprop =
            Envir.norm_term (Envir.empty 0)
              (subst_atomic tpairs
               (Type.inst_term_tvars(#tsig(Sign.rep_sg newsign),vTs) prop))
      val newth = Thm{sign= newsign, hyps= hyps,
                      maxidx= maxidx_of_term newprop, prop= newprop}
  in  if not(instl_ok(map #1 tpairs))
      then raise THM("instantiate: variables not distinct", 0, [th])
      else if not(null(findrep(map #1 vTs)))
      then raise THM("instantiate: type variables not distinct", 0, [th])
      else (*Check types of Vars for agreement*)
      case findrep (map (#1 o dest_Var) (term_vars newprop)) of
          ix::_ => raise THM("instantiate: conflicting types for variable " ^
                             Syntax.string_of_vname ix ^ "\n", 0, [newth])
        | [] =>
             case findrep (map #1 (term_tvars newprop)) of
             ix::_ => raise THM
                    ("instantiate: conflicting sorts for type variable " ^
                     Syntax.string_of_vname ix ^ "\n", 0, [newth])
        | [] => newth
  end
  handle TERM _ =>
           raise THM("instantiate: incompatible signatures",0,[th])
       | TYPE _ => raise THM("instantiate: type conflict", 0, [th]);

(*The trivial implication A==>A, justified by assume and forall rules.
  A can contain Vars, not so for assume!   *)
fun trivial ct : thm =
  let val {sign, t=A, T, maxidx} = rep_cterm ct
  in  if T<>propT then
            raise THM("trivial: the term must have type prop", 0, [])
      else Thm{sign= sign, maxidx= maxidx, hyps= [], prop= implies$A$A}
  end;

(* Replace all TFrees not in the hyps by new TVars *)
fun varifyT(Thm{sign,maxidx,hyps,prop}) =
  let val tfrees = foldr add_term_tfree_names (hyps,[])
  in Thm{sign=sign, maxidx=max[0,maxidx], hyps=hyps,
         prop= Type.varify(prop,tfrees)}
  end;

(* Replace all TVars by new TFrees *)
fun freezeT(Thm{sign,maxidx,hyps,prop}) =
  let val prop' = Type.freeze (K true) prop
  in Thm{sign=sign, maxidx=maxidx_of_term prop', hyps=hyps, prop=prop'} end;


(*** Inference rules for tactics ***)

(*Destruct proof state into constraints, other goals, goal(i), rest *)
fun dest_state (state as Thm{prop,...}, i) =
  let val (tpairs,horn) = Logic.strip_flexpairs prop
  in  case  Logic.strip_prems(i, [], horn) of
          (B::rBs, C) => (tpairs, rev rBs, B, C)
        | _ => raise THM("dest_state", i, [state])
  end
  handle TERM _ => raise THM("dest_state", i, [state]);

(*Increment variables and parameters of rule as required for
  resolution with goal i of state. *)
fun lift_rule (state, i) orule =
  let val Thm{prop=sprop,maxidx=smax,...} = state;
      val (Bi::_, _) = Logic.strip_prems(i, [], Logic.skip_flexpairs sprop)
        handle TERM _ => raise THM("lift_rule", i, [orule,state]);
      val (lift_abs,lift_all) = Logic.lift_fns(Bi,smax+1);
      val (Thm{sign,maxidx,hyps,prop}) = orule
      val (tpairs,As,B) = Logic.strip_horn prop
  in  Thm{hyps=hyps, sign= merge_theories(state,orule),
          maxidx= maxidx+smax+1,
          prop= Logic.rule_of(map (pairself lift_abs) tpairs,
                              map lift_all As,    lift_all B)}
  end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption. *)
fun assumption i state =
  let val Thm{sign,maxidx,hyps,prop} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      fun newth (env as Envir.Envir{maxidx, ...}, tpairs) =
          Thm{sign=sign, hyps=hyps, maxidx=maxidx, prop=
            if Envir.is_empty env then (*avoid wasted normalizations*)
              Logic.rule_of (tpairs, Bs, C)
            else (*normalize the new rule fully*)
              Envir.norm_term env (Logic.rule_of (tpairs, Bs, C))};
      fun addprfs [] = Sequence.null
        | addprfs ((t,u)::apairs) = Sequence.seqof (fn()=> Sequence.pull
             (Sequence.mapp newth
                (Unify.unifiers(sign,Envir.empty maxidx, (t,u)::tpairs))
                (addprfs apairs)))
  in  addprfs (Logic.assum_pairs Bi)  end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha-convertible to one of its assumptions*)
fun eq_assumption i state =
  let val Thm{sign,maxidx,hyps,prop} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
  in  if exists (op aconv) (Logic.assum_pairs Bi)
      then Thm{sign=sign, hyps=hyps, maxidx=maxidx,
               prop=Logic.rule_of(tpairs, Bs, C)}
      else  raise THM("eq_assumption", 0, [state])
  end;


(** User renaming of parameters in a subgoal **)

(*Calls error rather than raising an exception because it is intended
  for top-level use -- exception handling would not make sense here.
  The names in cs, if distinct, are used for the innermost parameters;
   preceding parameters may be renamed to make all params distinct.*)
fun rename_params_rule (cs, i) state =
  let val Thm{sign,maxidx,hyps,prop} = state
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      val iparams = map #1 (Logic.strip_params Bi)
      val short = length iparams - length cs
      val newnames =
            if short<0 then error"More names than abstractions!"
            else variantlist(take (short,iparams), cs) @ cs
      val freenames = map (#1 o dest_Free) (term_frees prop)
      val newBi = Logic.list_rename_params (newnames, Bi)
  in
  case findrep cs of
     c::_ => error ("Bound variables not distinct: " ^ c)
   | [] => (case cs inter freenames of
       a::_ => error ("Bound/Free variable clash: " ^ a)
     | [] => Thm{sign=sign, hyps=hyps, maxidx=maxidx, prop=
                    Logic.rule_of(tpairs, Bs@[newBi], C)})
  end;

(*** Preservation of bound variable names ***)

(*Scan a pair of terms; while they are similar,
  accumulate corresponding bound vars in "al"*)
fun match_bvs(Abs(x,_,s),Abs(y,_,t), al) = match_bvs(s,t,(x,y)::al)
  | match_bvs(f$s, g$t, al) = match_bvs(f,g,match_bvs(s,t,al))
  | match_bvs(_,_,al) = al;

(* strip abstractions created by parameters *)
fun match_bvars((s,t),al) = match_bvs(strip_abs_body s, strip_abs_body t, al);


(* strip_apply f A(,B) strips off all assumptions/parameters from A
   introduced by lifting over B, and applies f to remaining part of A*)
fun strip_apply f =
  let fun strip(Const("==>",_)$ A1 $ B1,
                Const("==>",_)$ _  $ B2) = implies $ A1 $ strip(B1,B2)
        | strip((c as Const("all",_)) $ Abs(a,T,t1),
                      Const("all",_)  $ Abs(_,_,t2)) = c$Abs(a,T,strip(t1,t2))
        | strip(A,_) = f A
  in strip end;

(*Use the alist to rename all bound variables and some unknowns in a term
  dpairs = current disagreement pairs;  tpairs = permanent ones (flexflex);
  Preserves unknowns in tpairs and on lhs of dpairs. *)
fun rename_bvs([],_,_,_) = I
  | rename_bvs(al,dpairs,tpairs,B) =
    let val vars = foldr add_term_vars
                        (map fst dpairs @ map fst tpairs @ map snd tpairs, [])
        (*unknowns appearing elsewhere be preserved!*)
        val vids = map (#1 o #1 o dest_Var) vars;
        fun rename(t as Var((x,i),T)) =
                (case assoc(al,x) of
                   Some(y) => if x mem vids orelse y mem vids then t
                              else Var((y,i),T)
                 | None=> t)
          | rename(Abs(x,T,t)) =
              Abs(case assoc(al,x) of Some(y) => y | None => x,
                  T, rename t)
          | rename(f$t) = rename f $ rename t
          | rename(t) = t;
        fun strip_ren Ai = strip_apply rename (Ai,B)
    in strip_ren end;

(*Function to rename bounds/unknowns in the argument, lifted over B*)
fun rename_bvars(dpairs, tpairs, B) =
        rename_bvs(foldr match_bvars (dpairs,[]), dpairs, tpairs, B);


(*** RESOLUTION ***)

(*strip off pairs of assumptions/parameters in parallel -- they are
  identical because of lifting*)
fun strip_assums2 (Const("==>", _) $ _ $ B1,
                   Const("==>", _) $ _ $ B2) = strip_assums2 (B1,B2)
  | strip_assums2 (Const("all",_)$Abs(a,T,t1),
                   Const("all",_)$Abs(_,_,t2)) =
      let val (B1,B2) = strip_assums2 (t1,t2)
      in  (Abs(a,T,B1), Abs(a,T,B2))  end
  | strip_assums2 BB = BB;


(*Composition of object rule r=(A1...Am/B) with proof state s=(B1...Bn/C)
  Unifies B with Bi, replacing subgoal i    (1 <= i <= n)
  If match then forbid instantiations in proof state
  If lifted then shorten the dpair using strip_assums2.
  If eres_flg then simultaneously proves A1 by assumption.
  nsubgoal is the number of new subgoals (written m above).
  Curried so that resolution calls dest_state only once.
*)
local open Sequence; exception Bicompose
in
fun bicompose_aux match (state, (stpairs, Bs, Bi, C), lifted)
                        (eres_flg, orule, nsubgoal) =
 let val Thm{maxidx=smax, hyps=shyps, ...} = state
     and Thm{maxidx=rmax, hyps=rhyps, prop=rprop,...} = orule;
     val sign = merge_theories(state,orule);
     (** Add new theorem with prop = '[| Bs; As |] ==> C' to thq **)
     fun addth As ((env as Envir.Envir {maxidx, ...}, tpairs), thq) =
       let val normt = Envir.norm_term env;
           (*perform minimal copying here by examining env*)
           val normp =
             if Envir.is_empty env then (tpairs, Bs @ As, C)
             else
             let val ntps = map (pairself normt) tpairs
             in if the (Envir.minidx env) > smax then (*no assignments in state*)
                  (ntps, Bs @ map normt As, C)
                else if match then raise Bicompose
                else (*normalize the new rule fully*)
                  (ntps, map normt (Bs @ As), normt C)
             end
           val th = Thm{sign=sign, hyps=rhyps union shyps, maxidx=maxidx,
                        prop= Logic.rule_of normp}
        in  cons(th, thq)  end  handle Bicompose => thq
     val (rtpairs,rhorn) = Logic.strip_flexpairs(rprop);
     val (rAs,B) = Logic.strip_prems(nsubgoal, [], rhorn)
       handle TERM _ => raise THM("bicompose: rule", 0, [orule,state]);
     (*Modify assumptions, deleting n-th if n>0 for e-resolution*)
     fun newAs(As0, n, dpairs, tpairs) =
       let val As1 = if !Logic.auto_rename orelse not lifted then As0
                     else map (rename_bvars(dpairs,tpairs,B)) As0
       in (map (Logic.flatten_params n) As1)
          handle TERM _ =>
          raise THM("bicompose: 1st premise", 0, [orule])
       end;
     val env = Envir.empty(max[rmax,smax]);
     val BBi = if lifted then strip_assums2(B,Bi) else (B,Bi);
     val dpairs = BBi :: (rtpairs@stpairs);
     (*elim-resolution: try each assumption in turn.  Initially n=1*)
     fun tryasms (_, _, []) = null
       | tryasms (As, n, (t,u)::apairs) =
          (case pull(Unify.unifiers(sign, env, (t,u)::dpairs))  of
               None                   => tryasms (As, n+1, apairs)
             | cell as Some((_,tpairs),_) =>
                   its_right (addth (newAs(As, n, [BBi,(u,t)], tpairs)))
                       (seqof (fn()=> cell),
                        seqof (fn()=> pull (tryasms (As, n+1, apairs)))));
     fun eres [] = raise THM("bicompose: no premises", 0, [orule,state])
       | eres (A1::As) = tryasms (As, 1, Logic.assum_pairs A1);
     (*ordinary resolution*)
     fun res(None) = null
       | res(cell as Some((_,tpairs),_)) =
             its_right (addth(newAs(rev rAs, 0, [BBi], tpairs)))
                       (seqof (fn()=> cell), null)
 in  if eres_flg then eres(rev rAs)
     else res(pull(Unify.unifiers(sign, env, dpairs)))
 end;
end;  (*open Sequence*)


fun bicompose match arg i state =
    bicompose_aux match (state, dest_state(state,i), false) arg;

(*Quick test whether rule is resolvable with the subgoal with hyps Hs
  and conclusion B.  If eres_flg then checks 1st premise of rule also*)
fun could_bires (Hs, B, eres_flg, rule) =
    let fun could_reshyp (A1::_) = exists (apl(A1,could_unify)) Hs
          | could_reshyp [] = false;  (*no premise -- illegal*)
    in  could_unify(concl_of rule, B) andalso
        (not eres_flg  orelse  could_reshyp (prems_of rule))
    end;

(*Bi-resolution of a state with a list of (flag,rule) pairs.
  Puts the rule above:  rule/state.  Renames vars in the rules. *)
fun biresolution match brules i state =
    let val lift = lift_rule(state, i);
        val (stpairs, Bs, Bi, C) = dest_state(state,i)
        val B = Logic.strip_assums_concl Bi;
        val Hs = Logic.strip_assums_hyp Bi;
        val comp = bicompose_aux match (state, (stpairs, Bs, Bi, C), true);
        fun res [] = Sequence.null
          | res ((eres_flg, rule)::brules) =
              if could_bires (Hs, B, eres_flg, rule)
              then Sequence.seqof (*delay processing remainder til needed*)
                  (fn()=> Some(comp (eres_flg, lift rule, nprems_of rule),
                               res brules))
              else res brules
    in  Sequence.flats (res brules)  end;


(**** THEORIES ****)

val pure_thy = Pure{sign = Sign.pure};

(*Look up the named axiom in the theory*)
fun get_axiom thy axname =
    let fun get (Pure _) = raise Match
          | get (Extend{axioms,thy,...}) =
             (case Symtab.lookup(axioms,axname) of
                  Some th => th
                | None => get thy)
         | get (Merge{thy1,thy2,...}) =
                get thy1  handle Match => get thy2
    in  get thy
        handle Match => raise THEORY("get_axiom: No axiom "^axname, [thy])
    end;

(*Converts Frees to Vars: axioms can be written without question marks*)
fun prepare_axiom sign sP =
    Logic.varify (term_of (read_cterm sign (sP,propT)));

(*Read an axiom for a new theory*)
fun read_ax sign (a, sP) : string*thm =
  let val prop = prepare_axiom sign sP
  in  (a, Thm{sign=sign, hyps=[], maxidx= maxidx_of_term prop, prop= prop})
  end
  handle ERROR =>
        error("extend_theory: The error above occurred in axiom " ^ a);

fun mk_axioms sign axpairs =
        Symtab.st_of_alist(map (read_ax sign) axpairs, Symtab.null)
        handle Symtab.DUPLICATE(a) => error("Two axioms named " ^ a);

(*Extension of a theory with given classes, types, constants and syntax.
  Reads the axioms from strings: axpairs have the form (axname, axiom). *)
fun extend_theory thy thyname ext axpairs =
  let val sign = Sign.extend (sign_of thy) thyname ext;
      val axioms= mk_axioms sign axpairs
  in  Extend{sign=sign, axioms= axioms, thy = thy}  end;

(*The union of two theories*)
fun merge_theories (thy1, thy2) =
  Merge {sign = Sign.merge (sign_of thy1, sign_of thy2),
         thy1 = thy1, thy2 = thy2} handle TERM (msg, _) => error msg;


(*** Meta simp sets ***)

type rrule = {thm:thm, lhs:term, perm:bool};
type cong = {thm:thm, lhs:term};
datatype meta_simpset =
  Mss of {net:rrule Net.net, congs:(string * cong)list, primes:string,
          prems: thm list, mk_rews: thm -> thm list};

(*A "mss" contains data needed during conversion:
  net: discrimination net of rewrite rules
  congs: association list of congruence rules
  primes: offset for generating unique new names
          for rewriting under lambda abstractions
  mk_rews: used when local assumptions are added
*)

val empty_mss = Mss{net= Net.empty, congs= [], primes="", prems= [],
                    mk_rews = K[]};

exception SIMPLIFIER of string * thm;

fun prtm a sign t = (writeln a; writeln(Sign.string_of_term sign t));

val trace_simp = ref false;

fun trace_term a sign t = if !trace_simp then prtm a sign t else ();

fun trace_thm a (Thm{sign,prop,...}) = trace_term a sign prop;

fun var_perm(Var _, Var _) = true
  | var_perm(Abs(_,_,s), Abs(_,_,t)) = var_perm(s,t)
  | var_perm(t1$t2, u1$u2) = var_perm(t1,u1) andalso var_perm(t2,u2)
  | var_perm(t,u) = (t=u);


(*simple test for looping rewrite*)
fun loops sign prems (lhs,rhs) =
  null(prems) andalso
  Pattern.eta_matches (#tsig(Sign.rep_sg sign)) (lhs,rhs);

fun mk_rrule (thm as Thm{hyps,sign,prop,maxidx,...}) =
  let val prems = Logic.strip_imp_prems prop
      val concl = Pattern.eta_contract (Logic.strip_imp_concl prop)
      val (lhs,rhs) = Logic.dest_equals concl handle TERM _ =>
                      raise SIMPLIFIER("Rewrite rule not a meta-equality",thm)
      val perm = var_perm(lhs,rhs) andalso not(lhs=rhs)
  in if not perm andalso loops sign prems (lhs,rhs)
     then (prtm "Warning: ignoring looping rewrite rule" sign prop; None)
     else Some{thm=thm,lhs=lhs,perm=perm}
  end;

local
 fun eq({thm=Thm{prop=p1,...},...}:rrule,
        {thm=Thm{prop=p2,...},...}:rrule) = p1 aconv p2
in

fun add_simp(mss as Mss{net,congs,primes,prems,mk_rews},
             thm as Thm{sign,prop,...}) =
  case mk_rrule thm of
    None => mss
  | Some(rrule as {lhs,...}) =>
      (trace_thm "Adding rewrite rule:" thm;
       Mss{net= (Net.insert_term((lhs,rrule),net,eq)
                 handle Net.INSERT =>
                  (prtm "Warning: ignoring duplicate rewrite rule" sign prop;
                   net)),
           congs=congs, primes=primes, prems=prems,mk_rews=mk_rews});

fun del_simp(mss as Mss{net,congs,primes,prems,mk_rews},
             thm as Thm{sign,prop,...}) =
  case mk_rrule thm of
    None => mss
  | Some(rrule as {lhs,...}) =>
      Mss{net= (Net.delete_term((lhs,rrule),net,eq)
                handle Net.INSERT =>
                 (prtm "Warning: rewrite rule not in simpset" sign prop;
                  net)),
             congs=congs, primes=primes, prems=prems,mk_rews=mk_rews}

end;

val add_simps = foldl add_simp;
val del_simps = foldl del_simp;

fun mss_of thms = add_simps(empty_mss,thms);

fun add_cong(Mss{net,congs,primes,prems,mk_rews},thm) =
  let val (lhs,_) = Logic.dest_equals(concl_of thm) handle TERM _ =>
                    raise SIMPLIFIER("Congruence not a meta-equality",thm)
      val lhs = Pattern.eta_contract lhs
      val (a,_) = dest_Const (head_of lhs) handle TERM _ =>
                  raise SIMPLIFIER("Congruence must start with a constant",thm)
  in Mss{net=net, congs=(a,{lhs=lhs,thm=thm})::congs, primes=primes,
         prems=prems, mk_rews=mk_rews}
  end;

val (op add_congs) = foldl add_cong;

fun add_prems(Mss{net,congs,primes,prems,mk_rews},thms) =
  Mss{net=net, congs=congs, primes=primes, prems=thms@prems, mk_rews=mk_rews};

fun prems_of_mss(Mss{prems,...}) = prems;

fun set_mk_rews(Mss{net,congs,primes,prems,...},mk_rews) =
  Mss{net=net, congs=congs, primes=primes, prems=prems, mk_rews=mk_rews};
fun mk_rews_of_mss(Mss{mk_rews,...}) = mk_rews;


(*** Meta-level rewriting
     uses conversions, omitting proofs for efficiency.  See
        L C Paulson, A higher-order implementation of rewriting,
        Science of Computer Programming 3 (1983), pages 119-149. ***)

type prover = meta_simpset -> thm -> thm option;
type termrec = (Sign.sg * term list) * term;
type conv = meta_simpset -> termrec -> termrec;

datatype order = LESS | EQUAL | GREATER;

fun stringord(a,b:string) = if a<b then LESS  else
                            if a=b then EQUAL else GREATER;

fun intord(i,j:int) = if i<j then LESS  else
                      if i=j then EQUAL else GREATER;

(* FIXME: "***ABSTRACTION***" is a hack and makes the ordering non-linear *)
fun string_of_hd(Const(a,_)) = a
  | string_of_hd(Free(a,_))  = a
  | string_of_hd(Var(v,_))   = Syntax.string_of_vname v
  | string_of_hd(Bound i)    = string_of_int i
  | string_of_hd(Abs _)      = "***ABSTRACTION***";

(* a strict (not reflexive) linear well-founded AC-compatible ordering
 * for terms:
 * s < t <=> 1. size(s) < size(t) or
             2. size(s) = size(t) and s=f(...) and t = g(...) and f<g or
             3. size(s) = size(t) and s=f(s1..sn) and t=f(t1..tn) and
                (s1..sn) < (t1..tn) (lexicographically)
 *)

(* FIXME: should really take types into account as well.
 * Otherwise not linear *)
fun termord(t,u) =
      (case intord(size_of_term t,size_of_term u) of
         EQUAL => let val (f,ts) = strip_comb t and (g,us) = strip_comb u
                  in case stringord(string_of_hd f, string_of_hd g) of
                       EQUAL => lextermord(ts,us)
                     | ord   => ord
                  end
       | ord => ord)
and lextermord(t::ts,u::us) =
      (case termord(t,u) of
         EQUAL => lextermord(ts,us)
       | ord   => ord)
  | lextermord([],[]) = EQUAL
  | lextermord _ = error("lextermord");

fun termless tu = (termord tu = LESS);

fun check_conv(thm as Thm{hyps,prop,...}, prop0) =
  let fun err() = (trace_thm "Proved wrong thm (Check subgoaler?)" thm; None)
      val (lhs0,_) = Logic.dest_equals(Logic.strip_imp_concl prop0)
  in case prop of
       Const("==",_) $ lhs $ rhs =>
         if (lhs = lhs0) orelse
            (lhs aconv (Envir.norm_term (Envir.empty 0) lhs0))
         then (trace_thm "SUCCEEDED" thm; Some(hyps,rhs))
         else err()
     | _ => err()
  end;

(*Conversion to apply the meta simpset to a term*)
fun rewritec (prover,signt) (mss as Mss{net,...}) (hypst,t) =
  let val t = Pattern.eta_contract t;
      fun rew {thm as Thm{sign,hyps,maxidx,prop,...}, lhs, perm} =
        let val unit = if Sign.subsig(sign,signt) then ()
                  else (writeln"Warning: rewrite rule from different theory";
                        raise Pattern.MATCH)
            val insts = Pattern.match (#tsig(Sign.rep_sg signt)) (lhs,t)
            val prop' = subst_vars insts prop;
            val hyps' = hyps union hypst;
            val thm' = Thm{sign=signt, hyps=hyps', prop=prop', maxidx=maxidx}
        in if nprems_of thm' = 0
           then let val (_,rhs) = Logic.dest_equals prop'
                in if perm andalso not(termless(rhs,t)) then None
                   else (trace_thm "Rewriting:" thm'; Some(hyps',rhs)) end
           else (trace_thm "Trying to rewrite:" thm';
                 case prover mss thm' of
                   None       => (trace_thm "FAILED" thm'; None)
                 | Some(thm2) => check_conv(thm2,prop'))
        end

      fun rews [] = None
        | rews (rrule::rrules) =
            let val opt = rew rrule handle Pattern.MATCH => None
            in case opt of None => rews rrules | some => some end;

  in case t of
       Abs(_,_,body) $ u => Some(hypst,subst_bounds([u], body))
     | _                 => rews(Net.match_term net t)
  end;

(*Conversion to apply a congruence rule to a term*)
fun congc (prover,signt) {thm=cong,lhs=lhs} (hypst,t) =
  let val Thm{sign,hyps,maxidx,prop,...} = cong
      val unit = if Sign.subsig(sign,signt) then ()
                 else error("Congruence rule from different theory")
      val tsig = #tsig(Sign.rep_sg signt)
      val insts = Pattern.match tsig (lhs,t) handle Pattern.MATCH =>
                  error("Congruence rule did not match")
      val prop' = subst_vars insts prop;
      val thm' = Thm{sign=signt, hyps=hyps union hypst,
                     prop=prop', maxidx=maxidx}
      val unit = trace_thm "Applying congruence rule" thm';
      fun err() = error("Failed congruence proof!")

  in case prover thm' of
       None => err()
     | Some(thm2) => (case check_conv(thm2,prop') of
                        None => err() | Some(x) => x)
  end;


fun bottomc ((simprem,useprem),prover,sign) =
  let fun botc mss trec = let val trec1 = subc mss trec
                          in case rewritec (prover,sign) mss trec1 of
                               None => trec1
                             | Some(trec2) => botc mss trec2
                          end

      and subc (mss as Mss{net,congs,primes,prems,mk_rews})
               (trec as (hyps,t)) =
        (case t of
            Abs(a,T,t) =>
              let val v = Free(".subc." ^ primes,T)
                  val mss' = Mss{net=net, congs=congs, primes=primes^"'",
                                 prems=prems,mk_rews=mk_rews}
                  val (hyps',t') = botc mss' (hyps,subst_bounds([v],t))
              in  (hyps', Abs(a, T, abstract_over(v,t')))  end
          | t$u => (case t of
              Const("==>",_)$s  => impc(hyps,s,u,mss)
            | Abs(_,_,body)     => subc mss (hyps,subst_bounds([u], body))
            | _                 =>
                let fun appc() = let val (hyps1,t1) = botc mss (hyps,t)
                                     val (hyps2,u1) = botc mss (hyps1,u)
                                 in (hyps2,t1$u1) end
                    val (h,ts) = strip_comb t
                in case h of
                     Const(a,_) =>
                       (case assoc(congs,a) of
                          None => appc()
                        | Some(cong) => congc (prover mss,sign) cong trec)
                   | _ => appc()
                end)
          | _ => trec)

      and impc(hyps,s,u,mss as Mss{mk_rews,...}) =
        let val (hyps1,s') = if simprem then botc mss (hyps,s) else (hyps,s)
            val mss' =
              if not useprem orelse maxidx_of_term s' <> ~1 then mss
              else let val thm = Thm{sign=sign,hyps=[s'],prop=s',maxidx= ~1}
                   in add_simps(add_prems(mss,[thm]), mk_rews thm) end
            val (hyps2,u') = botc mss' (hyps1,u)
            val hyps2' = if s' mem hyps1 then hyps2 else hyps2\s'
        in (hyps2', Logic.mk_implies(s',u')) end

  in botc end;


(*** Meta-rewriting: rewrites t to u and returns the theorem t==u ***)
(* Parameters:
   mode = (simplify A, use A in simplifying B) when simplifying A ==> B
   mss: contains equality theorems of the form [|p1,...|] ==> t==u
   prover: how to solve premises in conditional rewrites and congruences
*)

(*** FIXME: check that #primes(mss) does not "occur" in ct alread ***)
fun rewrite_cterm mode mss prover ct =
  let val {sign, t, T, maxidx} = rep_cterm ct;
      val (hyps,u) = bottomc (mode,prover,sign) mss ([],t);
      val prop = Logic.mk_equals(t,u)
  in  Thm{sign= sign, hyps= hyps, maxidx= maxidx_of_term prop, prop= prop}
  end

end;

