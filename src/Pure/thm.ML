(*  Title:      Pure/thm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The core of Isabelle's Meta Logic: certified types and terms, meta
theorems, meta rules (including resolution and simplification).
*)

signature BASIC_THM =
  sig
  (*certified types*)
  type ctyp
  val rep_ctyp          : ctyp -> {sign: Sign.sg, T: typ}
  val typ_of            : ctyp -> typ
  val ctyp_of           : Sign.sg -> typ -> ctyp
  val read_ctyp         : Sign.sg -> string -> ctyp

  (*certified terms*)
  type cterm
  exception CTERM of string
  val rep_cterm         : cterm -> {sign: Sign.sg, t: term, T: typ, maxidx: int}
  val crep_cterm        : cterm -> {sign: Sign.sg, t: term, T: ctyp, maxidx: int}
  val term_of           : cterm -> term
  val cterm_of          : Sign.sg -> term -> cterm
  val ctyp_of_term      : cterm -> ctyp
  val read_cterm        : Sign.sg -> string * typ -> cterm
  val cterm_fun         : (term -> term) -> (cterm -> cterm)
  val dest_comb         : cterm -> cterm * cterm
  val dest_abs          : cterm -> cterm * cterm
  val adjust_maxidx     : cterm -> cterm
  val capply            : cterm -> cterm -> cterm
  val cabs              : cterm -> cterm -> cterm
  val read_def_cterm    :
    Sign.sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> string * typ -> cterm * (indexname * typ) list
  val read_def_cterms   :
    Sign.sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ)list
    -> cterm list * (indexname * typ)list

  (*proof terms [must DUPLICATE declaration as a specification]*)
  datatype deriv_kind = MinDeriv | ThmDeriv | FullDeriv;
  type tag		(* = string * string list *)
  val keep_derivs       : deriv_kind ref
  datatype rule = 
      MinProof                          
    | Oracle		  of string * Sign.sg * Object.T
    | Axiom               of string * tag list
    | Theorem             of string * tag list
    | Assume              of cterm
    | Implies_intr        of cterm
    | Implies_intr_hyps
    | Implies_elim 
    | Forall_intr         of cterm
    | Forall_elim         of cterm
    | Reflexive           of cterm
    | Symmetric 
    | Transitive
    | Beta_conversion     of cterm
    | Extensional
    | Abstract_rule       of string * cterm
    | Combination
    | Equal_intr
    | Equal_elim
    | Trivial             of cterm
    | Lift_rule           of cterm * int 
    | Assumption          of int * Envir.env option
    | Rotate_rule         of int * int
    | Permute_prems       of int * int
    | Instantiate         of (indexname * ctyp) list * (cterm * cterm) list
    | Bicompose           of bool * bool * int * int * Envir.env
    | Flexflex_rule       of Envir.env            
    | Class_triv          of class       
    | VarifyT		  of string list
    | FreezeT
    | RewriteC            of cterm
    | CongC               of cterm
    | Rewrite_cterm       of cterm
    | Rename_params_rule  of string list * int;
  type deriv	(* = rule mtree *)

  (*meta theorems*)
  type thm
  val rep_thm           : thm -> {sign: Sign.sg, der: deriv, maxidx: int,
                                  shyps: sort list, hyps: term list, 
                                  prop: term}
  val crep_thm          : thm -> {sign: Sign.sg, der: deriv, maxidx: int,
                                  shyps: sort list, hyps: cterm list, 
                                  prop: cterm}
  exception THM of string * int * thm list
  type 'a attribute 	(* = 'a * thm -> 'a * thm *)
  val eq_thm		: thm * thm -> bool
  val sign_of_thm       : thm -> Sign.sg
  val transfer_sg	: Sign.sg -> thm -> thm
  val transfer		: theory -> thm -> thm
  val tpairs_of         : thm -> (term * term) list
  val prems_of          : thm -> term list
  val nprems_of         : thm -> int
  val concl_of          : thm -> term
  val cprop_of          : thm -> cterm
  val extra_shyps       : thm -> sort list
  val strip_shyps       : thm -> thm
  val get_axiom         : theory -> xstring -> thm
  val def_name		: string -> string
  val get_def           : theory -> xstring -> thm
  val axioms_of         : theory -> (string * thm) list

  (*meta rules*)
  val assume            : cterm -> thm
  val compress          : thm -> thm
  val implies_intr      : cterm -> thm -> thm
  val implies_elim      : thm -> thm -> thm
  val forall_intr       : cterm -> thm -> thm
  val forall_elim       : cterm -> thm -> thm
  val reflexive         : cterm -> thm
  val symmetric         : thm -> thm
  val transitive        : thm -> thm -> thm
  val beta_conversion   : cterm -> thm
  val extensional       : thm -> thm
  val abstract_rule     : string -> cterm -> thm -> thm
  val combination       : thm -> thm -> thm
  val equal_intr        : thm -> thm -> thm
  val equal_elim        : thm -> thm -> thm
  val implies_intr_hyps : thm -> thm
  val flexflex_rule     : thm -> thm Seq.seq
  val instantiate       :
    (indexname * ctyp) list * (cterm * cterm) list -> thm -> thm
  val trivial           : cterm -> thm
  val class_triv        : Sign.sg -> class -> thm
  val varifyT           : thm -> thm
  val varifyT'          : string list -> thm -> thm
  val freezeT           : thm -> thm
  val dest_state        : thm * int ->
    (term * term) list * term list * term * term
  val lift_rule         : (thm * int) -> thm -> thm
  val assumption        : int -> thm -> thm Seq.seq
  val eq_assumption     : int -> thm -> thm
  val rotate_rule       : int -> int -> thm -> thm
  val permute_prems     : int -> int -> thm -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val bicompose         : bool -> bool * thm * int ->
    int -> thm -> thm Seq.seq
  val biresolution      : bool -> (bool * thm) list ->
    int -> thm -> thm Seq.seq

  (*meta simplification*)
  exception SIMPLIFIER of string * thm
  type meta_simpset
  val dest_mss		: meta_simpset ->
    {simps: thm list, congs: thm list, procs: (string * cterm list) list}
  val empty_mss         : meta_simpset
  val clear_mss		: meta_simpset -> meta_simpset
  val merge_mss		: meta_simpset * meta_simpset -> meta_simpset
  val add_simps         : meta_simpset * thm list -> meta_simpset
  val del_simps         : meta_simpset * thm list -> meta_simpset
  val mss_of            : thm list -> meta_simpset
  val add_congs         : meta_simpset * thm list -> meta_simpset
  val del_congs         : meta_simpset * thm list -> meta_simpset
  val add_simprocs	: meta_simpset *
    (string * cterm list * (Sign.sg -> thm list -> term -> thm option) * stamp) list
      -> meta_simpset
  val del_simprocs	: meta_simpset *
    (string * cterm list * (Sign.sg -> thm list -> term -> thm option) * stamp) list
      -> meta_simpset
  val add_prems         : meta_simpset * thm list -> meta_simpset
  val prems_of_mss      : meta_simpset -> thm list
  val set_mk_rews       : meta_simpset * (thm -> thm list) -> meta_simpset
  val set_mk_sym        : meta_simpset * (thm -> thm option) -> meta_simpset
  val set_mk_eq_True    : meta_simpset * (thm -> thm option) -> meta_simpset
  val set_termless      : meta_simpset * (term * term -> bool) -> meta_simpset
  val trace_simp        : bool ref
  val debug_simp        : bool ref
  val rewrite_cterm     : bool * bool * bool -> meta_simpset ->
                          (meta_simpset -> thm -> thm option) -> cterm -> thm

  val invoke_oracle     : theory -> xstring -> Sign.sg * Object.T -> thm
end;

signature THM =
sig
  include BASIC_THM
  val major_prem_of	: thm -> term
  val no_prems		: thm -> bool
  val no_attributes	: 'a -> 'a * 'b attribute list
  val apply_attributes	: ('a * thm) * 'a attribute list -> ('a * thm)
  val applys_attributes	: ('a * thm list) * 'a attribute list -> ('a * thm list)
  val get_name_tags	: thm -> string * tag list
  val put_name_tags	: string * tag list -> thm -> thm
  val name_of_thm	: thm -> string
  val tags_of_thm	: thm -> tag list
  val name_thm		: string * thm -> thm
end;

structure Thm: THM =
struct

(*** Certified terms and types ***)

(** certified types **)

(*certified typs under a signature*)

datatype ctyp = Ctyp of {sign_ref: Sign.sg_ref, T: typ};

fun rep_ctyp (Ctyp {sign_ref, T}) = {sign = Sign.deref sign_ref, T = T};
fun typ_of (Ctyp {T, ...}) = T;

fun ctyp_of sign T =
  Ctyp {sign_ref = Sign.self_ref sign, T = Sign.certify_typ sign T};

fun read_ctyp sign s =
  Ctyp {sign_ref = Sign.self_ref sign, T = Sign.read_typ (sign, K None) s};



(** certified terms **)

(*certified terms under a signature, with checked typ and maxidx of Vars*)

datatype cterm = Cterm of {sign_ref: Sign.sg_ref, t: term, T: typ, maxidx: int};

fun rep_cterm (Cterm {sign_ref, t, T, maxidx}) =
  {sign = Sign.deref sign_ref, t = t, T = T, maxidx = maxidx};

fun crep_cterm (Cterm {sign_ref, t, T, maxidx}) =
  {sign = Sign.deref sign_ref, t = t, T = Ctyp {sign_ref = sign_ref, T = T},
    maxidx = maxidx};

fun term_of (Cterm {t, ...}) = t;

fun ctyp_of_term (Cterm {sign_ref, T, ...}) = Ctyp {sign_ref = sign_ref, T = T};

(*create a cterm by checking a "raw" term with respect to a signature*)
fun cterm_of sign tm =
  let val (t, T, maxidx) = Sign.certify_term sign tm
  in  Cterm {sign_ref = Sign.self_ref sign, t = t, T = T, maxidx = maxidx}
  end;

fun cterm_fun f (Cterm {sign_ref, t, ...}) = cterm_of (Sign.deref sign_ref) (f t);


exception CTERM of string;

(*Destruct application in cterms*)
fun dest_comb (Cterm {sign_ref, T, maxidx, t = A $ B}) =
      let val typeA = fastype_of A;
          val typeB =
            case typeA of Type("fun",[S,T]) => S
                        | _ => error "Function type expected in dest_comb";
      in
      (Cterm {sign_ref=sign_ref, maxidx=maxidx, t=A, T=typeA},
       Cterm {sign_ref=sign_ref, maxidx=maxidx, t=B, T=typeB})
      end
  | dest_comb _ = raise CTERM "dest_comb";

(*Destruct abstraction in cterms*)
fun dest_abs (Cterm {sign_ref, T as Type("fun",[_,S]), maxidx, t=Abs(x,ty,M)}) = 
      let val (y,N) = variant_abs (x,ty,M)
      in (Cterm {sign_ref = sign_ref, T = ty, maxidx = 0, t = Free(y,ty)},
          Cterm {sign_ref = sign_ref, T = S, maxidx = maxidx, t = N})
      end
  | dest_abs _ = raise CTERM "dest_abs";

(*Makes maxidx precise: it is often too big*)
fun adjust_maxidx (ct as Cterm {sign_ref, T, t, maxidx, ...}) =
  if maxidx = ~1 then ct 
  else  Cterm {sign_ref = sign_ref, T = T, maxidx = maxidx_of_term t, t = t};

(*Form cterm out of a function and an argument*)
fun capply (Cterm {t=f, sign_ref=sign_ref1, T=Type("fun",[dty,rty]), maxidx=maxidx1})
           (Cterm {t=x, sign_ref=sign_ref2, T, maxidx=maxidx2}) =
      if T = dty then
        Cterm{t=Sign.nodup_vars (f$x), sign_ref=Sign.merge_refs(sign_ref1,sign_ref2), T=rty,
          maxidx=Int.max(maxidx1, maxidx2)}
      else raise CTERM "capply: types don't agree"
  | capply _ _ = raise CTERM "capply: first arg is not a function"

fun cabs (Cterm {t=Free(a,ty), sign_ref=sign_ref1, T=T1, maxidx=maxidx1})
         (Cterm {t=t2, sign_ref=sign_ref2, T=T2, maxidx=maxidx2}) =
      Cterm {t=Sign.nodup_vars (absfree(a,ty,t2)), sign_ref=Sign.merge_refs(sign_ref1,sign_ref2),
             T = ty --> T2, maxidx=Int.max(maxidx1, maxidx2)}
  | cabs _ _ = raise CTERM "cabs: first arg is not a free variable";



(** read cterms **)   (*exception ERROR*)

(*read terms, infer types, certify terms*)
fun read_def_cterms (sign, types, sorts) used freeze sTs =
  let
    val syn = #syn (Sign.rep_sg sign)
    fun read(s,T) =
      let val T' = Sign.certify_typ sign T
                   handle TYPE (msg, _, _) => error msg
      in (Syntax.read syn T' s, T') end
    val tsTs = map read sTs
    val (ts',tye) = Sign.infer_types_simult sign types sorts used freeze tsTs;
    val cts = map (cterm_of sign) ts'
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in (cts, tye) end;

(*read term, infer types, certify term*)
fun read_def_cterm args used freeze aT =
  let val ([ct],tye) = read_def_cterms args used freeze [aT]
  in (ct,tye) end;

fun read_cterm sign = #1 o read_def_cterm (sign, K None, K None) [] true;



(*** Derivations ***)

(*tags provide additional comment, apart from the axiom/theorem name*)
type tag = string * string list;

(*Names of rules in derivations.  Includes logically trivial rules, if 
  executed in ML.*)
datatype rule = 
    MinProof                            (*for building minimal proof terms*)
  | Oracle              of string * Sign.sg * Object.T       (*oracles*)
(*Axioms/theorems*)
  | Axiom               of string * tag list
  | Theorem             of string * tag list
(*primitive inferences and compound versions of them*)
  | Assume              of cterm
  | Implies_intr        of cterm
  | Implies_intr_hyps
  | Implies_elim 
  | Forall_intr         of cterm
  | Forall_elim         of cterm
  | Reflexive           of cterm
  | Symmetric 
  | Transitive
  | Beta_conversion     of cterm
  | Extensional
  | Abstract_rule       of string * cterm
  | Combination
  | Equal_intr
  | Equal_elim
(*derived rules for tactical proof*)
  | Trivial             of cterm
        (*For lift_rule, the proof state is not a premise.
          Use cterm instead of thm to avoid mutual recursion.*)
  | Lift_rule           of cterm * int 
  | Assumption          of int * Envir.env option (*includes eq_assumption*)
  | Rotate_rule         of int * int
  | Permute_prems       of int * int
  | Instantiate         of (indexname * ctyp) list * (cterm * cterm) list
  | Bicompose           of bool * bool * int * int * Envir.env
  | Flexflex_rule       of Envir.env            (*identifies unifier chosen*)
(*other derived rules*)
  | Class_triv          of class
  | VarifyT		of string list
  | FreezeT
(*for the simplifier*)
  | RewriteC            of cterm
  | CongC               of cterm
  | Rewrite_cterm       of cterm
(*Logical identities, recorded since they are part of the proof process*)
  | Rename_params_rule  of string list * int;


type deriv = rule mtree;

datatype deriv_kind = MinDeriv | ThmDeriv | FullDeriv;

val keep_derivs = ref MinDeriv;


(*Build a minimal derivation.  Keep oracles; suppress atomic inferences;
  retain Theorems or their underlying links; keep anything else*)
fun squash_derivs [] = []
  | squash_derivs (der::ders) =
     (case der of
          Join (Oracle _, _) => der :: squash_derivs ders
        | Join (Theorem _, [der']) => if !keep_derivs=ThmDeriv 
                                      then der :: squash_derivs ders
                                      else squash_derivs (der'::ders)
        | Join (Axiom _, _) => if !keep_derivs=ThmDeriv 
                               then der :: squash_derivs ders
                               else squash_derivs ders
        | Join (_, [])      => squash_derivs ders
        | _                 => der :: squash_derivs ders);


(*Ensure sharing of the most likely derivation, the empty one!*)
val min_infer = Join (MinProof, []);

(*Make a minimal inference*)
fun make_min_infer []    = min_infer
  | make_min_infer [der] = der
  | make_min_infer ders  = Join (MinProof, ders);

fun infer_derivs (rl, [])   = Join (rl, [])
  | infer_derivs (rl, ders) =
    if !keep_derivs=FullDeriv then Join (rl, ders)
    else make_min_infer (squash_derivs ders);



(*** Meta theorems ***)

datatype thm = Thm of
 {sign_ref: Sign.sg_ref,       (*mutable reference to signature*)
  der: deriv,                  (*derivation*)
  maxidx: int,                 (*maximum index of any Var or TVar*)
  shyps: sort list,            (*sort hypotheses*)
  hyps: term list,             (*hypotheses*)
  prop: term};                 (*conclusion*)

fun rep_thm (Thm {sign_ref, der, maxidx, shyps, hyps, prop}) =
  {sign = Sign.deref sign_ref, der = der, maxidx = maxidx,
    shyps = shyps, hyps = hyps, prop = prop};

(*Version of rep_thm returning cterms instead of terms*)
fun crep_thm (Thm {sign_ref, der, maxidx, shyps, hyps, prop}) =
  let fun ctermf max t = Cterm{sign_ref=sign_ref, t=t, T=propT, maxidx=max};
  in {sign = Sign.deref sign_ref, der = der, maxidx = maxidx, shyps = shyps,
      hyps = map (ctermf ~1) hyps,
      prop = ctermf maxidx prop}
  end;

(*errors involving theorems*)
exception THM of string * int * thm list;

(*attributes subsume any kind of rules or addXXXs modifiers*)
type 'a attribute = 'a * thm -> 'a * thm;

fun no_attributes x = (x, []);
fun apply_attributes (x_th, atts) = Library.apply atts x_th;
fun applys_attributes (x_ths, atts) = foldl_map (Library.apply atts) x_ths;

(*equality of theorems uses equality of signatures and the
  a-convertible test for terms*)
fun eq_thm (th1, th2) =
  let
    val {sign = sg1, shyps = shyps1, hyps = hyps1, prop = prop1, ...} = rep_thm th1;
    val {sign = sg2, shyps = shyps2, hyps = hyps2, prop = prop2, ...} = rep_thm th2;
  in
    Sign.eq_sg (sg1, sg2) andalso
    eq_set_sort (shyps1, shyps2) andalso
    aconvs (hyps1, hyps2) andalso
    prop1 aconv prop2
  end;

fun sign_of_thm (Thm {sign_ref, ...}) = Sign.deref sign_ref;

(*merge signatures of two theorems; raise exception if incompatible*)
fun merge_thm_sgs
    (th1 as Thm {sign_ref = sgr1, ...}, th2 as Thm {sign_ref = sgr2, ...}) =
  Sign.merge_refs (sgr1, sgr2) handle TERM (msg, _) => raise THM (msg, 0, [th1, th2]);

(*transfer thm to super theory (non-destructive)*)
fun transfer_sg sign' thm =
  let
    val Thm {sign_ref, der, maxidx, shyps, hyps, prop} = thm;
    val sign = Sign.deref sign_ref;
  in
    if Sign.eq_sg (sign, sign') then thm
    else if Sign.subsig (sign, sign') then
      Thm {sign_ref = Sign.self_ref sign', der = der, maxidx = maxidx,
        shyps = shyps, hyps = hyps, prop = prop}
    else raise THM ("transfer: not a super theory", 0, [thm])
  end;

val transfer = transfer_sg o Theory.sign_of;

(*maps object-rule to tpairs*)
fun tpairs_of (Thm {prop, ...}) = #1 (Logic.strip_flexpairs prop);

(*maps object-rule to premises*)
fun prems_of (Thm {prop, ...}) =
  Logic.strip_imp_prems (Logic.skip_flexpairs prop);

(*counts premises in a rule*)
fun nprems_of (Thm {prop, ...}) =
  Logic.count_prems (Logic.skip_flexpairs prop, 0);

fun major_prem_of thm =
  (case prems_of thm of
    prem :: _ => prem
  | [] => raise THM ("major_prem_of: rule with no premises", 0, [thm]));

fun no_prems thm = nprems_of thm = 0;

(*maps object-rule to conclusion*)
fun concl_of (Thm {prop, ...}) = Logic.strip_imp_concl prop;

(*the statement of any thm is a cterm*)
fun cprop_of (Thm {sign_ref, maxidx, prop, ...}) =
  Cterm {sign_ref = sign_ref, maxidx = maxidx, T = propT, t = prop};



(** sort contexts of theorems **)

(* basic utils *)

(*accumulate sorts suppressing duplicates; these are coded low levelly
  to improve efficiency a bit*)

fun add_typ_sorts (Type (_, Ts), Ss) = add_typs_sorts (Ts, Ss)
  | add_typ_sorts (TFree (_, S), Ss) = ins_sort(S,Ss)
  | add_typ_sorts (TVar (_, S), Ss) = ins_sort(S,Ss)
and add_typs_sorts ([], Ss) = Ss
  | add_typs_sorts (T :: Ts, Ss) = add_typs_sorts (Ts, add_typ_sorts (T, Ss));

fun add_term_sorts (Const (_, T), Ss) = add_typ_sorts (T, Ss)
  | add_term_sorts (Free (_, T), Ss) = add_typ_sorts (T, Ss)
  | add_term_sorts (Var (_, T), Ss) = add_typ_sorts (T, Ss)
  | add_term_sorts (Bound _, Ss) = Ss
  | add_term_sorts (Abs (_,T,t), Ss) = add_term_sorts (t, add_typ_sorts (T,Ss))
  | add_term_sorts (t $ u, Ss) = add_term_sorts (t, add_term_sorts (u, Ss));

fun add_terms_sorts ([], Ss) = Ss
  | add_terms_sorts (t::ts, Ss) = add_terms_sorts (ts, add_term_sorts (t,Ss));

fun env_codT (Envir.Envir {iTs, ...}) = map snd (Vartab.dest iTs);

fun add_env_sorts (Envir.Envir {iTs, asol, ...}, Ss) =
  Vartab.foldl (add_term_sorts o swap o apsnd snd)
    (Vartab.foldl (add_typ_sorts o swap o apsnd snd) (Ss, iTs), asol);

fun add_thm_sorts (Thm {hyps, prop, ...}, Ss) =
  add_terms_sorts (hyps, add_term_sorts (prop, Ss));

fun add_thms_shyps ([], Ss) = Ss
  | add_thms_shyps (Thm {shyps, ...} :: ths, Ss) =
      add_thms_shyps (ths, union_sort (shyps, Ss));


(*get 'dangling' sort constraints of a thm*)
fun extra_shyps (th as Thm {shyps, ...}) =
  Term.rems_sort (shyps, add_thm_sorts (th, []));


(* fix_shyps *)

fun all_sorts_nonempty sign_ref = is_some (Sign.univ_witness (Sign.deref sign_ref));

(*preserve sort contexts of rule premises and substituted types*)
fun fix_shyps thms Ts (thm as Thm {sign_ref, der, maxidx, hyps, prop, ...}) =
  Thm
   {sign_ref = sign_ref,
    der = der,             (*no new derivation, as other rules call this*)
    maxidx = maxidx,
    shyps =
      if all_sorts_nonempty sign_ref then []
      else add_thm_sorts (thm, add_typs_sorts (Ts, add_thms_shyps (thms, []))),
    hyps = hyps, prop = prop}


(* strip_shyps *)

(*remove extra sorts that are non-empty by virtue of type signature information*)
fun strip_shyps (thm as Thm {shyps = [], ...}) = thm
  | strip_shyps (thm as Thm {sign_ref, der, maxidx, shyps, hyps, prop}) =
      let
        val sign = Sign.deref sign_ref;

        val present_sorts = add_thm_sorts (thm, []);
        val extra_shyps = Term.rems_sort (shyps, present_sorts);
        val witnessed_shyps = Sign.witness_sorts sign present_sorts extra_shyps;
      in
        Thm {sign_ref = sign_ref, der = der, maxidx = maxidx,
             shyps = Term.rems_sort (shyps, map #2 witnessed_shyps),
             hyps = hyps, prop = prop}
      end;



(** Axioms **)

(*look up the named axiom in the theory*)
fun get_axiom theory raw_name =
  let
    val name = Sign.intern (Theory.sign_of theory) Theory.axiomK raw_name;

    fun get_ax [] = None
      | get_ax (thy :: thys) =
          let val {sign, axioms, ...} = Theory.rep_theory thy in
            (case Symtab.lookup (axioms, name) of
              Some t =>
                Some (fix_shyps [] []
                  (Thm {sign_ref = Sign.self_ref sign,
                    der = infer_derivs (Axiom (name, []), []),
                    maxidx = maxidx_of_term t,
                    shyps = [], 
                    hyps = [], 
                    prop = t}))
            | None => get_ax thys)
          end;
  in
    (case get_ax (theory :: Theory.ancestors_of theory) of
      Some thm => thm
    | None => raise THEORY ("No axiom " ^ quote name, [theory]))
  end;

fun def_name name = name ^ "_def";
fun get_def thy = get_axiom thy o def_name;


(*return additional axioms of this theory node*)
fun axioms_of thy =
  map (fn (s, _) => (s, get_axiom thy s))
    (Symtab.dest (#axioms (Theory.rep_theory thy)));


(* name and tags -- make proof objects more readable *)

fun get_name_tags (Thm {der, ...}) =
  (case der of
    Join (Theorem x, _) => x
  | Join (Axiom x, _) => x
  | _ => ("", []));

fun put_name_tags x (Thm {sign_ref, der, maxidx, shyps, hyps, prop}) =
  let
    val der' =
      (case der of
        Join (Theorem _, ds) => Join (Theorem x, ds)
      | Join (Axiom _, ds) => Join (Axiom x, ds)
      | _ => Join (Theorem x, [der]));
  in
    Thm {sign_ref = sign_ref, der = der', maxidx = maxidx,
      shyps = shyps, hyps = hyps, prop = prop}
  end;

val name_of_thm = #1 o get_name_tags;
val tags_of_thm = #2 o get_name_tags;

fun name_thm (name, thm) = put_name_tags (name, tags_of_thm thm) thm;


(*Compression of theorems -- a separate rule, not integrated with the others,
  as it could be slow.*)
fun compress (Thm {sign_ref, der, maxidx, shyps, hyps, prop}) = 
    Thm {sign_ref = sign_ref, 
         der = der,     (*No derivation recorded!*)
         maxidx = maxidx,
         shyps = shyps, 
         hyps = map Term.compress_term hyps, 
         prop = Term.compress_term prop};



(*** Meta rules ***)

(*Check that term does not contain same var with different typing/sorting.
  If this check must be made, recalculate maxidx in hope of preventing its
  recurrence.*)
fun nodup_vars (thm as Thm{sign_ref, der, maxidx, shyps, hyps, prop}) s =
  Thm {sign_ref = sign_ref, 
         der = der,     
         maxidx = maxidx_of_term prop,
         shyps = shyps, 
         hyps = hyps, 
         prop = Sign.nodup_vars prop}
  handle TYPE(msg,Ts,ts) => raise TYPE(s^": "^msg,Ts,ts);


(** 'primitive' rules **)

(*discharge all assumptions t from ts*)
val disch = gen_rem (op aconv);

(*The assumption rule A|-A in a theory*)
fun assume raw_ct : thm =
  let val ct as Cterm {sign_ref, t=prop, T, maxidx} = adjust_maxidx raw_ct
  in  if T<>propT then
        raise THM("assume: assumptions must have type prop", 0, [])
      else if maxidx <> ~1 then
        raise THM("assume: assumptions may not contain scheme variables",
                  maxidx, [])
      else Thm{sign_ref   = sign_ref,
               der    = infer_derivs (Assume ct, []),
               maxidx = ~1, 
               shyps  = add_term_sorts(prop,[]), 
               hyps   = [prop], 
               prop   = prop}
  end;

(*Implication introduction
    [A]
     :
     B
  -------
  A ==> B
*)
fun implies_intr cA (thB as Thm{sign_ref,der,maxidx,hyps,prop,...}) : thm =
  let val Cterm {sign_ref=sign_refA, t=A, T, maxidx=maxidxA} = cA
  in  if T<>propT then
        raise THM("implies_intr: assumptions must have type prop", 0, [thB])
      else fix_shyps [thB] []
        (Thm{sign_ref = Sign.merge_refs (sign_ref,sign_refA),  
             der = infer_derivs (Implies_intr cA, [der]),
             maxidx = Int.max(maxidxA, maxidx),
             shyps = [],
             hyps = disch(hyps,A),
             prop = implies$A$prop})
      handle TERM _ =>
        raise THM("implies_intr: incompatible signatures", 0, [thB])
  end;


(*Implication elimination
  A ==> B    A
  ------------
        B
*)
fun implies_elim thAB thA : thm =
    let val Thm{maxidx=maxA, der=derA, hyps=hypsA, prop=propA,...} = thA
        and Thm{sign_ref, der, maxidx, hyps, prop,...} = thAB;
        fun err(a) = raise THM("implies_elim: "^a, 0, [thAB,thA])
    in  case prop of
            imp$A$B =>
                if imp=implies andalso  A aconv propA
                then fix_shyps [thAB, thA] []
                       (Thm{sign_ref= merge_thm_sgs(thAB,thA),
                            der = infer_derivs (Implies_elim, [der,derA]),
                            maxidx = Int.max(maxA,maxidx),
                            shyps = [],
                            hyps = union_term(hypsA,hyps),  (*dups suppressed*)
                            prop = B})
                else err("major premise")
          | _ => err("major premise")
    end;

(*Forall introduction.  The Free or Var x must not be free in the hypotheses.
    A
  -----
  !!x.A
*)
fun forall_intr cx (th as Thm{sign_ref,der,maxidx,hyps,prop,...}) =
  let val x = term_of cx;
      fun result(a,T) = fix_shyps [th] []
        (Thm{sign_ref = sign_ref, 
             der = infer_derivs (Forall_intr cx, [der]),
             maxidx = maxidx,
             shyps = [],
             hyps = hyps,
             prop = all(T) $ Abs(a, T, abstract_over (x,prop))})
  in  case x of
        Free(a,T) =>
          if exists (apl(x, Logic.occs)) hyps
          then  raise THM("forall_intr: variable free in assumptions", 0, [th])
          else  result(a,T)
      | Var((a,_),T) => result(a,T)
      | _ => raise THM("forall_intr: not a variable", 0, [th])
  end;

(*Forall elimination
  !!x.A
  ------
  A[t/x]
*)
fun forall_elim ct (th as Thm{sign_ref,der,maxidx,hyps,prop,...}) : thm =
  let val Cterm {sign_ref=sign_reft, t, T, maxidx=maxt} = ct
  in  case prop of
        Const("all",Type("fun",[Type("fun",[qary,_]),_])) $ A =>
          if T<>qary then
              raise THM("forall_elim: type mismatch", 0, [th])
          else let val thm = fix_shyps [th] []
                    (Thm{sign_ref= Sign.merge_refs(sign_ref,sign_reft),
                         der = infer_derivs (Forall_elim ct, [der]),
                         maxidx = Int.max(maxidx, maxt),
                         shyps = [],
                         hyps = hyps,  
                         prop = betapply(A,t)})
               in if maxt >= 0 andalso maxidx >= 0
                  then nodup_vars thm "forall_elim" 
                  else thm (*no new Vars: no expensive check!*)
               end
      | _ => raise THM("forall_elim: not quantified", 0, [th])
  end
  handle TERM _ =>
         raise THM("forall_elim: incompatible signatures", 0, [th]);


(* Equality *)

(*The reflexivity rule: maps  t   to the theorem   t==t   *)
fun reflexive ct =
  let val Cterm {sign_ref, t, T, maxidx} = ct
  in  fix_shyps [] []
       (Thm{sign_ref= sign_ref, 
            der = infer_derivs (Reflexive ct, []),
            shyps = [],
            hyps = [], 
            maxidx = maxidx,
            prop = Logic.mk_equals(t,t)})
  end;

(*The symmetry rule
  t==u
  ----
  u==t
*)
fun symmetric (th as Thm{sign_ref,der,maxidx,shyps,hyps,prop}) =
  case prop of
      (eq as Const("==",_)) $ t $ u =>
        (*no fix_shyps*)
          Thm{sign_ref = sign_ref,
              der = infer_derivs (Symmetric, [der]),
              maxidx = maxidx,
              shyps = shyps,
              hyps = hyps,
              prop = eq$u$t}
    | _ => raise THM("symmetric", 0, [th]);

(*The transitive rule
  t1==u    u==t2
  --------------
      t1==t2
*)
fun transitive th1 th2 =
  let val Thm{der=der1, maxidx=max1, hyps=hyps1, prop=prop1,...} = th1
      and Thm{der=der2, maxidx=max2, hyps=hyps2, prop=prop2,...} = th2;
      fun err(msg) = raise THM("transitive: "^msg, 0, [th1,th2])
  in case (prop1,prop2) of
       ((eq as Const("==",_)) $ t1 $ u, Const("==",_) $ u' $ t2) =>
          if not (u aconv u') then err"middle term"
          else let val thm =      
              fix_shyps [th1, th2] []
                (Thm{sign_ref= merge_thm_sgs(th1,th2), 
                     der = infer_derivs (Transitive, [der1, der2]),
                     maxidx = Int.max(max1,max2), 
                     shyps = [],
                     hyps = union_term(hyps1,hyps2),
                     prop = eq$t1$t2})
                 in if max1 >= 0 andalso max2 >= 0
                    then nodup_vars thm "transitive" 
                    else thm (*no new Vars: no expensive check!*)
                 end
     | _ =>  err"premises"
  end;

(*Beta-conversion: maps (%x.t)(u) to the theorem (%x.t)(u) == t[u/x] *)
fun beta_conversion ct =
  let val Cterm {sign_ref, t, T, maxidx} = ct
  in  case t of
          Abs(_,_,bodt) $ u => fix_shyps [] []
            (Thm{sign_ref = sign_ref,  
                 der = infer_derivs (Beta_conversion ct, []),
                 maxidx = maxidx,
                 shyps = [],
                 hyps = [],
                 prop = Logic.mk_equals(t, subst_bound (u,bodt))})
        | _ =>  raise THM("beta_conversion: not a redex", 0, [])
  end;

(*The extensionality rule   (proviso: x not free in f, g, or hypotheses)
  f(x) == g(x)
  ------------
     f == g
*)
fun extensional (th as Thm{sign_ref, der, maxidx,shyps,hyps,prop}) =
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
          (*no fix_shyps*)
          Thm{sign_ref = sign_ref,
              der = infer_derivs (Extensional, [der]),
              maxidx = maxidx,
              shyps = shyps,
              hyps = hyps, 
              prop = Logic.mk_equals(f,g)}
      end
 | _ =>  raise THM("extensional: premise", 0, [th]);

(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.
  The bound variable will be named "a" (since x will be something like x320)
     t == u
  ------------
  %x.t == %x.u
*)
fun abstract_rule a cx (th as Thm{sign_ref,der,maxidx,hyps,prop,...}) =
  let val x = term_of cx;
      val (t,u) = Logic.dest_equals prop
            handle TERM _ =>
                raise THM("abstract_rule: premise not an equality", 0, [th])
      fun result T = fix_shyps [th] []
          (Thm{sign_ref = sign_ref,
               der = infer_derivs (Abstract_rule (a,cx), [der]),
               maxidx = maxidx, 
               shyps = [], 
               hyps = hyps,
               prop = Logic.mk_equals(Abs(a, T, abstract_over (x,t)),
                                      Abs(a, T, abstract_over (x,u)))})
  in  case x of
        Free(_,T) =>
         if exists (apl(x, Logic.occs)) hyps
         then raise THM("abstract_rule: variable free in assumptions", 0, [th])
         else result T
      | Var(_,T) => result T
      | _ => raise THM("abstract_rule: not a variable", 0, [th])
  end;

(*The combination rule
  f == g  t == u
  --------------
   f(t) == g(u)
*)
fun combination th1 th2 =
  let val Thm{der=der1, maxidx=max1, shyps=shyps1, hyps=hyps1, 
              prop=prop1,...} = th1
      and Thm{der=der2, maxidx=max2, shyps=shyps2, hyps=hyps2, 
              prop=prop2,...} = th2
      fun chktypes (f,t) =
            (case fastype_of f of
                Type("fun",[T1,T2]) => 
                    if T1 <> fastype_of t then
                         raise THM("combination: types", 0, [th1,th2])
                    else ()
                | _ => raise THM("combination: not function type", 0, 
                                 [th1,th2]))
  in case (prop1,prop2)  of
       (Const("==",_) $ f $ g, Const("==",_) $ t $ u) =>
          let val _   = chktypes (f,t)
              val thm = (*no fix_shyps*)
                        Thm{sign_ref = merge_thm_sgs(th1,th2), 
                            der = infer_derivs (Combination, [der1, der2]),
                            maxidx = Int.max(max1,max2), 
                            shyps = union_sort(shyps1,shyps2),
                            hyps = union_term(hyps1,hyps2),
                            prop = Logic.mk_equals(f$t, g$u)}
          in if max1 >= 0 andalso max2 >= 0
             then nodup_vars thm "combination" 
             else thm (*no new Vars: no expensive check!*)  
          end
     | _ =>  raise THM("combination: premises", 0, [th1,th2])
  end;


(* Equality introduction
  A ==> B  B ==> A
  ----------------
       A == B
*)
fun equal_intr th1 th2 =
  let val Thm{der=der1,maxidx=max1, shyps=shyps1, hyps=hyps1, 
              prop=prop1,...} = th1
      and Thm{der=der2, maxidx=max2, shyps=shyps2, hyps=hyps2, 
              prop=prop2,...} = th2;
      fun err(msg) = raise THM("equal_intr: "^msg, 0, [th1,th2])
  in case (prop1,prop2) of
       (Const("==>",_) $ A $ B, Const("==>",_) $ B' $ A')  =>
          if A aconv A' andalso B aconv B'
          then
            (*no fix_shyps*)
              Thm{sign_ref = merge_thm_sgs(th1,th2),
                  der = infer_derivs (Equal_intr, [der1, der2]),
                  maxidx = Int.max(max1,max2),
                  shyps = union_sort(shyps1,shyps2),
                  hyps = union_term(hyps1,hyps2),
                  prop = Logic.mk_equals(A,B)}
          else err"not equal"
     | _ =>  err"premises"
  end;


(*The equal propositions rule
  A == B  A
  ---------
      B
*)
fun equal_elim th1 th2 =
  let val Thm{der=der1, maxidx=max1, hyps=hyps1, prop=prop1,...} = th1
      and Thm{der=der2, maxidx=max2, hyps=hyps2, prop=prop2,...} = th2;
      fun err(msg) = raise THM("equal_elim: "^msg, 0, [th1,th2])
  in  case prop1  of
       Const("==",_) $ A $ B =>
          if not (prop2 aconv A) then err"not equal"  else
            fix_shyps [th1, th2] []
              (Thm{sign_ref= merge_thm_sgs(th1,th2), 
                   der = infer_derivs (Equal_elim, [der1, der2]),
                   maxidx = Int.max(max1,max2),
                   shyps = [],
                   hyps = union_term(hyps1,hyps2),
                   prop = B})
     | _ =>  err"major premise"
  end;



(**** Derived rules ****)

(*Discharge all hypotheses.  Need not verify cterms or call fix_shyps.
  Repeated hypotheses are discharged only once;  fold cannot do this*)
fun implies_intr_hyps (Thm{sign_ref, der, maxidx, shyps, hyps=A::As, prop}) =
      implies_intr_hyps (*no fix_shyps*)
            (Thm{sign_ref = sign_ref, 
                 der = infer_derivs (Implies_intr_hyps, [der]), 
                 maxidx = maxidx, 
                 shyps = shyps,
                 hyps = disch(As,A),  
                 prop = implies$A$prop})
  | implies_intr_hyps th = th;

(*Smash" unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.
  Resulting sequence may contain multiple elements if the tpairs are
    not all flex-flex. *)
fun flexflex_rule (th as Thm{sign_ref, der, maxidx, hyps, prop,...}) =
  let fun newthm env =
          if Envir.is_empty env then th
          else
          let val (tpairs,horn) =
                        Logic.strip_flexpairs (Envir.norm_term env prop)
                (*Remove trivial tpairs, of the form t=t*)
              val distpairs = filter (not o op aconv) tpairs
              val newprop = Logic.list_flexpairs(distpairs, horn)
          in  fix_shyps [th] (env_codT env)
                (Thm{sign_ref = sign_ref, 
                     der = infer_derivs (Flexflex_rule env, [der]), 
                     maxidx = maxidx_of_term newprop, 
                     shyps = [], 
                     hyps = hyps,
                     prop = newprop})
          end;
      val (tpairs,_) = Logic.strip_flexpairs prop
  in Seq.map newthm
            (Unify.smash_unifiers(Sign.deref sign_ref, Envir.empty maxidx, tpairs))
  end;

(*Instantiation of Vars
           A
  -------------------
  A[t1/v1,....,tn/vn]
*)

local

(*Check that all the terms are Vars and are distinct*)
fun instl_ok ts = forall is_Var ts andalso null(findrep ts);

fun prt_typing sg_ref t T =
  let val sg = Sign.deref sg_ref in
    Pretty.block [Sign.pretty_term sg t, Pretty.str " ::", Pretty.brk 1, Sign.pretty_typ sg T]
  end;

(*For instantiate: process pair of cterms, merge theories*)
fun add_ctpair ((ct,cu), (sign_ref,tpairs)) =
  let
    val Cterm {sign_ref=sign_reft, t=t, T= T, ...} = ct
    and Cterm {sign_ref=sign_refu, t=u, T= U, ...} = cu;
    val sign_ref_merged = Sign.merge_refs (sign_ref, Sign.merge_refs (sign_reft, sign_refu));
  in
    if T=U then (sign_ref_merged, (t,u)::tpairs)
    else raise TYPE (Pretty.string_of (Pretty.block [Pretty.str "instantiate: type conflict",
      Pretty.fbrk, prt_typing sign_ref_merged t T,
      Pretty.fbrk, prt_typing sign_ref_merged u U]), [T,U], [t,u])
  end;

fun add_ctyp ((v,ctyp), (sign_ref',vTs)) =
  let val Ctyp {T,sign_ref} = ctyp
  in (Sign.merge_refs(sign_ref,sign_ref'), (v,T)::vTs) end;

in

(*Left-to-right replacements: ctpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms of same type.
  No longer normalizes the new theorem! *)
fun instantiate ([], []) th = th
  | instantiate (vcTs,ctpairs) (th as Thm{sign_ref,der,maxidx,hyps,prop,...}) =
  let val (newsign_ref,tpairs) = foldr add_ctpair (ctpairs, (sign_ref,[]));
      val (newsign_ref,vTs) = foldr add_ctyp (vcTs, (newsign_ref,[]));
      val newprop = subst_atomic tpairs
	             (Type.inst_term_tvars
		      (Sign.tsig_of (Sign.deref newsign_ref),vTs) prop)
      val newth =
            fix_shyps [th] (map snd vTs)
              (Thm{sign_ref = newsign_ref, 
                   der = infer_derivs (Instantiate(vcTs,ctpairs), [der]), 
                   maxidx = maxidx_of_term newprop, 
                   shyps = [],
                   hyps = hyps,
                   prop = newprop})
  in  if not(instl_ok(map #1 tpairs))
      then raise THM("instantiate: variables not distinct", 0, [th])
      else if not(null(findrep(map #1 vTs)))
      then raise THM("instantiate: type variables not distinct", 0, [th])
      else nodup_vars newth "instantiate"
  end
  handle TERM _ => raise THM("instantiate: incompatible signatures", 0, [th])
       | TYPE (msg, _, _) => raise THM (msg, 0, [th]);

end;


(*The trivial implication A==>A, justified by assume and forall rules.
  A can contain Vars, not so for assume!   *)
fun trivial ct : thm =
  let val Cterm {sign_ref, t=A, T, maxidx} = ct
  in  if T<>propT then
            raise THM("trivial: the term must have type prop", 0, [])
      else fix_shyps [] []
        (Thm{sign_ref = sign_ref, 
             der = infer_derivs (Trivial ct, []), 
             maxidx = maxidx, 
             shyps = [], 
             hyps = [],
             prop = implies$A$A})
  end;

(*Axiom-scheme reflecting signature contents: "OFCLASS(?'a::c, c_class)" *)
fun class_triv sign c =
  let val Cterm {sign_ref, t, maxidx, ...} =
    cterm_of sign (Logic.mk_inclass (TVar (("'a", 0), [c]), c))
      handle TERM (msg, _) => raise THM ("class_triv: " ^ msg, 0, []);
  in
    fix_shyps [] []
      (Thm {sign_ref = sign_ref, 
            der = infer_derivs (Class_triv c, []), 
            maxidx = maxidx, 
            shyps = [], 
            hyps = [], 
            prop = t})
  end;


(* Replace all TFrees not fixed or in the hyps by new TVars *)
fun varifyT' fixed (Thm{sign_ref,der,maxidx,shyps,hyps,prop}) =
  let val tfrees = foldr add_term_tfree_names (hyps,fixed)
  in let val thm = (*no fix_shyps*)
    Thm{sign_ref = sign_ref, 
        der = infer_derivs (VarifyT fixed, [der]), 
        maxidx = Int.max(0,maxidx), 
        shyps = shyps, 
        hyps = hyps,
        prop = Type.varify(prop,tfrees)}
     in nodup_vars thm "varifyT" end
(* this nodup_vars check can be removed if thms are guaranteed not to contain
duplicate TVars with different sorts *)
  end;

val varifyT = varifyT' [];

(* Replace all TVars by new TFrees *)
fun freezeT(Thm{sign_ref,der,maxidx,shyps,hyps,prop}) =
  let val (prop',_) = Type.freeze_thaw prop
  in (*no fix_shyps*)
    Thm{sign_ref = sign_ref, 
        der = infer_derivs (FreezeT, [der]),
        maxidx = maxidx_of_term prop',
        shyps = shyps,
        hyps = hyps,
        prop = prop'}
  end;


(*** Inference rules for tactics ***)

(*Destruct proof state into constraints, other goals, goal(i), rest *)
fun dest_state (state as Thm{prop,...}, i) =
  let val (tpairs,horn) = Logic.strip_flexpairs prop
  in  case  Logic.strip_prems(i, [], horn) of
          (B::rBs, C) => (tpairs, rev rBs, B, C)
        | _ => raise THM("dest_state", i, [state])
  end
  handle TERM _ => raise THM("dest_state", i, [state]);

(*Increment variables and parameters of orule as required for
  resolution with goal i of state. *)
fun lift_rule (state, i) orule =
  let val Thm{shyps=sshyps, prop=sprop, maxidx=smax, sign_ref=ssign_ref,...} = state
      val (Bi::_, _) = Logic.strip_prems(i, [], Logic.skip_flexpairs sprop)
        handle TERM _ => raise THM("lift_rule", i, [orule,state])
      val ct_Bi = Cterm {sign_ref=ssign_ref, maxidx=smax, T=propT, t=Bi}
      val (lift_abs,lift_all) = Logic.lift_fns(Bi,smax+1)
      val (Thm{sign_ref, der, maxidx,shyps,hyps,prop}) = orule
      val (tpairs,As,B) = Logic.strip_horn prop
  in  (*no fix_shyps*)
      Thm{sign_ref = merge_thm_sgs(state,orule),
          der = infer_derivs (Lift_rule(ct_Bi, i), [der]),
          maxidx = maxidx+smax+1,
          shyps=union_sort(sshyps,shyps), 
          hyps=hyps, 
          prop = Logic.rule_of (map (pairself lift_abs) tpairs,
                                map lift_all As,    
                                lift_all B)}
  end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption. *)
fun assumption i state =
  let val Thm{sign_ref,der,maxidx,hyps,prop,...} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      fun newth (env as Envir.Envir{maxidx, ...}, tpairs) =
        fix_shyps [state] (env_codT env)
          (Thm{sign_ref = sign_ref, 
               der = infer_derivs (Assumption (i, Some env), [der]),
               maxidx = maxidx,
               shyps = [],
               hyps = hyps,
               prop = 
               if Envir.is_empty env then (*avoid wasted normalizations*)
                   Logic.rule_of (tpairs, Bs, C)
               else (*normalize the new rule fully*)
                   Envir.norm_term env (Logic.rule_of (tpairs, Bs, C))});
      fun addprfs [] = Seq.empty
        | addprfs ((t,u)::apairs) = Seq.make (fn()=> Seq.pull
             (Seq.mapp newth
                (Unify.unifiers(Sign.deref sign_ref,Envir.empty maxidx, (t,u)::tpairs))
                (addprfs apairs)))
  in  addprfs (Logic.assum_pairs Bi)  end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha-convertible to one of its assumptions*)
fun eq_assumption i state =
  let val Thm{sign_ref,der,maxidx,hyps,prop,...} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
  in  if exists (op aconv) (Logic.assum_pairs Bi)
      then fix_shyps [state] []
             (Thm{sign_ref = sign_ref, 
                  der = infer_derivs (Assumption (i,None), [der]),
                  maxidx = maxidx,
                  shyps = [],
                  hyps = hyps,
                  prop = Logic.rule_of(tpairs, Bs, C)})
      else  raise THM("eq_assumption", 0, [state])
  end;


(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let val Thm{sign_ref,der,maxidx,hyps,prop,shyps} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      val params = Term.strip_all_vars Bi
      and rest   = Term.strip_all_body Bi
      val asms   = Logic.strip_imp_prems rest
      and concl  = Logic.strip_imp_concl rest
      val n      = length asms
      fun rot m  = if 0=m orelse m=n then Bi
		   else if 0<m andalso m<n 
		   then list_all 
			   (params, 
			    Logic.list_implies(List.drop(asms, m) @ 
					       List.take(asms, m),
					       concl))
		   else raise THM("rotate_rule", k, [state])
  in  (*no fix_shyps*)
      Thm{sign_ref = sign_ref, 
	  der = infer_derivs (Rotate_rule (k,i), [der]),
	  maxidx = maxidx,
	  shyps = shyps,
	  hyps = hyps,
	  prop = Logic.rule_of(tpairs, Bs@[rot (if k<0 then n+k else k)], C)}
  end;


(*Rotates a rule's premises to the left by k, leaving the first j premises
  unchanged.  Does nothing if k=0 or if k equals n-j, where n is the
  number of premises.  Useful with etac and underlies tactic/defer_tac*)
fun permute_prems j k rl =
  let val Thm{sign_ref,der,maxidx,hyps,prop,shyps} = rl
      val prems  = Logic.strip_imp_prems prop
      and concl  = Logic.strip_imp_concl prop
      val moved_prems = List.drop(prems, j)
      and fixed_prems = List.take(prems, j)
        handle Subscript => raise THM("permute_prems:j", j, [rl])
      val n_j    = length moved_prems
      fun rot m  = if 0 = m orelse m = n_j then prop
		   else if 0<m andalso m<n_j 
		   then Logic.list_implies(fixed_prems @
					   List.drop(moved_prems, m) @ 
					   List.take(moved_prems, m),
					   concl)
		   else raise THM("permute_prems:k", k, [rl])
  in  (*no fix_shyps*)
      Thm{sign_ref = sign_ref, 
	  der = infer_derivs (Permute_prems (j,k), [der]),
	  maxidx = maxidx,
	  shyps = shyps,
	  hyps = hyps,
	  prop = rot (if k<0 then n_j + k else k)}
  end;


(** User renaming of parameters in a subgoal **)

(*Calls error rather than raising an exception because it is intended
  for top-level use -- exception handling would not make sense here.
  The names in cs, if distinct, are used for the innermost parameters;
   preceding parameters may be renamed to make all params distinct.*)
fun rename_params_rule (cs, i) state =
  let val Thm{sign_ref,der,maxidx,hyps,...} = state
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      val iparams = map #1 (Logic.strip_params Bi)
      val short = length iparams - length cs
      val newnames =
            if short<0 then error"More names than abstractions!"
            else variantlist(take (short,iparams), cs) @ cs
      val freenames = map (#1 o dest_Free) (term_frees Bi)
      val newBi = Logic.list_rename_params (newnames, Bi)
  in
  case findrep cs of
     c::_ => (warning ("Can't rename.  Bound variables not distinct: " ^ c); 
	      state)
   | [] => (case cs inter_string freenames of
       a::_ => (warning ("Can't rename.  Bound/Free variable clash: " ^ a); 
		state)
     | [] => fix_shyps [state] []
                (Thm{sign_ref = sign_ref,
                     der = infer_derivs (Rename_params_rule(cs,i), [der]),
                     maxidx = maxidx,
                     shyps = [],
                     hyps = hyps,
                     prop = Logic.rule_of(tpairs, Bs@[newBi], C)}))
  end;

(*** Preservation of bound variable names ***)

(*Scan a pair of terms; while they are similar,
  accumulate corresponding bound vars in "al"*)
fun match_bvs(Abs(x,_,s),Abs(y,_,t), al) =
      match_bvs(s, t, if x="" orelse y="" then al
                                          else (x,y)::al)
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
                   Some(y) => if x mem_string vids orelse y mem_string vids then t
                              else Var((y,i),T)
                 | None=> t)
          | rename(Abs(x,T,t)) =
              Abs(case assoc_string(al,x) of Some(y) => y | None => x,
                  T, rename t)
          | rename(f$t) = rename f $ rename t
          | rename(t) = t;
        fun strip_ren Ai = strip_apply rename (Ai,B)
    in strip_ren end;

(*Function to rename bounds/unknowns in the argument, lifted over B*)
fun rename_bvars(dpairs, tpairs, B) =
        rename_bvs(foldr match_bvars (dpairs,[]), dpairs, tpairs, B);


(*** RESOLUTION ***)

(** Lifting optimizations **)

(*strip off pairs of assumptions/parameters in parallel -- they are
  identical because of lifting*)
fun strip_assums2 (Const("==>", _) $ _ $ B1,
                   Const("==>", _) $ _ $ B2) = strip_assums2 (B1,B2)
  | strip_assums2 (Const("all",_)$Abs(a,T,t1),
                   Const("all",_)$Abs(_,_,t2)) =
      let val (B1,B2) = strip_assums2 (t1,t2)
      in  (Abs(a,T,B1), Abs(a,T,B2))  end
  | strip_assums2 BB = BB;


(*Faster normalization: skip assumptions that were lifted over*)
fun norm_term_skip env 0 t = Envir.norm_term env t
  | norm_term_skip env n (Const("all",_)$Abs(a,T,t)) =
        let val Envir.Envir{iTs, ...} = env
            val T' = typ_subst_TVars_Vartab iTs T
            (*Must instantiate types of parameters because they are flattened;
              this could be a NEW parameter*)
        in  all T' $ Abs(a, T', norm_term_skip env n t)  end
  | norm_term_skip env n (Const("==>", _) $ A $ B) =
        implies $ A $ norm_term_skip env (n-1) B
  | norm_term_skip env n t = error"norm_term_skip: too few assumptions??";


(*Composition of object rule r=(A1...Am/B) with proof state s=(B1...Bn/C)
  Unifies B with Bi, replacing subgoal i    (1 <= i <= n)
  If match then forbid instantiations in proof state
  If lifted then shorten the dpair using strip_assums2.
  If eres_flg then simultaneously proves A1 by assumption.
  nsubgoal is the number of new subgoals (written m above).
  Curried so that resolution calls dest_state only once.
*)
local exception COMPOSE
in
fun bicompose_aux match (state, (stpairs, Bs, Bi, C), lifted)
                        (eres_flg, orule, nsubgoal) =
 let val Thm{der=sder, maxidx=smax, shyps=sshyps, hyps=shyps, ...} = state
     and Thm{der=rder, maxidx=rmax, shyps=rshyps, hyps=rhyps, 
             prop=rprop,...} = orule
         (*How many hyps to skip over during normalization*)
     and nlift = Logic.count_prems(strip_all_body Bi,
                                   if eres_flg then ~1 else 0)
     val sign_ref = merge_thm_sgs(state,orule);
     val sign = Sign.deref sign_ref;
     (** Add new theorem with prop = '[| Bs; As |] ==> C' to thq **)
     fun addth As ((env as Envir.Envir {maxidx, ...}, tpairs), thq) =
       let val normt = Envir.norm_term env;
           (*perform minimal copying here by examining env*)
           val normp =
             if Envir.is_empty env then (tpairs, Bs @ As, C)
             else
             let val ntps = map (pairself normt) tpairs
             in if Envir.above (smax, env) then
                  (*no assignments in state; normalize the rule only*)
                  if lifted
                  then (ntps, Bs @ map (norm_term_skip env nlift) As, C)
                  else (ntps, Bs @ map normt As, C)
                else if match then raise COMPOSE
                else (*normalize the new rule fully*)
                  (ntps, map normt (Bs @ As), normt C)
             end
           val th = (*tuned fix_shyps*)
             Thm{sign_ref = sign_ref,
                 der = infer_derivs (Bicompose(match, eres_flg,
                                               1 + length Bs, nsubgoal, env),
                                     [rder,sder]),
                 maxidx = maxidx,
                 shyps = add_env_sorts (env, union_sort(rshyps,sshyps)),
                 hyps = union_term(rhyps,shyps),
                 prop = Logic.rule_of normp}
        in  Seq.cons(th, thq)  end  handle COMPOSE => thq
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
     val env = Envir.empty(Int.max(rmax,smax));
     val BBi = if lifted then strip_assums2(B,Bi) else (B,Bi);
     val dpairs = BBi :: (rtpairs@stpairs);
     (*elim-resolution: try each assumption in turn.  Initially n=1*)
     fun tryasms (_, _, []) = Seq.empty
       | tryasms (As, n, (t,u)::apairs) =
          (case Seq.pull(Unify.unifiers(sign, env, (t,u)::dpairs))  of
               None                   => tryasms (As, n+1, apairs)
             | cell as Some((_,tpairs),_) =>
                   Seq.it_right (addth (newAs(As, n, [BBi,(u,t)], tpairs)))
                       (Seq.make (fn()=> cell),
                        Seq.make (fn()=> Seq.pull (tryasms (As, n+1, apairs)))));
     fun eres [] = raise THM("bicompose: no premises", 0, [orule,state])
       | eres (A1::As) = tryasms (As, 1, Logic.assum_pairs A1);
     (*ordinary resolution*)
     fun res(None) = Seq.empty
       | res(cell as Some((_,tpairs),_)) =
             Seq.it_right (addth(newAs(rev rAs, 0, [BBi], tpairs)))
                       (Seq.make (fn()=> cell), Seq.empty)
 in  if eres_flg then eres(rev rAs)
     else res(Seq.pull(Unify.unifiers(sign, env, dpairs)))
 end;
end;


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
        fun res [] = Seq.empty
          | res ((eres_flg, rule)::brules) =
              if could_bires (Hs, B, eres_flg, rule)
              then Seq.make (*delay processing remainder till needed*)
                  (fn()=> Some(comp (eres_flg, lift rule, nprems_of rule),
                               res brules))
              else res brules
    in  Seq.flat (res brules)  end;



(*** Meta Simplification ***)

(** diagnostics **)

exception SIMPLIFIER of string * thm;

fun prnt warn a = if warn then warning a else writeln a;

fun prtm warn a sign t =
  (prnt warn a; prnt warn (Sign.string_of_term sign t));

fun prthm warn a (thm as Thm{sign_ref, prop, ...}) =
  (prtm warn a (Sign.deref sign_ref) prop);

val trace_simp = ref false;
val debug_simp = ref false;

fun trace warn a = if !trace_simp then prnt warn a else ();
fun debug warn a = if !debug_simp then prnt warn a else ();

fun trace_term warn a sign t = if !trace_simp then prtm warn a sign t else ();
fun debug_term warn a sign t = if !debug_simp then prtm warn a sign t else ();

fun trace_thm warn a (thm as Thm{sign_ref, prop, ...}) =
  (trace_term warn a (Sign.deref sign_ref) prop);



(** meta simp sets **)

(* basic components *)

type rrule = {thm: thm, lhs: term, elhs: term, fo: bool, perm: bool};
(* thm: the rewrite rule
   lhs: the left-hand side
   elhs: the etac-contracted lhs.
   fo:  use first-order matching
   perm: the rewrite rule is permutative
Reamrks:
  - elhs is used for matching,
    lhs only for preservation of bound variable names.
  - fo is set iff
    either elhs is first-order (no Var is applied),
           in which case fo-matching is complete,
    or elhs is not a pattern,
       in which case there is nothing better to do.
*)
type cong = {thm: thm, lhs: term};
type simproc =
 {name: string, proc: Sign.sg -> thm list -> term -> thm option, lhs: cterm, id: stamp};

fun eq_rrule ({thm = Thm {prop = p1, ...}, ...}: rrule,
  {thm = Thm {prop = p2, ...}, ...}: rrule) = p1 aconv p2;

fun eq_cong ({thm = Thm {prop = p1, ...}, ...}: cong,
  {thm = Thm {prop = p2, ...}, ...}: cong) = p1 aconv p2;

fun eq_prem (Thm {prop = p1, ...}, Thm {prop = p2, ...}) = p1 aconv p2;

fun eq_simproc ({id = s1, ...}:simproc, {id = s2, ...}:simproc) = (s1 = s2);

fun mk_simproc (name, proc, lhs, id) =
  {name = name, proc = proc, lhs = lhs, id = id};


(* datatype mss *)

(*
  A "mss" contains data needed during conversion:
    rules: discrimination net of rewrite rules;
    congs: association list of congruence rules and
           a list of `weak' congruence constants.
           A congruence is `weak' if it avoids normalization of some argument.
    procs: discrimination net of simplification procedures
      (functions that prove rewrite rules on the fly);
    bounds: names of bound variables already used
      (for generating new names when rewriting under lambda abstractions);
    prems: current premises;
    mk_rews: mk: turns simplification thms into rewrite rules;
             mk_sym: turns == around; (needs Drule!)
             mk_eq_True: turns P into P == True - logic specific;
    termless: relation for ordered rewriting;
*)

datatype meta_simpset =
  Mss of {
    rules: rrule Net.net,
    congs: (string * cong) list * string list,
    procs: simproc Net.net,
    bounds: string list,
    prems: thm list,
    mk_rews: {mk: thm -> thm list,
              mk_sym: thm -> thm option,
              mk_eq_True: thm -> thm option},
    termless: term * term -> bool};

fun mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless) =
  Mss {rules = rules, congs = congs, procs = procs, bounds = bounds,
       prems=prems, mk_rews=mk_rews, termless=termless};

fun upd_rules(Mss{rules,congs,procs,bounds,prems,mk_rews,termless}, rules') =
  mk_mss(rules',congs,procs,bounds,prems,mk_rews,termless);

val empty_mss =
  let val mk_rews = {mk = K [], mk_sym = K None, mk_eq_True = K None}
  in mk_mss (Net.empty, ([], []), Net.empty, [], [], mk_rews, Term.termless) end;

fun clear_mss (Mss {mk_rews, termless, ...}) =
  mk_mss (Net.empty, ([], []), Net.empty, [], [], mk_rews, termless);



(** simpset operations **)

(* term variables *)

val add_term_varnames = foldl_aterms (fn (xs, Var (x, _)) => ins_ix (x, xs) | (xs, _) => xs);
fun term_varnames t = add_term_varnames ([], t);


(* dest_mss *)

fun dest_mss (Mss {rules, congs, procs, ...}) =
  {simps = map (fn (_, {thm, ...}) => thm) (Net.dest rules),
   congs = map (fn (_, {thm, ...}) => thm) (fst congs),
   procs =
     map (fn (_, {name, lhs, id, ...}) => ((name, lhs), id)) (Net.dest procs)
     |> partition_eq eq_snd
     |> map (fn ps => (#1 (#1 (hd ps)), map (#2 o #1) ps))};


(* merge_mss *)		(*NOTE: ignores mk_rews and termless of 2nd mss*)

fun merge_mss
 (Mss {rules = rules1, congs = (congs1,weak1), procs = procs1,
       bounds = bounds1, prems = prems1, mk_rews, termless},
  Mss {rules = rules2, congs = (congs2,weak2), procs = procs2,
       bounds = bounds2, prems = prems2, ...}) =
      mk_mss
       (Net.merge (rules1, rules2, eq_rrule),
        (generic_merge (eq_cong o pairself snd) I I congs1 congs2,
        merge_lists weak1 weak2),
        Net.merge (procs1, procs2, eq_simproc),
        merge_lists bounds1 bounds2,
        generic_merge eq_prem I I prems1 prems2,
        mk_rews, termless);


(* add_simps *)

fun mk_rrule2{thm,lhs,elhs,perm} =
  let val fo = Pattern.first_order elhs orelse not(Pattern.pattern elhs)
  in {thm=thm,lhs=lhs,elhs=elhs,fo=fo,perm=perm} end

fun insert_rrule(mss as Mss {rules,...},
                 rrule as {thm,lhs,elhs,perm}) =
  (trace_thm false "Adding rewrite rule:" thm;
   let val rrule2 as {elhs,...} = mk_rrule2 rrule
       val rules' = Net.insert_term ((elhs, rrule2), rules, eq_rrule)
   in upd_rules(mss,rules') end
   handle Net.INSERT =>
     (prthm true "Ignoring duplicate rewrite rule:" thm; mss));

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u);

fun var_perm (t, u) =
  vperm (t, u) andalso eq_set (term_varnames t, term_varnames u);

(* FIXME: it seems that the conditions on extra variables are too liberal if
prems are nonempty: does solving the prems really guarantee instantiation of
all its Vars? Better: a dynamic check each time a rule is applied.
*)
fun rewrite_rule_extra_vars prems elhs erhs =
  not (term_varnames erhs subset foldl add_term_varnames (term_varnames elhs, prems))
  orelse
  not ((term_tvars erhs) subset
       (term_tvars elhs  union  List.concat(map term_tvars prems)));

(*Simple test for looping rewrite rules and stupid orientations*)
fun reorient sign prems lhs rhs =
   rewrite_rule_extra_vars prems lhs rhs
  orelse
   is_Var (head_of lhs)
  orelse
   (exists (apl (lhs, Logic.occs)) (rhs :: prems))
  orelse
   (null prems andalso
    Pattern.matches (#tsig (Sign.rep_sg sign)) (lhs, rhs))
    (*the condition "null prems" is necessary because conditional rewrites
      with extra variables in the conditions may terminate although
      the rhs is an instance of the lhs. Example: ?m < ?n ==> f(?n) == f(?m)*)
  orelse
   (is_Const lhs andalso not(is_Const rhs))

fun decomp_simp(thm as Thm {sign_ref, prop, ...}) =
  let val sign = Sign.deref sign_ref;
      val prems = Logic.strip_imp_prems prop;
      val concl = Logic.strip_imp_concl prop;
      val (lhs, rhs) = Logic.dest_equals concl handle TERM _ =>
        raise SIMPLIFIER ("Rewrite rule not a meta-equality", thm)
      val elhs = Pattern.eta_contract lhs;
      val elhs = if elhs=lhs then lhs else elhs (* try to share *)
      val erhs = Pattern.eta_contract rhs;
      val perm = var_perm (elhs, erhs) andalso not (elhs aconv erhs)
                 andalso not (is_Var elhs)
  in (sign,prems,lhs,elhs,rhs,perm) end;

fun mk_eq_True (Mss{mk_rews={mk_eq_True,...},...}) thm =
  case mk_eq_True thm of
    None => []
  | Some eq_True => let val (_,_,lhs,elhs,_,_) = decomp_simp eq_True
                    in [{thm=eq_True, lhs=lhs, elhs=elhs, perm=false}] end;

(* create the rewrite rule and possibly also the ==True variant,
   in case there are extra vars on the rhs *)
fun rrule_eq_True(thm,lhs,elhs,rhs,mss,thm2) =
  let val rrule = {thm=thm, lhs=lhs, elhs=elhs, perm=false}
  in if (term_varnames rhs)  subset (term_varnames lhs) andalso
        (term_tvars rhs) subset (term_tvars lhs)
     then [rrule]
     else mk_eq_True mss thm2 @ [rrule]
  end;

fun mk_rrule mss thm =
  let val (_,prems,lhs,elhs,rhs,perm) = decomp_simp thm
  in if perm then [{thm=thm, lhs=lhs, elhs=elhs, perm=true}] else
     (* weak test for loops: *)
     if rewrite_rule_extra_vars prems lhs rhs orelse
        is_Var elhs
     then mk_eq_True mss thm
     else rrule_eq_True(thm,lhs,elhs,rhs,mss,thm)
  end;

fun orient_rrule mss thm =
  let val (sign,prems,lhs,elhs,rhs,perm) = decomp_simp thm
  in if perm then [{thm=thm,lhs=lhs,elhs=elhs,perm=true}]
     else if reorient sign prems lhs rhs
          then if reorient sign prems rhs lhs
               then mk_eq_True mss thm
               else let val Mss{mk_rews={mk_sym,...},...} = mss
                    in case mk_sym thm of
                         None => []
                       | Some thm' =>
                           let val (_,_,lhs',elhs',rhs',_) = decomp_simp thm'
                           in rrule_eq_True(thm',lhs',elhs',rhs',mss,thm) end
                    end
          else rrule_eq_True(thm,lhs,elhs,rhs,mss,thm)
  end;

fun extract_rews(Mss{mk_rews = {mk,...},...},thms) = flat(map mk thms);

fun orient_comb_simps comb mk_rrule (mss,thms) =
  let val rews = extract_rews(mss,thms)
      val rrules = flat (map mk_rrule rews)
  in foldl comb (mss,rrules) end

(* Add rewrite rules explicitly; do not reorient! *)
fun add_simps(mss,thms) =
  orient_comb_simps insert_rrule (mk_rrule mss) (mss,thms);

fun mss_of thms =
  foldl insert_rrule (empty_mss, flat(map (mk_rrule empty_mss) thms));

fun extract_safe_rrules(mss,thm) =
  flat (map (orient_rrule mss) (extract_rews(mss,[thm])));

fun add_safe_simp(mss,thm) =
  foldl insert_rrule (mss, extract_safe_rrules(mss,thm))

(* del_simps *)

fun del_rrule(mss as Mss {rules,...},
              rrule as {thm, elhs, ...}) =
  (upd_rules(mss, Net.delete_term ((elhs, rrule), rules, eq_rrule))
   handle Net.DELETE =>
     (prthm true "Rewrite rule not in simpset:" thm; mss));

fun del_simps(mss,thms) =
  orient_comb_simps del_rrule (map mk_rrule2 o mk_rrule mss) (mss,thms);


(* add_congs *)

fun is_full_cong_prems [] varpairs = null varpairs
  | is_full_cong_prems (p::prems) varpairs =
    (case Logic.strip_assums_concl p of
       Const("==",_) $ lhs $ rhs =>
         let val (x,xs) = strip_comb lhs and (y,ys) = strip_comb rhs
         in is_Var x  andalso  forall is_Bound xs  andalso
            null(findrep(xs))  andalso xs=ys andalso
            (x,y) mem varpairs andalso
            is_full_cong_prems prems (varpairs\(x,y))
         end
     | _ => false);

fun is_full_cong (Thm{prop,...}) =
let val prems = Logic.strip_imp_prems prop
    and concl = Logic.strip_imp_concl prop
    val (lhs,rhs) = Logic.dest_equals concl
    val (f,xs) = strip_comb lhs
    and (g,ys) = strip_comb rhs
in
  f=g andalso null(findrep(xs@ys)) andalso length xs = length ys andalso
  is_full_cong_prems prems (xs ~~ ys)
end

fun add_cong (Mss {rules,congs,procs,bounds,prems,mk_rews,termless}, thm) =
  let
    val (lhs, _) = Logic.dest_equals (concl_of thm) handle TERM _ =>
      raise SIMPLIFIER ("Congruence not a meta-equality", thm);
(*   val lhs = Pattern.eta_contract lhs; *)
    val (a, _) = dest_Const (head_of lhs) handle TERM _ =>
      raise SIMPLIFIER ("Congruence must start with a constant", thm);
    val (alist,weak) = congs
    val weak2 = if is_full_cong thm then weak else a::weak
  in
    mk_mss (rules, ((a, {lhs = lhs, thm = thm}) :: alist, weak2),
            procs, bounds, prems, mk_rews, termless)
  end;

val (op add_congs) = foldl add_cong;


(* del_congs *)

fun del_cong (Mss {rules,congs,procs,bounds,prems,mk_rews,termless}, thm) =
  let
    val (lhs, _) = Logic.dest_equals (concl_of thm) handle TERM _ =>
      raise SIMPLIFIER ("Congruence not a meta-equality", thm);
(*   val lhs = Pattern.eta_contract lhs; *)
    val (a, _) = dest_Const (head_of lhs) handle TERM _ =>
      raise SIMPLIFIER ("Congruence must start with a constant", thm);
    val (alist,_) = congs
    val alist2 = filter (fn (x,_)=> x<>a) alist
    val weak2 = mapfilter (fn(a,{thm,...}) => if is_full_cong thm then None
                                              else Some a)
                   alist2
  in
    mk_mss (rules, (alist2,weak2), procs, bounds, prems, mk_rews, termless)
  end;

val (op del_congs) = foldl del_cong;


(* add_simprocs *)

fun add_proc (mss as Mss {rules,congs,procs,bounds,prems,mk_rews,termless},
    (name, lhs as Cterm {sign_ref, t, ...}, proc, id)) =
  (trace_term false ("Adding simplification procedure " ^ quote name ^ " for")
      (Sign.deref sign_ref) t;
    mk_mss (rules, congs,
      Net.insert_term ((t, mk_simproc (name, proc, lhs, id)), procs, eq_simproc)
        handle Net.INSERT => 
	    (warning ("Ignoring duplicate simplification procedure \"" 
	              ^ name ^ "\""); 
	     procs),
        bounds, prems, mk_rews, termless));

fun add_simproc (mss, (name, lhss, proc, id)) =
  foldl add_proc (mss, map (fn lhs => (name, lhs, proc, id)) lhss);

val add_simprocs = foldl add_simproc;


(* del_simprocs *)

fun del_proc (mss as Mss {rules,congs,procs,bounds,prems,mk_rews,termless},
    (name, lhs as Cterm {t, ...}, proc, id)) =
  mk_mss (rules, congs,
    Net.delete_term ((t, mk_simproc (name, proc, lhs, id)), procs, eq_simproc)
      handle Net.DELETE => 
	  (warning ("Simplification procedure \"" ^ name ^
		       "\" not in simpset"); procs),
      bounds, prems, mk_rews, termless);

fun del_simproc (mss, (name, lhss, proc, id)) =
  foldl del_proc (mss, map (fn lhs => (name, lhs, proc, id)) lhss);

val del_simprocs = foldl del_simproc;


(* prems *)

fun add_prems (Mss {rules,congs,procs,bounds,prems,mk_rews,termless}, thms) =
  mk_mss (rules, congs, procs, bounds, thms @ prems, mk_rews, termless);

fun prems_of_mss (Mss {prems, ...}) = prems;


(* mk_rews *)

fun set_mk_rews
  (Mss {rules, congs, procs, bounds, prems, mk_rews, termless}, mk) =
    mk_mss (rules, congs, procs, bounds, prems,
            {mk=mk, mk_sym= #mk_sym mk_rews, mk_eq_True= #mk_eq_True mk_rews},
            termless);

fun set_mk_sym
  (Mss {rules, congs, procs, bounds, prems, mk_rews, termless}, mk_sym) =
    mk_mss (rules, congs, procs, bounds, prems,
            {mk= #mk mk_rews, mk_sym= mk_sym, mk_eq_True= #mk_eq_True mk_rews},
            termless);

fun set_mk_eq_True
  (Mss {rules, congs, procs, bounds, prems, mk_rews, termless}, mk_eq_True) =
    mk_mss (rules, congs, procs, bounds, prems,
            {mk= #mk mk_rews, mk_sym= #mk_sym mk_rews, mk_eq_True= mk_eq_True},
            termless);

(* termless *)

fun set_termless
  (Mss {rules, congs, procs, bounds, prems, mk_rews, termless = _}, termless) =
    mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless);



(** rewriting **)

(*
  Uses conversions, omitting proofs for efficiency.  See:
    L C Paulson, A higher-order implementation of rewriting,
    Science of Computer Programming 3 (1983), pages 119-149.
*)

type prover = meta_simpset -> thm -> thm option;
type termrec = (Sign.sg_ref * term list) * term;
type conv = meta_simpset -> termrec -> termrec;

fun check_conv
      (thm as Thm{shyps,hyps,prop,sign_ref,der,...}, prop0, ders) =
  let fun err() = (trace_thm false "Proved wrong thm (Check subgoaler?)" thm;
                   trace_term false "Should have proved:" (Sign.deref sign_ref) prop0;
                   None)
      val (lhs0,_) = Logic.dest_equals(Logic.strip_imp_concl prop0)
  in case prop of
       Const("==",_) $ lhs $ rhs =>
         if (lhs = lhs0) orelse
            (lhs aconv Envir.norm_term (Envir.empty 0) lhs0)
         then (trace_thm false "SUCCEEDED" thm; 
               Some(rhs, (shyps, hyps, der::ders)))
         else err()
     | _ => err()
  end;

fun ren_inst(insts,prop,pat,obj) =
  let val ren = match_bvs(pat,obj,[])
      fun renAbs(Abs(x,T,b)) =
            Abs(case assoc_string(ren,x) of None => x | Some(y) => y, T, renAbs(b))
        | renAbs(f$t) = renAbs(f) $ renAbs(t)
        | renAbs(t) = t
  in subst_vars insts (if null(ren) then prop else renAbs(prop)) end;

fun incr_insts i (in1:(indexname*typ)list,in2:(indexname*term)list) =
  let fun incr ((a,n),x) = ((a,n+i),x)
  in (map incr in1, map incr in2) end;

fun add_insts_sorts ((iTs, is), Ss) =
  add_typs_sorts (map snd iTs, add_terms_sorts (map snd is, Ss));


(* mk_procrule *)

fun mk_procrule thm =
  let val (_,prems,lhs,elhs,rhs,_) = decomp_simp thm
  in if rewrite_rule_extra_vars prems lhs rhs
     then (prthm true "Extra vars on rhs:" thm; [])
     else [mk_rrule2{thm=thm, lhs=lhs, elhs=elhs, perm=false}]
  end;


(* conversion to apply the meta simpset to a term *)

(* Since the rewriting strategy is bottom-up, we avoid re-normalizing already
   normalized terms by carrying around the rhs of the rewrite rule just
   applied. This is called the `skeleton'. It is decomposed in parallel
   with the term. Once a Var is encountered, the corresponding term is
   already in normal form.
   skel0 is a dummy skeleton that is to enforce complete normalization.
*)
val skel0 = Bound 0;

(* Use rhs as skeleton only if the lhs does not contain unnormalized bits.
   The latter may happen iff there are weak congruence rules for constants
   in the lhs.
*)
fun uncond_skel((_,weak),(lhs,rhs)) =
  if null weak then rhs (* optimization *)
  else if exists_Const (fn (c,_) => c mem weak) lhs then skel0
       else rhs;

(* Behaves like unconditional rule if rhs does not contain vars not in the lhs.
   Otherwise those vars may become instantiated with unnormalized terms
   while the premises are solved.
*)
fun cond_skel(args as (congs,(lhs,rhs))) =
  if term_varnames rhs subset term_varnames lhs then uncond_skel(args)
  else skel0;

(*
  we try in order:
    (1) beta reduction
    (2) unconditional rewrite rules
    (3) conditional rewrite rules
    (4) simplification procedures

  IMPORTANT: rewrite rules must not introduce new Vars or TVars!

*)

fun rewritec (prover,sign_reft,maxt)
             (mss as Mss{rules, procs, termless, prems, congs, ...}) 
             (t:term,etc as (shypst,hypst,ders)) =
  let
    val eta_t = Pattern.eta_contract t;
    val signt = Sign.deref sign_reft;
    val tsigt = Sign.tsig_of signt;
    fun rew{thm as Thm{sign_ref,der,shyps,hyps,prop,maxidx,...},
            lhs, elhs, fo, perm} =
      let
        val _ = if Sign.subsig (Sign.deref sign_ref, signt) then ()
                else (prthm true "Rewrite rule from different theory:" thm;
                      raise Pattern.MATCH);
        val rprop = if maxt = ~1 then prop
                    else Logic.incr_indexes([],maxt+1) prop;
        val insts = if fo then Pattern.first_order_match tsigt (elhs,eta_t)
                          else Pattern.match             tsigt (elhs,eta_t);
        val insts = if maxt = ~1 then insts else incr_insts (maxt+1) insts
        val prop' = ren_inst(insts,rprop,lhs,eta_t);
        val hyps' = union_term(hyps,hypst);
        val shyps' = add_insts_sorts (insts, union_sort(shyps,shypst));
        val unconditional = (Logic.count_prems(prop',0) = 0);
        val maxidx' = if unconditional then maxt else maxidx+maxt+1
        val ct' = Cterm{sign_ref = sign_reft,       (*used for deriv only*)
                        t = prop', T = propT, maxidx = maxidx'}
        val der' = infer_derivs (RewriteC ct', [der]);
        val thm' = Thm{sign_ref = sign_reft, der = der', shyps = shyps',
                       hyps = hyps', prop = prop', maxidx = maxidx'}
        val (lhs',rhs') = Logic.dest_equals(Logic.strip_imp_concl prop')
      in
        if perm andalso not(termless(rhs',lhs')) then None
        else
          (trace_thm false "Applying instance of rewrite rule:" thm;
           if unconditional
           then
             (trace_thm false "Rewriting:" thm';
              let val lr = Logic.dest_equals prop
                  val trec' = (rhs', (shyps', hyps', der'::ders))
              in Some(trec',uncond_skel(congs,lr)) end)
           else
             (trace_thm false "Trying to rewrite:" thm';
              case prover mss thm' of
                None       => (trace_thm false "FAILED" thm'; None)
              | Some(thm2) =>
                  (case check_conv(thm2,prop',ders) of
                     None => None |
                     Some trec =>
                       let val concl = Logic.strip_imp_concl prop
                           val lr = Logic.dest_equals concl
                       in Some(trec,cond_skel(congs,lr)) end)))
      end

    fun rews [] = None
      | rews (rrule :: rrules) =
          let val opt = rew rrule handle Pattern.MATCH => None
          in case opt of None => rews rrules | some => some end;

    fun sort_rrules rrs = let
      fun is_simple({thm as Thm{prop,...}, ...}:rrule) = case prop of 
                                      Const("==",_) $ _ $ _ => true
                                      | _                   => false 
      fun sort []        (re1,re2) = re1 @ re2
        | sort (rr::rrs) (re1,re2) = if is_simple rr 
                                     then sort rrs (rr::re1,re2)
                                     else sort rrs (re1,rr::re2)
    in sort rrs ([],[]) end

    fun proc_rews ([]:simproc list) = None
      | proc_rews ({name, proc, lhs = Cterm {t = plhs, ...}, ...} :: ps) =
          if Pattern.matches tsigt (plhs, t) then
            (debug_term false ("Trying procedure " ^ quote name ^ " on:") signt eta_t;
             case proc signt prems eta_t of
               None => (debug false "FAILED"; proc_rews ps)
             | Some raw_thm =>
                 (trace_thm false ("Procedure " ^ quote name ^ " produced rewrite rule:") raw_thm;
                  (case rews (mk_procrule raw_thm) of
                    None => (trace false "IGNORED"; proc_rews ps)
                  | some => some)))
          else proc_rews ps;
  in case eta_t of
       Abs (_, _, body) $ u => Some ((subst_bound (u, body), etc),skel0)
     | _ => (case rews (sort_rrules (Net.match_term rules eta_t)) of
               None => proc_rews (Net.match_term procs eta_t)
             | some => some)
  end;


(* conversion to apply a congruence rule to a term *)

fun congc (prover,sign_reft,maxt) {thm=cong,lhs=lhs} (t,(shypst,hypst,ders)) =
  let val signt = Sign.deref sign_reft;
      val tsig = Sign.tsig_of signt;
      val Thm{sign_ref,der,shyps,hyps,maxidx,prop,...} = cong
      val _ = if Sign.subsig(Sign.deref sign_ref,signt) then ()
                 else error("Congruence rule from different theory")
      val rprop = if maxt = ~1 then prop
                  else Logic.incr_indexes([],maxt+1) prop;
      val rlhs = if maxt = ~1 then lhs
                 else fst(Logic.dest_equals(Logic.strip_imp_concl rprop))
      val insts = Pattern.match tsig (rlhs,t)
      (* Pattern.match can raise Pattern.MATCH;
         is handled when congc is called *)
      val prop' = ren_inst(insts,rprop,rlhs,t);
      val shyps' = add_insts_sorts (insts, union_sort(shyps,shypst))
      val maxidx' = maxidx_of_term prop'
      val ct' = Cterm{sign_ref = sign_reft,     (*used for deriv only*)
                      t = prop',
                      T = propT,
                      maxidx = maxidx'}
      val thm' = Thm{sign_ref = sign_reft, 
                     der = infer_derivs (CongC ct', [der]),
                     shyps = shyps',
                     hyps = union_term(hyps,hypst),
                     prop = prop',
                     maxidx = maxidx'};
      val unit = trace_thm false "Applying congruence rule:" thm';
      fun err() = error("Failed congruence proof!")

  in case prover thm' of
       None => err()
     | Some(thm2) => (case check_conv(thm2,prop',ders) of
                        None => err() | some => some)
  end;

fun bottomc ((simprem,useprem,mutsimp),prover,sign_ref,maxidx) =
  let
    fun botc fail skel mss trec =
          if is_Var skel then if fail then None else Some(trec)
          else
          (case subc skel mss trec of
             some as Some(trec1) =>
               (case rewritec (prover,sign_ref,maxidx) mss trec1 of
                  Some(trec2,skel2) => botc false skel2 mss trec2
                | None => some)
           | None =>
               (case rewritec (prover,sign_ref,maxidx) mss trec of
                  Some(trec2,skel2) => botc false skel2 mss trec2
                | None => if fail then None else Some(trec)))

    and try_botc mss trec =
          (case botc true skel0 mss trec of
             Some(trec1) => trec1 | None => trec)

    and subc skel
             (mss as Mss{rules,congs,procs,bounds,prems,mk_rews,termless})
             (trec as (t0:term,etc:sort list*term list * rule mtree list)) =
       (case t0 of
           Abs(a,T,t) =>
             let val b = variant bounds a
                 val v = Free("." ^ b,T)
                 val mss' = mk_mss (rules, congs, procs, b :: bounds, prems, mk_rews, termless)
                 val skel' = case skel of Abs(_,_,sk) => sk | _ => skel0
             in case botc true skel' mss' (subst_bound(v,t),etc) of
                  Some(t',etc') => Some(Abs(a, T, abstract_over(v,t')), etc')
                | None => None
             end
         | t$u => (case t of
             Const("==>",_)$s  => Some(impc(s,u,mss,etc))
           | Abs(_,_,body) =>
               let val trec = (subst_bound(u,body), etc)
               in case subc skel0 mss trec of
                    None => Some(trec)
                  | trec => trec
               end
           | _  =>
               let fun appc() =
                     let val (tskel,uskel) =
                                case skel of tskel$uskel => (tskel,uskel)
                                           | _ => (skel0,skel0)
                     in
                     (case botc true tskel mss (t,etc) of
                        Some(t1,etc1) =>
                          (case botc true uskel mss (u,etc1) of
                             Some(u1,etc2) => Some(t1$u1, etc2)
                           | None => Some(t1$u, etc1))
                      | None =>
                          (case botc true uskel mss (u,etc) of
                             Some(u1,etc1) => Some(t$u1, etc1)
                           | None => None))
                     end
                   val (h,ts) = strip_comb t
               in case h of
                    Const(a,_) =>
                      (case assoc_string(fst congs,a) of
                         None => appc()
                       | Some(cong) =>
                           (congc (prover mss,sign_ref,maxidx) cong trec
                            handle Pattern.MATCH => appc() ) )
                  | _ => appc()
               end)
         | _ => None)

    and impc args =
      if mutsimp
      then let val (prem, conc, mss, etc) = args
           in snd(mut_impc([], prem, conc, mss, etc)) end
      else nonmut_impc args

    and mut_impc (prems, prem, conc, mss, etc) =
      let val (prem1,etc1) = try_botc mss (prem,etc)
      in mut_impc1(prems, prem1, conc, mss, etc1) end

    and mut_impc1(prems, prem1, conc, mss, etc1 as (_,hyps1,_)) =
      let
        fun uncond({thm,lhs,elhs,perm}) =
          if no_prems thm then Some lhs else None

        val (lhss1,mss1) =
          if maxidx_of_term prem1 <> ~1
          then (trace_term true "Cannot add premise as rewrite rule because it contains (type) unknowns:"
                           (Sign.deref sign_ref) prem1;
                ([],mss))
          else let val thm = assume (Cterm{sign_ref=sign_ref, t=prem1, 
                                           T=propT, maxidx= ~1})
                   val rrules1 = extract_safe_rrules(mss,thm)
                   val lhss1 = mapfilter uncond rrules1
                   val mss1 = foldl insert_rrule (add_prems(mss,[thm]),rrules1)
               in (lhss1, mss1) end

        fun disch1(conc2,(shyps2,hyps2,ders2)) =
          let val hyps2' = if gen_mem (op aconv) (prem1, hyps1)
                           then hyps2 else hyps2\prem1
          in (Logic.mk_implies(prem1,conc2),(shyps2,hyps2',ders2)) end

        fun rebuild trec2 =
          let val trec = disch1 trec2
          in case rewritec (prover,sign_ref,maxidx) mss trec of
               None => (None,trec)
             | Some((Const("==>",_)$prem$conc,etc),_) =>
                 mut_impc(prems,prem,conc,mss,etc)
             | Some(trec',_) => (None,trec')
          end

        fun simpconc() =
          case conc of
            Const("==>",_)$s$t =>
              (case mut_impc(prems@[prem1],s,t,mss1,etc1) of
                 (Some(i,prem),trec2) =>
                    let val trec2' = disch1 trec2
                    in if i=0 then mut_impc1(prems,prem,fst trec2',mss,snd trec2')
                       else (Some(i-1,prem),trec2')
                    end
               | (None,trec) => rebuild(trec))
          | _ => rebuild(try_botc mss1 (conc,etc1))

      in let val sg = Sign.deref sign_ref
                  val tsig = #tsig(Sign.rep_sg sg)
                  fun reducible t =
                    exists (fn lhs => Pattern.matches_subterm tsig (lhs,t))
                           lhss1;
              in case dropwhile (not o reducible) prems of
                   [] => simpconc()
                 | red::rest => (trace_term false "Can now reduce premise:" sg
                                            red;
                                 (Some(length rest,prem1),(conc,etc1)))
              end
      end

     (* legacy code - only for backwards compatibility *)
     and nonmut_impc(prem, conc, mss, etc as (_,hyps1,_)) =
       let val (prem1,etc1) = if simprem then try_botc mss (prem,etc)
                              else (prem,etc)
           val maxidx1 = maxidx_of_term prem1
           val mss1 =
             if not useprem then mss else
             if maxidx1 <> ~1
             then (trace_term true "Cannot add premise as rewrite rule because it contains (type) unknowns:"
                              (Sign.deref sign_ref) prem1;
                   mss)
             else let val thm = assume (Cterm{sign_ref=sign_ref, t=prem1, 
                                              T=propT, maxidx= ~1})
                  in add_safe_simp(add_prems(mss,[thm]), thm) end
           val (conc2,(shyps2,hyps2,ders2)) = try_botc mss1 (conc,etc1)
           val hyps2' = if prem1 mem hyps1 then hyps2 else hyps2\prem1
       in (Logic.mk_implies(prem1,conc2), (shyps2, hyps2', ders2)) end

 in try_botc end;


(*** Meta-rewriting: rewrites t to u and returns the theorem t==u ***)

(*
  Parameters:
    mode = (simplify A,
            use A in simplifying B,
            use prems of B (if B is again a meta-impl.) to simplify A)
           when simplifying A ==> B
    mss: contains equality theorems of the form [|p1,...|] ==> t==u
    prover: how to solve premises in conditional rewrites and congruences
*)

(* FIXME: check that #bounds(mss) does not "occur" in ct alread *)

fun rewrite_cterm mode mss prover ct =
  let val Cterm {sign_ref, t, T, maxidx} = ct;
      val (u,(shyps,hyps,ders)) = bottomc (mode,prover, sign_ref, maxidx) mss 
                                          (t, (add_term_sorts(t,[]), [], []));
      val prop = Logic.mk_equals(t,u)
  in
      Thm{sign_ref = sign_ref, 
          der = infer_derivs (Rewrite_cterm ct, ders),
          maxidx = maxidx,
          shyps = shyps, 
          hyps = hyps, 
          prop = prop}
  end;



(*** Oracles ***)

fun invoke_oracle thy raw_name =
  let
    val {sign = sg, oracles, ...} = Theory.rep_theory thy;
    val name = Sign.intern sg Theory.oracleK raw_name;
    val oracle =
      (case Symtab.lookup (oracles, name) of
        None => raise THM ("Unknown oracle: " ^ name, 0, [])
      | Some (f, _) => f);
  in
    fn (sign, exn) =>
      let
        val sign_ref' = Sign.merge_refs (Sign.self_ref sg, Sign.self_ref sign);
        val sign' = Sign.deref sign_ref';
        val (prop, T, maxidx) = Sign.certify_term sign' (oracle (sign', exn));
      in
        if T <> propT then
          raise THM ("Oracle's result must have type prop: " ^ name, 0, [])
        else fix_shyps [] []
          (Thm {sign_ref = sign_ref', 
            der = Join (Oracle (name, sign, exn), []),
            maxidx = maxidx,
            shyps = [], 
            hyps = [], 
            prop = prop})
      end
  end;


end;


structure BasicThm: BASIC_THM = Thm;
open BasicThm;
