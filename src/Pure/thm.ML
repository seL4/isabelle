(*  Title:      Pure/thm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The core of Isabelle's Meta Logic: certified types and terms, meta
theorems, meta rules (including lifting and resolution).
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
  val sign_of_cterm	: cterm -> Sign.sg
  val term_of           : cterm -> term
  val cterm_of          : Sign.sg -> term -> cterm
  val ctyp_of_term      : cterm -> ctyp
  val read_cterm        : Sign.sg -> string * typ -> cterm
  val cterm_fun         : (term -> term) -> (cterm -> cterm)
  val dest_comb         : cterm -> cterm * cterm
  val dest_abs          : string option -> cterm -> cterm * cterm
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
    | Eta_conversion      of cterm
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
  val rep_thm           : thm -> {sign: Sign.sg, der: bool * deriv, maxidx: int,
                                  shyps: sort list, hyps: term list, 
                                  prop: term}
  val crep_thm          : thm -> {sign: Sign.sg, der: bool * deriv, maxidx: int,
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
  val beta_conversion   : bool -> cterm -> thm
  val eta_conversion    : cterm -> thm
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
  val incr_indexes      : int -> thm -> thm
  val assumption        : int -> thm -> thm Seq.seq
  val eq_assumption     : int -> thm -> thm
  val rotate_rule       : int -> int -> thm -> thm
  val permute_prems     : int -> int -> thm -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val bicompose         : bool -> bool * thm * int ->
    int -> thm -> thm Seq.seq
  val biresolution      : bool -> (bool * thm) list ->
    int -> thm -> thm Seq.seq
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
  val rename_boundvars  : term -> term -> thm -> thm
  val cterm_match       : cterm * cterm ->
    (indexname * ctyp) list * (cterm * cterm) list
  val cterm_first_order_match : cterm * cterm ->
    (indexname * ctyp) list * (cterm * cterm) list
  val cterm_incr_indexes : int -> cterm -> cterm
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

fun sign_of_cterm (Cterm {sign_ref, ...}) = Sign.deref sign_ref;

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
fun dest_abs a (Cterm {sign_ref, T as Type("fun",[_,S]), maxidx, t=Abs(x,ty,M)}) = 
      let val (y,N) = variant_abs (if_none a x,ty,M)
      in (Cterm {sign_ref = sign_ref, T = ty, maxidx = 0, t = Free(y,ty)},
          Cterm {sign_ref = sign_ref, T = S, maxidx = maxidx, t = N})
      end
  | dest_abs _ _ = raise CTERM "dest_abs";

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

(*Matching of cterms*)
fun gen_cterm_match mtch
      (Cterm {sign_ref = sign_ref1, maxidx = maxidx1, t = t1, ...},
       Cterm {sign_ref = sign_ref2, maxidx = maxidx2, t = t2, ...}) =
  let
    val sign_ref = Sign.merge_refs (sign_ref1, sign_ref2);
    val tsig = Sign.tsig_of (Sign.deref sign_ref);
    val (Tinsts, tinsts) = mtch tsig (t1, t2);
    val maxidx = Int.max (maxidx1, maxidx2);
    val vars = map dest_Var (term_vars t1);
    fun mk_cTinsts (ixn, T) = (ixn, Ctyp {sign_ref = sign_ref, T = T});
    fun mk_ctinsts (ixn, t) =
      let val T = typ_subst_TVars Tinsts (the (assoc (vars, ixn)))
      in
        (Cterm {sign_ref = sign_ref, maxidx = maxidx, T = T, t = Var (ixn, T)},
         Cterm {sign_ref = sign_ref, maxidx = maxidx, T = T, t = t})
      end;
  in (map mk_cTinsts Tinsts, map mk_ctinsts tinsts) end;

val cterm_match = gen_cterm_match Pattern.match;
val cterm_first_order_match = gen_cterm_match Pattern.first_order_match;

(*Incrementing indexes*)
fun cterm_incr_indexes i (ct as Cterm {sign_ref, maxidx, t, T}) =
  if i < 0 then raise CTERM "negative increment" else 
  if i = 0 then ct else
    Cterm {sign_ref = sign_ref, maxidx = maxidx + i,
      t = Logic.incr_indexes ([], i) t, T = Term.incr_tvar i T};



(** read cterms **)   (*exception ERROR*)

(*read terms, infer types, certify terms*)
fun read_def_cterms (sign, types, sorts) used freeze sTs =
  let
    val (ts', tye) = Sign.read_def_terms (sign, types, sorts) used freeze sTs;
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
  | Eta_conversion      of cterm
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

local

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

fun is_oracle (Oracle _) = true
  | is_oracle _ = false;

in

fun infer_derivs (rl, []: (bool * deriv) list)   = (is_oracle rl, Join (rl, []))
  | infer_derivs (rl, ders) =
      (is_oracle rl orelse exists #1 ders,
        if !keep_derivs=FullDeriv then Join (rl, map #2 ders)
        else make_min_infer (squash_derivs (map #2 ders)));

end;



(*** Meta theorems ***)

datatype thm = Thm of
 {sign_ref: Sign.sg_ref,       (*mutable reference to signature*)
  der: bool * deriv,           (*derivation*)
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

fun eq_thm (th1, th2) =
  let
    val {sign = sg1, shyps = shyps1, hyps = hyps1, prop = prop1, maxidx = _, der = _} =
      rep_thm th1;
    val {sign = sg2, shyps = shyps2, hyps = hyps2, prop = prop2, maxidx = _, der = _} =
      rep_thm th2;
  in
    Sign.joinable (sg1, sg2) andalso
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

fun add_insts_sorts ((iTs, is), Ss) =
  add_typs_sorts (map snd iTs, add_terms_sorts (map snd is, Ss));

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
  (case #2 der of
    Join (Theorem x, _) => x
  | Join (Axiom x, _) => x
  | _ => ("", []));

fun put_name_tags x (Thm {sign_ref, der = (ora, der), maxidx, shyps, hyps, prop}) =
  let
    val der' =
      (case der of
        Join (Theorem _, ds) => Join (Theorem x, ds)
      | Join (Axiom _, ds) => Join (Axiom x, ds)
      | _ => Join (Theorem x, [der]));
  in
    Thm {sign_ref = sign_ref, der = (ora, der'), maxidx = maxidx,
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
fun implies_intr cA (thB as Thm{sign_ref,der,maxidx,hyps,shyps,prop}) : thm =
  let val Cterm {sign_ref=sign_refA, t=A, T, maxidx=maxidxA} = cA
  in  if T<>propT then
        raise THM("implies_intr: assumptions must have type prop", 0, [thB])
      else
         Thm{sign_ref = Sign.merge_refs (sign_ref,sign_refA),  
             der = infer_derivs (Implies_intr cA, [der]),
             maxidx = Int.max(maxidxA, maxidx),
             shyps = add_term_sorts (A, shyps),
             hyps = disch(hyps,A),
             prop = implies$A$prop}
      handle TERM _ =>
        raise THM("implies_intr: incompatible signatures", 0, [thB])
  end;


(*Implication elimination
  A ==> B    A
  ------------
        B
*)
fun implies_elim thAB thA : thm =
    let val Thm{maxidx=maxA, der=derA, hyps=hypsA, shyps=shypsA, prop=propA, ...} = thA
        and Thm{der, maxidx, hyps, shyps, prop, ...} = thAB;
        fun err(a) = raise THM("implies_elim: "^a, 0, [thAB,thA])
    in  case prop of
            imp$A$B =>
                if imp=implies andalso  A aconv propA
                then
                  Thm{sign_ref= merge_thm_sgs(thAB,thA),
                      der = infer_derivs (Implies_elim, [der,derA]),
                      maxidx = Int.max(maxA,maxidx),
                      shyps = union_sort (shypsA, shyps),
                      hyps = union_term(hypsA,hyps),  (*dups suppressed*)
                      prop = B}
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
  in Thm{sign_ref= sign_ref, 
         der = infer_derivs (Reflexive ct, []),
         shyps = add_term_sorts (t, []),
         hyps = [], 
         maxidx = maxidx,
         prop = Logic.mk_equals(t,t)}
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
  let val Thm{der=der1, maxidx=max1, hyps=hyps1, shyps=shyps1, prop=prop1,...} = th1
      and Thm{der=der2, maxidx=max2, hyps=hyps2, shyps=shyps2, prop=prop2,...} = th2;
      fun err(msg) = raise THM("transitive: "^msg, 0, [th1,th2])
  in case (prop1,prop2) of
       ((eq as Const("==",_)) $ t1 $ u, Const("==",_) $ u' $ t2) =>
          if not (u aconv u') then err"middle term"
          else let val thm =      
                 Thm{sign_ref= merge_thm_sgs(th1,th2), 
                     der = infer_derivs (Transitive, [der1, der2]),
                     maxidx = Int.max(max1,max2), 
                     shyps = union_sort (shyps1, shyps2),
                     hyps = union_term(hyps1,hyps2),
                     prop = eq$t1$t2}
                 in if max1 >= 0 andalso max2 >= 0
                    then nodup_vars thm "transitive" 
                    else thm (*no new Vars: no expensive check!*)
                 end
     | _ =>  err"premises"
  end;

(*Beta-conversion: maps (%x.t)(u) to the theorem (%x.t)(u) == t[u/x]
  Fully beta-reduces the term if full=true
*)
fun beta_conversion full ct =
  let val Cterm {sign_ref, t, T, maxidx} = ct
  in Thm
    {sign_ref = sign_ref,  
     der = infer_derivs (Beta_conversion ct, []),
     maxidx = maxidx,
     shyps = add_term_sorts (t, []),
     hyps = [],
     prop = Logic.mk_equals (t, if full then Envir.beta_norm t
       else case t of
          Abs(_, _, bodt) $ u => subst_bound (u, bodt)
        | _ => raise THM ("beta_conversion: not a redex", 0, []))}
  end;

fun eta_conversion ct =
  let val Cterm {sign_ref, t, T, maxidx} = ct
  in Thm
    {sign_ref = sign_ref,  
     der = infer_derivs (Eta_conversion ct, []),
     maxidx = maxidx,
     shyps = add_term_sorts (t, []),
     hyps = [],
     prop = Logic.mk_equals (t, Pattern.eta_contract t)}
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
fun abstract_rule a cx (th as Thm{sign_ref,der,maxidx,hyps,shyps,prop}) =
  let val x = term_of cx;
      val (t,u) = Logic.dest_equals prop
            handle TERM _ =>
                raise THM("abstract_rule: premise not an equality", 0, [th])
      fun result T =
           Thm{sign_ref = sign_ref,
               der = infer_derivs (Abstract_rule (a,cx), [der]),
               maxidx = maxidx, 
               shyps = add_typ_sorts (T, shyps), 
               hyps = hyps,
               prop = Logic.mk_equals(Abs(a, T, abstract_over (x,t)),
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
  f == g  t == u
  --------------
   f(t) == g(u)
*)
fun combination th1 th2 =
  let val Thm{der=der1, maxidx=max1, shyps=shyps1, hyps=hyps1, 
              prop=prop1,...} = th1
      and Thm{der=der2, maxidx=max2, shyps=shyps2, hyps=hyps2, 
              prop=prop2,...} = th2
      fun chktypes fT tT =
            (case fT of
                Type("fun",[T1,T2]) => 
                    if T1 <> tT then
                         raise THM("combination: types", 0, [th1,th2])
                    else ()
                | _ => raise THM("combination: not function type", 0, 
                                 [th1,th2]))
  in case (prop1,prop2)  of
       (Const ("==", Type ("fun", [fT, _])) $ f $ g,
        Const ("==", Type ("fun", [tT, _])) $ t $ u) =>
          let val _   = chktypes fT tT
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
  | instantiate (vcTs,ctpairs) (th as Thm{sign_ref,der,maxidx,hyps,shyps,prop}) =
  let val (newsign_ref,tpairs) = foldr add_ctpair (ctpairs, (sign_ref,[]));
      val (newsign_ref,vTs) = foldr add_ctyp (vcTs, (newsign_ref,[]));
      val newprop = subst_atomic tpairs
	             (Type.inst_term_tvars
		      (Sign.tsig_of (Sign.deref newsign_ref),vTs) prop)
      val newth =
            (Thm{sign_ref = newsign_ref, 
                 der = infer_derivs (Instantiate(vcTs,ctpairs), [der]), 
                 maxidx = maxidx_of_term newprop, 
                 shyps = add_insts_sorts ((vTs, tpairs), shyps),
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

fun incr_indexes i (thm as Thm {sign_ref, der, maxidx, shyps, hyps, prop}) =
  if i < 0 then raise THM ("negative increment", 0, [thm]) else
  if i = 0 then thm else
    Thm {sign_ref = sign_ref,
         der = der,
         maxidx = maxidx + i,
         shyps = shyps,
         hyps = hyps,
         prop = Logic.incr_indexes ([], i) prop};

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

fun rename_boundvars pat obj (thm as Thm {sign_ref,der,maxidx,hyps,shyps,prop}) =
  let val ren = match_bvs (pat, obj, [])
      fun renAbs (Abs (x, T, b)) =
            Abs (if_none (assoc_string (ren, x)) x, T, renAbs b)
        | renAbs (f $ t) = renAbs f $ renAbs t
        | renAbs t = t
  in if null ren then thm else Thm
    {sign_ref = sign_ref,
     der = der,
     maxidx = maxidx,
     hyps = hyps,
     shyps = shyps,
     prop = renAbs prop}
  end;


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
              Abs(if_none(assoc_string(al,x)) x, T, rename t)
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
            der = (true, Join (Oracle (name, sign, exn), [])),
            maxidx = maxidx,
            shyps = [], 
            hyps = [], 
            prop = prop})
      end
  end;


end;


structure BasicThm: BASIC_THM = Thm;
open BasicThm;
