(*  Title:      Pure/thm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The core of Isabelle's Meta Logic: certified types and terms, meta
theorems, meta rules (including resolution and simplification).
*)

signature THM =
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
  val rep_cterm         : cterm -> {sign: Sign.sg, t: term, T: typ,
                                    maxidx: int}
  val term_of           : cterm -> term
  val cterm_of          : Sign.sg -> term -> cterm
  val ctyp_of_term      : cterm -> ctyp
  val read_cterm        : Sign.sg -> string * typ -> cterm
  val read_cterms       : Sign.sg -> string list * typ list -> cterm list
  val cterm_fun         : (term -> term) -> (cterm -> cterm)
  val dest_comb         : cterm -> cterm * cterm
  val dest_abs          : cterm -> cterm * cterm
  val adjust_maxidx     : cterm -> cterm
  val capply            : cterm -> cterm -> cterm
  val cabs              : cterm -> cterm -> cterm
  val read_def_cterm    :
    Sign.sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> string * typ -> cterm * (indexname * typ) list

  (*theories*)

  (*proof terms [must DUPLICATE declaration as a specification]*)
  datatype deriv_kind = MinDeriv | ThmDeriv | FullDeriv;
  val keep_derivs       : deriv_kind ref
  datatype rule = 
      MinProof                          
    | Oracle of theory * Sign.sg * exn
    | Axiom               of theory * string
    | Theorem             of string       
    | Assume              of cterm
    | Implies_intr        of cterm
    | Implies_intr_shyps
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
    | Instantiate         of (indexname * ctyp) list * (cterm * cterm) list
    | Bicompose           of bool * bool * int * int * Envir.env
    | Flexflex_rule       of Envir.env            
    | Class_triv          of theory * class       
    | VarifyT
    | FreezeT
    | RewriteC            of cterm
    | CongC               of cterm
    | Rewrite_cterm       of cterm
    | Rename_params_rule  of string list * int;

  type deriv   (* = rule mtree *)

  (*meta theorems*)
  type thm
  exception THM of string * int * thm list
  val rep_thm           : thm -> {sign: Sign.sg, der: deriv, maxidx: int,
                                  shyps: sort list, hyps: term list, 
                                  prop: term}
  val crep_thm          : thm -> {sign: Sign.sg, der: deriv, maxidx: int,
                                  shyps: sort list, hyps: cterm list, 
                                  prop: cterm}
  val stamps_of_thm     : thm -> string ref list
  val tpairs_of         : thm -> (term * term) list
  val prems_of          : thm -> term list
  val nprems_of         : thm -> int
  val concl_of          : thm -> term
  val cprop_of          : thm -> cterm
  val extra_shyps       : thm -> sort list
  val force_strip_shyps : bool ref      (* FIXME tmp *)
  val strip_shyps       : thm -> thm
  val implies_intr_shyps: thm -> thm
  val get_axiom         : theory -> string -> thm
  val name_thm          : string * thm -> thm
  val axioms_of         : theory -> (string * thm) list

  (*meta rules*)
  val assume            : cterm -> thm
  val compress          : thm -> thm
  val implies_intr      : cterm -> thm -> thm
  val implies_elim      : thm -> thm -> thm
  val forall_intr       : cterm -> thm -> thm
  val forall_elim       : cterm -> thm -> thm
  val flexpair_def      : thm
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
  val flexflex_rule     : thm -> thm Sequence.seq
  val instantiate       :
    (indexname * ctyp) list * (cterm * cterm) list -> thm -> thm
  val trivial           : cterm -> thm
  val class_triv        : theory -> class -> thm
  val varifyT           : thm -> thm
  val freezeT           : thm -> thm
  val dest_state        : thm * int ->
    (term * term) list * term list * term * term
  val lift_rule         : (thm * int) -> thm -> thm
  val assumption        : int -> thm -> thm Sequence.seq
  val eq_assumption     : int -> thm -> thm
  val rotate_rule       : int -> int -> thm -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val bicompose         : bool -> bool * thm * int ->
    int -> thm -> thm Sequence.seq
  val biresolution      : bool -> (bool * thm) list ->
    int -> thm -> thm Sequence.seq

  (*meta simplification*)
  type meta_simpset
  exception SIMPLIFIER of string * thm
  val empty_mss         : meta_simpset
  val add_simps         : meta_simpset * thm list -> meta_simpset
  val del_simps         : meta_simpset * thm list -> meta_simpset
  val mss_of            : thm list -> meta_simpset
  val add_congs         : meta_simpset * thm list -> meta_simpset
  val del_congs         : meta_simpset * thm list -> meta_simpset
  val add_simprocs	: meta_simpset *
    (Sign.sg * term * (Sign.sg -> term -> thm option) * stamp) list -> meta_simpset
  val del_simprocs	: meta_simpset *
    (Sign.sg * term * (Sign.sg -> term -> thm option) * stamp) list -> meta_simpset
  val add_prems         : meta_simpset * thm list -> meta_simpset
  val prems_of_mss      : meta_simpset -> thm list
  val set_mk_rews       : meta_simpset * (thm -> thm list) -> meta_simpset
  val mk_rews_of_mss    : meta_simpset -> thm -> thm list
  val set_termless      : meta_simpset * (term * term -> bool) -> meta_simpset
  val trace_simp        : bool ref
  val rewrite_cterm     : bool * bool -> meta_simpset ->
                          (meta_simpset -> thm -> thm option) -> cterm -> thm

  val invoke_oracle     : theory * Sign.sg * exn -> thm
end;

structure Thm : THM =
struct

(*** Certified terms and types ***)

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

fun ctyp_of_term (Cterm {sign, T, ...}) = Ctyp {sign=sign, T=T};

(*create a cterm by checking a "raw" term with respect to a signature*)
fun cterm_of sign tm =
  let val (t, T, maxidx) = Sign.certify_term sign tm
  in  Cterm {sign = sign, t = t, T = T, maxidx = maxidx}
  end;

fun cterm_fun f (Cterm {sign, t, ...}) = cterm_of sign (f t);


exception CTERM of string;

(*Destruct application in cterms*)
fun dest_comb (Cterm{sign, T, maxidx, t = A $ B}) =
      let val typeA = fastype_of A;
          val typeB =
            case typeA of Type("fun",[S,T]) => S
                        | _ => error "Function type expected in dest_comb";
      in
      (Cterm {sign=sign, maxidx=maxidx, t=A, T=typeA},
       Cterm {sign=sign, maxidx=maxidx, t=B, T=typeB})
      end
  | dest_comb _ = raise CTERM "dest_comb";

(*Destruct abstraction in cterms*)
fun dest_abs (Cterm {sign, T as Type("fun",[_,S]), maxidx, t=Abs(x,ty,M)}) = 
      let val (y,N) = variant_abs (x,ty,M)
      in (Cterm {sign = sign, T = ty, maxidx = 0, t = Free(y,ty)},
          Cterm {sign = sign, T = S, maxidx = maxidx, t = N})
      end
  | dest_abs _ = raise CTERM "dest_abs";

(*Makes maxidx precise: it is often too big*)
fun adjust_maxidx (ct as Cterm {sign, T, t, maxidx, ...}) =
  if maxidx = ~1 then ct 
  else  Cterm {sign = sign, T = T, maxidx = maxidx_of_term t, t = t};

(*Form cterm out of a function and an argument*)
fun capply (Cterm {t=f, sign=sign1, T=Type("fun",[dty,rty]), maxidx=maxidx1})
           (Cterm {t=x, sign=sign2, T, maxidx=maxidx2}) =
      if T = dty then Cterm{t=f$x, sign=Sign.merge(sign1,sign2), T=rty,
                            maxidx=Int.max(maxidx1, maxidx2)}
      else raise CTERM "capply: types don't agree"
  | capply _ _ = raise CTERM "capply: first arg is not a function"

fun cabs (Cterm {t=Free(a,ty), sign=sign1, T=T1, maxidx=maxidx1})
         (Cterm {t=t2, sign=sign2, T=T2, maxidx=maxidx2}) =
      Cterm {t=absfree(a,ty,t2), sign=Sign.merge(sign1,sign2),
             T = ty --> T2, maxidx=Int.max(maxidx1, maxidx2)}
  | cabs _ _ = raise CTERM "cabs: first arg is not a free variable";



(** read cterms **)   (*exception ERROR*)

(*read term, infer types, certify term*)
fun read_def_cterm (sign, types, sorts) used freeze (a, T) =
  let
    val T' = Sign.certify_typ sign T
      handle TYPE (msg, _, _) => error msg;
    val ts = Syntax.read (#syn (Sign.rep_sg sign)) T' a;
    val (_, t', tye) =
          Sign.infer_types sign types sorts used freeze (ts, T');
    val ct = cterm_of sign t'
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in (ct, tye) end;

fun read_cterm sign = #1 o read_def_cterm (sign, K None, K None) [] true;

(*read a list of terms, matching them against a list of expected types.
  NO disambiguation of alternative parses via type-checking -- it is just
  not practical.*)
fun read_cterms sign (bs, Ts) =
  let
    val {tsig, syn, ...} = Sign.rep_sg sign;
    fun read (b, T) =
      (case Syntax.read syn T b of
        [t] => t
      | _  => error ("Error or ambiguity in parsing of " ^ b));

    val prt = setmp Syntax.show_brackets true (Sign.pretty_term sign);
    val prT = Sign.pretty_typ sign;
    val (us, _) =
      Type.infer_types prt prT tsig (Sign.const_type sign)
        (K None) (K None) [] true (map (Sign.certify_typ sign) Ts)
        (ListPair.map read (bs, Ts));
  in map (cterm_of sign) us end
  handle TYPE (msg, _, _) => error msg
       | TERM (msg, _) => error msg;



(*** Derivations ***)

(*Names of rules in derivations.  Includes logically trivial rules, if 
  executed in ML.*)
datatype rule = 
    MinProof                            (*for building minimal proof terms*)
  | Oracle              of theory * Sign.sg * exn       (*oracles*)
(*Axioms/theorems*)
  | Axiom               of theory * string
  | Theorem             of string
(*primitive inferences and compound versions of them*)
  | Assume              of cterm
  | Implies_intr        of cterm
  | Implies_intr_shyps
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
  | Instantiate         of (indexname * ctyp) list * (cterm * cterm) list
  | Bicompose           of bool * bool * int * int * Envir.env
  | Flexflex_rule       of Envir.env            (*identifies unifier chosen*)
(*other derived rules*)
  | Class_triv          of theory * class
  | VarifyT
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
  {sign: Sign.sg,               (*signature for hyps and prop*)
   der: deriv,                  (*derivation*)
   maxidx: int,                 (*maximum index of any Var or TVar*)
   shyps: sort list,            (*sort hypotheses*)
   hyps: term list,             (*hypotheses*)
   prop: term};                 (*conclusion*)

fun rep_thm (Thm args) = args;

(*Version of rep_thm returning cterms instead of terms*)
fun crep_thm (Thm {sign, der, maxidx, shyps, hyps, prop}) =
  let fun ctermf max t = Cterm{sign=sign, t=t, T=propT, maxidx=max};
  in {sign=sign, der=der, maxidx=maxidx, shyps=shyps,
      hyps = map (ctermf ~1) hyps,
      prop = ctermf maxidx prop}
  end;

(*errors involving theorems*)
exception THM of string * int * thm list;


val stamps_of_thm = #stamps o Sign.rep_sg o #sign o rep_thm;

(*merge signatures of two theorems; raise exception if incompatible*)
fun merge_thm_sgs (th1, th2) =
  Sign.merge (pairself (#sign o rep_thm) (th1, th2))
    handle TERM (msg, _) => raise THM (msg, 0, [th1, th2]);


(*maps object-rule to tpairs*)
fun tpairs_of (Thm {prop, ...}) = #1 (Logic.strip_flexpairs prop);

(*maps object-rule to premises*)
fun prems_of (Thm {prop, ...}) =
  Logic.strip_imp_prems (Logic.skip_flexpairs prop);

(*counts premises in a rule*)
fun nprems_of (Thm {prop, ...}) =
  Logic.count_prems (Logic.skip_flexpairs prop, 0);

(*maps object-rule to conclusion*)
fun concl_of (Thm {prop, ...}) = Logic.strip_imp_concl prop;

(*the statement of any thm is a cterm*)
fun cprop_of (Thm {sign, maxidx, prop, ...}) =
  Cterm {sign = sign, maxidx = maxidx, T = propT, t = prop};



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

fun env_codT (Envir.Envir {iTs, ...}) = map snd iTs;

fun add_env_sorts (env, Ss) =
  add_terms_sorts (map snd (Envir.alist_of env),
    add_typs_sorts (env_codT env, Ss));

fun add_thm_sorts (Thm {hyps, prop, ...}, Ss) =
  add_terms_sorts (hyps, add_term_sorts (prop, Ss));

fun add_thms_shyps ([], Ss) = Ss
  | add_thms_shyps (Thm {shyps, ...} :: ths, Ss) =
      add_thms_shyps (ths, union_sort(shyps,Ss));


(*get 'dangling' sort constraints of a thm*)
fun extra_shyps (th as Thm {shyps, ...}) =
  shyps \\ add_thm_sorts (th, []);


(* fix_shyps *)

(*preserve sort contexts of rule premises and substituted types*)
fun fix_shyps thms Ts thm =
  let
    val Thm {sign, der, maxidx, hyps, prop, ...} = thm;
    val shyps =
      add_thm_sorts (thm, add_typs_sorts (Ts, add_thms_shyps (thms, [])));
  in
    Thm {sign = sign, 
         der = der,             (*No new derivation, as other rules call this*)
         maxidx = maxidx,
         shyps = shyps, hyps = hyps, prop = prop}
  end;


(* strip_shyps *)       (* FIXME improve? (e.g. only minimal extra sorts) *)

val force_strip_shyps = ref true;  (* FIXME tmp *)

(*remove extra sorts that are known to be syntactically non-empty*)
fun strip_shyps thm =
  let
    val Thm {sign, der, maxidx, shyps, hyps, prop} = thm;
    val sorts = add_thm_sorts (thm, []);
    val maybe_empty = not o Sign.nonempty_sort sign sorts;
    val shyps' = filter (fn S => mem_sort(S,sorts) orelse maybe_empty S) shyps;
  in
    Thm {sign = sign, der = der, maxidx = maxidx,
         shyps =
         (if eq_set_sort (shyps',sorts) orelse 
             not (!force_strip_shyps) then shyps'
          else    (* FIXME tmp *)
              (warning ("Removed sort hypotheses: " ^
                        commas (map Sorts.str_of_sort (shyps' \\ sorts)));
               warning "Let's hope these sorts are non-empty!";
           sorts)),
      hyps = hyps, 
      prop = prop}
  end;


(* implies_intr_shyps *)

(*discharge all extra sort hypotheses*)
fun implies_intr_shyps thm =
  (case extra_shyps thm of
    [] => thm
  | xshyps =>
      let
        val Thm {sign, der, maxidx, shyps, hyps, prop} = thm;
        val shyps' = ins_sort (logicS, shyps \\ xshyps);
        val used_names = foldr add_term_tfree_names (prop :: hyps, []);
        val names =
          tl (variantlist (replicate (length xshyps + 1) "'", used_names));
        val tfrees = map (TFree o rpair logicS) names;

        fun mk_insort (T, S) = map (Logic.mk_inclass o pair T) S;
        val sort_hyps = List.concat (map2 mk_insort (tfrees, xshyps));
      in
        Thm {sign = sign, 
             der = infer_derivs (Implies_intr_shyps, [der]), 
             maxidx = maxidx, 
             shyps = shyps',
             hyps = hyps, 
             prop = Logic.list_implies (sort_hyps, prop)}
      end);


(** Axioms **)

(*look up the named axiom in the theory*)
fun get_axiom theory name =
  let
    fun get_ax [] = raise Match
      | get_ax (thy :: thys) =
          let val {sign, new_axioms, parents, ...} = rep_theory thy
          in case Symtab.lookup (new_axioms, name) of
                Some t => fix_shyps [] []
                           (Thm {sign = sign, 
                                 der = infer_derivs (Axiom(theory,name), []),
                                 maxidx = maxidx_of_term t,
                                 shyps = [], 
                                 hyps = [], 
                                 prop = t})
              | None => get_ax parents handle Match => get_ax thys
          end;
  in
    get_ax [theory] handle Match
      => raise THEORY ("get_axiom: no axiom " ^ quote name, [theory])
  end;


(*return additional axioms of this theory node*)
fun axioms_of thy =
  map (fn (s, _) => (s, get_axiom thy s))
    (Symtab.dest (#new_axioms (rep_theory thy)));

(*Attach a label to a theorem to make proof objects more readable*)
fun name_thm (name, th as Thm {sign, der, maxidx, shyps, hyps, prop}) = 
    Thm {sign = sign, 
         der = Join (Theorem name, [der]),
         maxidx = maxidx,
         shyps = shyps, 
         hyps = hyps, 
         prop = prop};


(*Compression of theorems -- a separate rule, not integrated with the others,
  as it could be slow.*)
fun compress (Thm {sign, der, maxidx, shyps, hyps, prop}) = 
    Thm {sign = sign, 
         der = der,     (*No derivation recorded!*)
         maxidx = maxidx,
         shyps = shyps, 
         hyps = map Term.compress_term hyps, 
         prop = Term.compress_term prop};



(*** Meta rules ***)

(*Check that term does not contain same var with different typing/sorting.
  If this check must be made, recalculate maxidx in hope of preventing its
  recurrence.*)
fun nodup_Vars (thm as Thm{sign, der, maxidx, shyps, hyps, prop}) s =
  (Sign.nodup_Vars prop; 
   Thm {sign = sign, 
         der = der,     
         maxidx = maxidx_of_term prop,
         shyps = shyps, 
         hyps = hyps, 
         prop = prop})
  handle TYPE(msg,Ts,ts) => raise TYPE(s^": "^msg,Ts,ts);

(** 'primitive' rules **)

(*discharge all assumptions t from ts*)
val disch = gen_rem (op aconv);

(*The assumption rule A|-A in a theory*)
fun assume ct : thm =
  let val {sign, t=prop, T, maxidx} = rep_cterm ct
  in  if T<>propT then
        raise THM("assume: assumptions must have type prop", 0, [])
      else if maxidx <> ~1 then
        raise THM("assume: assumptions may not contain scheme variables",
                  maxidx, [])
      else Thm{sign   = sign, 
               der    = infer_derivs (Assume ct, []), 
               maxidx = ~1, 
               shyps  = add_term_sorts(prop,[]), 
               hyps   = [prop], 
               prop   = prop}
  end;

(*Implication introduction
  A |- B
  -------
  A ==> B
*)
fun implies_intr cA (thB as Thm{sign,der,maxidx,hyps,prop,...}) : thm =
  let val {sign=signA, t=A, T, maxidx=maxidxA} = rep_cterm cA
  in  if T<>propT then
        raise THM("implies_intr: assumptions must have type prop", 0, [thB])
      else fix_shyps [thB] []
        (Thm{sign = Sign.merge (sign,signA),  
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
        and Thm{sign, der, maxidx, hyps, prop,...} = thAB;
        fun err(a) = raise THM("implies_elim: "^a, 0, [thAB,thA])
    in  case prop of
            imp$A$B =>
                if imp=implies andalso  A aconv propA
                then fix_shyps [thAB, thA] []
                       (Thm{sign= merge_thm_sgs(thAB,thA),
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
fun forall_intr cx (th as Thm{sign,der,maxidx,hyps,prop,...}) =
  let val x = term_of cx;
      fun result(a,T) = fix_shyps [th] []
        (Thm{sign = sign, 
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
fun forall_elim ct (th as Thm{sign,der,maxidx,hyps,prop,...}) : thm =
  let val {sign=signt, t, T, maxidx=maxt} = rep_cterm ct
  in  case prop of
        Const("all",Type("fun",[Type("fun",[qary,_]),_])) $ A =>
          if T<>qary then
              raise THM("forall_elim: type mismatch", 0, [th])
          else let val thm = fix_shyps [th] []
                    (Thm{sign= Sign.merge(sign,signt),
                         der = infer_derivs (Forall_elim ct, [der]),
                         maxidx = Int.max(maxidx, maxt),
                         shyps = [],
                         hyps = hyps,  
                         prop = betapply(A,t)})
               in if maxt >= 0 andalso maxidx >= 0
                  then nodup_Vars thm "forall_elim" 
                  else thm (*no new Vars: no expensive check!*)
               end
      | _ => raise THM("forall_elim: not quantified", 0, [th])
  end
  handle TERM _ =>
         raise THM("forall_elim: incompatible signatures", 0, [th]);


(* Equality *)

(* Definition of the relation =?= *)
val flexpair_def = fix_shyps [] []
  (Thm{sign= Sign.proto_pure, 
       der = Join(Axiom(pure_thy, "flexpair_def"), []),
       shyps = [], 
       hyps = [], 
       maxidx = 0,
       prop = term_of (read_cterm Sign.proto_pure
                       ("(?t =?= ?u) == (?t == ?u::?'a::{})", propT))});

(*The reflexivity rule: maps  t   to the theorem   t==t   *)
fun reflexive ct =
  let val {sign, t, T, maxidx} = rep_cterm ct
  in  fix_shyps [] []
       (Thm{sign= sign, 
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
fun symmetric (th as Thm{sign,der,maxidx,shyps,hyps,prop}) =
  case prop of
      (eq as Const("==",_)) $ t $ u =>
        (*no fix_shyps*)
          Thm{sign = sign,
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
                (Thm{sign= merge_thm_sgs(th1,th2), 
                     der = infer_derivs (Transitive, [der1, der2]),
                     maxidx = Int.max(max1,max2), 
                     shyps = [],
                     hyps = union_term(hyps1,hyps2),
                     prop = eq$t1$t2})
                 in if max1 >= 0 andalso max2 >= 0
                    then nodup_Vars thm "transitive" 
                    else thm (*no new Vars: no expensive check!*)
                 end
     | _ =>  err"premises"
  end;

(*Beta-conversion: maps (%x.t)(u) to the theorem (%x.t)(u) == t[u/x] *)
fun beta_conversion ct =
  let val {sign, t, T, maxidx} = rep_cterm ct
  in  case t of
          Abs(_,_,bodt) $ u => fix_shyps [] []
            (Thm{sign = sign,  
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
fun extensional (th as Thm{sign, der, maxidx,shyps,hyps,prop}) =
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
          Thm{sign = sign,
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
fun abstract_rule a cx (th as Thm{sign,der,maxidx,hyps,prop,...}) =
  let val x = term_of cx;
      val (t,u) = Logic.dest_equals prop
            handle TERM _ =>
                raise THM("abstract_rule: premise not an equality", 0, [th])
      fun result T = fix_shyps [th] []
          (Thm{sign = sign,
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
  f==g    t==u
  ------------
   f(t)==g(u)
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
                        Thm{sign = merge_thm_sgs(th1,th2), 
                            der = infer_derivs (Combination, [der1, der2]),
                            maxidx = Int.max(max1,max2), 
                            shyps = union_sort(shyps1,shyps2),
                            hyps = union_term(hyps1,hyps2),
                            prop = Logic.mk_equals(f$t, g$u)}
          in if max1 >= 0 andalso max2 >= 0
             then nodup_Vars thm "combination" 
             else thm (*no new Vars: no expensive check!*)  
          end
     | _ =>  raise THM("combination: premises", 0, [th1,th2])
  end;


(* Equality introduction
  A==>B    B==>A
  --------------
       A==B
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
              Thm{sign = merge_thm_sgs(th1,th2),
                  der = infer_derivs (Equal_intr, [der1, der2]),
                  maxidx = Int.max(max1,max2),
                  shyps = union_sort(shyps1,shyps2),
                  hyps = union_term(hyps1,hyps2),
                  prop = Logic.mk_equals(A,B)}
          else err"not equal"
     | _ =>  err"premises"
  end;


(*The equal propositions rule
  A==B    A
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
              (Thm{sign= merge_thm_sgs(th1,th2), 
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
fun implies_intr_hyps (Thm{sign, der, maxidx, shyps, hyps=A::As, prop}) =
      implies_intr_hyps (*no fix_shyps*)
            (Thm{sign = sign, 
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
fun flexflex_rule (th as Thm{sign, der, maxidx, hyps, prop,...}) =
  let fun newthm env =
          if Envir.is_empty env then th
          else
          let val (tpairs,horn) =
                        Logic.strip_flexpairs (Envir.norm_term env prop)
                (*Remove trivial tpairs, of the form t=t*)
              val distpairs = filter (not o op aconv) tpairs
              val newprop = Logic.list_flexpairs(distpairs, horn)
          in  fix_shyps [th] (env_codT env)
                (Thm{sign = sign, 
                     der = infer_derivs (Flexflex_rule env, [der]), 
                     maxidx = maxidx_of_term newprop, 
                     shyps = [], 
                     hyps = hyps,
                     prop = newprop})
          end;
      val (tpairs,_) = Logic.strip_flexpairs prop
  in Sequence.maps newthm
            (Unify.smash_unifiers(sign, Envir.empty maxidx, tpairs))
  end;

(*Instantiation of Vars
           A
  -------------------
  A[t1/v1,....,tn/vn]
*)

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
fun instantiate ([], []) th = th
  | instantiate (vcTs,ctpairs)  (th as Thm{sign,der,maxidx,hyps,prop,...}) =
  let val (newsign,tpairs) = foldr add_ctpair (ctpairs, (sign,[]));
      val (newsign,vTs) = foldr add_ctyp (vcTs, (newsign,[]));
      val newprop =
            Envir.norm_term (Envir.empty 0)
              (subst_atomic tpairs
               (Type.inst_term_tvars(#tsig(Sign.rep_sg newsign),vTs) prop))
      val newth =
            fix_shyps [th] (map snd vTs)
              (Thm{sign = newsign, 
                   der = infer_derivs (Instantiate(vcTs,ctpairs), [der]), 
                   maxidx = maxidx_of_term newprop, 
                   shyps = [],
                   hyps = hyps,
                   prop = newprop})
  in  if not(instl_ok(map #1 tpairs))
      then raise THM("instantiate: variables not distinct", 0, [th])
      else if not(null(findrep(map #1 vTs)))
      then raise THM("instantiate: type variables not distinct", 0, [th])
      else nodup_Vars newth "instantiate"
  end
  handle TERM _ =>
           raise THM("instantiate: incompatible signatures",0,[th])
       | TYPE (msg,_,_) => raise THM("instantiate: type conflict: " ^ msg, 
				     0, [th]);

(*The trivial implication A==>A, justified by assume and forall rules.
  A can contain Vars, not so for assume!   *)
fun trivial ct : thm =
  let val {sign, t=A, T, maxidx} = rep_cterm ct
  in  if T<>propT then
            raise THM("trivial: the term must have type prop", 0, [])
      else fix_shyps [] []
        (Thm{sign = sign, 
             der = infer_derivs (Trivial ct, []), 
             maxidx = maxidx, 
             shyps = [], 
             hyps = [],
             prop = implies$A$A})
  end;

(*Axiom-scheme reflecting signature contents: "OFCLASS(?'a::c, c_class)" *)
fun class_triv thy c =
  let val sign = sign_of thy;
      val Cterm {t, maxidx, ...} =
          cterm_of sign (Logic.mk_inclass (TVar (("'a", 0), [c]), c))
            handle TERM (msg, _) => raise THM ("class_triv: " ^ msg, 0, []);
  in
    fix_shyps [] []
      (Thm {sign = sign, 
            der = infer_derivs (Class_triv(thy,c), []), 
            maxidx = maxidx, 
            shyps = [], 
            hyps = [], 
            prop = t})
  end;


(* Replace all TFrees not in the hyps by new TVars *)
fun varifyT(Thm{sign,der,maxidx,shyps,hyps,prop}) =
  let val tfrees = foldr add_term_tfree_names (hyps,[])
  in let val thm = (*no fix_shyps*)
    Thm{sign = sign, 
        der = infer_derivs (VarifyT, [der]), 
        maxidx = Int.max(0,maxidx), 
        shyps = shyps, 
        hyps = hyps,
        prop = Type.varify(prop,tfrees)}
     in nodup_Vars thm "varifyT" end
(* this nodup_Vars check can be removed if thms are guaranteed not to contain
duplicate TVars with differnt sorts *)
  end;

(* Replace all TVars by new TFrees *)
fun freezeT(Thm{sign,der,maxidx,shyps,hyps,prop}) =
  let val prop' = Type.freeze prop
  in (*no fix_shyps*)
    Thm{sign = sign, 
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
  let val Thm{shyps=sshyps, prop=sprop, maxidx=smax, sign=ssign,...} = state
      val (Bi::_, _) = Logic.strip_prems(i, [], Logic.skip_flexpairs sprop)
        handle TERM _ => raise THM("lift_rule", i, [orule,state])
      val ct_Bi = Cterm {sign=ssign, maxidx=smax, T=propT, t=Bi}
      val (lift_abs,lift_all) = Logic.lift_fns(Bi,smax+1)
      val (Thm{sign, der, maxidx,shyps,hyps,prop}) = orule
      val (tpairs,As,B) = Logic.strip_horn prop
  in  (*no fix_shyps*)
      Thm{sign = merge_thm_sgs(state,orule),
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
  let val Thm{sign,der,maxidx,hyps,prop,...} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      fun newth (env as Envir.Envir{maxidx, ...}, tpairs) =
        fix_shyps [state] (env_codT env)
          (Thm{sign = sign, 
               der = infer_derivs (Assumption (i, Some env), [der]),
               maxidx = maxidx,
               shyps = [],
               hyps = hyps,
               prop = 
               if Envir.is_empty env then (*avoid wasted normalizations*)
                   Logic.rule_of (tpairs, Bs, C)
               else (*normalize the new rule fully*)
                   Envir.norm_term env (Logic.rule_of (tpairs, Bs, C))});
      fun addprfs [] = Sequence.null
        | addprfs ((t,u)::apairs) = Sequence.seqof (fn()=> Sequence.pull
             (Sequence.mapp newth
                (Unify.unifiers(sign,Envir.empty maxidx, (t,u)::tpairs))
                (addprfs apairs)))
  in  addprfs (Logic.assum_pairs Bi)  end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha-convertible to one of its assumptions*)
fun eq_assumption i state =
  let val Thm{sign,der,maxidx,hyps,prop,...} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
  in  if exists (op aconv) (Logic.assum_pairs Bi)
      then fix_shyps [state] []
             (Thm{sign = sign, 
                  der = infer_derivs (Assumption (i,None), [der]),
                  maxidx = maxidx,
                  shyps = [],
                  hyps = hyps,
                  prop = Logic.rule_of(tpairs, Bs, C)})
      else  raise THM("eq_assumption", 0, [state])
  end;


(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let val Thm{sign,der,maxidx,hyps,prop,shyps} = state;
      val (tpairs, Bs, Bi, C) = dest_state(state,i)
      val params = Logic.strip_params Bi
      and asms   = Logic.strip_assums_hyp Bi
      and concl  = Logic.strip_assums_concl Bi
      val n      = length asms
      fun rot m  = if 0=m orelse m=n then Bi
		   else if 0<m andalso m<n 
		   then list_all 
			   (params, 
			    Logic.list_implies(List.drop(asms, m) @ 
					       List.take(asms, m),
					       concl))
		   else raise THM("rotate_rule", m, [state])
  in  Thm{sign = sign, 
	  der = infer_derivs (Rotate_rule (k,i), [der]),
	  maxidx = maxidx,
	  shyps = shyps,
	  hyps = hyps,
	  prop = Logic.rule_of(tpairs, Bs@[rot (if k<0 then n+k else k)], C)}
  end;


(** User renaming of parameters in a subgoal **)

(*Calls error rather than raising an exception because it is intended
  for top-level use -- exception handling would not make sense here.
  The names in cs, if distinct, are used for the innermost parameters;
   preceding parameters may be renamed to make all params distinct.*)
fun rename_params_rule (cs, i) state =
  let val Thm{sign,der,maxidx,hyps,prop,...} = state
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
   | [] => (case cs inter_string freenames of
       a::_ => error ("Bound/Free variable clash: " ^ a)
     | [] => fix_shyps [state] []
                (Thm{sign = sign,
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
            val T' = typ_subst_TVars iTs T
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
local open Sequence; exception COMPOSE
in
fun bicompose_aux match (state, (stpairs, Bs, Bi, C), lifted)
                        (eres_flg, orule, nsubgoal) =
 let val Thm{der=sder, maxidx=smax, shyps=sshyps, hyps=shyps, ...} = state
     and Thm{der=rder, maxidx=rmax, shyps=rshyps, hyps=rhyps, 
             prop=rprop,...} = orule
         (*How many hyps to skip over during normalization*)
     and nlift = Logic.count_prems(strip_all_body Bi,
                                   if eres_flg then ~1 else 0)
     val sign = merge_thm_sgs(state,orule);
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
             Thm{sign = sign,
                 der = infer_derivs (Bicompose(match, eres_flg,
                                               1 + length Bs, nsubgoal, env),
                                     [rder,sder]),
                 maxidx = maxidx,
                 shyps = add_env_sorts (env, union_sort(rshyps,sshyps)),
                 hyps = union_term(rhyps,shyps),
                 prop = Logic.rule_of normp}
        in  cons(th, thq)  end  handle COMPOSE => thq
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
              then Sequence.seqof (*delay processing remainder till needed*)
                  (fn()=> Some(comp (eres_flg, lift rule, nprems_of rule),
                               res brules))
              else res brules
    in  Sequence.flats (res brules)  end;



(*** Meta Simplification ***)

(** diagnostics **)

exception SIMPLIFIER of string * thm;

fun prtm a sign t = (writeln a; writeln (Sign.string_of_term sign t));
fun prtm_warning a sign t = warning (a ^ "\n" ^ (Sign.string_of_term sign t));

val trace_simp = ref false;

fun trace_warning a = if ! trace_simp then warning a else ();
fun trace_term a sign t = if ! trace_simp then prtm a sign t else ();
fun trace_term_warning a sign t = if ! trace_simp then prtm_warning a sign t else ();
fun trace_thm a (Thm {sign, prop, ...}) = trace_term a sign prop;
fun trace_thm_warning a (Thm {sign, prop, ...}) = trace_term_warning a sign prop;



(** meta simp sets **)

(* basic components *)

type rrule = {thm: thm, lhs: term, perm: bool};
type cong = {thm: thm, lhs: term};
type simproc = (Sign.sg -> term -> thm option) * stamp;

fun eq_rrule ({thm = Thm{prop = p1, ...}, ...}: rrule,
  {thm = Thm {prop = p2, ...}, ...}: rrule) = p1 aconv p2;

val eq_simproc = eq_snd;


(* datatype mss *)

(*
  A "mss" contains data needed during conversion:
    rules: discrimination net of rewrite rules;
    congs: association list of congruence rules;
    procs: discrimination net of simplification procedures
      (functions that prove rewrite rules on the fly);
    bounds: names of bound variables already used
      (for generating new names when rewriting under lambda abstractions);
    prems: current premises;
    mk_rews: turns simplification thms into rewrite rules;
    termless: relation for ordered rewriting;
*)

datatype meta_simpset =
  Mss of {
    rules: rrule Net.net,
    congs: (string * cong) list,
    procs: simproc Net.net,
    bounds: string list,
    prems: thm list,
    mk_rews: thm -> thm list,
    termless: term * term -> bool};

fun mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless) =
  Mss {rules = rules, congs = congs, procs = procs, bounds = bounds,
    prems = prems, mk_rews = mk_rews, termless = termless};

val empty_mss =
  mk_mss (Net.empty, [], Net.empty, [], [], K [], Logic.termless);



(** simpset operations **)

(* mk_rrule *)

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u);

fun var_perm (t, u) =
  vperm (t, u) andalso eq_set_term (term_vars t, term_vars u);

(*simple test for looping rewrite*)
fun loops sign prems (lhs, rhs) =
   is_Var (head_of lhs)
  orelse
   (exists (apl (lhs, Logic.occs)) (rhs :: prems))
  orelse
   (null prems andalso
    Pattern.matches (#tsig (Sign.rep_sg sign)) (lhs, rhs));
(*the condition "null prems" in the last case is necessary because
  conditional rewrites with extra variables in the conditions may terminate
  although the rhs is an instance of the lhs. Example:
  ?m < ?n ==> f(?n) == f(?m)*)

fun mk_rrule (thm as Thm {sign, prop, ...}) =
  let
    val prems = Logic.strip_imp_prems prop;
    val concl = Logic.strip_imp_concl prop;
    val (lhs, _) = Logic.dest_equals concl handle TERM _ =>
      raise SIMPLIFIER ("Rewrite rule not a meta-equality", thm);
    val econcl = Pattern.eta_contract concl;
    val (elhs, erhs) = Logic.dest_equals econcl;
    val perm = var_perm (elhs, erhs) andalso not (elhs aconv erhs)
      andalso not (is_Var elhs);
  in
    if not ((term_vars erhs) subset
        (union_term (term_vars elhs, List.concat(map term_vars prems)))) then
      (prtm_warning "extra Var(s) on rhs" sign prop; None)
    else if not perm andalso loops sign prems (elhs, erhs) then
      (prtm_warning "ignoring looping rewrite rule" sign prop; None)
    else Some {thm = thm, lhs = lhs, perm = perm}
  end;


(* add_simps *)

fun add_simp
  (mss as Mss {rules, congs, procs, bounds, prems, mk_rews, termless},
    thm as Thm {sign, prop, ...}) =
  (case mk_rrule thm of
    None => mss
  | Some (rrule as {lhs, ...}) =>
      (trace_thm "Adding rewrite rule:" thm;
        mk_mss (Net.insert_term ((lhs, rrule), rules, eq_rrule) handle Net.INSERT =>
          (prtm_warning "ignoring duplicate rewrite rule" sign prop; rules),
            congs, procs, bounds, prems, mk_rews, termless)));

val add_simps = foldl add_simp;

fun mss_of thms = add_simps (empty_mss, thms);


(* del_simps *)

fun del_simp
  (mss as Mss {rules, congs, procs, bounds, prems, mk_rews, termless},
    thm as Thm {sign, prop, ...}) =
  (case mk_rrule thm of
    None => mss
  | Some (rrule as {lhs, ...}) =>
      mk_mss (Net.delete_term ((lhs, rrule), rules, eq_rrule) handle Net.DELETE =>
        (prtm_warning "rewrite rule not in simpset" sign prop; rules),
          congs, procs, bounds, prems, mk_rews, termless));

val del_simps = foldl del_simp;


(* add_congs *)

fun add_cong (Mss {rules, congs, procs, bounds, prems, mk_rews, termless}, thm) =
  let
    val (lhs, _) = Logic.dest_equals (concl_of thm) handle TERM _ =>
      raise SIMPLIFIER ("Congruence not a meta-equality", thm);
(*   val lhs = Pattern.eta_contract lhs; *)
    val (a, _) = dest_Const (head_of lhs) handle TERM _ =>
      raise SIMPLIFIER ("Congruence must start with a constant", thm);
  in
    mk_mss (rules, (a, {lhs = lhs, thm = thm}) :: congs, procs, bounds,
      prems, mk_rews, termless)
  end;

val (op add_congs) = foldl add_cong;


(* del_congs *)

fun del_cong (Mss {rules, congs, procs, bounds, prems, mk_rews, termless}, thm) =
  let
    val (lhs, _) = Logic.dest_equals (concl_of thm) handle TERM _ =>
      raise SIMPLIFIER ("Congruence not a meta-equality", thm);
(*   val lhs = Pattern.eta_contract lhs; *)
    val (a, _) = dest_Const (head_of lhs) handle TERM _ =>
      raise SIMPLIFIER ("Congruence must start with a constant", thm);
  in
    mk_mss (rules, filter (fn (x,_)=> x<>a) congs, procs, bounds,
      prems, mk_rews, termless)
  end;

val (op del_congs) = foldl del_cong;


(* add_simprocs *)

fun add_simproc (mss as Mss {rules, congs, procs, bounds, prems, mk_rews, termless},
    (sign, lhs, proc, id)) =
  (trace_term "Adding simplification procedure for:" sign lhs;
    mk_mss (rules, congs,
      Net.insert_term ((lhs, (proc, id)), procs, eq_simproc) handle Net.INSERT =>
        (trace_warning "ignored duplicate"; procs),
        bounds, prems, mk_rews, termless));

val add_simprocs = foldl add_simproc;


(* del_simprocs *)

fun del_simproc (mss as Mss {rules, congs, procs, bounds, prems, mk_rews, termless},
    (sign:Sign.sg, lhs, proc, id)) =
  mk_mss (rules, congs,
    Net.delete_term ((lhs, (proc, id)), procs, eq_simproc) handle Net.DELETE =>
      (trace_warning "simplification procedure not in simpset"; procs),
          bounds, prems, mk_rews, termless);

val del_simprocs = foldl del_simproc;


(* prems *)

fun add_prems (Mss {rules, congs, procs, bounds, prems, mk_rews, termless}, thms) =
  mk_mss (rules, congs, procs, bounds, thms @ prems, mk_rews, termless);

fun prems_of_mss (Mss {prems, ...}) = prems;


(* mk_rews *)

fun set_mk_rews
  (Mss {rules, congs, procs, bounds, prems, mk_rews = _, termless}, mk_rews) =
    mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless);

fun mk_rews_of_mss (Mss {mk_rews, ...}) = mk_rews;


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
type termrec = (Sign.sg * term list) * term;
type conv = meta_simpset -> termrec -> termrec;

fun check_conv (thm as Thm{shyps,hyps,prop,sign,der,maxidx,...}, prop0, ders) =
  let fun err() = (trace_thm "Proved wrong thm (Check subgoaler?)" thm;
                   trace_term "Should have proved" sign prop0;
                   None)
      val (lhs0,_) = Logic.dest_equals(Logic.strip_imp_concl prop0)
  in case prop of
       Const("==",_) $ lhs $ rhs =>
         if (lhs = lhs0) orelse
            (lhs aconv Envir.norm_term (Envir.empty 0) lhs0)
         then (trace_thm "SUCCEEDED" thm; 
               Some(shyps, hyps, maxidx, rhs, der::ders))
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

fun add_insts_sorts ((iTs, is), Ss) =
  add_typs_sorts (map snd iTs, add_terms_sorts (map snd is, Ss));


(* mk_procrule *)

fun mk_procrule (thm as Thm {sign, prop, ...}) =
  let
    val prems = Logic.strip_imp_prems prop;
    val concl = Logic.strip_imp_concl prop;
    val (lhs, _) = Logic.dest_equals concl handle TERM _ =>
      raise SIMPLIFIER ("Rewrite rule not a meta-equality", thm);
    val econcl = Pattern.eta_contract concl;
    val (elhs, erhs) = Logic.dest_equals econcl;
  in
    if not ((term_vars erhs) subset
        (union_term (term_vars elhs, List.concat(map term_vars prems)))) 
    then (prtm_warning "extra Var(s) on rhs" sign prop; [])
    else [{thm = thm, lhs = lhs, perm = false}]
  end;


(* conversion to apply the meta simpset to a term *)

(*
  we try in order:
    (1) beta reduction
    (2) unconditional rewrite rules
    (3) conditional rewrite rules
    (4) simplification procedures		(* FIXME (un-)conditional !! *)
*)

fun rewritec (prover,signt) (mss as Mss{rules, procs, mk_rews, termless, ...}) 
             (shypst,hypst,maxt,t,ders) =
  let fun rew {thm as Thm{sign,der,maxidx,shyps,hyps,prop,...}, lhs, perm} =
        let val unit = if Sign.subsig(sign,signt) then ()
                  else (trace_thm_warning "rewrite rule from different theory"
                          thm;
                        raise Pattern.MATCH)
            val rprop = if maxt = ~1 then prop
                        else Logic.incr_indexes([],maxt+1) prop;
            val rlhs = if maxt = ~1 then lhs
                       else fst(Logic.dest_equals(Logic.strip_imp_concl rprop))
            val insts = Pattern.match (#tsig(Sign.rep_sg signt)) (rlhs,t)
            val prop' = ren_inst(insts,rprop,rlhs,t);
            val hyps' = union_term(hyps,hypst);
            val shyps' = add_insts_sorts (insts, union_sort(shyps,shypst));
            val maxidx' = maxidx_of_term prop'
            val ct' = Cterm{sign = signt,       (*used for deriv only*)
                            t = prop',
                            T = propT,
                            maxidx = maxidx'}
            val der' = infer_derivs (RewriteC ct', [der])	(* FIXME fix!? *)
            val thm' = Thm{sign = signt, 
                           der = der',
                           shyps = shyps',
                           hyps = hyps',
                           prop = prop',
                           maxidx = maxidx'}
            val (lhs',rhs') = Logic.dest_equals(Logic.strip_imp_concl prop')
        in if perm andalso not(termless(rhs',lhs')) then None else
           if Logic.count_prems(prop',0) = 0
           then (trace_thm "Rewriting:" thm'; 
                 Some(shyps', hyps', maxidx', rhs', der'::ders))
           else (trace_thm "Trying to rewrite:" thm';
                 case prover mss thm' of
                   None       => (trace_thm "FAILED" thm'; None)
                 | Some(thm2) => check_conv(thm2,prop',ders))
        end

      fun rews [] = None
        | rews (rrule :: rrules) =
            let val opt = rew rrule handle Pattern.MATCH => None
            in case opt of None => rews rrules | some => some end;
      fun sort_rrules rrs = let
        fun is_simple {thm as Thm{prop,...}, lhs, perm} = case prop of 
                                        Const("==",_) $ _ $ _ => true
                                        | _                   => false 
        fun sort []        (re1,re2) = re1 @ re2
        |   sort (rr::rrs) (re1,re2) = if is_simple rr 
                                       then sort rrs (rr::re1,re2)
                                       else sort rrs (re1,rr::re2)
      in sort rrs ([],[]) 
      end

      fun proc_rews _ [] = None
        | proc_rews eta_t ((f, _) :: fs) =
            (case f signt eta_t of
              None => proc_rews eta_t fs
            | Some raw_thm =>
                (trace_thm "Proved rewrite rule: " raw_thm;
                 (case rews (mk_procrule raw_thm) of
                   None => proc_rews eta_t fs
                 | some => some)));
  in
    (case t of
      Abs (_, _, body) $ u =>		(* FIXME bug!? (because of beta/eta overlap) *)
        Some (shypst, hypst, maxt, subst_bound (u, body), ders)
     | _ =>
      (case rews (sort_rrules (Net.match_term rules t)) of
        None => proc_rews (Pattern.eta_contract t) (Net.match_term procs t)
      | some => some))
  end;


(* conversion to apply a congruence rule to a term *)

fun congc (prover,signt) {thm=cong,lhs=lhs} (shypst,hypst,maxt,t,ders) =
  let val Thm{sign,der,shyps,hyps,maxidx,prop,...} = cong
      val unit = if Sign.subsig(sign,signt) then ()
                 else error("Congruence rule from different theory")
      val tsig = #tsig(Sign.rep_sg signt)
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
      val ct' = Cterm{sign = signt,     (*used for deriv only*)
                      t = prop',
                      T = propT,
                      maxidx = maxidx'}
      val thm' = Thm{sign = signt, 
                     der = infer_derivs (CongC ct', [der]),	(* FIXME fix!? *)
                     shyps = shyps',
                     hyps = union_term(hyps,hypst),
                     prop = prop',
                     maxidx = maxidx'};
      val unit = trace_thm "Applying congruence rule" thm';
      fun err() = error("Failed congruence proof!")

  in case prover thm' of
       None => err()
     | Some(thm2) => (case check_conv(thm2,prop',ders) of
                        None => err() | some => some)
  end;



fun bottomc ((simprem,useprem),prover,sign) =
 let fun botc fail mss trec =
          (case subc mss trec of
             some as Some(trec1) =>
               (case rewritec (prover,sign) mss trec1 of
                  Some(trec2) => botc false mss trec2
                | None => some)
           | None =>
               (case rewritec (prover,sign) mss trec of
                  Some(trec2) => botc false mss trec2
                | None => if fail then None else Some(trec)))

     and try_botc mss trec = (case botc true mss trec of
                                Some(trec1) => trec1
                              | None => trec)

     and subc (mss as Mss{rules,congs,procs,bounds,prems,mk_rews,termless})
              (trec as (shyps,hyps,maxidx,t0,ders)) =
       (case t0 of
           Abs(a,T,t) =>
             let val b = variant bounds a
                 val v = Free("." ^ b,T)
                 val mss' = mk_mss (rules, congs, procs, b :: bounds, prems, mk_rews, termless)
             in case botc true mss' 
                       (shyps,hyps,maxidx,subst_bound (v,t),ders) of
                  Some(shyps',hyps',maxidx',t',ders') =>
                    Some(shyps', hyps', maxidx',
                         Abs(a, T, abstract_over(v,t')),
                         ders')
                | None => None
             end
         | t$u => (case t of
             Const("==>",_)$s  => Some(impc(shyps,hyps,maxidx,s,u,mss,ders))
           | Abs(_,_,body) =>
               let val trec = (shyps,hyps,maxidx,subst_bound (u,body),ders)
               in case subc mss trec of
                    None => Some(trec)
                  | trec => trec
               end
           | _  =>
               let fun appc() =
                     (case botc true mss (shyps,hyps,maxidx,t,ders) of
                        Some(shyps1,hyps1,maxidx1,t1,ders1) =>
                          (case botc true mss (shyps1,hyps1,maxidx,u,ders1) of
                             Some(shyps2,hyps2,maxidx2,u1,ders2) =>
                               Some(shyps2, hyps2, Int.max(maxidx1,maxidx2),
                                    t1$u1, ders2)
                           | None =>
                               Some(shyps1, hyps1, Int.max(maxidx1,maxidx), t1$u,
                                    ders1))
                      | None =>
                          (case botc true mss (shyps,hyps,maxidx,u,ders) of
                             Some(shyps1,hyps1,maxidx1,u1,ders1) =>
                               Some(shyps1, hyps1, Int.max(maxidx,maxidx1), 
                                    t$u1, ders1)
                           | None => None))
                   val (h,ts) = strip_comb t
               in case h of
                    Const(a,_) =>
                      (case assoc_string(congs,a) of
                         None => appc()
                       | Some(cong) => (congc (prover mss,sign) cong trec
                                        handle Pattern.MATCH => appc() ) )
                  | _ => appc()
               end)
         | _ => None)

     and impc(shyps, hyps, maxidx, s, u, mss as Mss{mk_rews,...}, ders) =
       let val (shyps1,hyps1,_,s1,ders1) =
             if simprem then try_botc mss (shyps,hyps,maxidx,s,ders)
                        else (shyps,hyps,0,s,ders);
           val maxidx1 = maxidx_of_term s1
           val mss1 =
             if not useprem then mss else
             if maxidx1 <> ~1 then (trace_term_warning
"Cannot add premise as rewrite rule because it contains (type) unknowns:"
                                                  sign s1; mss)
             else let val thm = assume (Cterm{sign=sign, t=s1, 
                                              T=propT, maxidx=maxidx1})
                  in add_simps(add_prems(mss,[thm]), mk_rews thm) end
           val (shyps2,hyps2,maxidx2,u1,ders2) = 
               try_botc mss1 (shyps1,hyps1,maxidx,u,ders1)
           val hyps3 = if gen_mem (op aconv) (s1, hyps1) 
                       then hyps2 else hyps2\s1
       in (shyps2, hyps3, Int.max(maxidx1,maxidx2), 
           Logic.mk_implies(s1,u1), ders2) 
       end

 in try_botc end;


(*** Meta-rewriting: rewrites t to u and returns the theorem t==u ***)

(*
  Parameters:
    mode = (simplify A, use A in simplifying B) when simplifying A ==> B
    mss: contains equality theorems of the form [|p1,...|] ==> t==u
    prover: how to solve premises in conditional rewrites and congruences
*)

(* FIXME: check that #bounds(mss) does not "occur" in ct alread *)

fun rewrite_cterm mode mss prover ct =
  let val {sign, t, T, maxidx} = rep_cterm ct;
      val (shyps,hyps,maxu,u,ders) =
        bottomc (mode,prover,sign) mss 
                (add_term_sorts(t,[]), [], maxidx, t, []);
      val prop = Logic.mk_equals(t,u)
  in
      Thm{sign = sign, 
          der = infer_derivs (Rewrite_cterm ct, ders),
          maxidx = Int.max (maxidx,maxu),
          shyps = shyps, 
          hyps = hyps, 
          prop = prop}
  end



(*** Oracles ***)

fun invoke_oracle (thy, sign, exn) =
    case #oraopt(rep_theory thy) of
        None => raise THM ("No oracle in supplied theory", 0, [])
      | Some oracle => 
            let val sign' = Sign.merge(sign_of thy, sign)
                val (prop, T, maxidx) = 
                    Sign.certify_term sign' (oracle (sign', exn))
            in if T<>propT then
                  raise THM("Oracle's result must have type prop", 0, [])
               else fix_shyps [] []
                     (Thm {sign = sign', 
                           der = Join (Oracle(thy,sign,exn), []),
                           maxidx = maxidx,
                           shyps = [], 
                           hyps = [], 
                           prop = prop})
            end;

end;

open Thm;
