(*  Title:      Pure/meta_simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Stefan Berghofer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Meta-level Simplification.
*)

signature BASIC_META_SIMPLIFIER =
sig
  val trace_simp: bool ref
  val debug_simp: bool ref
end;

signature META_SIMPLIFIER =
sig
  include BASIC_META_SIMPLIFIER
  exception SIMPLIFIER of string * thm
  type meta_simpset
  val dest_mss          : meta_simpset ->
    {simps: thm list, congs: thm list, procs: (string * cterm list) list}
  val empty_mss         : meta_simpset
  val clear_mss         : meta_simpset -> meta_simpset
  val merge_mss         : meta_simpset * meta_simpset -> meta_simpset
  val add_simps         : meta_simpset * thm list -> meta_simpset
  val del_simps         : meta_simpset * thm list -> meta_simpset
  val mss_of            : thm list -> meta_simpset
  val add_congs         : meta_simpset * thm list -> meta_simpset
  val del_congs         : meta_simpset * thm list -> meta_simpset
  val add_simprocs      : meta_simpset *
    (string * cterm list * (Sign.sg -> thm list -> term -> thm option) * stamp) list
      -> meta_simpset
  val del_simprocs      : meta_simpset *
    (string * cterm list * (Sign.sg -> thm list -> term -> thm option) * stamp) list
      -> meta_simpset
  val add_prems         : meta_simpset * thm list -> meta_simpset
  val prems_of_mss      : meta_simpset -> thm list
  val set_mk_rews       : meta_simpset * (thm -> thm list) -> meta_simpset
  val set_mk_sym        : meta_simpset * (thm -> thm option) -> meta_simpset
  val set_mk_eq_True    : meta_simpset * (thm -> thm option) -> meta_simpset
  val set_termless      : meta_simpset * (term * term -> bool) -> meta_simpset
  val beta_eta_conversion: cterm -> thm
  val rewrite_cterm: bool * bool * bool ->
    (meta_simpset -> thm -> thm option) -> meta_simpset -> cterm -> thm
  val goals_conv        : (int -> bool) -> (cterm -> thm) -> cterm -> thm
  val forall_conv       : (cterm -> thm) -> cterm -> thm
  val fconv_rule        : (cterm -> thm) -> thm -> thm
  val rewrite_aux       : (meta_simpset -> thm -> thm option) -> bool -> thm list -> cterm -> thm
  val simplify_aux      : (meta_simpset -> thm -> thm option) -> bool -> thm list -> thm -> thm
  val rewrite_thm       : bool * bool * bool
                          -> (meta_simpset -> thm -> thm option)
                          -> meta_simpset -> thm -> thm
  val rewrite_goals_rule_aux: (meta_simpset -> thm -> thm option) -> thm list -> thm -> thm
  val rewrite_goal_rule : bool* bool * bool
                          -> (meta_simpset -> thm -> thm option)
                          -> meta_simpset -> int -> thm -> thm
  val rewrite_term: Sign.sg -> thm list -> term -> term
end;

structure MetaSimplifier : META_SIMPLIFIER =
struct

(** diagnostics **)

exception SIMPLIFIER of string * thm;

val simp_depth = ref 0;

local

fun println a =
  tracing ((case ! simp_depth of 0 => "" | n => "[" ^ string_of_int n ^ "]") ^ a);

fun prnt warn a = if warn then warning a else println a;
fun prtm warn a sign t = prnt warn (a ^ "\n" ^ Sign.string_of_term sign t);
fun prctm warn a t = prnt warn (a ^ "\n" ^ Display.string_of_cterm t);

in

fun prthm warn a = prctm warn a o Thm.cprop_of;

val trace_simp = ref false;
val debug_simp = ref false;

fun trace warn a = if !trace_simp then prnt warn a else ();
fun debug warn a = if !debug_simp then prnt warn a else ();

fun trace_term warn a sign t = if !trace_simp then prtm warn a sign t else ();
fun trace_cterm warn a t = if !trace_simp then prctm warn a t else ();
fun debug_term warn a sign t = if !debug_simp then prtm warn a sign t else ();

fun trace_thm warn a thm =
  let val {sign, prop, ...} = rep_thm thm
  in trace_term warn a sign prop end;

end;


(** meta simp sets **)

(* basic components *)

type rrule = {thm: thm, lhs: term, elhs: cterm, fo: bool, perm: bool};
(* thm: the rewrite rule
   lhs: the left-hand side
   elhs: the etac-contracted lhs.
   fo:  use first-order matching
   perm: the rewrite rule is permutative
Remarks:
  - elhs is used for matching,
    lhs only for preservation of bound variable names.
  - fo is set iff
    either elhs is first-order (no Var is applied),
           in which case fo-matching is complete,
    or elhs is not a pattern,
       in which case there is nothing better to do.
*)
type cong = {thm: thm, lhs: cterm};
type simproc =
 {name: string, proc: Sign.sg -> thm list -> term -> thm option, lhs: cterm, id: stamp};

fun eq_rrule ({thm = thm1, ...}: rrule, {thm = thm2, ...}: rrule) =
  #prop (rep_thm thm1) aconv #prop (rep_thm thm2);

fun eq_cong ({thm = thm1, ...}: cong, {thm = thm2, ...}: cong) =
  #prop (rep_thm thm1) aconv #prop (rep_thm thm2);

fun eq_prem (thm1, thm2) =
  #prop (rep_thm thm1) aconv #prop (rep_thm thm2);

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
    depth: depth of conditional rewriting;
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
    termless: term * term -> bool,
    depth: int};

fun mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless, depth) =
  Mss {rules = rules, congs = congs, procs = procs, bounds = bounds,
       prems=prems, mk_rews=mk_rews, termless=termless, depth=depth};

fun upd_rules(Mss{rules,congs,procs,bounds,prems,mk_rews,termless,depth}, rules') =
  mk_mss(rules',congs,procs,bounds,prems,mk_rews,termless,depth);

val empty_mss =
  let val mk_rews = {mk = K [], mk_sym = K None, mk_eq_True = K None}
  in mk_mss (Net.empty, ([], []), Net.empty, [], [], mk_rews, Term.termless, 0) end;

fun clear_mss (Mss {mk_rews, termless, ...}) =
  mk_mss (Net.empty, ([], []), Net.empty, [], [], mk_rews, termless,0);

fun incr_depth(Mss{rules,congs,procs,bounds,prems,mk_rews,termless,depth}) =
  mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless, depth+1)



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
     |> map (fn ps => (#1 (#1 (hd ps)), map (#2 o #1) ps))
     |> Library.sort_wrt #1};


(* merge_mss *)       (*NOTE: ignores mk_rews, termless and depth of 2nd mss*)

fun merge_mss
 (Mss {rules = rules1, congs = (congs1,weak1), procs = procs1,
       bounds = bounds1, prems = prems1, mk_rews, termless, depth},
  Mss {rules = rules2, congs = (congs2,weak2), procs = procs2,
       bounds = bounds2, prems = prems2, ...}) =
      mk_mss
       (Net.merge (rules1, rules2, eq_rrule),
        (gen_merge_lists (eq_cong o pairself snd) congs1 congs2,
        merge_lists weak1 weak2),
        Net.merge (procs1, procs2, eq_simproc),
        merge_lists bounds1 bounds2,
        gen_merge_lists eq_prem prems1 prems2,
        mk_rews, termless, depth);


(* add_simps *)

fun mk_rrule2{thm,lhs,elhs,perm} =
  let val fo = Pattern.first_order (term_of elhs) orelse not(Pattern.pattern (term_of elhs))
  in {thm=thm,lhs=lhs,elhs=elhs,fo=fo,perm=perm} end

fun insert_rrule(mss as Mss {rules,...},
                 rrule as {thm,lhs,elhs,perm}) =
  (trace_thm false "Adding rewrite rule:" thm;
   let val rrule2 as {elhs,...} = mk_rrule2 rrule
       val rules' = Net.insert_term ((term_of elhs, rrule2), rules, eq_rrule)
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

fun decomp_simp thm =
  let val {sign, prop, ...} = rep_thm thm;
      val prems = Logic.strip_imp_prems prop;
      val concl = Drule.strip_imp_concl (cprop_of thm);
      val (lhs, rhs) = Drule.dest_equals concl handle TERM _ =>
        raise SIMPLIFIER ("Rewrite rule not a meta-equality", thm)
      val elhs = snd (Drule.dest_equals (cprop_of (Thm.eta_conversion lhs)));
      val elhs = if elhs=lhs then lhs else elhs (* try to share *)
      val erhs = Pattern.eta_contract (term_of rhs);
      val perm = var_perm (term_of elhs, erhs) andalso not (term_of elhs aconv erhs)
                 andalso not (is_Var (term_of elhs))
  in (sign, prems, term_of lhs, elhs, term_of rhs, perm) end;

fun decomp_simp' thm =
  let val (_, _, _, elhs, rhs, _) = decomp_simp thm in
    if Thm.nprems_of thm > 0 then raise SIMPLIFIER ("Bad conditional rewrite rule", thm)
    else (term_of elhs, rhs)
  end;

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
        is_Var (term_of elhs)
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
  (upd_rules(mss, Net.delete_term ((term_of elhs, rrule), rules, eq_rrule))
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

fun is_full_cong thm =
let val prems = prems_of thm
    and concl = concl_of thm
    val (lhs,rhs) = Logic.dest_equals concl
    val (f,xs) = strip_comb lhs
    and (g,ys) = strip_comb rhs
in
  f=g andalso null(findrep(xs@ys)) andalso length xs = length ys andalso
  is_full_cong_prems prems (xs ~~ ys)
end

fun add_cong (Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth}, thm) =
  let
    val (lhs, _) = Drule.dest_equals (Drule.strip_imp_concl (cprop_of thm)) handle TERM _ =>
      raise SIMPLIFIER ("Congruence not a meta-equality", thm);
(*   val lhs = Pattern.eta_contract lhs; *)
    val (a, _) = dest_Const (head_of (term_of lhs)) handle TERM _ =>
      raise SIMPLIFIER ("Congruence must start with a constant", thm);
    val (alist,weak) = congs
    val alist2 = overwrite_warn (alist, (a,{lhs=lhs, thm=thm}))
           ("Overwriting congruence rule for " ^ quote a);
    val weak2 = if is_full_cong thm then weak else a::weak
  in
    mk_mss (rules,(alist2,weak2),procs,bounds,prems,mk_rews,termless,depth)
  end;

val (op add_congs) = foldl add_cong;


(* del_congs *)

fun del_cong (Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth}, thm) =
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
    mk_mss (rules,(alist2,weak2),procs,bounds,prems,mk_rews,termless,depth)
  end;

val (op del_congs) = foldl del_cong;


(* add_simprocs *)

fun add_proc (mss as Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth},
    (name, lhs, proc, id)) =
  let val {sign, t, ...} = rep_cterm lhs
  in (trace_term false ("Adding simplification procedure " ^ quote name ^ " for")
      sign t;
    mk_mss (rules, congs,
      Net.insert_term ((t, mk_simproc (name, proc, lhs, id)), procs, eq_simproc)
        handle Net.INSERT =>
            (warning ("Ignoring duplicate simplification procedure \""
                      ^ name ^ "\"");
             procs),
        bounds, prems, mk_rews, termless,depth))
  end;

fun add_simproc (mss, (name, lhss, proc, id)) =
  foldl add_proc (mss, map (fn lhs => (name, lhs, proc, id)) lhss);

val add_simprocs = foldl add_simproc;


(* del_simprocs *)

fun del_proc (mss as Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth},
    (name, lhs, proc, id)) =
  mk_mss (rules, congs,
    Net.delete_term ((term_of lhs, mk_simproc (name, proc, lhs, id)), procs, eq_simproc)
      handle Net.DELETE =>
          (warning ("Simplification procedure \"" ^ name ^
                       "\" not in simpset"); procs),
      bounds, prems, mk_rews, termless, depth);

fun del_simproc (mss, (name, lhss, proc, id)) =
  foldl del_proc (mss, map (fn lhs => (name, lhs, proc, id)) lhss);

val del_simprocs = foldl del_simproc;


(* prems *)

fun add_prems (Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth}, thms) =
  mk_mss (rules, congs, procs, bounds, thms @ prems, mk_rews, termless, depth);

fun prems_of_mss (Mss {prems, ...}) = prems;


(* mk_rews *)

fun set_mk_rews
  (Mss {rules, congs, procs, bounds, prems, mk_rews, termless, depth}, mk) =
    mk_mss (rules, congs, procs, bounds, prems,
            {mk=mk, mk_sym= #mk_sym mk_rews, mk_eq_True= #mk_eq_True mk_rews},
            termless, depth);

fun set_mk_sym
  (Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth}, mk_sym) =
    mk_mss (rules, congs, procs, bounds, prems,
            {mk= #mk mk_rews, mk_sym= mk_sym, mk_eq_True= #mk_eq_True mk_rews},
            termless,depth);

fun set_mk_eq_True
  (Mss {rules,congs,procs,bounds,prems,mk_rews,termless,depth}, mk_eq_True) =
    mk_mss (rules, congs, procs, bounds, prems,
            {mk= #mk mk_rews, mk_sym= #mk_sym mk_rews, mk_eq_True= mk_eq_True},
            termless,depth);

(* termless *)

fun set_termless
  (Mss {rules, congs, procs, bounds, prems, mk_rews, depth, ...}, termless) =
    mk_mss (rules, congs, procs, bounds, prems, mk_rews, termless, depth);



(** rewriting **)

(*
  Uses conversions, see:
    L C Paulson, A higher-order implementation of rewriting,
    Science of Computer Programming 3 (1983), pages 119-149.
*)

type prover = meta_simpset -> thm -> thm option;
type termrec = (Sign.sg_ref * term list) * term;
type conv = meta_simpset -> termrec -> termrec;

val dest_eq = Drule.dest_equals o cprop_of;
val lhs_of = fst o dest_eq;
val rhs_of = snd o dest_eq;

fun beta_eta_conversion t =
  let val thm = beta_conversion true t;
  in transitive thm (eta_conversion (rhs_of thm)) end;

fun check_conv msg thm thm' =
  let
    val thm'' = transitive thm (transitive
      (symmetric (beta_eta_conversion (lhs_of thm'))) thm')
  in (if msg then trace_thm false "SUCCEEDED" thm' else (); Some thm'') end
  handle THM _ =>
    let val {sign, prop = _ $ _ $ prop0, ...} = rep_thm thm;
    in
      (trace_thm false "Proved wrong thm (Check subgoaler?)" thm';
       trace_term false "Should have proved:" sign prop0;
       None)
    end;


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

fun rewritec (prover, signt, maxt)
             (mss as Mss{rules, procs, termless, prems, congs, depth,...}) t =
  let
    val eta_thm = Thm.eta_conversion t;
    val eta_t' = rhs_of eta_thm;
    val eta_t = term_of eta_t';
    val tsigt = Sign.tsig_of signt;
    fun rew {thm, lhs, elhs, fo, perm} =
      let
        val {sign, prop, maxidx, ...} = rep_thm thm;
        val _ = if Sign.subsig (sign, signt) then ()
                else (prthm true "Ignoring rewrite rule from different theory:" thm;
                      raise Pattern.MATCH);
        val (rthm, elhs') = if maxt = ~1 then (thm, elhs)
          else (Thm.incr_indexes (maxt+1) thm, Thm.cterm_incr_indexes (maxt+1) elhs);
        val insts = if fo then Thm.cterm_first_order_match (elhs', eta_t')
                          else Thm.cterm_match (elhs', eta_t');
        val thm' = Thm.instantiate insts (Thm.rename_boundvars lhs eta_t rthm);
        val prop' = #prop (rep_thm thm');
        val unconditional = (Logic.count_prems (prop',0) = 0);
        val (lhs', rhs') = Logic.dest_equals (Logic.strip_imp_concl prop')
      in
        if perm andalso not (termless (rhs', lhs'))
        then (trace_thm false "Cannot apply permutative rewrite rule:" thm;
              trace_thm false "Term does not become smaller:" thm'; None)
        else (trace_thm false "Applying instance of rewrite rule:" thm;
           if unconditional
           then
             (trace_thm false "Rewriting:" thm';
              let val lr = Logic.dest_equals prop;
                  val Some thm'' = check_conv false eta_thm thm'
              in Some (thm'', uncond_skel (congs, lr)) end)
           else
             (trace_thm false "Trying to rewrite:" thm';
              case prover (incr_depth mss) thm' of
                None       => (trace_thm false "FAILED" thm'; None)
              | Some thm2 =>
                  (case check_conv true eta_thm thm2 of
                     None => None |
                     Some thm2' =>
                       let val concl = Logic.strip_imp_concl prop
                           val lr = Logic.dest_equals concl
                       in Some (thm2', cond_skel (congs, lr)) end)))
      end

    fun rews [] = None
      | rews (rrule :: rrules) =
          let val opt = rew rrule handle Pattern.MATCH => None
          in case opt of None => rews rrules | some => some end;

    fun sort_rrules rrs = let
      fun is_simple({thm, ...}:rrule) = case #prop (rep_thm thm) of
                                      Const("==",_) $ _ $ _ => true
                                      | _                   => false
      fun sort []        (re1,re2) = re1 @ re2
        | sort (rr::rrs) (re1,re2) = if is_simple rr
                                     then sort rrs (rr::re1,re2)
                                     else sort rrs (re1,rr::re2)
    in sort rrs ([],[]) end

    fun proc_rews ([]:simproc list) = None
      | proc_rews ({name, proc, lhs, ...} :: ps) =
          if Pattern.matches tsigt (term_of lhs, term_of t) then
            (debug_term false ("Trying procedure " ^ quote name ^ " on:") signt eta_t;
             case proc signt prems eta_t of
               None => (debug false "FAILED"; proc_rews ps)
             | Some raw_thm =>
                 (trace_thm false ("Procedure " ^ quote name ^ " produced rewrite rule:") raw_thm;
                  (case rews (mk_procrule raw_thm) of
                    None => (trace_cterm false "IGNORED - does not match" t; proc_rews ps)
                  | some => some)))
          else proc_rews ps;
  in case eta_t of
       Abs _ $ _ => Some (transitive eta_thm
         (beta_conversion false eta_t'), skel0)
     | _ => (case rews (sort_rrules (Net.match_term rules eta_t)) of
               None => proc_rews (Net.match_term procs eta_t)
             | some => some)
  end;


(* conversion to apply a congruence rule to a term *)

fun congc (prover,signt,maxt) {thm=cong,lhs=lhs} t =
  let val {sign, ...} = rep_thm cong
      val _ = if Sign.subsig (sign, signt) then ()
                 else error("Congruence rule from different theory")
      val rthm = if maxt = ~1 then cong else Thm.incr_indexes (maxt+1) cong;
      val rlhs = fst (Drule.dest_equals (Drule.strip_imp_concl (cprop_of rthm)));
      val insts = Thm.cterm_match (rlhs, t)
      (* Pattern.match can raise Pattern.MATCH;
         is handled when congc is called *)
      val thm' = Thm.instantiate insts (Thm.rename_boundvars (term_of rlhs) (term_of t) rthm);
      val unit = trace_thm false "Applying congruence rule:" thm';
      fun err (msg, thm) = (prthm false msg thm; error "Failed congruence proof!")
  in case prover thm' of
       None => err ("Could not prove", thm')
     | Some thm2 => (case check_conv true (beta_eta_conversion t) thm2 of
          None => err ("Should not have proved", thm2)
        | Some thm2' =>
            if op aconv (pairself term_of (dest_equals (cprop_of thm2')))
            then None else Some thm2')
  end;

val (cA, (cB, cC)) =
  apsnd dest_equals (dest_implies (hd (cprems_of Drule.imp_cong)));

fun transitive' thm1 None = Some thm1
  | transitive' thm1 (Some thm2) = Some (transitive thm1 thm2);

fun transitive'' None thm2 = Some thm2
  | transitive'' (Some thm1) thm2 = Some (transitive thm1 thm2);

fun bottomc ((simprem,useprem,mutsimp), prover, sign, maxidx) =
  let
    fun botc skel mss t =
          if is_Var skel then None
          else
          (case subc skel mss t of
             some as Some thm1 =>
               (case rewritec (prover, sign, maxidx) mss (rhs_of thm1) of
                  Some (thm2, skel2) =>
                    transitive' (transitive thm1 thm2)
                      (botc skel2 mss (rhs_of thm2))
                | None => some)
           | None =>
               (case rewritec (prover, sign, maxidx) mss t of
                  Some (thm2, skel2) => transitive' thm2
                    (botc skel2 mss (rhs_of thm2))
                | None => None))

    and try_botc mss t =
          (case botc skel0 mss t of
             Some trec1 => trec1 | None => (reflexive t))

    and subc skel
          (mss as Mss{rules,congs,procs,bounds,prems,mk_rews,termless,depth}) t0 =
       (case term_of t0 of
           Abs (a, T, t) =>
             let val b = variant bounds a
                 val (v, t') = Thm.dest_abs (Some ("." ^ b)) t0
                 val mss' = mk_mss (rules, congs, procs, b :: bounds, prems, mk_rews, termless,depth)
                 val skel' = case skel of Abs (_, _, sk) => sk | _ => skel0
             in case botc skel' mss' t' of
                  Some thm => Some (abstract_rule a v thm)
                | None => None
             end
         | t $ _ => (case t of
             Const ("==>", _) $ _  =>
               let val (s, u) = Drule.dest_implies t0
               in impc (s, u, mss) end
           | Abs _ =>
               let val thm = beta_conversion false t0
               in case subc skel0 mss (rhs_of thm) of
                    None => Some thm
                  | Some thm' => Some (transitive thm thm')
               end
           | _  =>
               let fun appc () =
                     let
                       val (tskel, uskel) = case skel of
                           tskel $ uskel => (tskel, uskel)
                         | _ => (skel0, skel0);
                       val (ct, cu) = Thm.dest_comb t0
                     in
                     (case botc tskel mss ct of
                        Some thm1 =>
                          (case botc uskel mss cu of
                             Some thm2 => Some (combination thm1 thm2)
                           | None => Some (combination thm1 (reflexive cu)))
                      | None =>
                          (case botc uskel mss cu of
                             Some thm1 => Some (combination (reflexive ct) thm1)
                           | None => None))
                     end
                   val (h, ts) = strip_comb t
               in case h of
                    Const(a, _) =>
                      (case assoc_string (fst congs, a) of
                         None => appc ()
                       | Some cong =>
(* post processing: some partial applications h t1 ... tj, j <= length ts,
   may be a redex. Example: map (%x.x) = (%xs.xs) wrt map_cong *)
                          (let
                             val thm = congc (prover mss, sign, maxidx) cong t0;
                             val t = if_none (apsome rhs_of thm) t0;
                             val (cl, cr) = Thm.dest_comb t
                             val dVar = Var(("", 0), dummyT)
                             val skel =
                               list_comb (h, replicate (length ts) dVar)
                           in case botc skel mss cl of
                                None => thm
                              | Some thm' => transitive'' thm
                                  (combination thm' (reflexive cr))
                           end handle TERM _ => error "congc result"
                                    | Pattern.MATCH => appc ()))
                  | _ => appc ()
               end)
         | _ => None)

    and impc args =
      if mutsimp
      then let val (prem, conc, mss) = args
           in apsome snd (mut_impc ([], prem, conc, mss)) end
      else nonmut_impc args

    and mut_impc (prems, prem, conc, mss) = (case botc skel0 mss prem of
        None => mut_impc1 (prems, prem, conc, mss)
      | Some thm1 =>
          let val prem1 = rhs_of thm1
          in (case mut_impc1 (prems, prem1, conc, mss) of
              None => Some (None,
                combination (combination refl_implies thm1) (reflexive conc))
            | Some (x, thm2) => Some (x, transitive (combination (combination
                refl_implies thm1) (reflexive conc)) thm2))
          end)

    and mut_impc1 (prems, prem1, conc, mss) =
      let
        fun uncond ({thm, lhs, elhs, perm}) =
          if Thm.no_prems thm then Some lhs else None

        val (lhss1, mss1) =
          if maxidx_of_term (term_of prem1) <> ~1
          then (trace_cterm true
            "Cannot add premise as rewrite rule because it contains (type) unknowns:" prem1;
                ([],mss))
          else let val thm = assume prem1
                   val rrules1 = extract_safe_rrules (mss, thm)
                   val lhss1 = mapfilter uncond rrules1
                   val mss1 = foldl insert_rrule (add_prems (mss, [thm]), rrules1)
               in (lhss1, mss1) end

        fun disch1 thm =
          let val (cB', cC') = dest_eq thm
          in
            implies_elim (Thm.instantiate
              ([], [(cA, prem1), (cB, cB'), (cC, cC')]) Drule.imp_cong)
              (implies_intr prem1 thm)
          end

        fun rebuild None = (case rewritec (prover, sign, maxidx) mss
            (mk_implies (prem1, conc)) of
              None => None
            | Some (thm, _) =>
                let val (prem, conc) = Drule.dest_implies (rhs_of thm)
                in (case mut_impc (prems, prem, conc, mss) of
                    None => Some (None, thm)
                  | Some (x, thm') => Some (x, transitive thm thm'))
                end handle TERM _ => Some (None, thm))
          | rebuild (Some thm2) =
            let val thm = disch1 thm2
            in (case rewritec (prover, sign, maxidx) mss (rhs_of thm) of
                 None => Some (None, thm)
               | Some (thm', _) =>
                   let val (prem, conc) = Drule.dest_implies (rhs_of thm')
                   in (case mut_impc (prems, prem, conc, mss) of
                       None => Some (None, transitive thm thm')
                     | Some (x, thm'') =>
                         Some (x, transitive (transitive thm thm') thm''))
                   end handle TERM _ => Some (None, transitive thm thm'))
            end

        fun simpconc () =
          let val (s, t) = Drule.dest_implies conc
          in case mut_impc (prems @ [prem1], s, t, mss1) of
               None => rebuild None
             | Some (Some i, thm2) =>
                  let
                    val (prem, cC') = Drule.dest_implies (rhs_of thm2);
                    val thm2' = transitive (disch1 thm2) (Thm.instantiate
                      ([], [(cA, prem1), (cB, prem), (cC, cC')])
                      Drule.swap_prems_eq)
                  in if i=0 then apsome (apsnd (transitive thm2'))
                       (mut_impc1 (prems, prem, mk_implies (prem1, cC'), mss))
                     else Some (Some (i-1), thm2')
                  end
             | Some (None, thm) => rebuild (Some thm)
          end handle TERM _ => rebuild (botc skel0 mss1 conc)

      in
        let
          val tsig = Sign.tsig_of sign
          fun reducible t =
            exists (fn lhs => Pattern.matches_subterm tsig (lhs, term_of t)) lhss1;
        in case dropwhile (not o reducible) prems of
            [] => simpconc ()
          | red::rest => (trace_cterm false "Can now reduce premise:" red;
              Some (Some (length rest), reflexive (mk_implies (prem1, conc))))
        end
      end

     (* legacy code - only for backwards compatibility *)
     and nonmut_impc (prem, conc, mss) =
       let val thm1 = if simprem then botc skel0 mss prem else None;
           val prem1 = if_none (apsome rhs_of thm1) prem;
           val maxidx1 = maxidx_of_term (term_of prem1)
           val mss1 =
             if not useprem then mss else
             if maxidx1 <> ~1
             then (trace_cterm true
               "Cannot add premise as rewrite rule because it contains (type) unknowns:" prem1;
                   mss)
             else let val thm = assume prem1
                  in add_safe_simp (add_prems (mss, [thm]), thm) end
       in (case botc skel0 mss1 conc of
           None => (case thm1 of
               None => None
             | Some thm1' => Some (combination
                 (combination refl_implies thm1') (reflexive conc)))
         | Some thm2 =>
           let
             val conc2 = rhs_of thm2;
             val thm2' = implies_elim (Thm.instantiate
               ([], [(cA, prem1), (cB, conc), (cC, conc2)]) Drule.imp_cong)
               (implies_intr prem1 thm2)
           in (case thm1 of
               None => Some thm2'
             | Some thm1' => Some (transitive (combination
                 (combination refl_implies thm1') (reflexive conc)) thm2'))
           end)
       end

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

fun rewrite_cterm mode prover mss ct =
  let val {sign, t, maxidx, ...} = rep_cterm ct
      val Mss{depth, ...} = mss
  in simp_depth := depth;
     bottomc (mode, prover, sign, maxidx) mss ct
  end
  handle THM (s, _, thms) =>
    error ("Exception THM was raised in simplifier:\n" ^ s ^ "\n" ^
      Pretty.string_of (Display.pretty_thms thms));

(*In [A1,...,An]==>B, rewrite the selected A's only -- for rewrite_goals_tac*)
(*Do not rewrite flex-flex pairs*)
fun goals_conv pred cv =
  let fun gconv i ct =
        let val (A,B) = Drule.dest_implies ct
            val (thA,j) = case term_of A of
                  Const("=?=",_)$_$_ => (reflexive A, i)
                | _ => (if pred i then cv A else reflexive A, i+1)
        in  combination (combination refl_implies thA) (gconv j B) end
        handle TERM _ => reflexive ct
  in gconv 1 end;

(* Rewrite A in !!x1,...,xn. A *)
fun forall_conv cv ct =
  let val p as (ct1, ct2) = Thm.dest_comb ct
  in (case pairself term_of p of
      (Const ("all", _), Abs (s, _, _)) =>
         let val (v, ct') = Thm.dest_abs (Some "@") ct2;
         in Thm.combination (Thm.reflexive ct1)
           (Thm.abstract_rule s v (forall_conv cv ct'))
         end
    | _ => cv ct)
  end handle TERM _ => cv ct;

(*Use a conversion to transform a theorem*)
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;

(*Rewrite a cterm*)
fun rewrite_aux _ _ [] = (fn ct => Thm.reflexive ct)
  | rewrite_aux prover full thms = rewrite_cterm (full, false, false) prover (mss_of thms);

(*Rewrite a theorem*)
fun simplify_aux _ _ [] = (fn th => th)
  | simplify_aux prover full thms =
      fconv_rule (rewrite_cterm (full, false, false) prover (mss_of thms));

fun rewrite_thm mode prover mss = fconv_rule (rewrite_cterm mode prover mss);

(*Rewrite the subgoals of a proof state (represented by a theorem) *)
fun rewrite_goals_rule_aux _ []   th = th
  | rewrite_goals_rule_aux prover thms th =
      fconv_rule (goals_conv (K true) (rewrite_cterm (true, true, false) prover
        (mss_of thms))) th;

(*Rewrite the subgoal of a proof state (represented by a theorem) *)
fun rewrite_goal_rule mode prover mss i thm =
  if 0 < i  andalso  i <= nprems_of thm
  then fconv_rule (goals_conv (fn j => j=i) (rewrite_cterm mode prover mss)) thm
  else raise THM("rewrite_goal_rule",i,[thm]);


(*simple term rewriting -- without proofs*)
fun rewrite_term sg rules = Pattern.rewrite_term (Sign.tsig_of sg) (map decomp_simp' rules);

end;

structure BasicMetaSimplifier: BASIC_META_SIMPLIFIER = MetaSimplifier;
open BasicMetaSimplifier;
