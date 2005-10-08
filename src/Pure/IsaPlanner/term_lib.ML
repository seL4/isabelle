(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Title:      Pure/IsaPlanner/term_lib.ML
    ID:		$Id$
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Created:    17 Aug 2002
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  DESCRIPTION:

    Additional code to work with terms.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature TERM_LIB =
sig
    val fo_term_height : term -> int
    val ho_term_height : term -> int

    (* Matching/unification with exceptions handled *)
    val clean_match : theory -> term * term
                      -> ((indexname * (sort * typ)) list
                         * (indexname * (typ * term)) list) option
    val clean_unify : theory -> int -> term * term
                      -> ((indexname * (sort * typ)) list
                         * (indexname * (typ * term)) list) Seq.seq

    (* managing variables in terms, can doing conversions *)
    val bounds_to_frees : term -> term
    val bounds_to_frees_with_vars :
       (string * typ) list -> term -> term

    val change_bounds_to_frees : term -> term
    val change_frees_to_vars : term -> term
    val change_vars_to_frees : term -> term
    val loose_bnds_to_frees :
       (string * typ) list -> term -> term

    (* make all variables named uniquely *)
    val unique_namify : term -> term

		(* breasking up a term and putting it into a normal form
       independent of internal term context *)
    val cleaned_term_conc : term -> term
    val cleaned_term_parts : term -> term list * term
    val cterm_of_term : term -> cterm

    (* terms of theorems and subgoals *)
    val term_of_thm : thm -> term
    val get_prems_of_sg_term : term -> term list
    val triv_thm_from_string : string -> thm

    (* some common term manipulations *)
    val try_dest_Goal : term -> term
    val try_dest_Trueprop : term -> term

    val bot_left_leaf_of : term -> term
    val bot_left_leaf_noabs_of : term -> term

    (* term containing another term - an embedding check *)
    val term_contains : term -> term -> bool

    (* name-convertable checking - like ae-convertable, but allows for
       var's and free's to be mixed - and doesn't used buggy code. :-) *)
		val get_name_eq_member : term -> term list -> term option
    val name_eq_member : term -> term list -> bool
    val term_name_eq :
       term ->
       term ->
       (term * term) list ->
       (term * term) list option

     (* is the typ a function or is it atomic *)
     val is_fun_typ : typ -> bool
     val is_atomic_typ : typ -> bool

    (* variable analysis *)
    val is_some_kind_of_var : term -> bool
    val same_var_check :
       ''a -> ''b -> (''a * ''b) list -> (''a * ''b) list option
		val has_new_vars : term * term -> bool
    val has_new_typ_vars : term * term -> bool
   (* checks to see if the lhs -> rhs is a invalid rewrite rule *)
    val is_not_valid_rwrule : theory -> (term * term) -> bool

    (* get the frees in a term that are of atomic type, ie non-functions *)
    val atomic_frees_of_term : term -> (string * typ) list

    (* get used names in a theorem to avoid upon instantiation. *)
    val usednames_of_term : term -> string list
    val usednames_of_thm : thm -> string list

    (* Isar term skolemisationm and unsolemisation *)
    (* I think this is written also in IsarRTechn and also in somewhere else *)
    (* val skolemise_term : (string,typ) list -> term -> term *)
    val unskolemise_all_term :
        term ->
        (((string * typ) * string) list * term)

    (* given a string describing term then a string for its type, returns
       read term *)
    val readwty : string -> string -> term

    (* pretty stuff *)
    val print_term : term -> unit
    val pretty_print_sort : string list -> string
    val pretty_print_term : term -> string
    val pretty_print_type : typ -> string
    val pretty_print_typelist :
       typ list -> (typ -> string) -> string

    (* for debugging: quickly get a string of a term w.r.t the_context() *)
    val string_of_term : term -> string

    (* Pretty printing in a way that allows them to be parsed by ML.
       these are perhaps redundent, check the standard basis
       lib for generic versions for any datatype? *)
    val writesort : string list -> unit
    val writeterm : term -> unit
    val writetype : typ -> unit
  end


structure TermLib : TERM_LIB =
struct

(* Two kinds of depth measure for HOAS terms, a first order (flat) and a
   higher order one.
   Note: not stable of eta-contraction: embedding eta-expands term,
   thus we assume eta-expanded *)
fun fo_term_height (a $ b) =
    Int.max (1 + fo_term_height b, (fo_term_height a))
  | fo_term_height (Abs(_,_,t)) = fo_term_height t
  | fo_term_height _ = 0;

fun ho_term_height  (a $ b) =
    1 + (Int.max (ho_term_height b, ho_term_height a))
  | ho_term_height (Abs(_,_,t)) = ho_term_height t
  | ho_term_height _ = 0;


(* Higher order matching with exception handled *)
(* returns optional instantiation *)
fun clean_match thy (a as (pat, t)) =
  let val (tyenv, tenv) = Pattern.match thy a
  in SOME (Vartab.dest tyenv, Vartab.dest tenv)
  end handle Pattern.MATCH => NONE;
(* Higher order unification with exception handled, return the instantiations *)
(* given Signature, max var index, pat, tgt *)
(* returns Seq of instantiations *)
fun clean_unify sgn ix (a as (pat, tgt)) =
    let
      (* type info will be re-derived, maybe this can be cached
         for efficiency? *)
      val pat_ty = Term.type_of pat;
      val tgt_ty = Term.type_of tgt;
      (* is it OK to ignore the type instantiation info?
         or should I be using it? *)
      val typs_unify =
          SOME (Sign.typ_unify sgn (pat_ty, tgt_ty) (Term.Vartab.empty, ix))
            handle Type.TUNIFY => NONE;
    in
      case typs_unify of
        SOME (typinsttab, ix2) =>
        let
      (* is it right to throw away the flexes?
         or should I be using them somehow? *)
          fun mk_insts env =
            (Vartab.dest (Envir.type_env env),
             Envir.alist_of env);
          val initenv = Envir.Envir {asol = Vartab.empty,
                                     iTs = typinsttab, maxidx = ix2};
          val useq = (Unify.smash_unifiers (sgn,initenv,[a]))
	            handle UnequalLengths => Seq.empty
		               | Term.TERM _ => Seq.empty;
          fun clean_unify' useq () =
              (case (Seq.pull useq) of
                 NONE => NONE
               | SOME (h,t) => SOME (mk_insts h, Seq.make (clean_unify' t)))
	      handle UnequalLengths => NONE
                   | Term.TERM _ => NONE;
        in
          (Seq.make (clean_unify' useq))
        end
      | NONE => Seq.empty
    end;

fun asm_mk t = assume (cterm_of (the_context()) t);
fun asm_read s = (Thm.assume (read_cterm (the_context()) (s,propT)));


(* more pretty printing code for Isabelle terms etc *)


(* pretty_print_typelist l f = print a typelist.
   l = list of types to print : typ list
   f = function used to print a single type : typ -> string
*)
fun pretty_print_typelist [] f = ""
  | pretty_print_typelist [(h: typ)] (f : typ -> string) = (f h)
  | pretty_print_typelist ((h: typ) :: t) (f : typ -> string) =
      (f h) ^ ", " ^ (pretty_print_typelist t f);



(* pretty_print_sort s = print a sort
   s = sort to print : string list
*)
fun pretty_print_sort [] = ""
  | pretty_print_sort ([h])  = "\"" ^ h ^ "\""
  | pretty_print_sort (h :: t)  = "\"" ^ h ^ "\"," ^ (pretty_print_sort t);


(* pretty_print_type t = print a type
   t = type to print : type
*)
fun pretty_print_type (Type (n, l)) =
      "Type(\"" ^ n ^ "\", [" ^ (pretty_print_typelist l pretty_print_type) ^ "])"
  | pretty_print_type (TFree (n, s)) =
      "TFree(\"" ^ n ^ "\", [" ^ (pretty_print_sort s) ^ "])"
  | pretty_print_type (TVar ((n, i), s)) =
      "TVar( (\"" ^ n ^ "\", " ^ (string_of_int i) ^ "), [" ^ (pretty_print_sort s) ^ "])";


(* pretty_print_term t = print a term prints types and sorts too.
   t = term to print : term
*)
fun pretty_print_term (Const (s, t)) =
      "Const(\"" ^ s ^ "\", " ^ (pretty_print_type t) ^ ")"
  | pretty_print_term (Free (s, t)) =
      "Free(\"" ^ s ^ "\", " ^ (pretty_print_type t) ^ ")"
  | pretty_print_term (Var ((n, i), t)) =
      "Var( (\"" ^ n ^ "\"," ^ (string_of_int i) ^ "), " ^ (pretty_print_type t) ^ ")"
  | pretty_print_term (Bound i) =
      "Bound(" ^ (string_of_int i) ^ ")"
  | pretty_print_term (Abs (s, t, r)) =
      "Abs(\"" ^ s ^ "\"," ^ (pretty_print_type t) ^ ", \n  " ^ (pretty_print_term r) ^ ")"
  | pretty_print_term (op $ (t1, t2)) =
      "(" ^ (pretty_print_term t1) ^ ") $\n (" ^ (pretty_print_term t2) ^ ")";

(* Write the term out nicly instead of just creating a string for it *)
fun writeterm t = writeln (pretty_print_term t);
fun writetype t = writeln (pretty_print_type t);
fun writesort s = writeln (pretty_print_sort s);

fun cterm_of_term (t : term) = Thm.cterm_of (the_context()) t;
fun term_of_thm t = (Thm.prop_of t);

fun string_of_term t = Sign.string_of_term (the_context()) t;
fun print_term t = writeln (string_of_term t);

(* create a trivial HOL thm from anything... *)
fun triv_thm_from_string s = Thm.trivial (cterm_of (the_context()) (read s));

  (* Checks if vars could be the same - alpha convertable
  w.r.t. previous vars, a and b are assumed to be vars,
  free vars, but not bound vars,
  Note frees and vars must all have unique names. *)
  fun same_var_check a b L =
  let
    fun bterm_from t [] = NONE
      | bterm_from t ((a,b)::m) =
          if t = a then SOME b else bterm_from t m

    val bl_opt = bterm_from a L
  in
		case bterm_from a L of
			NONE => SOME ((a,b)::L)
		| SOME b2 => if b2 = b then SOME L else NONE
  end;

  (* FIXME: make more efficient, only require a single new var! *)
  (* check if the new term has any meta variables not in the old term *)
  fun has_new_vars (old, new) =
			(case IsaPLib.lrem (op =) (Term.term_vars old) (Term.term_vars new) of
				 [] => false
			 | (_::_) => true);
  (* check if the new term has any meta variables not in the old term *)
  fun has_new_typ_vars (old, new) =
			(case IsaPLib.lrem (op =) (Term.term_tvars old) (Term.term_tvars new) of
				 [] => false
			 | (_::_) => true);

(* This version avoids name conflicts that might be introduced by
unskolemisation, and returns a list of (string * Term.typ) * string,
where the outer string is the original name, and the inner string is
the new name, and the type is the type of the free variable that was
renamed. *)
local
  fun myadd (n,ty) (L as (renames, names)) =
      let val n' = Syntax.dest_skolem n in
        case (Library.find_first (fn (_,n2) => (n2 = n)) renames) of
          NONE =>
          let val renamedn = Term.variant names n' in
            (renamedn, (((renamedn, ty), n) :: renames,
                        renamedn :: names)) end
        | (SOME ((renamedn, _), _)) => (renamedn, L)
      end
      handle Fail _ => (n, L);

  fun unsk (L,f) (t1 $ t2) =
      let val (L', t1') = unsk (L, I) t1
      in unsk (L', (fn x => f (t1' $ x))) t2 end
    | unsk (L,f) (Abs(n,ty,t)) =
      unsk (L, (fn x => Abs(n,ty,x))) t
    | unsk (L, f) (Free (n,ty)) =
      let val (renamed_n, L') = myadd (n ,ty) L
       in (L', f (Free (renamed_n, ty))) end
    | unsk (L, f) l = (L, f l);
in
fun unskolemise_all_term t =
    let
      val names = Term.add_term_names (t,[])
      val ((renames,names'),t') = unsk (([], names),I) t
    in (renames,t') end;
end

(* true if the type t is a function *)
fun is_fun_typ (Type(s, l)) =
    if s = "fun" then true else false
  | is_fun_typ _ = false;

val is_atomic_typ = not o is_fun_typ;

(* get the frees in a term that are of atomic type, ie non-functions *)
val atomic_frees_of_term =
     List.filter (is_atomic_typ o snd)
     o map Term.dest_Free
     o Term.term_frees;

fun usednames_of_term t = Term.add_term_names (t,[]);
fun usednames_of_thm th =
    let val rep = Thm.rep_thm th
      val hyps = #hyps rep
      val (tpairl,tpairr) = Library.split_list (#tpairs rep)
      val prop = #prop rep
    in
      List.foldr Term.add_term_names [] (prop :: (tpairl @ (tpairr @ hyps)))
    end;

(* read in a string and a top-level type and this will give back a term *)
fun readwty tstr tystr =
  let val thy = the_context()
  in Sign.simple_read_term thy (Sign.read_typ (thy, K NONE) tystr) tstr end;

  (* first term is equal to the second in some name convertable
  way... Note: This differs from the aeconv in the Term.ML file of
  Isabelle in that it allows a var to be alpha-equiv to a free var.

  Also, the isabelle term.ML version of aeconv uses a
  function that it claims doesn't work! *)
  fun term_name_eq (Abs(_,ty1,t1)) (Abs(_,ty2,t2)) l =
    if ty1 = ty2 then term_name_eq t1 t2 l
    else NONE
  | term_name_eq (ah $ at) (bh $ bt) l =
    let
      val lopt = (term_name_eq ah bh l)
    in
      if isSome lopt then
	      term_name_eq at bt (valOf lopt)
      else
        NONE
    end
  | term_name_eq (Const(a,T)) (Const(b,U)) l =
    if a=b andalso T=U then SOME l
    else NONE
  | term_name_eq (a as Free(s1,ty1)) (b as Free(s2,ty2)) l =
    same_var_check a b l
  | term_name_eq (a as Free(s1,ty1)) (b as Var(n2,ty2)) l =
    same_var_check a b l
  | term_name_eq (a as Var(n1,ty1)) (b as Free(s2,ty2)) l =
    same_var_check a b l
  | term_name_eq (a as Var(n1,ty1)) (b as Var(n2,ty2)) l =
    same_var_check a b l
  | term_name_eq (Bound i) (Bound j) l =
    if i = j then SOME l else NONE
  | term_name_eq a b l = ((*writeln ("unchecked case:\n" ^ "a:\n" ^ (pretty_print_term a) ^ "\nb:\n" ^ (pretty_print_term b));*) NONE);

 (* checks to see if the term in a name-equivalent member of the list of terms. *)
  fun get_name_eq_member a [] = NONE
    | get_name_eq_member a (h :: t) =
        if isSome (term_name_eq a h []) then SOME h
				else get_name_eq_member a t;

  fun name_eq_member a [] = false
    | name_eq_member a (h :: t) =
        if isSome (term_name_eq a h []) then true
				else name_eq_member a t;

  (* true if term is a variable *)
  fun is_some_kind_of_var (Free(s, ty)) = true
    | is_some_kind_of_var (Var(i, ty)) = true
    | is_some_kind_of_var (Bound(i)) = true
    | is_some_kind_of_var _ = false;

    (* checks to see if the lhs -> rhs is a invalid rewrite rule *)
(* FIXME: we should really check that there is a subterm on the lhs
which embeds into the rhs, this would be much closer to the normal
notion of valid wave rule - ie there exists at least one case where it
is a valid wave rule... *)
	fun is_not_valid_rwrule thy (lhs, rhs) =
      Term.is_Var (Term.head_of lhs) (* if lhs is essentially just a var *)
      orelse has_new_vars (lhs,rhs)
      orelse has_new_typ_vars (lhs,rhs)
      orelse Pattern.matches_subterm thy (lhs, rhs);


  (* first term contains the second in some name convertable way... *)
  (* note: this is equivalent to an alpha-convertable emedding *)
  (* takes as args: term containing a, term contained b,
     (bound vars of a, bound vars of b),
     current alpha-conversion-pairs,
     returns: bool:can convert, new alpha-conversion table *)
  (* in bellow: we *don't* use: a loose notion that only requires
  variables to match variables, and doesn't worry about the actual
  pattern in the variables. *)
  fun term_contains1 (Bs, FVs) (Abs(s,ty,t)) (Abs(s2,ty2,t2)) =
			if ty = ty2 then
				term_contains1 ((SOME(s,s2,ty)::Bs), FVs) t t2
			else []

  | term_contains1 T t1 (Abs(s2,ty2,t2)) = []

  | term_contains1 (Bs, FVs) (Abs(s,ty,t)) t2 =
    term_contains1 (NONE::Bs, FVs) t t2

  | term_contains1 T (ah $ at) (bh $ bt) =
    (term_contains1 T ah (bh $ bt)) @
    (term_contains1 T at (bh $ bt)) @
    (List.concat (map (fn inT => (term_contains1 inT at bt))
               (term_contains1 T ah bh)))

  | term_contains1 T a (bh $ bt) = []

  | term_contains1 T (ah $ at) b =
		(term_contains1 T ah b) @ (term_contains1 T at b)

  | term_contains1 T a b =
  (* simple list table lookup to check if a named variable has been
  mapped to a variable, if not adds the mapping and return some new
  list mapping, if it is then it checks that the pair are mapped to
  each other, if so returns the current mapping list, else none. *)
		let
			fun bterm_from t [] = NONE
				| bterm_from t ((a,b)::m) =
					if t = a then SOME b else bterm_from t m

  (* check to see if, w.r.t. the variable mapping, two terms are leaf
  terms and are mapped to each other. Note constants are only mapped
  to the same constant. *)
			fun same_leaf_check (T as (Bs,FVs)) (Bound i) (Bound j) =
					let
						fun aux_chk (i1,i2) [] = false
							| aux_chk (0,0) ((SOME _) :: bnds) = true
							| aux_chk (i1,0) (NONE :: bnds) = false
							| aux_chk (i1,i2) ((SOME _) :: bnds) =
								aux_chk (i1 - 1,i2 - 1) bnds
							| aux_chk (i1,i2) (NONE :: bnds) =
								aux_chk (i1,i2 - 1) bnds
					in
						if (aux_chk (i,j) Bs) then [T]
						else []
					end
				| same_leaf_check (T as (Bs,(Fs,Vs)))
                          (a as (Free (an,aty)))
                          (b as (Free (bn,bty))) =
					(case bterm_from an Fs of
						 SOME b2n => if bn = b2n then [T]
												 else [] (* conflict of var name *)
					 | NONE => [(Bs,((an,bn)::Fs,Vs))])
				| same_leaf_check (T as (Bs,(Fs,Vs)))
                          (a as (Var (an,aty)))
                          (b as (Var (bn,bty))) =
					(case bterm_from an Vs of
						 SOME b2n => if bn = b2n then [T]
												 else [] (* conflict of var name *)
					 | NONE => [(Bs,(Fs,(an,bn)::Vs))])
				| same_leaf_check T (a as (Const _)) (b as (Const _)) =
					if a = b then [T] else []
				| same_leaf_check T _ _ = []

		in
			same_leaf_check T a b
		end;

  (* wrapper for term_contains1: checks if the term "a" contains in
  some embedded way, (w.r.t. name -convertable) the term "b" *)
  fun term_contains a b =
			case term_contains1 ([],([],[])) a b of
			  (_ :: _) => true
			| [] => false;

  (* change all bound variables to see ones with appropriate name and
  type *)
  (* naming convention is OK as we use 'variant' from term.ML *)
  (* Note "bounds_to_frees" defined below, its better and quicker, but
  keeps the quantifiers handing about, and changes all bounds, not
  just universally quantified ones. *)
  fun change_bounds_to_frees t =
    let
      val vars = strip_all_vars t
      val frees_names = map (fn Free(s,n) => s | _ => "") (term_frees t)
      val body = strip_all_body t

      fun bnds_to_frees [] _ acc = acc
        | bnds_to_frees ((name,ty)::more) names acc =
            let
	      val new_name = variant names name
	    in
	      bnds_to_frees more (new_name::names) (Free(new_name,ty)::acc)
	    end
    in
      (subst_bounds ((bnds_to_frees vars frees_names []), body))
    end;

(* a runtime-quick function which makes sure that every variable has a
unique name *)
fun unique_namify_aux (ntab,(Abs(s,ty,t))) =
    (case Symtab.lookup ntab s of
       NONE =>
       let
	 val (ntab2,t2) = unique_namify_aux (Symtab.update (s, s) ntab, t)
       in
	 (ntab2,Abs(s,ty,t2))
       end
     | SOME s2 =>
       let
	 val s_new = (Term.variant (Symtab.keys ntab) s)
	 val (ntab2,t2) =
	     unique_namify_aux (Symtab.update (s_new, s_new) ntab, t)
       in
	 (ntab2,Abs(s_new,ty,t2))
       end)
  | unique_namify_aux (ntab,(a $ b)) =
    let
      val (ntab1,t1) = unique_namify_aux (ntab,a)
      val (ntab2,t2) = unique_namify_aux (ntab1,b)		
    in
      (ntab2, t1$t2)
    end
  | unique_namify_aux (nt as (ntab,Const x)) = nt
  | unique_namify_aux (nt as (ntab,f as Free (s,ty))) =
    (case Symtab.lookup ntab s of
       NONE => (Symtab.update (s, s) ntab, f)
     | SOME _ => nt)
  | unique_namify_aux (nt as (ntab,v as Var ((s,i),ty))) =
    (case Symtab.lookup ntab s of
       NONE => (Symtab.update (s, s) ntab, v)
     | SOME _ => nt)
  | unique_namify_aux (nt as (ntab, Bound i)) = nt;
		
fun unique_namify t =
    #2 (unique_namify_aux (Symtab.empty, t));

(* a runtime-quick function which makes sure that every variable has a
unique name and also changes bound variables to free variables, used
for embedding checks, Note that this is a pretty naughty term
manipulation, which doesn't have necessary relation to the original
sematics of the term. This is really a trick for our embedding code. *)

fun bounds_to_frees_aux T (ntab,(Abs(s,ty,t))) =
    (case Symtab.lookup ntab s of
      NONE =>
      let
	val (ntab2,t2) =
          bounds_to_frees_aux ((s,ty)::T) (Symtab.update (s, s) ntab, t)
      in
	(ntab2,Abs(s,ty,t2))
      end
    | SOME s2 =>
      let
	val s_new = (Term.variant (Symtab.keys ntab) s)
	val (ntab2,t2) =
	  bounds_to_frees_aux ((s_new,ty)::T)
            (Symtab.update (s_new, s_new) ntab, t)
      in
	(ntab2,Abs(s_new,ty,t2))
      end)
  | bounds_to_frees_aux T (ntab,(a $ b)) =
    let
      val (ntab1,t1) = bounds_to_frees_aux T (ntab,a)
      val (ntab2,t2) = bounds_to_frees_aux T (ntab1,b)		
    in
      (ntab2, t1$t2)
    end
  | bounds_to_frees_aux T (nt as (ntab,Const x)) = nt
  | bounds_to_frees_aux T (nt as (ntab,f as Free (s,ty))) =
    (case Symtab.lookup ntab s of
      NONE => (Symtab.update (s, s) ntab, f)
    | SOME _ => nt)
  | bounds_to_frees_aux T (nt as (ntab,v as Var ((s,i),ty))) =
     (case Symtab.lookup ntab s of
      NONE => (Symtab.update (s, s) ntab, v)
    | SOME _ => nt)
  | bounds_to_frees_aux T (nt as (ntab, Bound i)) =
    let
      val (s,ty) = List.nth (T,i)
    in
      (ntab, Free (s,ty))
    end;


fun bounds_to_frees t =
    #2 (bounds_to_frees_aux [] (Symtab.empty,t));

fun bounds_to_frees_with_vars vars t =
    #2 (bounds_to_frees_aux vars (Symtab.empty,t));



(* loose bounds to frees *)
fun loose_bnds_to_frees_aux (bnds,vars) (Abs(s,ty,t)) =
    Abs(s,ty,loose_bnds_to_frees_aux (bnds + 1,vars) t)
  | loose_bnds_to_frees_aux (bnds,vars) (a $ b) =
    (loose_bnds_to_frees_aux (bnds,vars) a)
      $ (loose_bnds_to_frees_aux (bnds,vars) b)
  | loose_bnds_to_frees_aux (bnds,vars) (t as (Bound i)) =
    if (bnds <= i) then Free (List.nth (vars,i - bnds))
    else t
  | loose_bnds_to_frees_aux (bnds,vars) t = t;


fun loose_bnds_to_frees vars t =
    loose_bnds_to_frees_aux (0,vars) t;


  fun try_dest_Goal (Const("Goal", _) $ T) = T
    | try_dest_Goal T = T;

  fun try_dest_Trueprop (Const("Trueprop", _) $ T) = T
    | try_dest_Trueprop T = T;

  fun bot_left_leaf_of (l $ r) = bot_left_leaf_of l
    | bot_left_leaf_of (Abs(s,ty,t)) = bot_left_leaf_of t
    | bot_left_leaf_of x = x;

  fun bot_left_leaf_noabs_of (l $ r) = bot_left_leaf_noabs_of l
    | bot_left_leaf_noabs_of x = x;

(* cleaned up normal form version of the subgoal terms conclusion *)
fun cleaned_term_conc t =
    let
      val concl = Logic.strip_imp_concl (change_bounds_to_frees t)
    in
      (try_dest_Trueprop (try_dest_Goal concl))
    end;

(*   fun get_prems_of_sg_term t =
			map opt_dest_Trueprop (Logic.strip_imp_prems t); *)

fun get_prems_of_sg_term t =
		map try_dest_Trueprop (Logic.strip_assums_hyp t);


(* drop premices, clean bound var stuff, and make a trueprop... *)
  fun cleaned_term_parts t =
      let
				val t2 = (change_bounds_to_frees t)
        val concl = Logic.strip_imp_concl t2
				val prems = map try_dest_Trueprop (Logic.strip_imp_prems t2)
      in
				(prems, (try_dest_Trueprop (try_dest_Goal concl)))
      end;

  (* change free variables to vars and visa versa *)
  (* *** check naming is OK, can we just use the vasr old name? *)
  (* *** Check: Logic.varify and Logic.unvarify *)
  fun change_vars_to_frees (a$b) =
        (change_vars_to_frees a) $ (change_vars_to_frees b)
    | change_vars_to_frees (Abs(s,ty,t)) =
        (Abs(s,Type.varifyT ty,change_vars_to_frees t))
    | change_vars_to_frees (Var((s,i),ty)) = (Free(s,Type.unvarifyT ty))
    | change_vars_to_frees l = l;

  fun change_frees_to_vars (a$b) =
        (change_frees_to_vars a) $ (change_frees_to_vars b)
    | change_frees_to_vars (Abs(s,ty,t)) =
        (Abs(s,Type.varifyT ty,change_frees_to_vars t))
    | change_frees_to_vars (Free(s,ty)) = (Var((s,0),Type.varifyT ty))
    | change_frees_to_vars l = l;


end;
