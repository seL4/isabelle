(*  Title: 	Types and Sorts
    ID:         $Id$
    Author:	Tobias Nipkow & Lawrence C Paulson

Maybe type classes should go in a separate module?
*)


signature TYPE =
sig
  structure Symtab:SYMTAB
  type type_sig
  val defaultS: type_sig -> sort
  val extend: type_sig * (class * class list)list * sort *
	      (string list * int)list *
	      (string list * (sort list * class))list -> type_sig
  val freeze: (indexname -> bool) -> term -> term
  val freeze_vars: typ -> typ
  val infer_types: type_sig * typ Symtab.table * (indexname -> typ option) *
		   (indexname -> sort option) * (typ -> string) * typ * term
		   -> term * (indexname*typ)list
  val inst_term_tvars: type_sig * (indexname * typ)list -> term -> term
  val logical_type: type_sig -> string -> bool
   val logical_types: type_sig -> string list
  val merge: type_sig * type_sig -> type_sig
  val thaw_vars: typ -> typ
  val tsig0: type_sig
  val type_errors: type_sig * (typ->string) -> typ * string list -> string list
  val typ_instance: type_sig * typ * typ -> bool
  val typ_match: type_sig -> (indexname*typ)list * (typ*typ) ->
		 (indexname*typ)list
  val unify: type_sig -> (typ*typ) * (indexname*typ)list -> (indexname*typ)list
  val varifyT: typ -> typ
  val varify: term * string list -> term
  exception TUNIFY
  exception TYPE_MATCH;
end;

functor TypeFun(structure Symtab:SYMTAB and Syntax:SYNTAX) : TYPE =
struct
structure Symtab = Symtab

(* Miscellany *)

val commas = space_implode ",";
fun str_of_sort S = "{" ^ commas S ^ "}";
fun str_of_dom dom = "(" ^ commas (map str_of_sort dom) ^ ")";
fun str_of_decl(t,w,C) = t ^ ": " ^ str_of_dom w ^ C;


(* Association list Manipulation  *)


(* two-fold Association list lookup *)

fun assoc2 (aal,(key1,key2)) = case assoc (aal,key1) of
    Some (al) => assoc (al,key2)
  | None => None;



(**** TYPE CLASSES ****)

type domain = sort list;
type arity = domain * class;

datatype type_sig =
   TySg of {classes: class list,
	    default: sort,
	    subclass: (class * class list) list,
	    args: (string * int) list,
	    coreg: (string * (class * domain) list) list };

(* classes: a list of all declared classes;
   default: the default sort attached to all unconstrained TVars
            occurring in a term to be type-inferred;
   subclass: association list representation of subclass relationship;
             (c,cs) is interpreted as "c is a proper subclass of all
             elemenst of cs". Note that c itself is not a memeber of cs.
   args: an association list of all declared types with the number of their
         arguments
   coreg: a two-fold association list of all type arities; (t,al) means that
          type constructor t has the arities in al; an element (c,ss) of al
          represents the arity (ss)c
*)


val tsig0 = TySg{classes = [],
		 default = [],
		 subclass = [],
		 args = [],
		 coreg = []};

fun undcl_class (s) = error("Class " ^ s ^ " has not been declared");

fun undcl_type(c) = "Undeclared type: " ^ c;
fun undcl_type_err(c) = error(undcl_type(c));


(* 'leq' checks the partial order on classes according to the
   statements in the association list 'a' (i.e.'subclass')
*)

fun less a (C,D) = case assoc (a,C) of
     Some(ss) => D mem ss
   | None => undcl_class (C) ;

fun leq a (C,D)  =  C = D orelse less a (C,D);


fun defaultS(TySg{default,...}) = default;

(* 'logical_type' checks if some type declaration t has as range
   a class which is a subclass of "logic" *)

fun logical_type(tsig as TySg{subclass,coreg,...}) t =
  let fun is_log C = leq subclass (C,"logic")
  in case assoc (coreg,t) of
      Some(ars) => exists (is_log o #1) ars
    | None => undcl_type_err(t)
  end;

fun logical_types (tsig as TySg {args, ...}) =
  filter (logical_type tsig) (map #1 args);


(* 'sortorder' checks the ordering on sets of classes,i.e. on sorts:
   S1 <= S2 ,iff for every class C2 in S2 there exists a class C1 in S1
   with C1 <= C2 (according to an association list 'a')
*)

fun sortorder a (S1,S2) =
  forall  (fn C2 => exists  (fn C1 => leq a (C1,C2))  S1)  S2;


(* 'inj' inserts a new class C into a given class set S (i.e.sort) only if
  there exists no class in S which is <= C;
  the resulting set is minimal if S was minimal
*)

fun inj a (C,S) =
  let fun inj1 [] = [C]
        | inj1 (D::T) = if leq a (D,C) then D::T
                        else if leq a (C,D) then inj1 T
                             else D::(inj1 T)
  in inj1 S end;


(* 'union_sort' forms the minimal union set of two sorts S1 and S2
   under the assumption that S2 is minimal *)

fun union_sort a = foldr (inj a);


(* 'elementwise_union' forms elementwise the minimal union set of two
   sort lists under the assumption that the two lists have the same length
*) 

fun elementwise_union a (Ss1,Ss2) = map (union_sort a) (Ss1~~Ss2);
   

(* 'lew' checks for two sort lists the ordering for all corresponding list
   elements (i.e. sorts) *)

fun lew a (w1,w2) = forall (sortorder a)  (w1~~w2);

 
(* 'is_min' checks if a class C is minimal in a given sort S under the 
   assumption that S contains C *) 

fun is_min a S C = not (exists (fn (D) => less a (D,C)) S);


(* 'min_sort' reduces a sort to its minimal classes *)

fun min_sort a S = distinct(filter (is_min a S) S);


(* 'min_domain' minimizes the domain sorts of type declarationsl;
   the function will be applied on the type declarations in extensions *) 

fun min_domain subclass =
  let fun one_min (f,(doms,ran)) = (f, (map (min_sort subclass) doms, ran))
  in map one_min end;


(* 'min_filter' filters a list 'ars' consisting of arities (domain * class)
   and gives back a list of those range classes whose domains meet the 
   predicate 'pred' *)
   
fun min_filter a pred ars =
  let fun filt ([],l) = l
        | filt ((c,x)::xs,l) = if pred(x) then filt (xs,inj a (c,l))
                               else filt (xs,l)
  in filt (ars,[]) end;


(* 'cod_above' filters all arities whose domains are elementwise >= than
   a given domain 'w' and gives back a list of the corresponding range 
   classes *)

fun cod_above (a,w,ars) = min_filter a (fn w' => lew a (w,w')) ars;


(* 'least_sort' returns for a given type its maximum sort:
   - type variables, free types: the sort brought with
   - type constructors: recursive determination of the maximum sort of the
                    arguments if the type is declared in 'coreg' of the 
                    given type signature  *) 

fun least_sort (tsig as TySg{subclass,coreg,...}) =
  let fun ls(T as Type(a,Ts)) =
	  let val ars = case assoc (coreg,a) of Some(ars) => ars
			      | None => raise TYPE(undcl_type a,[T],[]);
	  in cod_above(subclass,map ls Ts,ars) end
	| ls(TFree(a,S)) = S
	| ls(TVar(a,S)) = S
  in ls end;


fun check_has_sort(tsig as TySg{subclass,coreg,...},T,S) =
  if sortorder subclass ((least_sort tsig T),S) then ()
  else raise TYPE("Type not of sort " ^ (str_of_sort S),[T],[])


(*Instantiation of type variables in types *)
fun inst_typ_tvars(tsig,tye) =
  let fun inst(Type(a,Ts)) = Type(a, map inst Ts)
	| inst(T as TFree _) = T
	| inst(T as TVar(v,S)) = (case assoc(tye,v) of
		None => T | Some(U) => (check_has_sort(tsig,U,S); U))
  in inst end;

(*Instantiation of type variables in terms *)
fun inst_term_tvars(tsig,tye) = map_term_types (inst_typ_tvars(tsig,tye));

exception TYPE_MATCH;

(* Typ matching
   typ_match(ts,s,(U,T)) = s' <=> s'(U)=T and s' is an extension of s *)
fun typ_match tsig =
let fun tm(subs, (TVar(v,S), T)) = (case assoc(subs,v) of
		None => ( (v, (check_has_sort(tsig,T,S); T))::subs
			handle TYPE _ => raise TYPE_MATCH )
	      | Some(U) => if U=T then subs else raise TYPE_MATCH)
      | tm(subs, (Type(a,Ts), Type(b,Us))) =
	if a<>b then raise TYPE_MATCH
	else foldl tm (subs, Ts~~Us)
      | tm(subs, (TFree(x), TFree(y))) =
	if x=y then subs else raise TYPE_MATCH
      | tm _ = raise TYPE_MATCH
in tm end;

fun typ_instance(tsig,T,U) = let val x = typ_match tsig ([],(U,T)) in true end
			     handle TYPE_MATCH => false;


(* EXTENDING AND MERGIN TYPE SIGNATURES *)

fun not_ident(s) = error("Must be an identifier: " ^ s);

fun twice(a) = error("Type constructor " ^a^ " has already been declared.");

(*Is the type valid? Accumulates error messages in "errs".*)
fun type_errors (tsig as TySg{classes,subclass,args,...},
                 string_of_typ) (T,errs) =
let fun class_err([],errs) = errs
     |  class_err(S::Ss,errs) = 
          if S mem classes then class_err (Ss,errs)
	  else class_err (Ss,("Class " ^ S ^ " has not been declared") :: errs)
    fun errors(Type(c,Us), errs) =
	let val errs' = foldr errors (Us,errs)
	in case assoc(args,c) of
	     None => (undcl_type c) :: errs
	   | Some(n) => if n=length(Us) then errs'
		        else ("Wrong number of arguments: " ^ c) :: errs
	end
      | errors(TFree(_,S), errs) = class_err(S,errs)
      | errors(TVar(_,S), errs) = class_err(S,errs);
in case errors(T,[]) of
     [] => ((least_sort tsig T; errs)
	    handle TYPE(_,[U],_) => ("Ill-formed type: " ^ string_of_typ U)
				    :: errs)
   | errs' => errs'@errs
end;


(* 'add_class' adds a new class to the list of all existing classes *) 

fun add_class (classes,(s,_)) =
  if s mem classes then error("Class " ^ s ^ " declared twice.")
  else s::classes;

(* 'add_subclass' adds a tuple consisiting of a new class (the new class
   has already been inserted into the 'classes' list) and its
   superclasses (they must be declared in 'classes' too) to the 'subclass' 
   list of the given type signature; 
   furthermore all inherited superclasses according to the superclasses 
   brought with are inserted and there is a check that there are no
   cycles (i.e. C <= D <= C, with C <> D); *)

fun add_subclass classes (subclass,(s,ges)) =
let fun upd (subclass,s') = if s' mem classes then
        let val Some(ges') = assoc (subclass,s)
        in case assoc (subclass,s') of
             Some(sups) => if s mem sups
                           then error(" Cycle :" ^ s^" <= "^ s'^" <= "^ s )
                           else overwrite (subclass,(s,sups union ges'))
           | None => subclass
         end
         else undcl_class(s')
in foldl upd (subclass@[(s,ges)],ges) end;


(* 'extend_classes' inserts all new classes into the corresponding
   lists ('classes','subclass') if possible *)

fun extend_classes (classes,subclass,newclasses) =
  if newclasses = [] then (classes,subclass) else
  let val classes' = foldl add_class (classes,newclasses);
      val subclass' = foldl (add_subclass classes') (subclass,newclasses);
  in (classes',subclass') end;

(* Corregularity *)

(* 'is_unique_decl' checks if there exists just one declaration t:(Ss)C *)

fun is_unique_decl coreg (t,(s,w)) = case assoc2 (coreg,(t,s)) of
      Some(w1) => if w = w1 then () else
	error("There are two declarations\n" ^
              str_of_decl(t,w,s) ^ " and\n" ^
	      str_of_decl(t,w1,s) ^ "\n" ^
              "with the same result class.")
    | None => ();

(* 'restr2' checks if there are two declarations t:(Ss1)C1 and t:(Ss2)C2
   such that C1 >= C2 then Ss1 >= Ss2 (elementwise) *)

fun subs (classes,subclass) C = 
  let fun sub (rl,l) = if leq subclass (l,C) then l::rl else rl
  in foldl sub ([],classes) end;

fun coreg_err(t,(w1,C),(w2,D)) =
    error("Declarations " ^ str_of_decl(t,w1,C) ^ " and "
                          ^ str_of_decl(t,w2,D) ^ " are in conflict");

fun restr2 classes (subclass,coreg) (t,(s,w)) =
  let fun restr ([],test) = ()
        | restr (s1::Ss,test) = (case assoc2 (coreg,(t,s1)) of
              Some (dom) => if lew subclass (test (w,dom)) then restr (Ss,test)
                            else coreg_err (t,(w,s),(dom,s1))
            | None => restr (Ss,test))
      fun forward (t,(s,w)) =
        let val s_sups = case assoc (subclass,s) of
                   Some(s_sups) => s_sups | None => undcl_class(s);
        in restr (s_sups,I) end
      fun backward (t,(s,w)) =
        let val s_subs = subs (classes,subclass) s
        in restr (s_subs,fn (x,y) => (y,x)) end
  in (backward (t,(s,w)); forward (t,(s,w))) end;


fun varying_decls(t) =
    error("Type constructor "^t^" has varying number of arguments.");



(* 'coregular' checks
   - the two restriction conditions 'is_unique_decl' and 'restr2'
   - if the classes in the new type declarations are known in the 
     given type signature
   - if one type constructor has always the same number of arguments;
   if one type declaration has passed all checks it is inserted into 
   the 'coreg' association list of the given type signatrure  *)

fun coregular (classes,subclass,args) =
  let fun ex C = if C mem classes then () else undcl_class(C);

      fun addar(w,C) (coreg,t) = case assoc(args,t) of
            Some(n) => if n <> length w then varying_decls(t) else
                     (is_unique_decl coreg (t,(C,w));
	              (seq o seq) ex w;
	              restr2 classes (subclass,coreg) (t,(C,w));
                      let val Some(ars) = assoc(coreg,t)
                      in overwrite(coreg,(t,(C,w) ins ars)) end)
          | None => undcl_type_err(t);

      fun addts(coreg,(ts,ar)) = foldl (addar ar) (coreg,ts)

  in addts end;


(* 'close' extends the 'coreg' association list after all new type
   declarations have been inserted successfully:
   for every declaration t:(Ss)C , for all classses D with C <= D:
      if there is no declaration t:(Ss')C' with C < C' and C' <= D
      then insert the declaration t:(Ss)D into 'coreg'
   this means, if there exists a declaration t:(Ss)C and there is
   no declaration t:(Ss')D with C <=D then the declaration holds
   for all range classes more general than C *)   
   
fun close (coreg,subclass) =
  let fun check sl (l,(s,dom)) = case assoc (subclass,s) of
          Some(sups) =>
            let fun close_sup (l,sup) =
                  if exists (fn s'' => less subclass (s,s'') andalso
                                       leq subclass (s'',sup)) sl
                  then l
                  else (sup,dom)::l
            in foldl close_sup (l,sups) end
        | None => l;
      fun ext (s,l) = (s, foldl (check (map #1 l)) (l,l));
  in map ext coreg end;

fun add_types(ac,(ts,n)) =
  let fun add_type((args,coreg),t) = case assoc(args,t) of
          Some _ => twice(t) | None => ((t,n)::args,(t,[])::coreg)
  in if n<0
     then error("Type constructor cannot have negative number of arguments")
     else foldl add_type (ac,ts)
  end;

(* 'extend' takes the above described check- and extend-functions to
   extend a given type signature with new classes and new type declarations *)

fun extend (TySg{classes,default,subclass,args,coreg},
            newclasses,newdefault,types,arities) =
let val (classes',subclass') = extend_classes(classes,subclass,newclasses);
    val (args',coreg') = foldl add_types ((args,coreg),types);
    val old_coreg = map #1 coreg;
    fun is_old(c) = if c mem old_coreg then () else undcl_type_err(c);
    fun is_new(c) = if c mem old_coreg then twice(c) else ();
    val coreg'' = foldl (coregular (classes',subclass',args'))
                        (coreg',min_domain subclass' arities);
    val coreg''' = close (coreg'',subclass');
    val default' = if null newdefault then default else newdefault;
in TySg{classes=classes', default=default',subclass=subclass', args=args',
	coreg=coreg'''} end;


(* 'assoc_union' merges two association lists if the contents associated
   the keys are lists *)

fun assoc_union (as1,[]) = as1
  | assoc_union (as1,(key,l2)::as2) = case assoc (as1,key) of
        Some(l1) => assoc_union (overwrite(as1,(key,l1 union l2)),as2)
      | None => assoc_union ((key,l2)::as1,as2);


fun trcl r =
  let val r' = transitive_closure r
  in if exists (op mem) r' then error("Cyclic class structure!") else r' end;


(* 'merge_coreg' builds the union of two 'coreg' lists;
   it only checks the two restriction conditions and inserts afterwards
   all elements of the second list into the first one *) 

fun merge_coreg classes subclass1 =
  let fun test_ar classes (t,ars1) (coreg1,(s,w)) =
        (is_unique_decl coreg1 (t,(s,w));
	 restr2 classes (subclass1,coreg1) (t,(s,w));
	 overwrite (coreg1,(t,(s,w) ins ars1)));

      fun merge_c (coreg1,(c as (t,ars2))) = case assoc (coreg1,t) of
          Some(ars1) => foldl (test_ar classes (t,ars1)) (coreg1,ars2)
        | None => c::coreg1
  in foldl merge_c end;

fun merge_args(args,(t,n)) = case assoc(args,t) of
      Some(m) => if m=n then args else varying_decls(t)
    | None => (t,n)::args;

(* 'merge' takes the above declared functions to merge two type signatures *)

fun merge(TySg{classes=classes1,default=default1,subclass=subclass1,args=args1,
           coreg=coreg1},
	  TySg{classes=classes2,default=default2,subclass=subclass2,args=args2,
           coreg=coreg2}) =
  let val classes' = classes1 union classes2;
      val subclass' = trcl (assoc_union (subclass1,subclass2));
      val args' = foldl merge_args (args1,args2)
      val coreg' = merge_coreg classes' subclass' (coreg1,coreg2);
      val default' = min_sort subclass' (default1 @ default2)
  in TySg{classes=classes' , default=default',subclass=subclass', args=args',
	  coreg=coreg'} 
  end;

(**** TYPE INFERENCE ****)

(*

Input:
- a 'raw' term which contains only dummy types and some explicit type
  constraints encoded as terms.
- the expected type of the term.

Output:
- the correctly typed term
- the substitution needed to unify the actual type of the term with its
  expected type; only the TVars in the expected type are included.

During type inference all TVars in the term have negative index. This keeps
them apart from normal TVars, which is essential, because at the end the type
of the term is unified with the expected type, which contains normal TVars.

1. Add initial type information to the term (add_types).
   This freezes (freeze_vars) TVars in explicitly provided types (eg
   constraints or defaults) by turning them into TFrees.
2. Carry out type inference, possibly introducing new negative TVars.
3. Unify actual and expected type.
4. Turn all (negative) TVars into unique new TFrees (freeze).
5. Thaw all TVars frozen in step 1 (thaw_vars).

*)

(*Raised if types are not unifiable*)
exception TUNIFY;

val tyvar_count = ref(~1);

fun tyinit() = (tyvar_count := ~1);

fun new_tvar_inx() = (tyvar_count := !tyvar_count-1; !tyvar_count)

(*
Generate new TVar.  Index is < ~1 to distinguish it from TVars generated from
variable names (see id_type).  Name is arbitrary because index is new.
*)

fun gen_tyvar(S) = TVar(("'a", new_tvar_inx()),S);
fun new_id_type(a) = TVar(("'"^a, new_tvar_inx()),[]);

(*Occurs check: type variable occurs in type?*)
fun occ v tye =
  let fun occ(Type(_,Ts)) = exists occ Ts
        | occ(TFree _) = false
        | occ(TVar(w,_)) = v=w orelse
                           (case assoc(tye,w) of
                              None   => false
                            | Some U => occ U);
  in occ end;

(*Chase variable assignments in tye.  
  If devar (T,tye) returns a type var then it must be unassigned.*) 
fun devar (T as TVar(v,_), tye) = (case  assoc(tye,v)  of
          Some U =>  devar (U,tye)
        | None   =>  T)
  | devar (T,tye) = T;


(* 'dom' returns for a type constructor t the list of those domains
   which deliver a given range class C *)

fun dom coreg t C = case assoc2 (coreg, (t,C)) of
    Some(Ss) => Ss
  | None => raise TUNIFY;


(* 'Dom' returns the union of all domain lists of 'dom' for a given sort S
   (i.e. a set of range classes ); the union is carried out elementwise
   for the seperate sorts in the domains *)

fun Dom (subclass,coreg) (t,S) =
  let val domlist = map (dom coreg t) S;
  in if null domlist then []
     else foldl (elementwise_union subclass) (hd domlist,tl domlist)
  end;


fun W ((T,S),tsig as TySg{subclass,coreg,...},tye) =
  let fun Wd ((T,S),tye) = W ((devar (T,tye),S),tsig,tye)
      fun Wk(T as TVar(v,S')) = 
	      if sortorder subclass (S',S) then tye
	      else (v,gen_tyvar(union_sort subclass (S',S)))::tye
	| Wk(T as TFree(v,S')) = if sortorder subclass (S',S) then tye
				 else raise TUNIFY
	| Wk(T as Type(f,Ts)) = 
	   if null S then tye 
	   else foldr Wd (Ts~~(Dom (subclass,coreg) (f,S)) ,tye)
  in Wk(T) end;


(* Order-sorted Unification of Types (U)  *)


(* Precondition: both types are well-formed w.r.t. type constructor arities *)
fun unify (tsig as TySg{subclass,coreg,...}) = 
  let fun unif ((T,U),tye) =
        case (devar(T,tye), devar(U,tye)) of
	  (T as TVar(v,S1), U as TVar(w,S2)) =>
             if v=w then tye else
             if sortorder subclass (S1,S2) then (w,T)::tye else
             if sortorder subclass (S2,S1) then (v,U)::tye
             else let val nu = gen_tyvar (union_sort subclass (S1,S2))
                  in (v,nu)::(w,nu)::tye end
        | (T as TVar(v,S), U) =>
             if occ v tye U then raise TUNIFY else W ((U,S),tsig,(v,U)::tye)
        | (U, T as TVar (v,S)) =>
             if occ v tye U then raise TUNIFY else W ((U,S),tsig,(v,U)::tye)
        | (Type(a,Ts),Type(b,Us)) =>
	     if a<>b then raise TUNIFY else foldr unif (Ts~~Us,tye)
        | (T,U) => if T=U then tye else raise TUNIFY
  in unif end;

(*Instantiation of type variables in types*)
(*Pre: instantiations obey restrictions! *)
fun inst_typ tye =
  let fun inst(Type(a,Ts)) = Type(a, map inst Ts)
        | inst(T as TFree _) = T
        | inst(T as TVar(v,_)) =
            (case assoc(tye,v) of Some U => inst U | None => T)
  in inst end;

(*Type inference for polymorphic term*)
fun infer tsig =
  let fun inf(Ts, Const (_,T), tye) = (T,tye)
        | inf(Ts, Free  (_,T), tye) = (T,tye)
        | inf(Ts, Bound i, tye) = ((nth_elem(i,Ts) , tye)
          handle LIST _=> raise TYPE ("loose bound variable", [], [Bound i]))
        | inf(Ts, Var (_,T), tye) = (T,tye)
        | inf(Ts, Abs (_,T,body), tye) = 
	    let val (U,tye') = inf(T::Ts, body, tye) in  (T-->U, tye')  end
        | inf(Ts, f$u, tye) =
	    let val (U,tyeU) = inf(Ts, u, tye);
	        val (T,tyeT) = inf(Ts, f, tyeU);
                fun err s =
                  raise TYPE(s, [inst_typ tyeT T, inst_typ tyeT U], [f$u])
	    in case T of
	         Type("fun",[T1,T2]) =>
		   ( (T2, unify tsig ((T1,U), tyeT))
                     handle TUNIFY => err"type mismatch in application" )
	       | TVar _ => 
                   let val T2 = gen_tyvar([])
                   in (T2, unify tsig ((T, U-->T2), tyeT))
                      handle TUNIFY => err"type mismatch in application"
                   end
               | _ => err"rator must have function type"
           end
  in inf end;

fun freeze_vars(Type(a,Ts)) = Type(a,map freeze_vars Ts)
  | freeze_vars(T as TFree _) = T
  | freeze_vars(TVar(v,S)) = TFree(Syntax.string_of_vname v, S);

(* Attach a type to a constant *)
fun type_const (a,T) = Const(a, incr_tvar (new_tvar_inx()) T);

(*Find type of ident.  If not in table then use ident's name for tyvar
  to get consistent typing.*)
fun type_of_ixn(types,ixn as (a,_)) =
      case types ixn of Some T => freeze_vars T | None => TVar(("'"^a,~1),[]);

fun constrain(term,T) = Const(Syntax.constrainC,T-->T) $ term;
fun constrainAbs(Abs(a,_,body),T) = Abs(a,T,body);

(*

Attach types to a term.  Input is a "parse tree" containing dummy types.
Type constraints are translated and checked for validity wrt tsig.
TVars in constraints are frozen.

The atoms in the resulting term satisfy the following spec:

Const(a,T):
  T is a renamed copy of the generic type of a; renaming decreases index of
  all TVars by new_tvar_inx(), which is less than ~1. The index of all TVars
  in the generic type must be 0 for this to work!

Free(a,T), Var(ixn,T):
  T is either the frozen default type of a or TVar(("'"^a,~1),[])

Abs(a,T,_):
  T is either a type constraint or TVar(("'"^a,i),[]), where i is generated
  by new_tvar_inx(). Thus different abstractions can have the bound variables
  of the same name but different types.

*)

fun add_types (tsig, const_tab, types, sorts, string_of_typ) =
  let val S0 = defaultS tsig;
      fun defS0 ixn = case sorts ixn of Some S => S | None => S0;
      fun prepareT(typ) =
	let val T = Syntax.typ_of_term defS0 typ;
	    val T' = freeze_vars T
	in case type_errors (tsig,string_of_typ) (T,[]) of
	     [] => T'
	   | errs => raise TYPE(cat_lines errs,[T],[])
	end
      fun add (Const(a,_)) =
            (case Symtab.lookup(const_tab, a) of
               Some T => type_const(a,T)
             | None => raise TYPE ("No such constant: "^a, [], []))
        | add (Bound i) = Bound i
        | add (Free(a,_)) =
            (case Symtab.lookup(const_tab, a) of
               Some T => type_const(a,T)
             | None => Free(a, type_of_ixn(types,(a,~1))))
        | add (Var(ixn,_)) = Var(ixn, type_of_ixn(types,ixn))
        | add (Abs(a,_,body)) = Abs(a, new_id_type a, add body)
        | add ((f as Const(a,_)$t1)$t2) =
	    if a=Syntax.constrainC then constrain(add t1,prepareT t2) else
	    if a=Syntax.constrainAbsC then constrainAbs(add t1,prepareT t2)
	    else add f $ add t2
        | add (f$t) = add f $ add t
  in  add  end;


(* Post-Processing *)


(*Instantiation of type variables in terms*)
fun inst_types tye = map_term_types (inst_typ tye);

(*Delete explicit constraints -- occurrences of "_constrain" *)
fun unconstrain (Abs(a,T,t)) = Abs(a, T, unconstrain t)
  | unconstrain ((f as Const(a,_)) $ t) =
      if a=Syntax.constrainC then unconstrain t
      else unconstrain f $ unconstrain t
  | unconstrain (f$t) = unconstrain f $ unconstrain t
  | unconstrain (t) = t;


(* Turn all TVars which satisfy p into new TFrees *)
fun freeze p t =
  let val fs = add_term_tfree_names(t,[]);
      val inxs = filter p (add_term_tvar_ixns(t,[]));
      val vmap = inxs ~~ variantlist(map #1 inxs, fs);
      fun free(Type(a,Ts)) = Type(a, map free Ts)
        | free(T as TVar(v,S)) =
            (case assoc(vmap,v) of None => T | Some(a) => TFree(a,S))
        | free(T as TFree _) = T
  in map_term_types free t end;

(* Thaw all TVars that were frozen in freeze_vars *)
fun thaw_vars(Type(a,Ts)) = Type(a, map thaw_vars Ts)
  | thaw_vars(T as TFree(a,S)) = (case explode a of
	  "?"::"'"::vn => let val ((b,i),_) = Syntax.scan_varname vn
			  in TVar(("'"^b,i),S) end
	| _ => T)
  | thaw_vars(T) = T;


fun restrict tye =
  let fun clean(tye1, ((a,i),T)) =
	if i < 0 then tye1 else ((a,i),inst_typ tye T) :: tye1
  in foldl clean ([],tye) end


(*Infer types for term t using tables. Check that t's type and T unify *)

fun infer_term (tsig, const_tab, types, sorts, string_of_typ, T, t) =
  let val u = add_types (tsig, const_tab, types, sorts, string_of_typ) t;
      val (U,tye) = infer tsig ([], u, []);
      val uu = unconstrain u;
      val tye' = unify tsig ((T,U),tye) handle TUNIFY => raise TYPE
	("Term does not have expected type", [T, U], [inst_types tye uu])
      val Ttye = restrict tye' (* restriction to TVars in T *)
      val all = Const("", Type("", map snd Ttye)) $ (inst_types tye' uu)
        (* all is a dummy term which contains all exported TVars *)
      val Const(_,Type(_,Ts)) $ u'' =
            map_term_types thaw_vars (freeze (fn (_,i) => i<0) all)
        (* turn all internally generated TVars into TFrees
           and thaw all initially frozen TVars *)
  in (u'', (map fst Ttye) ~~ Ts) end;

fun infer_types args = (tyinit(); infer_term args);


(* Turn TFrees into TVars to allow types & axioms to be written without "?" *)
fun varifyT(Type(a,Ts)) = Type(a,map varifyT Ts)
  | varifyT(TFree(a,S)) = TVar((a,0),S)
  | varifyT(T) = T;

(* Turn TFrees except those in fixed into new TVars *)
fun varify(t,fixed) =
  let val fs = add_term_tfree_names(t,[]) \\ fixed;
      val ixns = add_term_tvar_ixns(t,[]);
      val fmap = fs ~~ variantlist(fs, map #1 ixns)
      fun thaw(Type(a,Ts)) = Type(a, map thaw Ts)
        | thaw(T as TVar _) = T
        | thaw(T as TFree(a,S)) =
            (case assoc(fmap,a) of None => T | Some b => TVar((b,0),S))
  in map_term_types thaw t end;


end;
