(*  Title:      HOLCF/domain/library.ML
    ID:         $Id$
    Author : David von Oheimb
    Copyright 1995, 1996 TU Muenchen

library for domain section
*)


(* ----- general support ---------------------------------------------------- *)

fun Id x = x;

fun mapn f n []      = []
|   mapn f n (x::xs) = (f n x) :: mapn f (n+1) xs;

fun foldr'' f (l,f2) = let fun itr []  = raise LIST "foldr''"
			     | itr [a] = f2 a
			     | itr (a::l) = f(a, itr l)
in  itr l  end;
fun foldr' f l = foldr'' f (l,Id);
fun map_cumulr f start xs = foldr (fn (x,(ys,res))=>case f(x,res) of (y,res2) =>
						  (y::ys,res2)) (xs,([],start));


fun first  (x,_,_) = x; fun second (_,x,_) = x; fun third  (_,_,x) = x;
fun upd_first  f (x,y,z) = (f x,   y,   z);
fun upd_second f (x,y,z) = (  x, f y,   z);
fun upd_third  f (x,y,z) = (  x,   y, f z);

fun atomize thm = let val r_inst = read_instantiate;
    fun at  thm = case concl_of thm of
      _$(Const("op &",_)$_$_)       => at(thm RS conjunct1)@at(thm RS conjunct2)
    | _$(Const("All" ,_)$Abs(s,_,_))=> at(thm RS (r_inst [("x","?"^s)] spec))
    | _				    => [thm];
in map zero_var_indexes (at thm) end;

(* ----- specific support for domain ---------------------------------------- *)

structure Domain_Library = struct

open HOLCFLogic;

exception Impossible of string;
fun Imposs msg = raise Impossible ("Domain:"^msg);

(* ----- name handling ----- *)

val strip_esc = let fun strip ("'" :: c :: cs) = c :: strip cs
		    |   strip ["'"] = []
		    |   strip (c :: cs) = c :: strip cs
		    |   strip [] = [];
in implode o strip o Symbol.explode end;

fun extern_name con = case Symbol.explode con of 
		   ("o"::"p"::" "::rest) => implode rest
		   | _ => con;
fun dis_name  con = "is_"^ (extern_name con);
fun dis_name_ con = "is_"^ (strip_esc   con);

(* make distinct names out of the type list, 
   forbidding "o","n..","x..","f..","P.." as names *)
(* a number string is added if necessary *)
fun mk_var_names ids : string list = let
    fun nonreserved s = if s mem ["n","x","f","P"] then s^"'" else s;
    fun index_vnames(vn::vns,occupied) =
          (case assoc(occupied,vn) of
             None => if vn mem vns
                     then (vn^"1") :: index_vnames(vns,(vn,1)  ::occupied)
                     else  vn      :: index_vnames(vns,          occupied)
           | Some(i) => (vn^(string_of_int (i+1)))
				   :: index_vnames(vns,(vn,i+1)::occupied))
      | index_vnames([],occupied) = [];
in index_vnames(map nonreserved ids, [("O",0),("o",0)]) end;

fun rep_Type  (Type  x) = x | rep_Type  _ = Imposs "library:rep_Type";
fun rep_TFree (TFree x) = x | rep_TFree _ = Imposs "library:rep_TFree";
val tsig_of = #tsig o Sign.rep_sg;

fun pcpo_type sg t = Sign.of_sort sg (Sign.certify_typ sg t, pcpoS);
fun string_of_typ sg = Sign.string_of_typ sg o Sign.certify_typ sg;
fun str2typ sg = typ_of o read_ctyp sg;

(* ----- constructor list handling ----- *)

type cons = (string *			(* operator name of constr *)
	    ((bool*int)*		(*  (lazy,recursive element or ~1) *)
	      string*			(*   selector name    *)
	      string)			(*   argument name    *)
	    list);			(* argument list      *)
type eq = (string *		(* name      of abstracted type *)
	   typ list) *		(* arguments of abstracted type *)
	  cons list;		(* represented type, as a constructor list *)

fun rec_of arg  = snd (first arg);
fun is_lazy arg = fst (first arg);
val sel_of    =       second;
val     vname =       third;
val upd_vname =   upd_third;
fun is_rec         arg = rec_of arg >=0;
fun is_nonlazy_rec arg = is_rec arg andalso not (is_lazy arg);
fun nonlazy     args   = map vname (filter_out is_lazy    args);
fun nonlazy_rec args   = map vname (filter is_nonlazy_rec args);

(* ----- support for type and mixfix expressions ----- *)

infixr 5 -->;

(* ----- support for term expressions ----- *)

fun %: s = Free(s,dummyT);
fun %# arg = %:(vname arg);
fun %%: s = Const(s,dummyT);

local open HOLogic in
val mk_trp = mk_Trueprop;
fun mk_conj (S,T) = conj $ S $ T;
fun mk_disj (S,T) = disj $ S $ T;
fun mk_imp  (S,T) = imp  $ S $ T;
fun mk_lam  (x,T) = Abs(x,dummyT,T);
fun mk_all  (x,P) = HOLogic.mk_all (x,dummyT,P);
local 
		    fun sg [s]     = %:s
		    |   sg (s::ss) = %%:"_classes" $ %:s $ sg ss
	 	    |   sg _       = Imposs "library:sg";
		    fun sf [] = %%:"_emptysort"
		    |   sf s  = %%:"_sort" $ sg s
		    fun tf (Type (s,args)) = foldl (op $) (%:s,map tf args)
		    |   tf (TFree(s,sort)) = %%:"_ofsort" $ %:s $ sf sort
		    |   tf _               = Imposs "library:tf";
in
fun mk_constrain      (typ,T) = %%:"_constrain" $ T $ tf typ;
fun mk_constrainall (x,typ,P) = %%:"All" $ (%%:"_constrainAbs" $ mk_lam(x,P) $ tf typ);
end;
fun mk_ex   (x,P) = mk_exists (x,dummyT,P);
end;

fun mk_All  (x,P) = %%:"all" $ mk_lam(x,P); (* meta universal quantification *)

infixr 0 ===>;fun S ===> T = %%:"==>" $ S $ T;
infixr 0 ==>;fun S ==> T = mk_trp S ===> mk_trp T;
infix 0 ==;  fun S ==  T = %%:"==" $ S $ T;
infix 1 ===; fun S === T = %%:"op =" $ S $ T;
infix 1 ~=;  fun S ~=  T = mk_not (S === T);
infix 1 <<;  fun S <<  T = %%:"op <<" $ S $ T;
infix 1 ~<<; fun S ~<< T = mk_not (S << T);

infix 9 `  ; fun f`  x = %%:"Rep_CFun" $ f $ x;
infix 9 `% ; fun f`% s = f` %: s;
infix 9 `%%; fun f`%%s = f` %%:s;
fun mk_cRep_CFun (F,As) = foldl (op `) (F,As);
fun con_app2 con f args = mk_cRep_CFun(%%:con,map f args);
fun con_app con = con_app2 con %#;
fun if_rec  arg f y   = if is_rec arg then f (rec_of arg) else y;
fun app_rec_arg p arg = if_rec arg (fn n => fn x => (p n)`x) Id (%# arg);
fun prj _  _  x (   _::[]) _ = x
|   prj f1 _  x (_::y::ys) 0 = f1 x y
|   prj f1 f2 x (y::   ys) j = prj f1 f2 (f2 x y) ys (j-1);
fun fix_tp (tn, args) = (tn, map (K oneT) args); (* instantiate type to
						    avoid type varaibles *)
fun  proj x      = prj (fn S => K(%%:"fst" $S)) (fn S => K(%%:"snd" $S)) x;
fun cproj x      = prj (fn S => K(%%:"cfst"`S)) (fn S => K(%%:"csnd"`S)) x;
fun cproj' T eqs = prj 
	(fn S => fn t => Const("cfst",mk_prodT(dummyT,t)->>dummyT)`S) 
	(fn S => fn t => Const("csnd",mk_prodT(t,dummyT)->>dummyT)`S) 
		       T (map ((fn tp => tp ->> tp) o Type o fix_tp o fst) eqs);
fun lift tfn = foldr (fn (x,t)=> (mk_trp(tfn x) ===> t));

fun /\ v T = %%:"Abs_CFun" $ mk_lam(v,T);
fun /\# (arg,T) = /\ (vname arg) T;
infixr 9 oo; fun S oo T = %%:"cfcomp"`S`T;
val UU = %%:"UU";
fun strict f = f`UU === UU;
fun defined t = t ~= UU;
fun cpair (S,T) = %%:"cpair"`S`T;
fun lift_defined f = lift (fn x => defined (f x));
fun bound_arg vns v = Bound(length vns -find_index_eq v vns -1);

fun cont_eta_contract (Const("Abs_CFun",TT) $ Abs(a,T,body)) = 
      (case cont_eta_contract body  of
        body' as (Const("Rep_CFun",Ta) $ f $ Bound 0) => 
	  if not (0 mem loose_bnos f) then incr_boundvars ~1 f 
	  else   Const("Abs_CFun",TT) $ Abs(a,T,body')
      | body' => Const("Abs_CFun",TT) $ Abs(a,T,body'))
|   cont_eta_contract(f$t) = cont_eta_contract f $ cont_eta_contract t
|   cont_eta_contract t    = t;

fun idx_name dnames s n = s^(if length dnames = 1 then "" else string_of_int n);
fun when_funs cons = if length cons = 1 then ["f"] 
                     else mapn (fn n => K("f"^(string_of_int n))) 1 cons;
fun when_body cons funarg = let
	fun one_fun n (_,[]  ) = /\ "dummy" (funarg(1,n))
	|   one_fun n (_,args) = let
		val l2 = length args;
		fun idxs m arg = (if is_lazy arg then fn x=> %%:"fup"`%%"ID"`x
					         else Id) (Bound(l2-m));
		in cont_eta_contract (foldr'' 
			(fn (a,t) => %%:"ssplit"`(/\# (a,t)))
			(args,
			fn a=> /\#(a,(mk_cRep_CFun(funarg(l2,n),mapn idxs 1 args))))
			) end;
in (if length cons = 1 andalso length(snd(hd cons)) <= 1
    then fn t => %%:"strictify"`t else Id)
     (foldr' (fn (x,y)=> %%:"sscase"`x`y) (mapn one_fun 1 cons)) end;
end; (* struct *)
