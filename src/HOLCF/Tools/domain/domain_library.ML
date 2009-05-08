(*  Title:      HOLCF/Tools/domain/domain_library.ML
    Author:     David von Oheimb

Library for domain command.
*)


(* ----- general support ---------------------------------------------------- *)

fun mapn f n []      = []
|   mapn f n (x::xs) = (f n x) :: mapn f (n+1) xs;

fun foldr'' f (l,f2) = let fun itr []  = raise Fail "foldr''"
			     | itr [a] = f2 a
			     | itr (a::l) = f(a, itr l)
in  itr l  end;
fun map_cumulr f start xs = List.foldr (fn (x,(ys,res))=>case f(x,res) of (y,res2) =>
						  (y::ys,res2)) ([],start) xs;


fun first  (x,_,_) = x; fun second (_,x,_) = x; fun third  (_,_,x) = x;
fun upd_first  f (x,y,z) = (f x,   y,   z);
fun upd_second f (x,y,z) = (  x, f y,   z);
fun upd_third  f (x,y,z) = (  x,   y, f z);

fun atomize ctxt thm = let val r_inst = read_instantiate ctxt;
    fun at  thm = case concl_of thm of
      _$(Const("op &",_)$_$_)       => at(thm RS conjunct1)@at(thm RS conjunct2)
    | _$(Const("All" ,_)$Abs(s,_,_))=> at(thm RS (r_inst [(("x", 0), "?" ^ s)] spec))
    | _				    => [thm];
in map zero_var_indexes (at thm) end;

(* infix syntax *)

infixr 5 -->;
infixr 6 ->>;
infixr 0 ===>;
infixr 0 ==>;
infix 0 ==;
infix 1 ===;
infix 1 ~=;
infix 1 <<;
infix 1 ~<<;

infix 9 `  ;
infix 9 `% ;
infix 9 `%%;


(* ----- specific support for domain ---------------------------------------- *)

signature DOMAIN_LIBRARY =
sig
  val Imposs : string -> 'a;
  val pcpo_type : theory -> typ -> bool;
  val string_of_typ : theory -> typ -> string;

  (* Creating HOLCF types *)
  val mk_cfunT : typ * typ -> typ;
  val ->> : typ * typ -> typ;
  val mk_ssumT : typ * typ -> typ;
  val mk_sprodT : typ * typ -> typ;
  val mk_uT : typ -> typ;
  val oneT : typ;
  val trT : typ;
  val mk_maybeT : typ -> typ;
  val mk_ctupleT : typ list -> typ;
  val mk_TFree : string -> typ;
  val pcpoS : sort;

  (* Creating HOLCF terms *)
  val %: : string -> term;
  val %%: : string -> term;
  val ` : term * term -> term;
  val `% : term * string -> term;
  val /\ : string -> term -> term;
  val UU : term;
  val TT : term;
  val FF : term;
  val mk_up : term -> term;
  val mk_sinl : term -> term;
  val mk_sinr : term -> term;
  val mk_stuple : term list -> term;
  val mk_ctuple : term list -> term;
  val mk_fix : term -> term;
  val mk_iterate : term * term * term -> term;
  val mk_fail : term;
  val mk_return : term -> term;
  val cproj : term -> 'a list -> int -> term;
  val list_ccomb : term * term list -> term;
  val con_app : string -> ('a * 'b * string) list -> term;
  val con_app2 : string -> ('a -> term) -> 'a list -> term;
  val proj : term -> 'a list -> int -> term;
  val prj : ('a -> 'b -> 'a) -> ('a -> 'b -> 'a) -> 'a -> 'b list -> int -> 'a;
  val mk_ctuple_pat : term list -> term;
  val mk_branch : term -> term;

  (* Creating propositions *)
  val mk_conj : term * term -> term;
  val mk_disj : term * term -> term;
  val mk_imp : term * term -> term;
  val mk_lam : string * term -> term;
  val mk_all : string * term -> term;
  val mk_ex : string * term -> term;
  val mk_constrain : typ * term -> term;
  val mk_constrainall : string * typ * term -> term;
  val === : term * term -> term;
  val << : term * term -> term;
  val ~<< : term * term -> term;
  val strict : term -> term;
  val defined : term -> term;
  val mk_adm : term -> term;
  val mk_compact : term -> term;
  val lift : ('a -> term) -> 'a list * term -> term;
  val lift_defined : ('a -> term) -> 'a list * term -> term;

  (* Creating meta-propositions *)
  val mk_trp : term -> term; (* HOLogic.mk_Trueprop *)
  val == : term * term -> term;
  val ===> : term * term -> term;
  val ==> : term * term -> term;
  val mk_All : string * term -> term;

  (* Domain specifications *)
  type arg = (bool * int * DatatypeAux.dtyp) * string option * string;
  type cons = string * arg list;
  type eq = (string * typ list) * cons list;
  val is_lazy : arg -> bool;
  val rec_of : arg -> int;
  val sel_of : arg -> string option;
  val vname : arg -> string;
  val upd_vname : (string -> string) -> arg -> arg;
  val is_rec : arg -> bool;
  val is_nonlazy_rec : arg -> bool;
  val nonlazy : arg list -> string list;
  val nonlazy_rec : arg list -> string list;
  val %# : arg -> term;
  val /\# : arg * term -> term;
  val when_body : cons list -> (int * int -> term) -> term;
  val when_funs : 'a list -> string list;
  val bound_arg : ''a list -> ''a -> term; (* ''a = arg or string *)
  val idx_name : 'a list -> string -> int -> string;
  val app_rec_arg : (int -> term) -> arg -> term;

  (* Name mangling *)
  val strip_esc : string -> string;
  val extern_name : string -> string;
  val dis_name : string -> string;
  val mat_name : string -> string;
  val pat_name : string -> string;
  val mk_var_names : string list -> string list;
end;

structure Domain_Library :> DOMAIN_LIBRARY =
struct

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
fun mat_name  con = "match_"^ (extern_name con);
fun mat_name_ con = "match_"^ (strip_esc   con);
fun pat_name  con = (extern_name con) ^ "_pat";
fun pat_name_ con = (strip_esc   con) ^ "_pat";

(* make distinct names out of the type list, 
   forbidding "o","n..","x..","f..","P.." as names *)
(* a number string is added if necessary *)
fun mk_var_names ids : string list = let
    fun nonreserved s = if s mem ["n","x","f","P"] then s^"'" else s;
    fun index_vnames(vn::vns,occupied) =
          (case AList.lookup (op =) occupied vn of
             NONE => if vn mem vns
                     then (vn^"1") :: index_vnames(vns,(vn,1)  ::occupied)
                     else  vn      :: index_vnames(vns,          occupied)
           | SOME(i) => (vn^(string_of_int (i+1)))
				   :: index_vnames(vns,(vn,i+1)::occupied))
      | index_vnames([],occupied) = [];
in index_vnames(map nonreserved ids, [("O",0),("o",0)]) end;

fun pcpo_type sg t = Sign.of_sort sg (Sign.certify_typ sg t, @{sort pcpo});
fun string_of_typ sg = Syntax.string_of_typ_global sg o Sign.certify_typ sg;

(* ----- constructor list handling ----- *)

type arg =
  (bool * int * DatatypeAux.dtyp) *	(*  (lazy,recursive element or ~1) *)
  string option *			(*   selector name    *)
  string;				(*   argument name    *)

type cons =
  string *				(* operator name of constr *)
  arg list;				(* argument list      *)

type eq =
  (string *		(* name      of abstracted type *)
   typ list) *		(* arguments of abstracted type *)
  cons list;		(* represented type, as a constructor list *)

fun rec_of arg  = second (first arg);
fun is_lazy arg = first (first arg);
val sel_of    =       second;
val     vname =       third;
val upd_vname =   upd_third;
fun is_rec         arg = rec_of arg >=0;
fun is_nonlazy_rec arg = is_rec arg andalso not (is_lazy arg);
fun nonlazy     args   = map vname (filter_out is_lazy    args);
fun nonlazy_rec args   = map vname (List.filter is_nonlazy_rec args);

(* ----- support for type and mixfix expressions ----- *)

fun mk_uT T = Type(@{type_name "u"}, [T]);
fun mk_cfunT (T, U) = Type(@{type_name "->"}, [T, U]);
fun mk_sprodT (T, U) = Type(@{type_name "**"}, [T, U]);
fun mk_ssumT (T, U) = Type(@{type_name "++"}, [T, U]);
val oneT = @{typ one};
val trT = @{typ tr};

val op ->> = mk_cfunT;

fun mk_TFree s = TFree ("'" ^ s, @{sort pcpo});

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
fun mk_ex   (x,P) = mk_exists (x,dummyT,P);
val mk_constrain = uncurry TypeInfer.constrain;
fun mk_constrainall (x,typ,P) = %%:"All" $ (TypeInfer.constrain (typ --> boolT) (mk_lam(x,P)));
end

fun mk_All  (x,P) = %%:"all" $ mk_lam(x,P); (* meta universal quantification *)

infixr 0 ===>;  fun S ===> T = %%:"==>" $ S $ T;
infixr 0 ==>;   fun S ==> T = mk_trp S ===> mk_trp T;
infix 0 ==;     fun S ==  T = %%:"==" $ S $ T;
infix 1 ===;    fun S === T = %%:"op =" $ S $ T;
infix 1 ~=;     fun S ~=  T = HOLogic.mk_not (S === T);
infix 1 <<;     fun S <<  T = %%: @{const_name Porder.below} $ S $ T;
infix 1 ~<<;    fun S ~<< T = HOLogic.mk_not (S << T);

infix 9 `  ; fun f ` x = %%: @{const_name Rep_CFun} $ f $ x;
infix 9 `% ; fun f`% s = f` %: s;
infix 9 `%%; fun f`%%s = f` %%:s;

fun mk_adm t = %%: @{const_name adm} $ t;
fun mk_compact t = %%: @{const_name compact} $ t;
val ID = %%: @{const_name ID};
fun mk_strictify t = %%: @{const_name strictify}`t;
fun mk_cfst t = %%: @{const_name cfst}`t;
fun mk_csnd t = %%: @{const_name csnd}`t;
(*val csplitN    = "Cprod.csplit";*)
(*val sfstN      = "Sprod.sfst";*)
(*val ssndN      = "Sprod.ssnd";*)
fun mk_ssplit t = %%: @{const_name ssplit}`t;
fun mk_sinl t = %%: @{const_name sinl}`t;
fun mk_sinr t = %%: @{const_name sinr}`t;
fun mk_sscase (x, y) = %%: @{const_name sscase}`x`y;
fun mk_up t = %%: @{const_name up}`t;
fun mk_fup (t,u) = %%: @{const_name fup} ` t ` u;
val ONE = @{term ONE};
val TT = @{term TT};
val FF = @{term FF};
fun mk_iterate (n,f,z) = %%: @{const_name iterate} $ n ` f ` z;
fun mk_fix t = %%: @{const_name fix}`t;
fun mk_return t = %%: @{const_name Fixrec.return}`t;
val mk_fail = %%: @{const_name Fixrec.fail};

fun mk_branch t = %%: @{const_name Fixrec.branch} $ t;

val pcpoS = @{sort pcpo};

val list_ccomb = Library.foldl (op `); (* continuous version of list_comb *)
fun con_app2 con f args = list_ccomb(%%:con,map f args);
fun con_app con = con_app2 con %#;
fun if_rec  arg f y   = if is_rec arg then f (rec_of arg) else y;
fun app_rec_arg p arg = if_rec arg (fn n => fn x => (p n)`x) I (%# arg);
fun prj _  _  x (   _::[]) _ = x
|   prj f1 _  x (_::y::ys) 0 = f1 x y
|   prj f1 f2 x (y::   ys) j = prj f1 f2 (f2 x y) ys (j-1);
fun  proj x      = prj (fn S => K(%%:"fst" $S)) (fn S => K(%%:"snd" $S)) x;
fun cproj x      = prj (fn S => K(mk_cfst S)) (fn S => K(mk_csnd S)) x;
fun lift tfn = Library.foldr (fn (x,t)=> (mk_trp(tfn x) ===> t));

fun /\ v T = %%: @{const_name Abs_CFun} $ mk_lam(v,T);
fun /\# (arg,T) = /\ (vname arg) T;
infixr 9 oo; fun S oo T = %%: @{const_name cfcomp}`S`T;
val UU = %%: @{const_name UU};
fun strict f = f`UU === UU;
fun defined t = t ~= UU;
fun cpair (t,u) = %%: @{const_name cpair}`t`u;
fun spair (t,u) = %%: @{const_name spair}`t`u;
fun mk_ctuple [] = HOLogic.unit (* used in match_defs *)
|   mk_ctuple ts = foldr1 cpair ts;
fun mk_stuple [] = ONE
|   mk_stuple ts = foldr1 spair ts;
fun mk_ctupleT [] = HOLogic.unitT   (* used in match_defs *)
|   mk_ctupleT Ts = foldr1 HOLogic.mk_prodT Ts;
fun mk_maybeT T = Type ("Fixrec.maybe",[T]);
fun cpair_pat (p1,p2) = %%: @{const_name cpair_pat} $ p1 $ p2;
val mk_ctuple_pat = foldr1 cpair_pat;
fun lift_defined f = lift (fn x => defined (f x));
fun bound_arg vns v = Bound(length vns -find_index_eq v vns -1);

fun cont_eta_contract (Const("Cfun.Abs_CFun",TT) $ Abs(a,T,body)) = 
      (case cont_eta_contract body  of
        body' as (Const("Cfun.Rep_CFun",Ta) $ f $ Bound 0) => 
	  if not (0 mem loose_bnos f) then incr_boundvars ~1 f 
	  else   Const("Cfun.Abs_CFun",TT) $ Abs(a,T,body')
      | body' => Const("Cfun.Abs_CFun",TT) $ Abs(a,T,body'))
|   cont_eta_contract(f$t) = cont_eta_contract f $ cont_eta_contract t
|   cont_eta_contract t    = t;

fun idx_name dnames s n = s^(if length dnames = 1 then "" else string_of_int n);
fun when_funs cons = if length cons = 1 then ["f"] 
                     else mapn (fn n => K("f"^(string_of_int n))) 1 cons;
fun when_body cons funarg = let
	fun one_fun n (_,[]  ) = /\ "dummy" (funarg(1,n))
	|   one_fun n (_,args) = let
		val l2 = length args;
		fun idxs m arg = (if is_lazy arg then (fn t => mk_fup (ID, t))
					         else I) (Bound(l2-m));
		in cont_eta_contract (foldr'' 
			(fn (a,t) => mk_ssplit (/\# (a,t)))
			(args,
			fn a=> /\#(a,(list_ccomb(funarg(l2,n),mapn idxs 1 args))))
			) end;
in (if length cons = 1 andalso length(snd(hd cons)) <= 1
    then mk_strictify else I)
     (foldr1 mk_sscase (mapn one_fun 1 cons)) end;
end; (* struct *)
