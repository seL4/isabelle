(*  Title:      HOLCF/Tools/Domain/domain_library.ML
    Author:     David von Oheimb

Library for domain command.
*)


(* infix syntax *)

infixr 5 -->;
infixr 6 ->>;
infixr 0 ===>;
infixr 0 ==>;
infix 0 ==;
infix 1 ===;
infix 1 ~=;

infix 9 `  ;
infix 9 `% ;
infix 9 `%%;


(* ----- specific support for domain ---------------------------------------- *)

signature DOMAIN_LIBRARY =
sig
  val first  : 'a * 'b * 'c -> 'a
  val second : 'a * 'b * 'c -> 'b
  val third  : 'a * 'b * 'c -> 'c
  val upd_second : ('b -> 'd) -> 'a * 'b * 'c -> 'a * 'd * 'c
  val upd_third  : ('c -> 'd) -> 'a * 'b * 'c -> 'a * 'b * 'd
  val mapn : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
  val atomize : Proof.context -> thm -> thm list

  val Imposs : string -> 'a;
  val cpo_type : theory -> typ -> bool;
  val pcpo_type : theory -> typ -> bool;
  val string_of_typ : theory -> typ -> string;

  (* Creating HOLCF types *)
  val mk_ssumT : typ * typ -> typ;
  val mk_sprodT : typ * typ -> typ;
  val mk_uT : typ -> typ;
  val oneT : typ;
  val pcpoS : sort;

  (* Creating HOLCF terms *)
  val %: : string -> term;
  val %%: : string -> term;
  val ` : term * term -> term;
  val `% : term * string -> term;
  val UU : term;
  val ID : term;
  val list_ccomb : term * term list -> term;
  val con_app2 : string -> ('a -> term) -> 'a list -> term;
  val prj : ('a -> 'b -> 'a) -> ('a -> 'b -> 'a) -> 'a -> 'b list -> int -> 'a
  val proj : term -> 'a list -> int -> term;

  (* Creating propositions *)
  val mk_conj : term * term -> term;
  val mk_disj : term * term -> term;
  val mk_imp : term * term -> term;
  val mk_lam : string * term -> term;
  val mk_all : string * term -> term;
  val mk_ex : string * term -> term;
  val mk_constrainall : string * typ * term -> term;
  val === : term * term -> term;
  val defined : term -> term;
  val mk_adm : term -> term;
  val lift : ('a -> term) -> 'a list * term -> term;
  val lift_defined : ('a -> term) -> 'a list * term -> term;

  (* Creating meta-propositions *)
  val mk_trp : term -> term; (* HOLogic.mk_Trueprop *)
  val == : term * term -> term;
  val ===> : term * term -> term;
  val mk_All : string * term -> term;

      (* Domain specifications *)
      eqtype arg;
  type cons = string * arg list;
  type eq = (string * typ list) * cons list;
  val mk_arg : (bool * Datatype.dtyp) * string -> arg;
  val is_lazy : arg -> bool;
  val rec_of : arg -> int;
  val dtyp_of : arg -> Datatype.dtyp;
  val vname : arg -> string;
  val upd_vname : (string -> string) -> arg -> arg;
  val is_rec : arg -> bool;
  val is_nonlazy_rec : arg -> bool;
  val nonlazy : arg list -> string list;
  val nonlazy_rec : arg list -> string list;
  val %# : arg -> term;
  val bound_arg : ''a list -> ''a -> term; (* ''a = arg or string *)
  val idx_name : 'a list -> string -> int -> string;
  val con_app : string -> arg list -> term;
end;

structure Domain_Library :> DOMAIN_LIBRARY =
struct

fun first  (x,_,_) = x;
fun second (_,x,_) = x;
fun third  (_,_,x) = x;

fun upd_first  f (x,y,z) = (f x,   y,   z);
fun upd_second f (x,y,z) = (  x, f y,   z);
fun upd_third  f (x,y,z) = (  x,   y, f z);

fun mapn f n []      = []
  | mapn f n (x::xs) = (f n x) :: mapn f (n+1) xs;

fun foldr'' f (l,f2) =
    let fun itr []  = raise Fail "foldr''" 
          | itr [a] = f2 a
          | itr (a::l) = f(a, itr l)
    in  itr l  end;

fun atomize ctxt thm =
    let
      val r_inst = read_instantiate ctxt;
      fun at thm =
          case concl_of thm of
            _$(Const("op &",_)$_$_)       => at(thm RS conjunct1)@at(thm RS conjunct2)
          | _$(Const("All" ,_)$Abs(s,_,_))=> at(thm RS (r_inst [(("x", 0), "?" ^ s)] spec))
          | _                             => [thm];
    in map zero_var_indexes (at thm) end;

exception Impossible of string;
fun Imposs msg = raise Impossible ("Domain:"^msg);

fun cpo_type sg t = Sign.of_sort sg (Sign.certify_typ sg t, @{sort cpo});
fun pcpo_type sg t = Sign.of_sort sg (Sign.certify_typ sg t, @{sort pcpo});
fun string_of_typ sg = Syntax.string_of_typ_global sg o Sign.certify_typ sg;

(* ----- constructor list handling ----- *)

type arg =
     (bool * Datatype.dtyp) *   (*  (lazy, recursive element) *)
     string;                       (*   argument name    *)

type cons =
     string *         (* operator name of constr *)
     arg list;        (* argument list      *)

type eq =
     (string *        (* name      of abstracted type *)
      typ list) *     (* arguments of abstracted type *)
     cons list;       (* represented type, as a constructor list *)

val mk_arg = I;

fun rec_of ((_,dtyp),_) =
    case dtyp of Datatype_Aux.DtRec i => i | _ => ~1;
(* FIXME: what about indirect recursion? *)

fun is_lazy arg = fst (fst arg);
fun dtyp_of arg = snd (fst arg);
val     vname =       snd;
val upd_vname =   apsnd;
fun is_rec         arg = rec_of arg >=0;
fun is_nonlazy_rec arg = is_rec arg andalso not (is_lazy arg);
fun nonlazy     args   = map vname (filter_out is_lazy args);
fun nonlazy_rec args   = map vname (filter is_nonlazy_rec args);


(* ----- support for type and mixfix expressions ----- *)

fun mk_uT T = Type(@{type_name "u"}, [T]);
fun mk_sprodT (T, U) = Type(@{type_name sprod}, [T, U]);
fun mk_ssumT (T, U) = Type(@{type_name ssum}, [T, U]);
val oneT = @{typ one};

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
fun mk_constrainall (x,typ,P) = %%:"All" $ (TypeInfer.constrain (typ --> boolT) (mk_lam(x,P)));
end

fun mk_All  (x,P) = %%:"all" $ mk_lam(x,P); (* meta universal quantification *)

infixr 0 ===>;  fun S ===> T = %%:"==>" $ S $ T;
infix 0 ==;     fun S ==  T = %%:"==" $ S $ T;
infix 1 ===;    fun S === T = %%:"op =" $ S $ T;
infix 1 ~=;     fun S ~=  T = HOLogic.mk_not (S === T);

infix 9 `  ; fun f ` x = %%: @{const_name Rep_CFun} $ f $ x;
infix 9 `% ; fun f`% s = f` %: s;
infix 9 `%%; fun f`%%s = f` %%:s;

fun mk_adm t = %%: @{const_name adm} $ t;
val ID = %%: @{const_name ID};
fun mk_strictify t = %%: @{const_name strictify}`t;
fun mk_ssplit t = %%: @{const_name ssplit}`t;
fun mk_sscase (x, y) = %%: @{const_name sscase}`x`y;
fun mk_fup (t,u) = %%: @{const_name fup} ` t ` u;

val pcpoS = @{sort pcpo};

val list_ccomb = Library.foldl (op `); (* continuous version of list_comb *)
fun con_app2 con f args = list_ccomb(%%:con,map f args);
fun con_app con = con_app2 con %#;
fun prj _  _  x (   _::[]) _ = x
  | prj _  _  _ []         _ = raise Fail "Domain_Library.prj: empty list"
  | prj f1 _  x (_::y::ys) 0 = f1 x y
  | prj f1 f2 x (y::   ys) j = prj f1 f2 (f2 x y) ys (j-1);
fun  proj x      = prj (fn S => K(%%:"fst" $S)) (fn S => K(%%:"snd" $S)) x;
fun lift tfn = Library.foldr (fn (x,t)=> (mk_trp(tfn x) ===> t));

val UU = %%: @{const_name UU};
fun defined t = t ~= UU;
fun cpair (t,u) = %%: @{const_name Pair} $ t $ u;
fun spair (t,u) = %%: @{const_name spair}`t`u;
fun lift_defined f = lift (fn x => defined (f x));
fun bound_arg vns v = Bound (length vns - find_index (fn v' => v' = v) vns - 1);

fun cont_eta_contract (Const("Cfun.Abs_CFun",TT) $ Abs(a,T,body)) = 
    (case cont_eta_contract body  of
       body' as (Const("Cfun.Rep_CFun",Ta) $ f $ Bound 0) => 
       if not (0 mem loose_bnos f) then incr_boundvars ~1 f 
       else   Const("Cfun.Abs_CFun",TT) $ Abs(a,T,body')
     | body' => Const("Cfun.Abs_CFun",TT) $ Abs(a,T,body'))
  | cont_eta_contract(f$t) = cont_eta_contract f $ cont_eta_contract t
  | cont_eta_contract t    = t;

fun idx_name dnames s n = s^(if length dnames = 1 then "" else string_of_int n);

end; (* struct *)
