(* syntax.ML
   Author:  David von Oheimb
   Created: 31-May-95
   Updated: 16-Aug-95 case translation
   Updated: 28-Aug-95 corrections for case translation, simultaneous domain equations
   Copyright 1995 TU Muenchen
*)


structure Domain_Syntax = struct 

local 

open Domain_Library;
infixr 5 -->; infixr 6 ~>;
fun calc_syntax dtypeprod ((dname, typevars), (cons':
			   (string * ThyOps.cmixfix * (bool*string*typ) list) list)) =
let
(* ----- constants concerning the isomorphism ------------------------------------- *)

local
  fun opt_lazy (lazy,_,t) = if lazy then Type("u",[t]) else t
  fun prod     (_,_,args) = if args = [] then Type("one",[])
				         else foldr'(mk_typ "**") (map opt_lazy args);
  fun freetvar s = if (mk_tvar s) mem typevars then freetvar ("t"^s) else mk_tvar s;
  fun when_type (_   ,_,args) = foldr (op ~>)       (map third args,freetvar "t");
in
  val dtype  = Type(dname,typevars);
  val dtype2 = foldr' (mk_typ "++") (map prod cons');
  val const_rep  = (dname^"_rep" ,              dtype  ~> dtype2, NoSyn');
  val const_abs  = (dname^"_abs" ,              dtype2 ~> dtype , NoSyn');
  val const_when = (dname^"_when", foldr (op ~>) ((map when_type cons'),
						 dtype ~> freetvar "t"), NoSyn');
  val const_copy = (dname^"_copy", dtypeprod ~> dtype  ~> dtype , NoSyn');
end;

(* ----- constants concerning the constructors, discriminators and selectors ------ *)

fun is_infix (ThyOps.CInfixl       _ ) = true
|   is_infix (ThyOps.CInfixr       _ ) = true
|   is_infix (ThyOps.Mixfix(Infixl _)) = true
|   is_infix (ThyOps.Mixfix(Infixr _)) = true
|   is_infix  _                        = false;

local
  val escape = let
	fun esc (c :: cs) = if c mem ["'","_","(",")","/"] then "'" :: c :: esc cs
							   else        c :: esc cs
	|   esc []        = []
	in implode o esc o explode end;
  fun con       (name,s,args) = (name,foldr (op ~>) (map third args,dtype),s);
  fun dis       (con ,s,_   ) = (dis_name_ con, dtype~>Type("tr",[]),
			 	 ThyOps.Mixfix(Mixfix("is'_"^
				 (if is_infix s then Id else escape)con,[],max_pri)));
  fun sel       (_   ,_,args) = map (fn(_,sel,typ)=>(sel,dtype ~> typ,NoSyn'))args;
in
  val consts_con = map con cons';
  val consts_dis = map dis cons';
  val consts_sel = flat(map sel cons');
end;

(* ----- constants concerning induction ------------------------------------------- *)

  val const_take   = (dname^"_take"  , Type("nat",[]) --> dtype ~> dtype, NoSyn');
  val const_finite = (dname^"_finite", dtype-->HOLogic.boolT	        , NoSyn');

(* ----- case translation --------------------------------------------------------- *)

local open Syntax in
  val case_trans = let 
	fun c_ast con syn = Constant (ThyOps.const_name con syn);
	fun expvar n      = Variable ("e"^(string_of_int n));
	fun argvar n m _  = Variable ("a"^(string_of_int n)^"_"^(string_of_int m));
	fun app s (l,r)   = mk_appl (Constant s) [l,r];
	fun case1 n (con,syn,args) = mk_appl (Constant "@case1")
		 [if is_infix syn
		  then mk_appl (c_ast con syn) (mapn (argvar n) 1 args)
		  else foldl (app "@fapp") (c_ast con syn, (mapn (argvar n) 1 args)),
		  expvar n];
	fun arg1 n (con,_,args) = if args = [] then expvar n 
				  else mk_appl (Constant "LAM ") 
		 [foldr' (app "_idts") (mapn (argvar n) 1 args) , expvar n];
  in mk_appl (Constant "@case") [Variable "x", foldr'
				 (fn (c,cs) => mk_appl (Constant "@case2") [c,cs])
				 (mapn case1 1 cons')] <->
     mk_appl (Constant "@fapp") [foldl 
				 (fn (w,a ) => mk_appl (Constant "@fapp" ) [w,a ])
				 (Constant (dname^"_when"),mapn arg1 1 cons'),
				 Variable "x"]
  end;
end;

in ([const_rep, const_abs, const_when, const_copy] @ 
     consts_con @ consts_dis @ consts_sel @
    [const_take, const_finite],
    [case_trans])
end; (* let *)

(* ----- putting all the syntax stuff together ------------------------------------ *)

in (* local *)

fun add_syntax (comp_dname,eqs': ((string * typ list) *
		(string * ThyOps.cmixfix * (bool*string*typ) list) list) list) thy'' =
let
  fun thy_type  (dname,typevars)  = (dname, length typevars, NoSyn);
  fun thy_arity (dname,typevars)  = (dname, map (K ["pcpo"]) typevars, ["pcpo"]); 
  val thy_types   = map (thy_type  o fst) eqs';
  val thy_arities = map (thy_arity o fst) eqs';
  val dtypes      = map (Type      o fst) eqs';
  val funprod = foldr' (mk_typ "*") (map (fn tp => tp ~> tp                  )dtypes);
  val relprod = foldr' (mk_typ "*") (map (fn tp => tp--> tp --> HOLogic.boolT)dtypes);
  val const_copy   = (comp_dname^"_copy"  ,funprod ~> funprod       , NoSyn');
  val const_bisim  = (comp_dname^"_bisim" ,relprod --> HOLogic.boolT, NoSyn');
  val ctt           = map (calc_syntax funprod) eqs';
  val add_cur_ops_i = ThyOps.add_ops_i {curried=true, strict=false, total=false};
in thy'' |> add_types      thy_types
	 |> add_arities    thy_arities
	 |> add_cur_ops_i (flat(map fst ctt))
	 |> add_cur_ops_i ((if length eqs'>1 then [const_copy] else[])@[const_bisim])
	 |> add_trrules_i (flat(map snd ctt))
end; (* let *)

end; (* local *)
end; (* struct *)
