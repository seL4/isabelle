(*  Title:      HOLCF/domain/syntax.ML
    ID:         $Id$
    Author:     David von Oheimb

Syntax generator for domain section.
*)

structure Domain_Syntax = struct 

local 

open Domain_Library;
infixr 5 -->; infixr 6 ->>;
fun calc_syntax dtypeprod ((dname, typevars), 
	(cons': (string * mixfix * (bool*string*typ) list) list)) =
let
(* ----- constants concerning the isomorphism ------------------------------- *)

local
  fun opt_lazy (lazy,_,t) = if lazy then mk_uT t else t
  fun prod     (_,_,args) = if args = [] then oneT
			    else foldr' mk_sprodT (map opt_lazy args);
  fun freetvar s = let val tvar = mk_TFree s in
		   if tvar mem typevars then freetvar ("t"^s) else tvar end;
  fun when_type (_   ,_,args) = foldr (op ->>) (map third args,freetvar "t");
in
  val dtype  = Type(dname,typevars);
  val dtype2 = foldr' mk_ssumT (map prod cons');
  val dnam = Sign.base_name dname;
  val const_rep  = (dnam^"_rep" ,              dtype  ->> dtype2, NoSyn);
  val const_abs  = (dnam^"_abs" ,              dtype2 ->> dtype , NoSyn);
  val const_when = (dnam^"_when",foldr (op ->>) ((map when_type cons'),
					        dtype ->> freetvar "t"), NoSyn);
  val const_copy = (dnam^"_copy", dtypeprod ->> dtype  ->> dtype , NoSyn);
end;

(* ----- constants concerning constructors, discriminators, and selectors --- *)

local
  val escape = let
	fun esc (c::cs) = if c mem ["'","_","(",")","/"] then "'"::c::esc cs
							 else      c::esc cs
	|   esc []      = []
	in implode o esc o Symbol.explode end;
  fun con (name,s,args) = (name,foldr (op ->>) (map third args,dtype),s);
  fun dis (con ,s,_   ) = (dis_name_ con, dtype->>trT,
			   Mixfix(escape ("is_" ^ con), [], Syntax.max_pri));
			(* stricly speaking, these constants have one argument,
			   but the mixfix (without arguments) is introduced only
			   to generate parse rules for non-alphanumeric names*)
  fun sel (_   ,_,args) = map (fn(_,sel,typ)=>(sel,dtype ->> typ,NoSyn))args;
in
  val consts_con = map con cons';
  val consts_dis = map dis cons';
  val consts_sel = flat(map sel cons');
end;

(* ----- constants concerning induction ------------------------------------- *)

  val const_take   = (dnam^"_take"  , HOLogic.natT-->dtype->>dtype, NoSyn);
  val const_finite = (dnam^"_finite", dtype-->HOLogic.boolT       , NoSyn);

(* ----- case translation --------------------------------------------------- *)

local open Syntax in
  val case_trans = let 
	fun c_ast con mx = Constant (const_name con mx);
	fun expvar n     = Variable ("e"^(string_of_int n));
	fun argvar n m _ = Variable ("a"^(string_of_int n)^"_"^
					 (string_of_int m));
	fun app s (l,r)   = mk_appl (Constant s) [l,r];
	fun case1 n (con,mx,args) = mk_appl (Constant "_case1")
		 [foldl (app "Rep_CFun") (c_ast con mx, (mapn (argvar n) 1 args)),
		  expvar n];
	fun arg1 n (con,_,args) = if args = [] then expvar n 
				  else mk_appl (Constant "LAM ") 
		 [foldr' (app "_idts") (mapn (argvar n) 1 args) , expvar n];
  in
    ParsePrintRule
      (mk_appl (Constant "_case_syntax") [Variable "x", foldr'
				(fn (c,cs) => mk_appl (Constant"_case2") [c,cs])
				 (mapn case1 1 cons')],
       mk_appl (Constant "Rep_CFun") [foldl 
				(fn (w,a ) => mk_appl (Constant"Rep_CFun" ) [w,a ])
				 (Constant (dnam^"_when"),mapn arg1 1 cons'),
				 Variable "x"])
  end;
end;

in ([const_rep, const_abs, const_when, const_copy] @ 
     consts_con @ consts_dis @ consts_sel @
    [const_take, const_finite],
    [case_trans])
end; (* let *)

(* ----- putting all the syntax stuff together ------------------------------ *)

in (* local *)

fun add_syntax (comp_dnam,eqs': ((string * typ list) *
	(string * mixfix * (bool*string*typ) list) list) list) thy'' =
let
  val dtypes  = map (Type o fst) eqs';
  val boolT   = HOLogic.boolT;
  val funprod = foldr' mk_prodT (map (fn tp => tp ->> tp          ) dtypes);
  val relprod = foldr' mk_prodT (map (fn tp => tp --> tp --> boolT) dtypes);
  val const_copy   = (comp_dnam^"_copy"  ,funprod ->> funprod, NoSyn);
  val const_bisim  = (comp_dnam^"_bisim" ,relprod --> boolT  , NoSyn);
  val ctt           = map (calc_syntax funprod) eqs';
in thy'' |> ContConsts.add_consts_i (flat (map fst ctt) @ 
				    (if length eqs'>1 then [const_copy] else[])@
				    [const_bisim])
	 |> Theory.add_trrules_i (flat(map snd ctt))
end; (* let *)

end; (* local *)
end; (* struct *)
