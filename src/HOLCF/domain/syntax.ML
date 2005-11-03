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
	(cons': (string * mixfix * (bool * string option * typ) list) list)) =
let
(* ----- constants concerning the isomorphism ------------------------------- *)

local
  fun opt_lazy (lazy,_,t) = if lazy then mk_uT t else t
  fun prod     (_,_,args) = if args = [] then oneT
			    else foldr1 mk_sprodT (map opt_lazy args);
  fun freetvar s = let val tvar = mk_TFree s in
		   if tvar mem typevars then freetvar ("t"^s) else tvar end;
  fun when_type (_   ,_,args) = foldr (op ->>) (freetvar "t") (map third args);
in
  val dtype  = Type(dname,typevars);
  val dtype2 = foldr1 mk_ssumT (map prod cons');
  val dnam = Sign.base_name dname;
  val const_rep  = (dnam^"_rep" ,              dtype  ->> dtype2, NoSyn);
  val const_abs  = (dnam^"_abs" ,              dtype2 ->> dtype , NoSyn);
  val const_when = (dnam^"_when",foldr (op ->>) (dtype ->> freetvar "t") (map when_type cons'), NoSyn);
  val const_copy = (dnam^"_copy", dtypeprod ->> dtype  ->> dtype , NoSyn);
end;

(* ----- constants concerning constructors, discriminators, and selectors --- *)

local
  val escape = let
	fun esc (c::cs) = if c mem ["'","_","(",")","/"] then "'"::c::esc cs
							 else      c::esc cs
	|   esc []      = []
	in implode o esc o Symbol.explode end;
  fun con (name,s,args) = (name,foldr (op ->>) dtype (map third args),s);
  fun dis (con ,s,_   ) = (dis_name_ con, dtype->>trT,
			   Mixfix(escape ("is_" ^ con), [], Syntax.max_pri));
			(* strictly speaking, these constants have one argument,
			   but the mixfix (without arguments) is introduced only
			   to generate parse rules for non-alphanumeric names*)
  fun mat (con ,s,args) = (mat_name_ con, dtype->>mk_ssumT(oneT,mk_uT(mk_ctupleT(map third args))),
			   Mixfix(escape ("match_" ^ con), [], Syntax.max_pri));
  fun sel1 (_,sel,typ)  = Option.map (fn s => (s,dtype ->> typ,NoSyn)) sel;
  fun sel (_   ,_,args) = List.mapPartial sel1 args;
in
  val consts_con = map con cons';
  val consts_dis = map dis cons';
  val consts_mat = map mat cons';
  val consts_sel = List.concat(map sel cons');
end;

(* ----- constants concerning induction ------------------------------------- *)

  val const_take   = (dnam^"_take"  , HOLogic.natT-->dtype->>dtype, NoSyn);
  val const_finite = (dnam^"_finite", dtype-->HOLogic.boolT       , NoSyn);

(* ----- case translation --------------------------------------------------- *)

local open Syntax in
  local
    fun c_ast con mx = Constant (const_name con mx);
    fun expvar n     = Variable ("e"^(string_of_int n));
    fun argvar n m _ = Variable ("a"^(string_of_int n)^"_"^
				     (string_of_int m));
    fun app s (l,r)   = mk_appl (Constant s) [l,r];
    val cabs = app "_cabs";
    val capp = app "Rep_CFun";
    fun con1 n (con,mx,args) = Library.foldl capp (c_ast con mx, mapn (argvar n) 1 args);
    fun case1 n (con,mx,args) = app "_case1" (con1 n (con,mx,args), expvar n);
    fun arg1 n (con,_,args) = foldr cabs (expvar n) (mapn (argvar n) 1 args);
    fun when1 n m = if n = m then arg1 n else K (Constant "UU");
  in
    val case_trans = ParsePrintRule
        (app "_case_syntax" (Variable "x", foldr1 (app "_case2") (mapn case1 1 cons')),
         capp (Library.foldl capp (Constant (dnam^"_when"), mapn arg1 1 cons'), Variable "x"));
    
    val abscon_trans = mapn (fn n => fn (con,mx,args) => ParsePrintRule
        (cabs (con1 n (con,mx,args), expvar n),
         Library.foldl capp (Constant (dnam^"_when"), mapn (when1 n) 1 cons'))) 1 cons';
  end;
end;

in ([const_rep, const_abs, const_when, const_copy] @ 
     consts_con @ consts_dis @ consts_mat @ consts_sel @
    [const_take, const_finite],
    (case_trans::abscon_trans))
end; (* let *)

(* ----- putting all the syntax stuff together ------------------------------ *)

in (* local *)

fun add_syntax (comp_dnam,eqs': ((string * typ list) *
	(string * mixfix * (bool * string option * typ) list) list) list) thy'' =
let
  val dtypes  = map (Type o fst) eqs';
  val boolT   = HOLogic.boolT;
  val funprod = foldr1 HOLogic.mk_prodT (map (fn tp => tp ->> tp          ) dtypes);
  val relprod = foldr1 HOLogic.mk_prodT (map (fn tp => tp --> tp --> boolT) dtypes);
  val const_copy   = (comp_dnam^"_copy"  ,funprod ->> funprod, NoSyn);
  val const_bisim  = (comp_dnam^"_bisim" ,relprod --> boolT  , NoSyn);
  val ctt           = map (calc_syntax funprod) eqs';
in thy'' |> ContConsts.add_consts_i (List.concat (map fst ctt) @ 
				    (if length eqs'>1 then [const_copy] else[])@
				    [const_bisim])
	 |> Theory.add_trrules_i (List.concat(map snd ctt))
end; (* let *)

end; (* local *)
end; (* struct *)
