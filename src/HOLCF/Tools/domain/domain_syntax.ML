(*  Title:      HOLCF/Tools/domain/domain_syntax.ML
    Author:     David von Oheimb

Syntax generator for domain command.
*)

signature DOMAIN_SYNTAX =
sig
  val add_syntax: string -> ((string * typ list) *
	(binding * (bool * binding option * typ) list * mixfix) list) list
    -> theory -> theory
end;


structure Domain_Syntax : DOMAIN_SYNTAX =
struct 

local 

open Domain_Library;
infixr 5 -->; infixr 6 ->>;
fun calc_syntax dtypeprod ((dname, typevars), 
	(cons': (binding * (bool * binding option * typ) list * mixfix) list)) : ((binding * typ * mixfix) list * ast Syntax.trrule list) =
let
(* ----- constants concerning the isomorphism ------------------------------- *)

local
  fun opt_lazy (lazy,_,t) = if lazy then mk_uT t else t
  fun prod     (_,args,_) = case args of [] => oneT
                            | _ => foldr1 mk_sprodT (map opt_lazy args);
  fun freetvar s = let val tvar = mk_TFree s in
		   if tvar mem typevars then freetvar ("t"^s) else tvar end;
  fun when_type (_,args,_) = List.foldr (op ->>) (freetvar "t") (map third args);
in
  val dtype  = Type(dname,typevars);
  val dtype2 = foldr1 mk_ssumT (map prod cons');
  val dnam = Long_Name.base_name dname;
  fun dbind s = Binding.name (dnam ^ s);
  val const_rep  = (dbind "_rep" ,              dtype  ->> dtype2, NoSyn);
  val const_abs  = (dbind "_abs" ,              dtype2 ->> dtype , NoSyn);
  val const_when = (dbind "_when", List.foldr (op ->>) (dtype ->> freetvar "t") (map when_type cons'), NoSyn);
  val const_copy = (dbind "_copy", dtypeprod ->> dtype  ->> dtype , NoSyn);
end;

(* ----- constants concerning constructors, discriminators, and selectors --- *)

local
  val escape = let
	fun esc (c::cs) = if c mem ["'","_","(",")","/"] then "'"::c::esc cs
							 else      c::esc cs
	|   esc []      = []
	in implode o esc o Symbol.explode end;
  fun dis_name_ con     = Binding.name ("is_" ^ strip_esc (Binding.name_of con));
  fun mat_name_ con     = Binding.name ("match_" ^ strip_esc (Binding.name_of con));
  fun pat_name_ con     = Binding.name (strip_esc (Binding.name_of con) ^ "_pat");
  fun con (name,args,mx) = (name, List.foldr (op ->>) dtype (map third args), mx);
  fun dis (con,args,mx) = (dis_name_ con, dtype->>trT,
			   Mixfix(escape ("is_" ^ Binding.name_of con), [], Syntax.max_pri));
			(* strictly speaking, these constants have one argument,
			   but the mixfix (without arguments) is introduced only
			   to generate parse rules for non-alphanumeric names*)
  fun freetvar s n      = let val tvar = mk_TFree (s ^ string_of_int n) in
			  if tvar mem typevars then freetvar ("t"^s) n else tvar end;
  fun mk_matT (a,bs,c)  = a ->> foldr (op ->>) (mk_maybeT c) bs ->> mk_maybeT c;
  fun mat (con,args,mx) = (mat_name_ con,
                           mk_matT(dtype, map third args, freetvar "t" 1),
			   Mixfix(escape ("match_" ^ Binding.name_of con), [], Syntax.max_pri));
  fun sel1 (_,sel,typ)  = Option.map (fn s => (s,dtype ->> typ,NoSyn)) sel;
  fun sel (con,args,mx) = List.mapPartial sel1 args;
  fun mk_patT (a,b)     = a ->> mk_maybeT b;
  fun pat_arg_typ n arg = mk_patT (third arg, freetvar "t" n);
  fun pat (con,args,mx) = (pat_name_ con, (mapn pat_arg_typ 1 args) --->
			   mk_patT (dtype, mk_ctupleT (map (freetvar "t") (1 upto length args))),
			   Mixfix(escape (Binding.name_of con ^ "_pat"), [], Syntax.max_pri));

in
  val consts_con = map con cons';
  val consts_dis = map dis cons';
  val consts_mat = map mat cons';
  val consts_pat = map pat cons';
  val consts_sel = List.concat(map sel cons');
end;

(* ----- constants concerning induction ------------------------------------- *)

  val const_take   = (dbind "_take"  , HOLogic.natT-->dtype->>dtype, NoSyn);
  val const_finite = (dbind "_finite", dtype-->HOLogic.boolT       , NoSyn);

(* ----- case translation --------------------------------------------------- *)

local open Syntax in
  local
    fun c_ast con mx = Constant (Syntax.const_name mx (Binding.name_of con));
    fun expvar n     = Variable ("e"^(string_of_int n));
    fun argvar n m _ = Variable ("a"^(string_of_int n)^"_"^
				     (string_of_int m));
    fun argvars n args = mapn (argvar n) 1 args;
    fun app s (l,r)  = mk_appl (Constant s) [l,r];
    val cabs = app "_cabs";
    val capp = app "Rep_CFun";
    fun con1 n (con,args,mx) = Library.foldl capp (c_ast con mx, argvars n args);
    fun case1 n (con,args,mx) = app "_case1" (con1 n (con,args,mx), expvar n);
    fun arg1 n (con,args,_) = List.foldr cabs (expvar n) (argvars n args);
    fun when1 n m = if n = m then arg1 n else K (Constant "UU");

    fun app_var x = mk_appl (Constant "_variable") [x, Variable "rhs"];
    fun app_pat x = mk_appl (Constant "_pat") [x];
    fun args_list [] = Constant "_noargs"
    |   args_list xs = foldr1 (app "_args") xs;
  in
    val case_trans = ParsePrintRule
        (app "_case_syntax" (Variable "x", foldr1 (app "_case2") (mapn case1 1 cons')),
         capp (Library.foldl capp (Constant (dnam^"_when"), mapn arg1 1 cons'), Variable "x"));
    
    val abscon_trans = mapn (fn n => fn (con,mx,args) => ParsePrintRule
        (cabs (con1 n (con,mx,args), expvar n),
         Library.foldl capp (Constant (dnam^"_when"), mapn (when1 n) 1 cons'))) 1 cons';
    
    val Case_trans = List.concat (map (fn (con,args,mx) =>
      let
        val cname = c_ast con mx;
        val pname = Constant (strip_esc (Binding.name_of con) ^ "_pat");
        val ns = 1 upto length args;
        val xs = map (fn n => Variable ("x"^(string_of_int n))) ns;
        val ps = map (fn n => Variable ("p"^(string_of_int n))) ns;
        val vs = map (fn n => Variable ("v"^(string_of_int n))) ns;
      in
        [ParseRule (app_pat (Library.foldl capp (cname, xs)),
                    mk_appl pname (map app_pat xs)),
         ParseRule (app_var (Library.foldl capp (cname, xs)),
                    app_var (args_list xs)),
         PrintRule (Library.foldl capp (cname, ListPair.map (app "_match") (ps,vs)),
                    app "_match" (mk_appl pname ps, args_list vs))]
      end) cons');
  end;
end;

in ([const_rep, const_abs, const_when, const_copy] @ 
     consts_con @ consts_dis @ consts_mat @ consts_pat @ consts_sel @
    [const_take, const_finite],
    (case_trans::(abscon_trans @ Case_trans)))
end; (* let *)

(* ----- putting all the syntax stuff together ------------------------------ *)

in (* local *)

fun add_syntax
  (comp_dnam : string)
  (eqs' : ((string * typ list) *
	(binding * (bool * binding option * typ) list * mixfix) list) list)
  (thy'' : theory) =
let
  val dtypes  = map (Type o fst) eqs';
  val boolT   = HOLogic.boolT;
  val funprod = foldr1 HOLogic.mk_prodT (map (fn tp => tp ->> tp          ) dtypes);
  val relprod = foldr1 HOLogic.mk_prodT (map (fn tp => tp --> tp --> boolT) dtypes);
  val const_copy = (Binding.name (comp_dnam^"_copy"), funprod ->> funprod, NoSyn);
  val const_bisim = (Binding.name (comp_dnam^"_bisim"), relprod --> boolT, NoSyn);
  val ctt : ((binding * typ * mixfix) list * ast Syntax.trrule list) list = map (calc_syntax funprod) eqs';
in thy'' |> ContConsts.add_consts_i (List.concat (map fst ctt) @ 
				    (if length eqs'>1 then [const_copy] else[])@
				    [const_bisim])
	 |> Sign.add_trrules_i (List.concat(map snd ctt))
end; (* let *)

end; (* local *)
end; (* struct *)
