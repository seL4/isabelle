(*  Title:      HOLCF/Tools/Domain/domain_syntax.ML
    Author:     David von Oheimb

Syntax generator for domain command.
*)

signature DOMAIN_SYNTAX =
sig
  val calc_syntax:
      theory ->
      bool ->
      typ ->
      (string * typ list) *
      (binding * (bool * binding option * typ) list * mixfix) list ->
      (binding * typ * mixfix) list * ast Syntax.trrule list

  val add_syntax:
      bool ->
      string ->
      ((string * typ list) *
       (binding * (bool * binding option * typ) list * mixfix) list) list ->
      theory -> theory
end;


structure Domain_Syntax :> DOMAIN_SYNTAX =
struct

open Domain_Library;
infixr 5 -->; infixr 6 ->>;

fun calc_syntax thy
    (definitional : bool)
    (dtypeprod : typ)
    ((dname : string, typevars : typ list), 
     (cons': (binding * (bool * binding option * typ) list * mixfix) list))
    : (binding * typ * mixfix) list * ast Syntax.trrule list =
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

(* ----- constants concerning induction ------------------------------------- *)

    val const_take   = (dbind "_take"  , HOLogic.natT-->dtype->>dtype, NoSyn);
    val const_finite = (dbind "_finite", dtype-->HOLogic.boolT       , NoSyn);

(* ----- case translation --------------------------------------------------- *)

    fun syntax b = Syntax.mark_const (Sign.full_bname thy b);

    local open Syntax in
    local
      fun c_ast authentic con = Constant ((authentic ? syntax) (Binding.name_of con));
      fun expvar n = Variable ("e" ^ string_of_int n);
      fun argvar n m _ = Variable ("a" ^ string_of_int n ^ "_" ^ string_of_int m);
      fun argvars n args = mapn (argvar n) 1 args;
      fun app s (l, r) = mk_appl (Constant s) [l, r];
      val cabs = app "_cabs";
      val capp = app @{const_syntax Rep_CFun};
      fun con1 authentic n (con,args,mx) =
        Library.foldl capp (c_ast authentic con, argvars n args);
      fun case1 authentic n (con,args,mx) =
        app "_case1" (con1 authentic n (con,args,mx), expvar n);
      fun arg1 n (con,args,_) = List.foldr cabs (expvar n) (argvars n args);
      fun when1 n m = if n = m then arg1 n else K (Constant @{const_syntax UU});
          
      fun app_var x = mk_appl (Constant "_variable") [x, Variable "rhs"];
      fun app_pat x = mk_appl (Constant "_pat") [x];
      fun args_list [] = Constant "_noargs"
        | args_list xs = foldr1 (app "_args") xs;
    in
    fun case_trans authentic =
        ParsePrintRule
          (app "_case_syntax" (Variable "x", foldr1 (app "_case2") (mapn (case1 authentic) 1 cons')),
           capp (Library.foldl capp
            (Constant (syntax (dnam ^ "_when")), mapn arg1 1 cons'), Variable "x"));
        
    fun one_abscon_trans authentic n (con,mx,args) =
        ParsePrintRule
          (cabs (con1 authentic n (con,mx,args), expvar n),
           Library.foldl capp (Constant (syntax (dnam ^ "_when")), mapn (when1 n) 1 cons'));
    fun abscon_trans authentic = mapn (one_abscon_trans authentic) 1 cons';
        
    end;
    end;
    val optional_consts =
        if definitional then [] else [const_rep, const_abs, const_copy];

  in (optional_consts @ [const_when] @ 
      [const_take, const_finite],
      (case_trans false :: case_trans true :: (abscon_trans false @ abscon_trans true)))
  end; (* let *)

(* ----- putting all the syntax stuff together ------------------------------ *)

fun add_syntax
    (definitional : bool)
    (comp_dnam : string)
    (eqs' : ((string * typ list) *
             (binding * (bool * binding option * typ) list * mixfix) list) list)
    (thy'' : theory) =
  let
    val dtypes  = map (Type o fst) eqs';
    val boolT   = HOLogic.boolT;
    val funprod =
        foldr1 HOLogic.mk_prodT (map (fn tp => tp ->> tp          ) dtypes);
    val relprod =
        foldr1 HOLogic.mk_prodT (map (fn tp => tp --> tp --> boolT) dtypes);
    val const_copy =
        (Binding.name (comp_dnam^"_copy"), funprod ->> funprod, NoSyn);
    val const_bisim =
        (Binding.name (comp_dnam^"_bisim"), relprod --> boolT, NoSyn);
    val ctt : ((binding * typ * mixfix) list * ast Syntax.trrule list) list =
        map (calc_syntax thy'' definitional funprod) eqs';
  in thy''
       |> Cont_Consts.add_consts
           (maps fst ctt @ 
            (if length eqs'>1 andalso not definitional
             then [const_copy] else []) @
            [const_bisim])
       |> Sign.add_trrules_i (maps snd ctt)
  end; (* let *)

end; (* struct *)
