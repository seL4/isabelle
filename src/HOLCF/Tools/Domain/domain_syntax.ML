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
      (binding * typ * mixfix) list

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
    : (binding * typ * mixfix) list =
  let
(* ----- constants concerning the isomorphism ------------------------------- *)
    local
      fun opt_lazy (lazy,_,t) = if lazy then mk_uT t else t
      fun prod     (_,args,_) = case args of [] => oneT
                                           | _ => foldr1 mk_sprodT (map opt_lazy args);
      fun freetvar s = let val tvar = mk_TFree s in
                         if tvar mem typevars then freetvar ("t"^s) else tvar end;
    in
    val dtype  = Type(dname,typevars);
    val dtype2 = foldr1 mk_ssumT (map prod cons');
    val dnam = Long_Name.base_name dname;
    fun dbind s = Binding.name (dnam ^ s);
    val const_rep  = (dbind "_rep" ,              dtype  ->> dtype2, NoSyn);
    val const_abs  = (dbind "_abs" ,              dtype2 ->> dtype , NoSyn);
    val const_copy = (dbind "_copy", dtypeprod ->> dtype  ->> dtype , NoSyn);
    end;

(* ----- constants concerning induction ------------------------------------- *)

    val const_take   = (dbind "_take"  , HOLogic.natT-->dtype->>dtype, NoSyn);
    val const_finite = (dbind "_finite", dtype-->HOLogic.boolT       , NoSyn);

    val optional_consts =
        if definitional then [] else [const_rep, const_abs, const_copy];

  in (optional_consts @ [const_take, const_finite])
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
    val ctt : (binding * typ * mixfix) list list =
        map (calc_syntax thy'' definitional funprod) eqs';
  in thy''
       |> Cont_Consts.add_consts
           (flat ctt @ 
            (if length eqs'>1 andalso not definitional
             then [const_copy] else []) @
            [const_bisim])
  end; (* let *)

end; (* struct *)
