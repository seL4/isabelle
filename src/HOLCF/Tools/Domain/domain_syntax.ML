(*  Title:      HOLCF/Tools/Domain/domain_syntax.ML
    Author:     David von Oheimb

Syntax generator for domain command.
*)

signature DOMAIN_SYNTAX =
sig
  val calc_syntax:
      theory ->
      bool ->
      (string * typ list) *
      (binding * (bool * binding option * typ) list * mixfix) list ->
      (binding * typ * mixfix) list

  val add_syntax:
      bool ->
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
    ((dname : string, typevars : typ list), 
     (cons': (binding * (bool * binding option * typ) list * mixfix) list))
    : (binding * typ * mixfix) list =
  let
(* ----- constants concerning the isomorphism ------------------------------- *)
    local
      fun opt_lazy (lazy,_,t) = if lazy then mk_uT t else t
      fun prod     (_,args,_) = case args of [] => oneT
                                           | _ => foldr1 mk_sprodT (map opt_lazy args);
    in
    val dtype  = Type(dname,typevars);
    val dtype2 = foldr1 mk_ssumT (map prod cons');
    val dnam = Long_Name.base_name dname;
    fun dbind s = Binding.name (dnam ^ s);
    val const_rep  = (dbind "_rep" ,              dtype  ->> dtype2, NoSyn);
    val const_abs  = (dbind "_abs" ,              dtype2 ->> dtype , NoSyn);
    end;

    val optional_consts =
        if definitional then [] else [const_rep, const_abs];

  in optional_consts
  end; (* let *)

(* ----- putting all the syntax stuff together ------------------------------ *)

fun add_syntax
    (definitional : bool)
    (eqs' : ((string * typ list) *
             (binding * (bool * binding option * typ) list * mixfix) list) list)
    (thy'' : theory) =
  let
    val ctt : (binding * typ * mixfix) list list =
        map (calc_syntax thy'' definitional) eqs';
  in thy''
       |> Cont_Consts.add_consts (flat ctt)
  end; (* let *)

end; (* struct *)
