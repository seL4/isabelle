(*  Title:      HOLCF/Tools/cont_consts.ML
    ID:         $Id$
    Author:     Tobias Mayr, David von Oheimb, and Markus Wenzel

HOLCF version of consts: handle continuous function types in mixfix
syntax.
*)

signature CONT_CONSTS =
sig
  val add_consts: (bstring * string * mixfix) list -> theory -> theory
  val add_consts_i: (bstring * typ * mixfix) list -> theory -> theory
end;

structure ContConsts: CONT_CONSTS =
struct


(* misc utils *)

open HOLCFLogic;

fun first  (x,_,_) = x;
fun second (_,x,_) = x;
fun third  (_,_,x) = x;
fun upd_first  f (x,y,z) = (f x,   y,   z);
fun upd_second f (x,y,z) = (  x, f y,   z);
fun upd_third  f (x,y,z) = (  x,   y, f z);

fun change_arrow 0 T               = T
|   change_arrow n (Type(_,[S,T])) = Type ("fun",[S,change_arrow (n-1) T])
|   change_arrow _ _               = sys_error "cont_consts: change_arrow";

fun trans_rules name2 name1 n mx = let
  fun argnames _ 0 = []
  |   argnames c n = chr c::argnames (c+1) (n-1);
  val vnames = argnames (ord "A") n;
  val extra_parse_rule = Syntax.ParseRule (Constant name2, Constant name1);
  in [Syntax.ParsePrintRule (Syntax.mk_appl (Constant name2) (map Variable vnames),
                          Library.foldl (fn (t,arg) => (Syntax.mk_appl (Constant "Rep_CFun")
                                                [t,Variable arg]))
                          (Constant name1,vnames))]
     @(case mx of InfixName _ => [extra_parse_rule]
                | InfixlName _ => [extra_parse_rule]
                | InfixrName _ => [extra_parse_rule] | _ => []) end;


(* transforming infix/mixfix declarations of constants with type ...->...
   a declaration of such a constant is transformed to a normal declaration with
   an internal name, the same type, and nofix. Additionally, a purely syntactic
   declaration with the original name, type ...=>..., and the original mixfix
   is generated and connected to the other declaration via some translation.
*)
fun fix_mixfix (syn                     , T, mx as Infix           p ) =
               (Syntax.const_name mx syn, T,       InfixName (syn, p))
  | fix_mixfix (syn                     , T, mx as Infixl           p ) =
               (Syntax.const_name mx syn, T,       InfixlName (syn, p))
  | fix_mixfix (syn                     , T, mx as Infixr           p ) =
               (Syntax.const_name mx syn, T,       InfixrName (syn, p))
  | fix_mixfix decl = decl;
fun transform decl = let
        val (c, T, mx) = fix_mixfix decl;
        val c2 = "_cont_" ^ c;
        val n  = Syntax.mixfix_args mx
    in     ((c ,               T,NoSyn),
            (c2,change_arrow n T,mx   ),
            trans_rules c2 c n mx) end;

fun cfun_arity (Type(n,[_,T])) = if n = cfun_arrow then 1+cfun_arity T else 0
|   cfun_arity _               = 0;

fun is_contconst (_,_,NoSyn   ) = false
|   is_contconst (_,_,Binder _) = false
|   is_contconst (c,T,mx      ) = cfun_arity T >= Syntax.mixfix_args mx
                         handle ERROR msg => cat_error msg ("in mixfix annotation for " ^
                                               quote (Syntax.const_name mx c));


(* add_consts(_i) *)

fun gen_add_consts prep_typ raw_decls thy =
  let
    val decls = map (upd_second (prep_typ thy)) raw_decls;
    val (contconst_decls, normal_decls) = List.partition is_contconst decls;
    val transformed_decls = map transform contconst_decls;
  in
    thy
    |> (Sign.add_consts_i o map (upd_first Binding.name))
      (normal_decls @ map first transformed_decls @ map second transformed_decls)
    |> Sign.add_trrules_i (maps third transformed_decls)
  end;

val add_consts = gen_add_consts Syntax.read_typ_global;
val add_consts_i = gen_add_consts Sign.certify_typ;


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val _ =
  OuterSyntax.command "consts" "declare constants (HOLCF)" K.thy_decl
    (Scan.repeat1 P.const >> (Toplevel.theory o add_consts));

end;

end;
