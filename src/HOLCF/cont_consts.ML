(*  Title:      HOLCF/cont_consts.ML
    ID:         $Id$
    Author:     Tobias Mayr and David von Oheimb

Theory extender for consts section.
*)

structure ContConsts =
struct

local

open HOLCFLogic;

exception Impossible of string;
fun Imposs msg = raise Impossible ("ContConst:"^msg);
fun first  (x,_,_) = x; fun second (_,x,_) = x; fun third  (_,_,x) = x;
fun upd_first  f (x,y,z) = (f x,   y,   z);
fun upd_second f (x,y,z) = (  x, f y,   z);
fun upd_third  f (x,y,z) = (  x,   y, f z);

fun filter2 (pred: 'a->bool) : 'a list -> 'a list * 'a list =
  let fun filt []      = ([],[])
        | filt (x::xs) = let val (ys,zs) = filt xs in
			 if pred x then (x::ys,zs) else (ys,x::zs) end
  in filt end;

fun change_arrow 0 T               = T
|   change_arrow n (Type(_,[S,T])) = Type ("fun",[S,change_arrow (n-1) T])
|   change_arrow _ _               = Imposs "change_arrow";

fun trans_rules name2 name1 n mx = let
  fun argnames _ 0 = []
  |   argnames c n = chr c::argnames (c+1) (n-1);
  val vnames = argnames (ord "A") n;
  val extra_parse_rule = Syntax.ParseRule (Constant name2, Constant name1);
  in [Syntax.ParsePrintRule (Ast.mk_appl (Constant name2) (map Variable vnames),
			  foldl (fn (t,arg) => (Ast.mk_appl (Constant "fapp") 
						[t,Variable arg]))
			  (Constant name1,vnames))]
     @(case mx of InfixlName _ => [extra_parse_rule] 
                | InfixrName _ => [extra_parse_rule] | _ => []) end; 


(* transforming infix/mixfix declarations of constants with type ...->...
   a declaration of such a constant is transformed to a normal declaration with 
   an internal name, the same type, and nofix. Additionally, a purely syntactic
   declaration with the original name, type ...=>..., and the original mixfix
   is generated and connected to the other declaration via some translation.
*)
fun fix_mixfix (syn                     , T, mx as Infixl           p ) = 
	       (Syntax.const_name syn mx, T,       InfixlName (syn, p))
  | fix_mixfix (syn                     , T, mx as Infixr           p ) = 
	       (Syntax.const_name syn mx, T,       InfixrName (syn, p))
  | fix_mixfix decl = decl;
fun transform decl = let 
	val (c, T, mx) = fix_mixfix decl; 
	val c2 = "@"^c;
	val n  = Syntax.mixfix_args mx
    in	   ((c ,               T,NoSyn),
	    (c2,change_arrow n T,mx   ),
	    trans_rules c2 c n mx) end;

fun cfun_arity (Type(n,[_,T])) = if n = cfun_arrow then 1+cfun_arity T else 0
|   cfun_arity _               = 0;

fun is_contconst (_,_,NoSyn   ) = false
|   is_contconst (_,_,Binder _) = false
|   is_contconst (c,T,mx      ) = cfun_arity T >= Syntax.mixfix_args mx
			 handle ERROR => error ("in mixfix annotation for " ^
			 		       quote (Syntax.const_name c mx));

in (* local *)

fun ext_consts prep_typ raw_decls thy =
let val decls = map (upd_second (typ_of o prep_typ (sign_of thy))) raw_decls;
    val (contconst_decls, normal_decls) = filter2 is_contconst decls;
    val transformed_decls = map transform contconst_decls;
in thy |> Theory.add_consts_i                    normal_decls
       |> Theory.add_consts_i        (map first  transformed_decls)
       |> Theory.add_syntax_i        (map second transformed_decls)
       |> Theory.add_trrules_i (flat (map third  transformed_decls))
    handle ERROR =>
      error ("The error(s) above occurred in (cont)consts section")
end;

fun cert_typ sg typ =
  ctyp_of sg typ handle TYPE (msg, _, _) => error msg;

val add_consts   = ext_consts read_ctyp;
val add_consts_i = ext_consts cert_typ;

end; (* local *)

end; (* struct *)

val _ = ThySyn.add_syntax []
    [ThyParse.section "consts" "|> ContConsts.add_consts" ThyParse.const_decls];

