(*  Title:      Pure/Isar/local_syntax.ML
    ID:         $Id$
    Author:     Makarius

Local syntax depending on theory syntax.
*)

val show_structs = ref false;

signature LOCAL_SYNTAX =
sig
  type T
  val syn_of: T -> Syntax.syntax
  val structs_of: T -> string list
  val init: theory -> T
  val rebuild: theory -> T -> T
  val add_syntax: theory -> (bool * (string * typ * mixfix)) list -> T -> T
  val extern_term: (string -> xstring) -> theory -> T -> term -> term
end;

structure LocalSyntax: LOCAL_SYNTAX =
struct

(* datatype T *)

datatype T = Syntax of
 {thy_syntax: Syntax.syntax,
  local_syntax: Syntax.syntax,
  mixfixes: (((string * bool) * string list list) * (string * typ * mixfix)) list,
  idents: string list * string list * string list};

fun make_syntax (thy_syntax, local_syntax, mixfixes, idents) =
  Syntax {thy_syntax = thy_syntax, local_syntax = local_syntax,
    mixfixes = mixfixes, idents = idents};

fun map_syntax f (Syntax {thy_syntax, local_syntax, mixfixes, idents}) =
  make_syntax (f (thy_syntax, local_syntax, mixfixes, idents));

fun is_consistent thy (syntax as Syntax {thy_syntax, ...}) =
  Syntax.eq_syntax (Sign.syn_of thy, thy_syntax);

fun syn_of (Syntax {local_syntax, ...}) = local_syntax;
fun idents_of (Syntax {idents, ...}) = idents;
val structs_of = #1 o idents_of;


(* build syntax *)

fun build_syntax thy (mixfixes, idents as (structs, _, _)) =
  let
    val thy_syntax = Sign.syn_of thy;
    val is_logtype = Sign.is_logtype thy;
    val (atrs, trs, trs', atrs') = Syntax.struct_trfuns structs;
    val local_syntax = thy_syntax
      |> Syntax.extend_trfuns
         (map Syntax.mk_trfun atrs, map Syntax.mk_trfun trs,
          map Syntax.mk_trfun trs', map Syntax.mk_trfun atrs')
      |> Syntax.extend_const_gram is_logtype ("", false)
         (map (fn (((x, _), _), (c, T, _)) => (c, T, Syntax.literal x)) mixfixes)
      |> Syntax.extend_const_gram is_logtype ("", true) (map snd mixfixes)
  in make_syntax (thy_syntax, local_syntax, mixfixes, idents) end

fun init thy = build_syntax thy ([], ([], [], []));

fun rebuild thy (syntax as Syntax {mixfixes, idents, ...}) =
  if is_consistent thy syntax then syntax
  else build_syntax thy (mixfixes, idents);


(* mixfix declarations *)

local

fun mixfix_nosyn (_, (_, _, mx)) = mx = NoSyn;
fun mixfix_struct (_, (_, _, mx)) = mx = Structure;

fun mixfix_conflict (content1: string list list, ((_, content2), _)) =
  exists (fn x => exists (fn y => x = y) content2) content1;

fun add_mixfix (fixed, (x, T, mx)) =
  let
    val content = Syntax.mixfix_content mx;
    val c = if fixed then Syntax.fixedN ^ x else Syntax.constN ^ x;
  in remove mixfix_conflict content #> cons (((x, fixed), content), (c, T, mx)) end;

fun prep_struct (fixed, (c, _, Structure)) =
      if fixed then SOME c
      else error ("Bad mixfix declaration for const: " ^ quote c)
  | prep_struct _ = NONE;

in

fun add_syntax thy raw_decls (syntax as (Syntax {mixfixes, idents = (structs, _, _), ...})) =
  (case filter_out mixfix_nosyn raw_decls of
    [] => syntax
  | decls =>
      let
        val mixfixes' = mixfixes |> fold add_mixfix (filter_out mixfix_struct decls);
        val fixes' = fold (fn (((x, true), _), _) => cons x | _ => I) mixfixes' [];
        val consts' = fold (fn (((x, false), _), _) => cons x | _ => I) mixfixes' [];
        val structs' = structs @ List.mapPartial prep_struct decls;
      in build_syntax thy (mixfixes', (structs', fixes', consts')) end);

end;


(* extern_term *)

fun extern_term extern_const thy syntax =
  let
    val (structs, fixes, consts) = idents_of syntax;
    fun map_const c =
      if member (op =) consts c then Syntax.constN ^ c else extern_const c;
    fun map_free (t as Free (x, T)) =
          let val i = Library.find_index_eq x structs + 1 in
            if i = 0 andalso member (op =) fixes x then
              Const (Syntax.fixedN ^ x, T)
            else if i = 1 andalso not (! show_structs) then
              Syntax.const "_struct" $ Syntax.const "_indexdefault"
            else t
          end
      | map_free t = t;
  in Sign.extern_term map_const thy #> Term.map_aterms map_free end;


end;
