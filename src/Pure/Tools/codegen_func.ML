(*  Title:      Pure/Tools/codegen_func.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Handling defining equations ("func"s) for code generator framework
*)

(* FIXME move various stuff here *)

signature CODEGEN_FUNC =
sig
  val expand_eta: theory -> int -> thm -> thm
end;

structure CodegenFunc : CODEGEN_FUNC =
struct

(* FIXME get rid of this code duplication *)
val purify_name =
  let
    fun is_valid s = Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "'";
    val is_junk = not o is_valid andf Symbol.not_eof;
    val junk = Scan.many is_junk;
    val scan_valids = Symbol.scanner "Malformed input"
      ((junk |--
        (Scan.optional (Scan.one Symbol.is_ascii_letter) "x" ^^ (Scan.many is_valid >> implode)
        --| junk))
      -- Scan.repeat ((Scan.many1 is_valid >> implode) --| junk) >> op ::);
  in explode #> scan_valids #> space_implode "_" end;

val purify_lower =
  explode
  #> (fn cs => (if forall Symbol.is_ascii_upper cs
        then map else nth_map 0) Symbol.to_ascii_lower cs)
  #> implode;

fun purify_var "" = "x"
  | purify_var v = (purify_name #> purify_lower) v;

fun expand_eta thy k thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Drule.plain_prop_of) thm;
    val (head, args) = strip_comb lhs;
    val l = if k = ~1
      then (length o fst o strip_abs) rhs
      else Int.max (0, k - length args);
    val used = Name.make_context (map (fst o fst) (Term.add_vars lhs []));
    fun get_name _ 0 used = ([], used)
      | get_name (Abs (v, ty, t)) k used =
          used
          |> Name.variants [purify_var v]
          ||>> get_name t (k - 1)
          |>> (fn ([v'], vs') => (v', ty) :: vs')
      | get_name t k used = 
          let
            val (tys, _) = (strip_type o fastype_of) t
          in case tys
           of [] => raise TERM ("expand_eta", [t])
            | ty :: _ =>
                used
                |> Name.variants [""]
                |-> (fn [v] => get_name (t $ Var ((v, 0), ty)) (k - 1)
                #>> (fn vs' => (v, ty) :: vs'))
          end;
    val (vs, _) = get_name rhs l used;
    val vs_refl = map (fn (v, ty) => Thm.reflexive (Thm.cterm_of thy (Var ((v, 0), ty)))) vs;
  in
    fold (fn refl => fn thm => Thm.combination thm refl) vs_refl thm
  end;

end;
