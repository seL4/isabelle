(*  Title:      find_consts.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

  Hoogle-like (http://www-users.cs.york.ac.uk/~ndm/hoogle) searching by type
  over constants, but matching is not fuzzy
*)

signature FIND_CONSTS =
sig
  datatype criterion = Strict of string
                     | Loose of string
                     | Name of string

  val default_criteria : (bool * criterion) list ref

  val find_consts : Proof.context -> (bool * criterion) list -> unit
end;

structure FindConsts : FIND_CONSTS =
struct

datatype criterion = Strict of string
                   | Loose of string
                   | Name of string;

val default_criteria = ref [(false, Name ".sko_")];

fun add_tye (_, (_, t)) n = size_of_typ t + n;

fun matches_subtype thy typat = let
    val p = can (fn ty => Sign.typ_match thy (typat, ty) Vartab.empty);

    fun fs [] = false
      | fs (t::ts) = f t orelse fs ts

    and f (t as Type (_, ars)) = p t orelse fs ars
      | f t = p t;
  in f end;

fun check_const p (nm, (ty, _)) = if p (nm, ty)
                                  then SOME (size_of_typ ty)
                                  else NONE;

fun opt_not f (c as (_, (ty, _))) = if is_some (f c)
                                    then NONE else SOME (size_of_typ ty);

fun find_consts ctxt raw_criteria = let
    val thy = ProofContext.theory_of ctxt;
    val low_ranking = 10000;

    fun make_pattern crit = ProofContext.read_term_pattern ctxt ("_::" ^ crit)
                            |> type_of;

    fun make_match (Strict arg) =
          let val qty = make_pattern arg; in
            fn (_, (ty, _)) => let
                val tye = Sign.typ_match thy (qty, ty) Vartab.empty;
                val sub_size = Vartab.fold add_tye tye 0;
              in SOME sub_size end handle MATCH => NONE
          end

      | make_match (Loose arg) =
          check_const (matches_subtype thy (make_pattern arg) o snd)
      
      | make_match (Name arg) = check_const (match_string arg o fst);

    fun make_criterion (b, crit) = (if b then I else opt_not) (make_match crit);
    val criteria = map make_criterion ((!default_criteria) @ raw_criteria);

    val (_, consts) = (#constants o Consts.dest o Sign.consts_of) thy;

    fun filter_const (_, NONE) = NONE
      | filter_const (f, (SOME (c, r))) = Option.map
                                            (pair c o ((curry Int.min) r))
                                            (f c);

    fun eval_entry c = foldl filter_const (SOME (c, low_ranking)) criteria;

    fun show (nm, ty) = let
        val ty' = Logic.unvarifyT ty;
      in
        (Pretty.block [Pretty.quote (Pretty.str nm), Pretty.fbrk,
                       Pretty.str "::", Pretty.brk 1,
                       Pretty.quote (Syntax.pretty_typ ctxt ty')])
      end;
  in
    Symtab.fold (cons o eval_entry) consts []
    |> map_filter I
    |> sort (rev_order o int_ord o pairself snd)
    |> map ((apsnd fst) o fst)
    |> map show
    |> Pretty.big_list "results:"
    |> Pretty.writeln
  end handle ERROR s => Output.error_msg s

end;

