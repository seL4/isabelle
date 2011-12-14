(*  Title:      HOL/Tools/ATP/atp_redirect.ML
    Author:     Jasmin Blanchette, TU Muenchen

Transformation of a proof by contradiction into a direct proof.
*)

signature ATP_REDIRECT =
sig
  type ref_sequent = int list * int
  type ref_graph = unit Int_Graph.T

  type clause = int list
  type direct_sequent = int list * clause
  type direct_graph = unit Int_Graph.T

  type rich_sequent = clause list * clause

  datatype inference =
    Have of rich_sequent |
    Hence of rich_sequent |
    Cases of (clause * inference list) list

  type proof = inference list

  val make_ref_graph : (int list * int) list -> ref_graph
  val sequents_of_ref_graph : ref_graph -> ref_sequent list
  val redirect_sequent : int list -> int -> ref_sequent -> direct_sequent
  val direct_graph : direct_sequent list -> direct_graph
  val redirect_graph : int list -> ref_graph -> proof
  val chain_proof : proof -> proof
  val string_of_proof : proof -> string
end;

structure ATP_Redirect : ATP_REDIRECT =
struct

type ref_sequent = int list * int
type ref_graph = unit Int_Graph.T

type clause = int list
type direct_sequent = int list * clause
type direct_graph = unit Int_Graph.T

type rich_sequent = clause list * clause

datatype inference =
  Have of rich_sequent |
  Hence of rich_sequent |
  Cases of (clause * inference list) list

type proof = inference list

fun make_ref_graph infers =
  let
    fun add_edge to from =
      Int_Graph.default_node (from, ())
      #> Int_Graph.default_node (to, ())
      #> Int_Graph.add_edge_acyclic (from, to)
    fun add_infer (froms, to) = fold (add_edge to) froms
  in Int_Graph.empty |> fold add_infer infers end

fun sequents_of_ref_graph g =
  map (`(Int_Graph.immediate_preds g))
      (filter_out (Int_Graph.is_minimal g) (Int_Graph.keys g))

fun redirect_sequent tainted bot (ante, l) =
  if member (op =) tainted l then
    ante |> List.partition (not o member (op =) tainted) |>> l <> bot ? cons l
  else
    (ante, [l])

fun direct_graph seqs =
  let
    fun add_edge from to =
      Int_Graph.default_node (from, ())
      #> Int_Graph.default_node (to, ())
      #> Int_Graph.add_edge_acyclic (from, to)
    fun add_seq (ante, c) = fold (fn l => fold (add_edge l) c) ante
  in Int_Graph.empty |> fold add_seq seqs end

fun disj cs = fold (union (op =)) cs [] |> sort int_ord

fun concl_of_inf (Have (_, c)) = c
  | concl_of_inf (Hence (_, c)) = c
  | concl_of_inf (Cases cases) = concl_of_cases cases
and concl_of_case (c, []) = c
  | concl_of_case (_, infs) = concl_of_inf (List.last infs)
and concl_of_cases cases = disj (map concl_of_case cases)

fun dest_Have (Have z) = z
  | dest_Have _ = raise Fail "non-Have"

fun enrich_Have nontrivs trivs (cs, c) =
  (cs |> map (fn c => if member (op =) nontrivs c then disj (c :: trivs)
                      else c),
   disj (c :: trivs))
  |> Have

fun s_cases cases =
  case cases |> List.partition (null o snd) of
    (trivs, [(nontriv0, proof)]) =>
    if forall (can dest_Have) proof then
      let val seqs = proof |> map dest_Have in
        seqs |> map (enrich_Have (nontriv0 :: map snd seqs) (map fst trivs))
      end
    else
      [Cases cases]
  | _ => [Cases cases]

fun descendants seqs =
  these o try (Int_Graph.all_succs (direct_graph seqs)) o single

fun zones_of 0 _ = []
  | zones_of n (ls :: lss) =
    (fold (subtract (op =)) lss) ls :: zones_of (n - 1) (lss @ [ls])

fun redirect c proved seqs =
  if null seqs then
    []
  else if length c < 2 then
    let
      val proved = c @ proved
      val provable = filter (fn (ante, _) => subset (op =) (ante, proved)) seqs
      val horn_provable = filter (fn (_, [_]) => true | _ => false) provable
      val seq as (ante, c) = hd (horn_provable @ provable)
    in
      Have (map single ante, c) ::
      redirect c proved (filter (curry (op <>) seq) seqs)
    end
  else
    let
      fun subsequents seqs zone =
        filter (fn (ante, _) => subset (op =) (ante, zone @ proved)) seqs
      val zones = zones_of (length c) (map (descendants seqs) c)
      val subseqss = map (subsequents seqs) zones
      val seqs = fold (subtract (op =)) subseqss seqs
      val cases =
        map2 (fn l => fn subseqs => ([l], redirect [l] proved subseqs))
             c subseqss
    in [Cases cases] @ redirect (concl_of_cases cases) proved seqs end

fun redirect_graph conjecture g =
  let
    val axioms = subtract (op =) conjecture (Int_Graph.minimals g)
    val tainted = Int_Graph.all_succs g conjecture
    val [bot] = Int_Graph.maximals g
    val seqs = map (redirect_sequent tainted bot) (sequents_of_ref_graph g)
  in redirect [] axioms seqs end

val chain_proof =
  let
    fun chain_inf cl0 (seq as Have (cs, c)) =
        if member (op =) cs cl0 then Hence (filter_out (curry (op =) cl0) cs, c)
        else seq
      | chain_inf _ (Cases cases) = Cases (map chain_case cases)
    and chain_case (c, is) = (c, chain_proof (SOME c) is)
    and chain_proof _ [] = []
      | chain_proof (SOME prev) (i :: is) =
        chain_inf prev i :: chain_proof (SOME (concl_of_inf i)) is
      | chain_proof _ (i :: is) = i :: chain_proof (SOME (concl_of_inf i)) is
  in chain_proof NONE end

fun indent 0 = ""
  | indent n = "  " ^ indent (n - 1)

fun string_of_clause [] = "\<bottom>"
  | string_of_clause ls = space_implode " \<or> " (map signed_string_of_int ls)

fun string_of_rich_sequent ch ([], c) = ch ^ " " ^ string_of_clause c
  | string_of_rich_sequent ch (cs, c) =
    commas (map string_of_clause cs) ^ " " ^ ch ^ " " ^ string_of_clause c

fun string_of_case depth (c, proof) =
  indent (depth + 1) ^ "[" ^ string_of_clause c ^ "]"
  |> not (null proof) ? suffix ("\n" ^ string_of_subproof (depth + 1) proof)

and string_of_inference depth (Have seq) =
    indent depth ^ string_of_rich_sequent "\<triangleright>" seq
  | string_of_inference depth (Hence seq) =
    indent depth ^ string_of_rich_sequent "\<guillemotright>" seq
  | string_of_inference depth (Cases cases) =
    indent depth ^ "[\n" ^
    space_implode ("\n" ^ indent depth ^ "|\n")
                  (map (string_of_case depth) cases) ^ "\n" ^
    indent depth ^ "]"

and string_of_subproof depth proof =
  cat_lines (map (string_of_inference depth) proof)

val string_of_proof = string_of_subproof 0

end;
