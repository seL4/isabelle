signature Thry_sig =
sig
  type Type
  type Preterm
  type Term
  type Thm
  type Thry
  type 'a binding

  structure USyntax : USyntax_sig
  val match_term : Thry -> Preterm -> Preterm 
                    -> Preterm binding list * Type binding list

  val match_type : Thry -> Type -> Type -> Type binding list

  val typecheck : Thry -> Preterm -> Term

  val make_definition: Thry -> string -> Preterm -> Thm * Thry

  (* Datatype facts of various flavours *)
  val match_info: Thry -> string -> {constructors:Preterm list,
                                     case_const:Preterm} USyntax.Utils.option

  val induct_info: Thry -> string -> {constructors:Preterm list,
                                      nchotomy:Thm} USyntax.Utils.option

  val extract_info: Thry -> {case_congs:Thm list, case_rewrites:Thm list}

end;


