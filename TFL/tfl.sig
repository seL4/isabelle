signature TFL_sig =
sig
   structure Rules: Rules_sig
   structure Thms : Thms_sig
   structure Thry : Thry_sig
   structure USyntax : USyntax_sig

   type Preterm
   type Term
   type Thm
   type Thry
   type Tactic
   
   datatype pattern = GIVEN of Preterm * int
                    | OMITTED of Preterm * int

   val mk_functional : Thry -> Preterm
                       -> {functional:Preterm,
                           pats: pattern list}

   val wfrec_definition0 : Thry -> Preterm -> Preterm -> Thm * Thry

   val post_definition : Thry * (Thm * pattern list)
                              -> {theory : Thry,
                                  rules  : Thm, 
                                    TCs  : Preterm list list,
                          full_pats_TCs  : (Preterm * Preterm list) list, 
                               patterns  : pattern list}


   val wfrec_eqns : Thry -> Preterm
                     -> {WFR : Preterm, 
                         proto_def : Preterm,
                         extracta :(Thm * Preterm list) list,
                         pats  : pattern list}


   val lazyR_def : Thry
                   -> Preterm
                   -> {theory:Thry,
                       rules :Thm,
                           R :Preterm,
                       full_pats_TCs :(Preterm * Preterm list) list, 
                       patterns: pattern list}

   val mk_induction : Thry 
                       -> Preterm -> Preterm 
                         -> (Preterm * Preterm list) list
                           -> Thm

   val postprocess: {WFtac:Tactic, terminator:Tactic, simplifier:Term -> Thm}
                     -> Thry 
                      -> {rules:Thm, induction:Thm, TCs:Preterm list list}
                       -> {rules:Thm, induction:Thm, nested_tcs:Thm list}

   structure Context
     : sig
         val read : unit -> Thm list
         val write : Thm list -> unit
       end
end;
