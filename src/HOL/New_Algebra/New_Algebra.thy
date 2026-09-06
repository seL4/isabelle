section \<open>The New-Algebra Development\<close>

theory New_Algebra
  imports
    (* groups *)
    Subgroup_Lattice
    Simple_Group
    Group_Iso_Classes
    Normal_Series
    Composition_Series
    Composition_Factor_Classes
    Normal_Chain
    Group_Product
    Group_Family_Product
    Zassenhaus_Sanity
    Series_Refinement
    Schreier_Refinement
    Schreier_Sanity
    Reduced_Schreier_Refinement
    Simple_Factor_Chain
    Jordan_Hoelder_Uniqueness
    Maximal_Normal_Subgroup
    Finite_Composition_Series
    Composition_Sanity
    Abel_Ruffini
    P_Group
    (* rings, ideals, divisibility *)
    Subring_Generated
    Finite_Field_Cardinality
    Ideal_Extension
    Chinese_Remainder_Rings
    Field_Of_Fractions
    Poly_Divisibility_Bridge
    Closure_Algebraic
    Int_Ring
    (* modules and vector spaces *)
    Module_Complements
    Module_Exact_Sequence
    Module_Family_Product
    Free_Module_Universal
    Vector_Space_Typeclass
    Grassmann_Dimension
    Finite_Dimensional_Isomorphism
    Finite_Dimensional_Splitting
    (* fields, extensions, Galois theory *)
    Field_Extension
    Field_Mult_Cyclic
    Rats_Irreducibility
    Galois_Degree
    Galois_Simple_Degree
    Galois_Restriction_Splitting
    Artin_Degree
    Finite_Extension
    Primitive_Element
    Normal_Closure
    (* finite fields *)
    GF4
    GF8
    GF9
begin

text \<open>
  The single entry point to the development, in the manner of HOL-Algebra's \<open>Algebra\<close>: importing
  this theory makes the whole of New-Algebra available, and \<^file>\<open>ROOT\<close> need name nothing else.

  Only the \<^emph>\<open>maximal\<close> theories are listed, exactly as \<^file>\<open>ROOT\<close> used to list them: every other
  theory in the session is reached transitively, so a theory that some theory above already imports
  does not belong here.  The groupings are the mathematical ones and carry no logical force.
\<close>

end
