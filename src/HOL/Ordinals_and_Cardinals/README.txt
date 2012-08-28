Authors: Andrei Popescu & Dmitriy Traytel


PDF Documentation:
-----------------

See "document/root.pdf".



Short description of the theories' main content:
-----------------------------------------------

The "minor" theories Fun_More, Wellfounded_More and Order_Relation_More are
extensions of the existing theories Fun, Wellfounded and
Order_Relation: 
-- Fun_More states more facts (mainly) concerning injections, bijections,
inverses, and (numeric) cardinals of finite sets.
-- Wellfounded_More states variations of well-founded 
recursion and well-founded recursion. 
-- Order_Relation_More fixes a relation, defines upper and lower bounds
operators and proves many basic properties for these
(depending on assumptions such as reflexivity or transitivity).

The "major" theories are:
-- Wellorder_Relation: Here one fixes a well-order relation, and then:
----- 1) Defines the concepts of maximum (of two elements), minimum (of a set), supremum,
      successor (of a set), and order filter (i.e., downwards closed set, a.k.a.
      initial segment).  
-- Wellorder_Embedding:
----- 2) For two well-order relations,
      defines *well-order embeddings* as injective functions copying
      the source into an order filter of the target and *compatible functions*
      as those preserving the order.  Also, *isomorphisms* 
      and *strict embeddings* are defined to be embeddings that are, and respectively
      are not, bijections.

-- Constructions_on_Wellorders:
----- 1) Defines direct images, restrictions, disjoint unions and 
      bounded squares of well-orders.
----- 2) Defines the relations "ordLeq", "ordLess" and "ordIso" 
      between well-order relations (concrete syntax: r <=o r', r <o r' and 
      r =o r', respectively), defined by the existence of an embedding, 
      strict embedding and isomorphism, respectively between the two members.  
      Among the properties proved for these relations:
--------- ordLeq is total;
--------- ordLess (on a fixed type) is well-founded.

-- Cardinal_Order_Relation:
---- 1) Defines a *cardinal order* to be a well-order minim w.r.t. "ordLeq" 
     (or, equivalently, minimal w.r.t. "ordLess").
     ordLess being well-founded together with the well-ordering theorem (from theory Zorn.thy)
     ensures the existence of a cardinal relation on any given set. In addition, 
     a cardinal relation on a set is unique up to order isomorphism. 
---- 2) Defines the cardinal of a set A, |A|, to be SOME cardinal
     order on it (unique up to =o, according to the above). 
---- 3) Proves properties of cardinals, including their
     interactions with sums, products, unions, lists,
     powersets, sets of finite sets. Among them, nontrivial
     facts concerning the invariance of infinite cardinals
     under some of these constructs -- e.g., if A is infinite,
     than the cardinal of lists/words over A is the same (up to
     the "cardinal equality" =o) as that of A.
---- 5) Studies the connection between the introduced (order-based) notion
     of cardinal and the numeric one previously defined for
     finite sets (operator "card").  On the way, one introduces the cardinal omega
     (natLeq) and the finite cardinals (natLeq_on n).
---- 6) Defines and proves the existence of successor cardinals.  

-- Cardinal_Arithmetic


Here is a list of names of proved facts concerning cardinalities that are 
expressed independently of notions of order, and of potential interest 
for "working mathematicians":
--- one_set_greater, one_type_greater (their proofs use the 
    fact that ordinals are totally ordered)
--- Plus_into_Times, Plus_into_Times_types, 
    Plus_infinite_bij_betw, Plus_infinite_bij_betw_types,  
    Times_same_infinite_bij_betw, Times_same_infinite_bij_betw_types, 
    Times_infinite_bij_betw, Times_infinite_bij_betw_types
    inj_on_UNION_infinite, List_infinite_bij_betw, List_infinite_bij_betw_types
    Fpow_infinite_bij_betw 
    (their proofs employ cardinals)




Minor technicalities and naming issues:
---------------------------------------

1. Most of the definitions and theorems are proved in files suffixed with
"_Base". Bootstrapping considerations (for the (co)datatype package) made this
division desirable.


2. Even though we would have preferred to use "initial segment" instead of 
"order filter", we chose the latter to avoid terminological clash with 
the operator "init_seg_of" from Zorn.thy.  The latter expresses a related, but different 
concept -- it considers a relation, rather than a set, as initial segment of a relation.  


3. We prefer to define the upper-bound operations under, underS,
etc., as opposed to working with combinations of relation image,
converse and diagonal, because the former seem more intuitive
notations when we think of orderings (but of course we cannot
define them as abbreviations, as this would have a global
effect, also affecting cases where one does not think of relations 
as orders). Moreover, in my locales the relation parameter r for
under, underS etc. is fixed, hence these operations can keep r
implicit. To get a concrete glimpse at my aesthetic reason for
introducing these operations: otherwise, instead of "underS a",
we would have to write "(r - Id)^-1 `` {a}" or "r^-1 `` {a} - Id".


4. Even though the main focus of this development are
the well-order relations, we prove the basic results on order relations
and bounds as generally as possible.
To the contrary, the results concerning minima, suprema and successors
are stated for well-order relations, not maximally generally.


5. "Refl_on A r" requires in particular that "r <= A <*> A",
and therefore whenever "Refl_on A r", we have that necessarily
"A = Field r". This means that in a theory of orders the domain
A would be redundant -- we decided not to include it explicitly
for most of the tehory.


6. An infinite ordinal/cardinal is one for which the field is infinite.
We always prefer the slightly more verbose "finite (Field r)" to the more
compact but less standard equivalent condition "finite r".


7. After we proved lots of facts about injections and
bijections, we discovered that a couple of
fancier (set-restricted) version of some of them are proved in
the theory FuncSet. However, we did not need here restricted
abstraction and such, and felt we should not import the whole
theory for just a couple of minor facts.







Notes for anyone who would like to enrich these theories in the future
--------------------------------------------------------------------------------------

Theory Fun_More (and Fun_More_Base):
- Careful: "inj" is an abbreviation for "inj_on UNIV", while  
  "bij" is not an abreviation for "bij_betw UNIV UNIV", but 
  a defined constant; there is no "surj_betw", but only "surj". 
  "inv" is an abbreviation for "inv_into UNIV"
- In subsection "Purely functional properties": 
-- Recall lemma "comp_inj_on". 
-- A lemma for inj_on corresponding to "bij_betw_same_card" already exists, and is called "card_inj_on_le".
- In subsection "Properties involving Hilbert choice": 
-- One should refrain from trying to prove "intuitive" properties of f conditioned 
  by properties of (inv_into f A), such as "bij_betw A' A (inv_into f A) ==> bij_betw A A' f".  
  They usually do not hold, since one cannot usually infer the well-definedness of "inv_into f A". 
- A lemma "bij_betw_inv_into_LEFT" -- why didn't 
"proof(auto simp add: bij_betw_inv_into_left)" finish the proof?
-- Recall lemma "bij_betw_inv_into". 
- In subsection "Other facts": 
-- Does the lemma "atLeastLessThan_injective" already exist anywhere? 

Theory Order_Relation_More (and Order_Relation_More_Base):
- In subsection "Auxiliaries": 
-- Recall the lemmas "order_on_defs", "Field_def", "Domain_def", "Range_def", "converse_def". 
-- Recall that "refl_on r A" forces r to not be defined outside A.  
   This is  why "partial_order_def" 
   can afford to use non-parameterized versions of antisym and trans.  
-- Recall the ASCII notation for "converse r": "r ^-1". 
-- Recall the abbreviations: 
   abbreviation "Refl r ≡ refl_on (Field r) r"
   abbreviation "Preorder r ≡ preorder_on (Field r) r"
   abbreviation "Partial_order r ≡ partial_order_on (Field r) r"
   abbreviation "Total r ≡ total_on (Field r) r"
   abbreviation "Linear_order r ≡ linear_order_on (Field r) r"
   abbreviation "Well_order r ≡ well_order_on (Field r) r"

Theory Wellorder_Relation (and Wellorder_Relation_Base):
- In subsection "Auxiliaries": recall lemmas "order_on_defs"
- In subsection "The notions of maximum, minimum, supremum, successor and order filter": 
  Should we define all constants from "wo_rel" in "rel" instead, 
  so that their outside definition not be conditional in "wo_rel r"? 

Theory Wellfounded_More (and Wellfounded_More_Base):
  Recall the lemmas "wfrec" and "wf_induct". 

Theory Wellorder_Embedding (and Wellorder_Embedding_Base):
- Recall "inj_on_def" and "bij_betw_def". 
- Line 5 in the proof of lemma embed_in_Field: we have to figure out for this and many other 
  situations:  Why did it work without annotations to Refl_under_in?
- At the proof of theorem "wellorders_totally_ordered" (and, similarly, elsewhere): 
  Had we used metavariables instead of local definitions for H, f, g and test, the 
  goals (in the goal window) would have become unreadable, 
  making impossible to debug theorem instantiations.  
- At lemma "embed_unique": If we add the attribute "rule format" at lemma, we get an error at qed.

Theory Constructions_on_Wellorders (and Constructions_on_Wellorders_Base):
- Some of the lemmas in this section are about more general kinds of relations than 
  well-orders, but it is not clear whether they are useful in such more general contexts.
- Recall that "equiv" does not have the "equiv_on" and "Equiv" versions, 
 like the order relation. "equiv" corresponds, for instance, to "well_order_on". 
- The lemmas "ord_trans" are not clearly useful together, as their employment within blast or auto 
tends to diverge.  

Theory Cardinal_Order_Relation (and Cardinal_Order_Relation_Base):
- Careful: if "|..|" meets an outer parehthesis, an extra space needs to be inserted, as in
  "( |A| )". 
- At lemma like ordLeq_Sigma_mono1: Not worth stating something like ordLeq_Sigma_mono2 -- 
  would be a mere instance of card_of_Sigma_mono2.  
- At lemma ordLeq_Sigma_cong2: Again, no reason for stating something like ordLeq_Sigma_cong2.  
- At lemma Fpow_Pow_finite: why wouldn't a version of this lemma with "... Int finite" 
also be proved by blast?
