
header {* Basic group theory *}

theory Group = Main:

text {*
 \medskip\noindent The meta-level type system of Isabelle supports
 \emph{intersections} and \emph{inclusions} of type classes. These
 directly correspond to intersections and inclusions of type
 predicates in a purely set theoretic sense. This is sufficient as a
 means to describe simple hierarchies of structures.  As an
 illustration, we use the well-known example of semigroups, monoids,
 general groups and Abelian groups.
*}

subsection {* Monoids and Groups *}

text {*
 First we declare some polymorphic constants required later for the
 signature parts of our structures.
*}

consts
  times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<odot>" 70)
  invers :: "'a \<Rightarrow> 'a"    ("(_\<inv>)" [1000] 999)
  one :: 'a    ("\<unit>")

text {*
 \noindent Next we define class @{text monoid} of monoids with
 operations @{text \<odot>} and @{text \<unit>}.  Note that multiple class
 axioms are allowed for user convenience --- they simply represent the
 conjunction of their respective universal closures.
*}

axclass monoid \<subseteq> "term"
  assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  left_unit: "\<unit> \<odot> x = x"
  right_unit: "x \<odot> \<unit> = x"

text {*
 \noindent So class @{text monoid} contains exactly those types @{text
 \<tau>} where @{text "\<odot> \<Colon> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>"} and @{text "\<unit> \<Colon> \<tau>"} are
 specified appropriately, such that @{text \<odot>} is associative and
 @{text \<unit>} is a left and right unit element for the @{text \<odot>}
 operation.
*}

text {*
 \medskip Independently of @{text monoid}, we now define a linear
 hierarchy of semigroups, general groups and Abelian groups.  Note
 that the names of class axioms are automatically qualified with each
 class name, so we may re-use common names such as @{text assoc}.
*}

axclass semigroup \<subseteq> "term"
  assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"

axclass group \<subseteq> semigroup
  left_unit: "\<unit> \<odot> x = x"
  left_inverse: "x\<inv> \<odot> x = \<unit>"

axclass agroup \<subseteq> group
  commute: "x \<odot> y = y \<odot> x"

text {*
 \noindent Class @{text group} inherits associativity of @{text \<odot>}
 from @{text semigroup} and adds two further group axioms. Similarly,
 @{text agroup} is defined as the subset of @{text group} such that
 for all of its elements @{text \<tau>}, the operation @{text "\<odot> \<Colon> \<tau> \<Rightarrow> \<tau> \<Rightarrow>
 \<tau>"} is even commutative.
*}


subsection {* Abstract reasoning *}

text {*
 In a sense, axiomatic type classes may be viewed as \emph{abstract
 theories}.  Above class definitions gives rise to abstract axioms
 @{text assoc}, @{text left_unit}, @{text left_inverse}, @{text
 commute}, where any of these contain a type variable @{text "'a \<Colon> c"}
 that is restricted to types of the corresponding class @{text c}.
 \emph{Sort constraints} like this express a logical precondition for
 the whole formula.  For example, @{text assoc} states that for all
 @{text \<tau>}, provided that @{text "\<tau> \<Colon> semigroup"}, the operation
 @{text "\<odot> \<Colon> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>"} is associative.

 \medskip From a technical point of view, abstract axioms are just
 ordinary Isabelle theorems, which may be used in proofs without
 special treatment.  Such ``abstract proofs'' usually yield new
 ``abstract theorems''.  For example, we may now derive the following
 well-known laws of general groups.
*}

theorem group_right_inverse: "x \<odot> x\<inv> = (\<unit>\<Colon>'a\<Colon>group)"
proof -
  have "x \<odot> x\<inv> = \<unit> \<odot> (x \<odot> x\<inv>)"
    by (simp only: group.left_unit)
  also have "... = \<unit> \<odot> x \<odot> x\<inv>"
    by (simp only: semigroup.assoc)
  also have "... = (x\<inv>)\<inv> \<odot> x\<inv> \<odot> x \<odot> x\<inv>"
    by (simp only: group.left_inverse)
  also have "... = (x\<inv>)\<inv> \<odot> (x\<inv> \<odot> x) \<odot> x\<inv>"
    by (simp only: semigroup.assoc)
  also have "... = (x\<inv>)\<inv> \<odot> \<unit> \<odot> x\<inv>"
    by (simp only: group.left_inverse)
  also have "... = (x\<inv>)\<inv> \<odot> (\<unit> \<odot> x\<inv>)"
    by (simp only: semigroup.assoc)
  also have "... = (x\<inv>)\<inv> \<odot> x\<inv>"
    by (simp only: group.left_unit)
  also have "... = \<unit>"
    by (simp only: group.left_inverse)
  finally show ?thesis .
qed

text {*
 \noindent With @{text group_right_inverse} already available, @{text
 group_right_unit}\label{thm:group-right-unit} is now established much
 easier.
*}

theorem group_right_unit: "x \<odot> \<unit> = (x\<Colon>'a\<Colon>group)"
proof -
  have "x \<odot> \<unit> = x \<odot> (x\<inv> \<odot> x)"
    by (simp only: group.left_inverse)
  also have "... = x \<odot> x\<inv> \<odot> x"
    by (simp only: semigroup.assoc)
  also have "... = \<unit> \<odot> x"
    by (simp only: group_right_inverse)
  also have "... = x"
    by (simp only: group.left_unit)
  finally show ?thesis .
qed

text {*
 \medskip Abstract theorems may be instantiated to only those types
 @{text \<tau>} where the appropriate class membership @{text "\<tau> \<Colon> c"} is
 known at Isabelle's type signature level.  Since we have @{text
 "agroup \<subseteq> group \<subseteq> semigroup"} by definition, all theorems of @{text
 semigroup} and @{text group} are automatically inherited by @{text
 group} and @{text agroup}.
*}


subsection {* Abstract instantiation *}

text {*
 From the definition, the @{text monoid} and @{text group} classes
 have been independent.  Note that for monoids, @{text right_unit} had
 to be included as an axiom, but for groups both @{text right_unit}
 and @{text right_inverse} are derivable from the other axioms.  With
 @{text group_right_unit} derived as a theorem of group theory (see
 page~\pageref{thm:group-right-unit}), we may now instantiate @{text
 "monoid \<subseteq> semigroup"} and @{text "group \<subseteq> monoid"} properly as
 follows (cf.\ \figref{fig:monoid-group}).

 \begin{figure}[htbp]
   \begin{center}
     \small
     \unitlength 0.6mm
     \begin{picture}(65,90)(0,-10)
       \put(15,10){\line(0,1){10}} \put(15,30){\line(0,1){10}}
       \put(15,50){\line(1,1){10}} \put(35,60){\line(1,-1){10}}
       \put(15,5){\makebox(0,0){@{text agroup}}}
       \put(15,25){\makebox(0,0){@{text group}}}
       \put(15,45){\makebox(0,0){@{text semigroup}}}
       \put(30,65){\makebox(0,0){@{text "term"}}} \put(50,45){\makebox(0,0){@{text monoid}}}
     \end{picture}
     \hspace{4em}
     \begin{picture}(30,90)(0,0)
       \put(15,10){\line(0,1){10}} \put(15,30){\line(0,1){10}}
       \put(15,50){\line(0,1){10}} \put(15,70){\line(0,1){10}}
       \put(15,5){\makebox(0,0){@{text agroup}}}
       \put(15,25){\makebox(0,0){@{text group}}}
       \put(15,45){\makebox(0,0){@{text monoid}}}
       \put(15,65){\makebox(0,0){@{text semigroup}}}
       \put(15,85){\makebox(0,0){@{text term}}}
     \end{picture}
     \caption{Monoids and groups: according to definition, and by proof}
     \label{fig:monoid-group}
   \end{center}
 \end{figure}
*}

instance monoid \<subseteq> semigroup
proof
  fix x y z :: "'a\<Colon>monoid"
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (rule monoid.assoc)
qed

instance group \<subseteq> monoid
proof
  fix x y z :: "'a\<Colon>group"
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (rule semigroup.assoc)
  show "\<unit> \<odot> x = x"
    by (rule group.left_unit)
  show "x \<odot> \<unit> = x"
    by (rule group_right_unit)
qed

text {*
 \medskip The $\INSTANCE$ command sets up an appropriate goal that
 represents the class inclusion (or type arity, see
 \secref{sec:inst-arity}) to be proven (see also
 \cite{isabelle-isar-ref}).  The initial proof step causes
 back-chaining of class membership statements wrt.\ the hierarchy of
 any classes defined in the current theory; the effect is to reduce to
 the initial statement to a number of goals that directly correspond
 to any class axioms encountered on the path upwards through the class
 hierarchy.
*}


subsection {* Concrete instantiation \label{sec:inst-arity} *}

text {*
 So far we have covered the case of the form $\INSTANCE$~@{text
 "c\<^sub>1 \<subseteq> c\<^sub>2"}, namely \emph{abstract instantiation} ---
 $c@1$ is more special than @{text "c\<^sub>1"} and thus an instance
 of @{text "c\<^sub>2"}.  Even more interesting for practical
 applications are \emph{concrete instantiations} of axiomatic type
 classes.  That is, certain simple schemes @{text "(\<alpha>\<^sub>1, \<dots>,
 \<alpha>\<^sub>n) t \<Colon> c"} of class membership may be established at the
 logical level and then transferred to Isabelle's type signature
 level.

 \medskip As a typical example, we show that type @{typ bool} with
 exclusive-or as @{text \<odot>} operation, identity as @{text \<inv>}, and
 @{term False} as @{text \<unit>} forms an Abelian group.
*}

defs (overloaded)
  times_bool_def: "x \<odot> y \<equiv> x \<noteq> (y\<Colon>bool)"
  inverse_bool_def: "x\<inv> \<equiv> x\<Colon>bool"
  unit_bool_def: "\<unit> \<equiv> False"

text {*
 \medskip It is important to note that above $\DEFS$ are just
 overloaded meta-level constant definitions, where type classes are
 not yet involved at all.  This form of constant definition with
 overloading (and optional recursion over the syntactic structure of
 simple types) are admissible as definitional extensions of plain HOL
 \cite{Wenzel:1997:TPHOL}.  The Haskell-style type system is not
 required for overloading.  Nevertheless, overloaded definitions are
 best applied in the context of type classes.

 \medskip Since we have chosen above $\DEFS$ of the generic group
 operations on type @{typ bool} appropriately, the class membership
 @{text "bool \<Colon> agroup"} may be now derived as follows.
*}

instance bool :: agroup
proof (intro_classes,
    unfold times_bool_def inverse_bool_def unit_bool_def)
  fix x y z
  show "((x \<noteq> y) \<noteq> z) = (x \<noteq> (y \<noteq> z))" by blast
  show "(False \<noteq> x) = x" by blast
  show "(x \<noteq> x) = False" by blast
  show "(x \<noteq> y) = (y \<noteq> x)" by blast
qed

text {*
 The result of an $\INSTANCE$ statement is both expressed as a theorem
 of Isabelle's meta-logic, and as a type arity of the type signature.
 The latter enables type-inference system to take care of this new
 instance automatically.

 \medskip We could now also instantiate our group theory classes to
 many other concrete types.  For example, @{text "int \<Colon> agroup"}
 (e.g.\ by defining @{text \<odot>} as addition, @{text \<inv>} as negation
 and @{text \<unit>} as zero) or @{text "list \<Colon> (term) semigroup"}
 (e.g.\ if @{text \<odot>} is defined as list append).  Thus, the
 characteristic constants @{text \<odot>}, @{text \<inv>}, @{text \<unit>}
 really become overloaded, i.e.\ have different meanings on different
 types.
*}


subsection {* Lifting and Functors *}

text {*
 As already mentioned above, overloading in the simply-typed HOL
 systems may include recursion over the syntactic structure of types.
 That is, definitional equations @{text "c\<^sup>\<tau> \<equiv> t"} may also
 contain constants of name @{text c} on the right-hand side --- if
 these have types that are structurally simpler than @{text \<tau>}.

 This feature enables us to \emph{lift operations}, say to Cartesian
 products, direct sums or function spaces.  Subsequently we lift
 @{text \<odot>} component-wise to binary products @{typ "'a \<times> 'b"}.
*}

defs (overloaded)
  times_prod_def: "p \<odot> q \<equiv> (fst p \<odot> fst q, snd p \<odot> snd q)"

text {*
 It is very easy to see that associativity of @{text \<odot>} on @{typ 'a}
 and @{text \<odot>} on @{typ 'b} transfers to @{text \<odot>} on @{typ "'a \<times>
 'b"}.  Hence the binary type constructor @{text \<odot>} maps semigroups to
 semigroups.  This may be established formally as follows.
*}

instance * :: (semigroup, semigroup) semigroup
proof (intro_classes, unfold times_prod_def)
  fix p q r :: "'a\<Colon>semigroup \<times> 'b\<Colon>semigroup"
  show
    "(fst (fst p \<odot> fst q, snd p \<odot> snd q) \<odot> fst r,
      snd (fst p \<odot> fst q, snd p \<odot> snd q) \<odot> snd r) =
       (fst p \<odot> fst (fst q \<odot> fst r, snd q \<odot> snd r),
        snd p \<odot> snd (fst q \<odot> fst r, snd q \<odot> snd r))"
    by (simp add: semigroup.assoc)
qed

text {*
 Thus, if we view class instances as ``structures'', then overloaded
 constant definitions with recursion over types indirectly provide
 some kind of ``functors'' --- i.e.\ mappings between abstract
 theories.
*}

end