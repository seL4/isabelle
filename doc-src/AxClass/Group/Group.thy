
header {* Basic group theory *};

theory Group = Main:;

text {*
 \medskip\noindent The meta type system of Isabelle supports
 \emph{intersections} and \emph{inclusions} of type classes. These
 directly correspond to intersections and inclusions of type
 predicates in a purely set theoretic sense. This is sufficient as a
 means to describe simple hierarchies of structures.  As an
 illustration, we use the well-known example of semigroups, monoids,
 general groups and abelian groups.
*};

subsection {* Monoids and Groups *};

text {*
 First we declare some polymorphic constants required later for the
 signature parts of our structures.
*};

consts
  times :: "'a => 'a => 'a"    (infixl "\<Otimes>" 70)
  inverse :: "'a => 'a"        ("(_\<inv>)" [1000] 999)
  one :: 'a                    ("\<unit>");

text {*
 \noindent Next we define class $monoid$ of monoids with operations
 $\TIMES$ and $1$.  Note that multiple class axioms are allowed for
 user convenience --- they simply represent the conjunction of their
 respective universal closures.
*};

axclass
  monoid < "term"
  assoc:      "(x \<Otimes> y) \<Otimes> z = x \<Otimes> (y \<Otimes> z)"
  left_unit:  "\<unit> \<Otimes> x = x"
  right_unit: "x \<Otimes> \<unit> = x";

text {*
 \noindent So class $monoid$ contains exactly those types $\tau$ where
 $\TIMES :: \tau \To \tau \To \tau$ and $1 :: \tau$ are specified
 appropriately, such that $\TIMES$ is associative and $1$ is a left
 and right unit element for $\TIMES$.
*};

text {*
 \medskip Independently of $monoid$, we now define a linear hierarchy
 of semigroups, general groups and abelian groups.  Note that the
 names of class axioms are automatically qualified with the class
 name; thus we may re-use common names such as $assoc$.
*};

axclass
  semigroup < "term"
  assoc: "(x \<Otimes> y) \<Otimes> z = x \<Otimes> (y \<Otimes> z)";

axclass
  group < semigroup
  left_unit:    "\<unit> \<Otimes> x = x"
  left_inverse: "inverse x \<Otimes> x = \<unit>";

axclass
  agroup < group
  commute: "x \<Otimes> y = y \<Otimes> x";

text {*
 \noindent Class $group$ inherits associativity of $\TIMES$ from
 $semigroup$ and adds the other two group axioms. Similarly, $agroup$
 is defined as the subset of $group$ such that for all of its elements
 $\tau$, the operation $\TIMES :: \tau \To \tau \To \tau$ is even
 commutative.
*};


subsection {* Abstract reasoning *};

text {*
 In a sense, axiomatic type classes may be viewed as \emph{abstract
 theories}.  Above class definitions gives rise to abstract axioms
 $assoc$, $left_unit$, $left_inverse$, $commute$, where all of these
 contain type a variable $\alpha :: c$ that is restricted to types of
 the corresponding class $c$.  \emph{Sort constraints} like this
 express a logical precondition for the whole formula.  For example,
 $assoc$ states that for all $\tau$, provided that $\tau ::
 semigroup$, the operation $\TIMES :: \tau \To \tau \To \tau$ is
 associative.

 \medskip From a technical point of view, abstract axioms are just
 ordinary Isabelle theorems, which may be used in proofs without
 special treatment.  Such ``abstract proofs'' usually yield new
 ``abstract theorems''.  For example, we may now derive the following
 laws of general groups.
*};

theorem group_right_inverse: "x \<Otimes> x\<inv> = (\<unit>\<Colon>'a\<Colon>group)";
proof -;
  have "x \<Otimes> x\<inv> = \<unit> \<Otimes> (x \<Otimes> x\<inv>)";
    by (simp only: group.left_unit);
  also; have "... = (\<unit> \<Otimes> x) \<Otimes> x\<inv>";
    by (simp only: semigroup.assoc);
  also; have "... = (x\<inv>)\<inv> \<Otimes> x\<inv> \<Otimes> x \<Otimes> x\<inv>";
    by (simp only: group.left_inverse);
  also; have "... = (x\<inv>)\<inv> \<Otimes> (x\<inv> \<Otimes> x) \<Otimes> x\<inv>";
    by (simp only: semigroup.assoc);
  also; have "... = (x\<inv>)\<inv> \<Otimes> \<unit> \<Otimes> x\<inv>";
    by (simp only: group.left_inverse);
  also; have "... = (x\<inv>)\<inv> \<Otimes> (\<unit> \<Otimes> x\<inv>)";
    by (simp only: semigroup.assoc);
  also; have "... = (x\<inv>)\<inv> \<Otimes> x\<inv>";
    by (simp only: group.left_unit);
  also; have "... = \<unit>";
    by (simp only: group.left_inverse);
  finally; show ?thesis; .;
qed;

text {*
 \noindent With $group_right_inverse$ already available,
 $group_right_unit$\label{thm:group-right-unit} is now established
 much easier.
*};

theorem group_right_unit: "x \<Otimes> \<unit> = (x\<Colon>'a\<Colon>group)";
proof -;
  have "x \<Otimes> \<unit> = x \<Otimes> (x\<inv> \<Otimes> x)";
    by (simp only: group.left_inverse);
  also; have "... = x \<Otimes> x\<inv> \<Otimes> x";
    by (simp only: semigroup.assoc);
  also; have "... = \<unit> \<Otimes> x";
    by (simp only: group_right_inverse);
  also; have "... = x";
    by (simp only: group.left_unit);
  finally; show ?thesis; .;
qed;

text {*
 \medskip Abstract theorems may be instantiated to only those types
 $\tau$ where the appropriate class membership $\tau :: c$ is known at
 Isabelle's type signature level.  Since we have $agroup \subseteq
 group \subseteq semigroup$ by definition, all theorems of $semigroup$
 and $group$ are automatically inherited by $group$ and $agroup$.
*};


subsection {* Abstract instantiation *};

text {*
 From the definition, the $monoid$ and $group$ classes have been
 independent.  Note that for monoids, $right_unit$ had to be included
 as an axiom, but for groups both $right_unit$ and $right_inverse$ are
 derivable from the other axioms.  With $group_right_unit$ derived as
 a theorem of group theory (see page~\pageref{thm:group-right-unit}),
 we may now instantiate $group \subseteq monoid$ properly as follows
 (cf.\ \figref{fig:monoid-group}).

 \begin{figure}[htbp]
   \begin{center}
     \small
     \unitlength 0.6mm
     \begin{picture}(65,90)(0,-10)
       \put(15,10){\line(0,1){10}} \put(15,30){\line(0,1){10}}
       \put(15,50){\line(1,1){10}} \put(35,60){\line(1,-1){10}}
       \put(15,5){\makebox(0,0){$agroup$}}
       \put(15,25){\makebox(0,0){$group$}}
       \put(15,45){\makebox(0,0){$semigroup$}}
       \put(30,65){\makebox(0,0){$term$}} \put(50,45){\makebox(0,0){$monoid$}}
     \end{picture}
     \hspace{4em}
     \begin{picture}(30,90)(0,0)
       \put(15,10){\line(0,1){10}} \put(15,30){\line(0,1){10}}
       \put(15,50){\line(0,1){10}} \put(15,70){\line(0,1){10}}
       \put(15,5){\makebox(0,0){$agroup$}}
       \put(15,25){\makebox(0,0){$group$}}
       \put(15,45){\makebox(0,0){$monoid$}}
       \put(15,65){\makebox(0,0){$semigroup$}}
       \put(15,85){\makebox(0,0){$term$}}
     \end{picture}
     \caption{Monoids and groups: according to definition, and by proof}
     \label{fig:monoid-group}
   \end{center}
 \end{figure}

 We know by definition that $\TIMES$ is associative for monoids, i.e.\
 $monoid \subseteq semigroup$. Furthermore we have $assoc$,
 $left_unit$ and $right_unit$ for groups (where $right_unit$ is
 derivable from the group axioms), that is $group \subseteq monoid$.
 Thus we may establish the following class instantiations.
*};

instance monoid < semigroup;
proof intro_classes;
  fix x y z :: "'a\<Colon>monoid";
  show "x \<Otimes> y \<Otimes> z = x \<Otimes> (y \<Otimes> z)";
    by (rule monoid.assoc);
qed;

instance group < monoid;
proof intro_classes;
  fix x y z :: "'a\<Colon>group";
  show "x \<Otimes> y \<Otimes> z = x \<Otimes> (y \<Otimes> z)";
    by (rule semigroup.assoc);
  show "\<unit> \<Otimes> x = x";
    by (rule group.left_unit);
  show "x \<Otimes> \<unit> = x";
    by (rule group_right_unit);
qed;

text {*
 \medskip The $\isakeyword{instance}$ command sets up an appropriate
 goal that represents the class inclusion (or type arity) to be proven
 (see also \cite{isabelle-isar-ref}).  The $intro_classes$ proof
 method does back-chaining of class membership statements wrt.\ the
 hierarchy of any classes defined in the current theory; the effect is
 to reduce to any logical class axioms as subgoals.
*};


subsection {* Concrete instantiation *};

text {*
 So far we have covered the case of the form
 $\isakeyword{instance}~c@1 < c@2$, namely \emph{abstract
 instantiation} --- $c@1$ is more special than $c@2$ and thus an
 instance of $c@2$.  Even more interesting for practical applications
 are \emph{concrete instantiations} of axiomatic type classes.  That
 is, certain simple schemes $(\alpha@1, \ldots, \alpha@n)t :: c$ of
 class membership may be established at the logical level and then
 transferred to Isabelle's type signature level.

 \medskip

 As an typical example, we show that type $bool$ with exclusive-or as
 operation $\TIMES$, identity as $\isasyminv$, and $False$ as $1$
 forms an Abelian group.
*};

defs
  times_bool_def:   "x \<Otimes> y \\<equiv> x \\<noteq> (y\\<Colon>bool)"
  inverse_bool_def: "x\<inv> \\<equiv> x\\<Colon>bool"
  unit_bool_def:    "\<unit> \\<equiv> False";

text {*
 \medskip It is important to note that above $\DEFS$ are just
 overloaded meta-level constant definitions.  In particular, type
 classes are not yet involved at all!  This form of constant
 definition with overloading (and optional recursion over the
 syntactic structure of simple types) are admissible of proper
 definitional extensions in any version of HOL
 \cite{Wenzel:1997:TPHOL}.  Nevertheless, overloaded definitions are
 best applied in the context of type classes.

 \medskip Since we have chosen above $\DEFS$ of the generic group
 operations on type $bool$ appropriately, the class membership $bool
 :: agroup$ may be now derived as follows.
*};

instance bool :: agroup;
proof (intro_classes,
    unfold times_bool_def inverse_bool_def unit_bool_def);
  fix x y z :: bool;
  show "((x \\<noteq> y) \\<noteq> z) = (x \\<noteq> (y \\<noteq> z))"; by blast;
  show "(False \\<noteq> x) = x"; by blast;
  show "(x \\<noteq> x) = False"; by blast;
  show "(x \\<noteq> y) = (y \\<noteq> x)"; by blast;
qed;

text {*
 The result of $\isakeyword{instance}$ is both expressed as a theorem
 of Isabelle's meta-logic, and a type arity statement of the type
 signature.  The latter enables the type-inference system to take care
 of this new instance automatically.

 \medskip In a similarly fashion, we could also instantiate our group
 theory classes to many other concrete types.  For example, $int ::
 agroup$ (e.g.\ by defining $\TIMES$ as addition, $\isasyminv$ as
 negation and $1$ as zero) or $list :: (term)semigroup$ (e.g.\ if
 $\TIMES$ is defined as list append).  Thus, the characteristic
 constants $\TIMES$, $\isasyminv$, $1$ really become overloaded, i.e.\
 have different meanings on different types.
*};


subsection {* Lifting and Functors *};

text {*
 As already mentioned above, overloading in the simply-typed HOL
 systems may include recursion over the syntactic structure of types.
 That is, definitional equations $c^\tau \equiv t$ may also contain
 constants of name $c$ on the right-hand side --- if these have types
 that are structurally simpler than $\tau$.

 This feature enables us to \emph{lift operations}, say to Cartesian
 products, direct sums or function spaces.  Subsequently we lift
 $\TIMES$ component-wise to binary Cartesian products $\alpha \times
 \beta$.
*};

defs
  prod_prod_def: "p \<Otimes> q \\<equiv> (fst p \<Otimes> fst q, snd p \<Otimes> snd q)";

text {*
 It is very easy to see that associativity of $\TIMES^\alpha$,
 $\TIMES^\beta$ transfers to ${\TIMES}^{\alpha \times \beta}$.  Hence
 the binary type constructor $\times$ maps semigroups to semigroups.
 This may be established formally as follows.
*};

instance * :: (semigroup, semigroup) semigroup;
proof (intro_classes, unfold prod_prod_def);
  fix p q r :: "'a\<Colon>semigroup * 'b\<Colon>semigroup";
  show
    "(fst (fst p \<Otimes> fst q, snd p \<Otimes> snd q) \<Otimes> fst r,
      snd (fst p \<Otimes> fst q, snd p \<Otimes> snd q) \<Otimes> snd r) =
       (fst p \<Otimes> fst (fst q \<Otimes> fst r, snd q \<Otimes> snd r),
        snd p \<Otimes> snd (fst q \<Otimes> fst r, snd q \<Otimes> snd r))";
    by (simp add: semigroup.assoc);
qed;

text {*
 Thus, if we view class instances as ``structures'', then overloaded
 constant definitions with primitive recursion over types indirectly
 provide some kind of ``functors'' --- i.e.\ mappings between abstract
 theories.
*};

end;