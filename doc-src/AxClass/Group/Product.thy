
header {* Syntactic classes *};

theory Product = Main:;

text {*
 \medskip\noindent There is still a feature of Isabelle's type system
 left that we have not yet discussed.  When declaring polymorphic
 constants $c :: \sigma$, the type variables occurring in $\sigma$ may
 be constrained by type classes (or even general sorts) in an
 arbitrary way.  Note that by default, in Isabelle/HOL the declaration
 $\TIMES :: \alpha \To \alpha \To \alpha$ is actually an abbreviation
 for $\TIMES :: (\alpha::term) \To \alpha \To \alpha$.  Since class
 $term$ is the universal class of HOL, this is not really a constraint
 at all.

 The $product$ class below provides a less degenerate example of
 syntactic type classes.
*};

axclass
  product < "term";
consts
  product :: "'a::product \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\\<Otimes>" 70);

text {*
 Here class $product$ is defined as subclass of $term$ without any
 additional axioms.  This effects in logical equivalence of $product$
 and $term$, as is reflected by the trivial introduction rule
 generated for this definition.

 \medskip So what is the difference of declaring $\TIMES :: (\alpha ::
 product) \To \alpha \To \alpha$ vs.\ declaring $\TIMES :: (\alpha ::
 term) \To \alpha \To \alpha$ anyway?  In this particular case where
 $product \equiv term$, it should be obvious that both declarations
 are the same from the logic's point of view.  It even makes the most
 sense to remove sort constraints from constant declarations, as far
 as the purely logical meaning is concerned \cite{Wenzel:1997:TPHOL}.

 On the other hand there are syntactic differences, of course.
 Constants $\TIMES^\tau$ are rejected by the type-checker, unless the
 arity $\tau :: product$ is part of the type signature.  In our
 example, this arity may be always added when required by means of an
 $\isarkeyword{instance}$ with the trivial proof $\BY{intro_classes}$.

 \medskip Thus, we may observe the following discipline of using
 syntactic classes.  Overloaded polymorphic constants have their type
 arguments restricted to an associated (logically trivial) class $c$.
 Only immediately before \emph{specifying} these constants on a
 certain type $\tau$ do we instantiate $\tau :: c$.

 This is done for class $product$ and type $bool$ as follows.
*};

instance bool :: product;
  by intro_classes;
defs
  product_bool_def: "x \\<Otimes> y \\<equiv> x \\<and> y";

text {*
 The definition $prod_bool_def$ becomes syntactically well-formed only
 after the arity $bool :: product$ is made known to the type checker.

 \medskip It is very important to see that above $\DEFS$ are not
 directly connected with $\isarkeyword{instance}$ at all!  We were
 just following our convention to specify $\TIMES$ on $bool$ after
 having instantiated $bool :: product$.  Isabelle does not require
 these definitions, which is in contrast to programming languages like
 Haskell \cite{haskell-report}.

 \medskip While Isabelle type classes and those of Haskell are almost
 the same as far as type-checking and type inference are concerned,
 there are important semantic differences.  Haskell classes require
 their instances to \emph{provide operations} of certain \emph{names}.
 Therefore, its \texttt{instance} has a \texttt{where} part that tells
 the system what these ``member functions'' should be.

 This style of \texttt{instance} won't make much sense in Isabelle's
 meta-logic, because there is no internal notion of ``providing
 operations'' or even ``names of functions''.
*};

end;