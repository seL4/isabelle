(*  Title:      HOL/Unix/Unix.thy
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Unix file-systems \label{sec:unix-file-system} *}

theory Unix
imports
  Nested_Environment
  "~~/src/HOL/Library/List_Prefix"
begin

text {*
  We give a simple mathematical model of the basic structures
  underlying the Unix file-system, together with a few fundamental
  operations that could be imagined to be performed internally by the
  Unix kernel.  This forms the basis for the set of Unix system-calls
  to be introduced later (see \secref{sec:unix-trans}), which are the
  actual interface offered to processes running in user-space.

  \medskip Basically, any Unix file is either a \emph{plain file} or a
  \emph{directory}, consisting of some \emph{content} plus
  \emph{attributes}.  The content of a plain file is plain text.  The
  content of a directory is a mapping from names to further
  files.\footnote{In fact, this is the only way that names get
  associated with files.  In Unix files do \emph{not} have a name in
  itself.  Even more, any number of names may be associated with the
  very same file due to \emph{hard links} (although this is excluded
  from our model).}  Attributes include information to control various
  ways to access the file (read, write etc.).

  Our model will be quite liberal in omitting excessive detail that is
  easily seen to be ``irrelevant'' for the aspects of Unix
  file-systems to be discussed here.  First of all, we ignore
  character and block special files, pipes, sockets, hard links,
  symbolic links, and mount points.
*}


subsection {* Names *}

text {*
  User ids and file name components shall be represented by natural
  numbers (without loss of generality).  We do not bother about
  encoding of actual names (e.g.\ strings), nor a mapping between user
  names and user ids as would be present in a reality.
*}

type_synonym uid = nat
type_synonym name = nat
type_synonym path = "name list"


subsection {* Attributes *}

text {*
  Unix file attributes mainly consist of \emph{owner} information and
  a number of \emph{permission} bits which control access for
  ``user'', ``group'', and ``others'' (see the Unix man pages @{text
  "chmod(2)"} and @{text "stat(2)"} for more details).

  \medskip Our model of file permissions only considers the ``others''
  part.  The ``user'' field may be omitted without loss of overall
  generality, since the owner is usually able to change it anyway by
  performing @{text chmod}.\footnote{The inclined Unix expert may try
  to figure out some exotic arrangements of a real-world Unix
  file-system such that the owner of a file is unable to apply the
  @{text chmod} system call.}  We omit ``group'' permissions as a
  genuine simplification as we just do not intend to discuss a model
  of multiple groups and group membership, but pretend that everyone
  is member of a single global group.\footnote{A general HOL model of
  user group structures and related issues is given in
  \cite{Naraschewski:2001}.}
*}

datatype perm =
    Readable
  | Writable
  | Executable    -- "(ignored)"

type_synonym perms = "perm set"

record att =
  owner :: uid
  others :: perms

text {*
  For plain files @{term Readable} and @{term Writable} specify read
  and write access to the actual content, i.e.\ the string of text
  stored here.  For directories @{term Readable} determines if the set
  of entry names may be accessed, and @{term Writable} controls the
  ability to create or delete any entries (both plain files or
  sub-directories).

  As another simplification, we ignore the @{term Executable}
  permission altogether.  In reality it would indicate executable
  plain files (also known as ``binaries''), or control actual lookup
  of directory entries (recall that mere directory browsing is
  controlled via @{term Readable}).  Note that the latter means that
  in order to perform any file-system operation whatsoever, all
  directories encountered on the path would have to grant @{term
  Executable}.  We ignore this detail and pretend that all directories
  give @{term Executable} permission to anybody.
*}


subsection {* Files *}

text {*
  In order to model the general tree structure of a Unix file-system
  we use the arbitrarily branching datatype @{typ "('a, 'b, 'c) env"}
  from the standard library of Isabelle/HOL
  \cite{Bauer-et-al:2002:HOL-Library}.  This type provides
  constructors @{term Val} and @{term Env} as follows:

  \medskip
  {\def\isastyleminor{\isastyle}
  \begin{tabular}{l}
  @{term [source] "Val :: 'a \<Rightarrow> ('a, 'b, 'c) env"} \\
  @{term [source] "Env :: 'b \<Rightarrow> ('c \<Rightarrow> ('a, 'b, 'c) env option) \<Rightarrow> ('a, 'b, 'c) env"} \\
  \end{tabular}}
  \medskip

  Here the parameter @{typ 'a} refers to plain values occurring at
  leaf positions, parameter @{typ 'b} to information kept with inner
  branch nodes, and parameter @{typ 'c} to the branching type of the
  tree structure.  For our purpose we use the type instance with @{typ
  "att \<times> string"} (representing plain files), @{typ att} (for
  attributes of directory nodes), and @{typ name} (for the index type
  of directory nodes).
*}

type_synonym "file" = "(att \<times> string, att, name) env"

text {*
  \medskip The HOL library also provides @{term lookup} and @{term
  update} operations for general tree structures with the subsequent
  primitive recursive characterizations.

  \medskip
  {\def\isastyleminor{\isastyle}
  \begin{tabular}{l}
  @{term [source] "lookup :: ('a, 'b, 'c) env \<Rightarrow> 'c list \<Rightarrow> ('a, 'b, 'c) env option"} \\
  @{term [source]
  "update :: 'c list \<Rightarrow> ('a, 'b, 'c) env option \<Rightarrow> ('a, 'b, 'c) env \<Rightarrow> ('a, 'b, 'c) env"} \\
  \end{tabular}}

  @{thm [display, indent = 2, eta_contract = false] lookup_eq [no_vars]}
  @{thm [display, indent = 2, eta_contract = false] update_eq [no_vars]}

  Several further properties of these operations are proven in
  \cite{Bauer-et-al:2002:HOL-Library}.  These will be routinely used
  later on without further notice.

  \bigskip Apparently, the elements of type @{typ "file"} contain an
  @{typ att} component in either case.  We now define a few auxiliary
  operations to manipulate this field uniformly, following the
  conventions for record types in Isabelle/HOL
  \cite{Nipkow-et-al:2000:HOL}.
*}

definition
  "attributes file =
    (case file of
      Val (att, text) \<Rightarrow> att
    | Env att dir \<Rightarrow> att)"

definition
  "map_attributes f file =
    (case file of
      Val (att, text) \<Rightarrow> Val (f att, text)
    | Env att dir \<Rightarrow> Env (f att) dir)"

lemma [simp]: "attributes (Val (att, text)) = att"
  by (simp add: attributes_def)

lemma [simp]: "attributes (Env att dir) = att"
  by (simp add: attributes_def)

lemma [simp]: "attributes (map_attributes f file) = f (attributes file)"
  by (cases "file") (simp_all add: attributes_def map_attributes_def
    split_tupled_all)

lemma [simp]: "map_attributes f (Val (att, text)) = Val (f att, text)"
  by (simp add: map_attributes_def)

lemma [simp]: "map_attributes f (Env att dir) = Env (f att) dir"
  by (simp add: map_attributes_def)


subsection {* Initial file-systems *}

text {*
  Given a set of \emph{known users} a file-system shall be initialized
  by providing an empty home directory for each user, with read-only
  access for everyone else.  (Note that we may directly use the user
  id as home directory name, since both types have been identified.)
  Certainly, the very root directory is owned by the super user (who
  has user id 0).
*}

definition
  "init users =
    Env \<lparr>owner = 0, others = {Readable}\<rparr>
      (\<lambda>u. if u \<in> users then Some (Env \<lparr>owner = u, others = {Readable}\<rparr> empty)
        else None)"


subsection {* Accessing file-systems *}

text {*
  The main internal file-system operation is access of a file by a
  user, requesting a certain set of permissions.  The resulting @{typ
  "file option"} indicates if a file had been present at the
  corresponding @{typ path} and if access was granted according to the
  permissions recorded within the file-system.

  Note that by the rules of Unix file-system security (e.g.\
  \cite{Tanenbaum:1992}) both the super-user and owner may always
  access a file unconditionally (in our simplified model).
*}

definition
  "access root path uid perms =
    (case lookup root path of
      None \<Rightarrow> None
    | Some file \<Rightarrow>
        if uid = 0
          \<or> uid = owner (attributes file)
          \<or> perms \<subseteq> others (attributes file)
        then Some file
        else None)"

text {*
  \medskip Successful access to a certain file is the main
  prerequisite for system-calls to be applicable (cf.\
  \secref{sec:unix-trans}).  Any modification of the file-system is
  then performed using the basic @{term update} operation.

  \medskip We see that @{term access} is just a wrapper for the basic
  @{term lookup} function, with additional checking of
  attributes. Subsequently we establish a few auxiliary facts that
  stem from the primitive @{term lookup} used within @{term access}.
*}

lemma access_empty_lookup: "access root path uid {} = lookup root path"
  by (simp add: access_def split: option.splits)

lemma access_some_lookup:
  "access root path uid perms = Some file \<Longrightarrow>
    lookup root path = Some file"
  by (simp add: access_def split: option.splits if_splits)

lemma access_update_other:
  assumes parallel: "path' \<parallel> path"
  shows "access (update path' opt root) path uid perms = access root path uid perms"
proof -
  from parallel obtain y z xs ys zs where
      "y \<noteq> z" and "path' = xs @ y # ys" and "path = xs @ z # zs"
    by (blast dest: parallel_decomp)
  then have "lookup (update path' opt root) path = lookup root path"
    by (blast intro: lookup_update_other)
  then show ?thesis by (simp only: access_def)
qed


section {* File-system transitions \label{sec:unix-trans} *}

subsection {* Unix system calls \label{sec:unix-syscall} *}

text {*
  According to established operating system design (cf.\
  \cite{Tanenbaum:1992}) user space processes may only initiate system
  operations by a fixed set of \emph{system-calls}.  This enables the
  kernel to enforce certain security policies in the first
  place.\footnote{Incidently, this is the very same principle employed
  by any ``LCF-style'' theorem proving system according to Milner's
  principle of ``correctness by construction'', such as Isabelle/HOL
  itself.}

  \medskip In our model of Unix we give a fixed datatype @{text
  operation} for the syntax of system-calls, together with an
  inductive definition of file-system state transitions of the form
  @{text "root \<midarrow>x\<rightarrow> root'"} for the operational semantics.
*}

datatype operation =
    Read uid string path
  | Write uid string path
  | Chmod uid perms path
  | Creat uid perms path
  | Unlink uid path
  | Mkdir uid perms path
  | Rmdir uid path
  | Readdir uid "name set" path

text {*
  The @{typ uid} field of an operation corresponds to the
  \emph{effective user id} of the underlying process, although our
  model never mentions processes explicitly.  The other parameters are
  provided as arguments by the caller; the @{term path} one is common
  to all kinds of system-calls.
*}

primrec uid_of :: "operation \<Rightarrow> uid"
where
    "uid_of (Read uid text path) = uid"
  | "uid_of (Write uid text path) = uid"
  | "uid_of (Chmod uid perms path) = uid"
  | "uid_of (Creat uid perms path) = uid"
  | "uid_of (Unlink uid path) = uid"
  | "uid_of (Mkdir uid path perms) = uid"
  | "uid_of (Rmdir uid path) = uid"
  | "uid_of (Readdir uid names path) = uid"

primrec path_of :: "operation \<Rightarrow> path"
where
    "path_of (Read uid text path) = path"
  | "path_of (Write uid text path) = path"
  | "path_of (Chmod uid perms path) = path"
  | "path_of (Creat uid perms path) = path"
  | "path_of (Unlink uid path) = path"
  | "path_of (Mkdir uid perms path) = path"
  | "path_of (Rmdir uid path) = path"
  | "path_of (Readdir uid names path) = path"

text {*
  \medskip Note that we have omitted explicit @{text Open} and @{text
  Close} operations, pretending that @{term Read} and @{term Write}
  would already take care of this behind the scenes.  Thus we have
  basically treated actual sequences of real system-calls @{text
  "open"}--@{text read}/@{text write}--@{text close} as atomic.

  In principle, this could make big a difference in a model with
  explicit concurrent processes.  On the other hand, even on a real
  Unix system the exact scheduling of concurrent @{text "open"} and
  @{text close} operations does \emph{not} directly affect the success
  of corresponding @{text read} or @{text write}.  Unix allows several
  processes to have files opened at the same time, even for writing!
  Certainly, the result from reading the contents later may be hard to
  predict, but the system-calls involved here will succeed in any
  case.

  \bigskip The operational semantics of system calls is now specified
  via transitions of the file-system configuration.  This is expressed
  as an inductive relation (although there is no actual recursion
  involved here).
*}

inductive transition :: "file \<Rightarrow> operation \<Rightarrow> file \<Rightarrow> bool"
  ("_ \<midarrow>_\<rightarrow> _" [90, 1000, 90] 100)
where
  read:
    "access root path uid {Readable} = Some (Val (att, text)) \<Longrightarrow>
      root \<midarrow>(Read uid text path)\<rightarrow> root" |
  "write":
    "access root path uid {Writable} = Some (Val (att, text')) \<Longrightarrow>
      root \<midarrow>(Write uid text path)\<rightarrow> update path (Some (Val (att, text))) root" |

  chmod:
    "access root path uid {} = Some file \<Longrightarrow>
      uid = 0 \<or> uid = owner (attributes file) \<Longrightarrow>
      root \<midarrow>(Chmod uid perms path)\<rightarrow> update path
        (Some (map_attributes (others_update (\<lambda>_. perms)) file)) root" |

  creat:
    "path = parent_path @ [name] \<Longrightarrow>
      access root parent_path uid {Writable} = Some (Env att parent) \<Longrightarrow>
      access root path uid {} = None \<Longrightarrow>
      root \<midarrow>(Creat uid perms path)\<rightarrow> update path
        (Some (Val (\<lparr>owner = uid, others = perms\<rparr>, []))) root" |
  unlink:
    "path = parent_path @ [name] \<Longrightarrow>
      access root parent_path uid {Writable} = Some (Env att parent) \<Longrightarrow>
      access root path uid {} = Some (Val plain) \<Longrightarrow>
      root \<midarrow>(Unlink uid path)\<rightarrow> update path None root" |

  mkdir:
    "path = parent_path @ [name] \<Longrightarrow>
      access root parent_path uid {Writable} = Some (Env att parent) \<Longrightarrow>
      access root path uid {} = None \<Longrightarrow>
      root \<midarrow>(Mkdir uid perms path)\<rightarrow> update path
        (Some (Env \<lparr>owner = uid, others = perms\<rparr> empty)) root" |
  rmdir:
    "path = parent_path @ [name] \<Longrightarrow>
      access root parent_path uid {Writable} = Some (Env att parent) \<Longrightarrow>
      access root path uid {} = Some (Env att' empty) \<Longrightarrow>
      root \<midarrow>(Rmdir uid path)\<rightarrow> update path None root" |

  readdir:
    "access root path uid {Readable} = Some (Env att dir) \<Longrightarrow>
      names = dom dir \<Longrightarrow>
      root \<midarrow>(Readdir uid names path)\<rightarrow> root"

text {*
  \medskip Certainly, the above specification is central to the whole
  formal development.  Any of the results to be established later on
  are only meaningful to the outside world if this transition system
  provides an adequate model of real Unix systems.  This kind of
  ``reality-check'' of a formal model is the well-known problem of
  \emph{validation}.

  If in doubt, one may consider to compare our definition with the
  informal specifications given the corresponding Unix man pages, or
  even peek at an actual implementation such as
  \cite{Torvalds-et-al:Linux}.  Another common way to gain confidence
  into the formal model is to run simple simulations (see
  \secref{sec:unix-examples}), and check the results with that of
  experiments performed on a real Unix system.
*}


subsection {* Basic properties of single transitions \label{sec:unix-single-trans} *}

text {*
  The transition system @{text "root \<midarrow>x\<rightarrow> root'"} defined above
  determines a unique result @{term root'} from given @{term root} and
  @{term x} (this is holds rather trivially, since there is even only
  one clause for each operation).  This uniqueness statement will
  simplify our subsequent development to some extent, since we only
  have to reason about a partial function rather than a general
  relation.
*}

theorem transition_uniq:
  assumes root': "root \<midarrow>x\<rightarrow> root'"
    and root'': "root \<midarrow>x\<rightarrow> root''"
  shows "root' = root''"
  using root''
proof cases
  case read
  with root' show ?thesis by cases auto
next
  case "write"
  with root' show ?thesis by cases auto
next
  case chmod
  with root' show ?thesis by cases auto
next
  case creat
  with root' show ?thesis by cases auto
next
  case unlink
  with root' show ?thesis by cases auto
next
  case mkdir
  with root' show ?thesis by cases auto
next
  case rmdir
  with root' show ?thesis by cases auto
next
  case readdir
  with root' show ?thesis by cases blast+
qed

text {*
  \medskip Apparently, file-system transitions are \emph{type-safe} in
  the sense that the result of transforming an actual directory yields
  again a directory.
*}

theorem transition_type_safe:
  assumes tr: "root \<midarrow>x\<rightarrow> root'"
    and inv: "\<exists>att dir. root = Env att dir"
  shows "\<exists>att dir. root' = Env att dir"
proof (cases "path_of x")
  case Nil
  with tr inv show ?thesis
    by cases (auto simp add: access_def split: if_splits)
next
  case Cons
  from tr obtain opt where
      "root' = root \<or> root' = update (path_of x) opt root"
    by cases auto
  with inv Cons show ?thesis
    by (auto simp add: update_eq split: list.splits)
qed

text {*
  The previous result may be seen as the most basic invariant on the
  file-system state that is enforced by any proper kernel
  implementation.  So user processes --- being bound to the
  system-call interface --- may never mess up a file-system such that
  the root becomes a plain file instead of a directory, which would be
  a strange situation indeed.
*}


subsection {* Iterated transitions *}

text {*
  Iterated system transitions via finite sequences of system
  operations are modeled inductively as follows.  In a sense, this
  relation describes the cumulative effect of the sequence of
  system-calls issued by a number of running processes over a finite
  amount of time.
*}

inductive transitions :: "file \<Rightarrow> operation list \<Rightarrow> file \<Rightarrow> bool"
  ("_ =_\<Rightarrow> _" [90, 1000, 90] 100)
where
    nil: "root =[]\<Rightarrow> root"
  | cons: "root \<midarrow>x\<rightarrow> root' \<Longrightarrow> root' =xs\<Rightarrow> root'' \<Longrightarrow> root =(x # xs)\<Rightarrow> root''"

text {*
  \medskip We establish a few basic facts relating iterated
  transitions with single ones, according to the recursive structure
  of lists.
*}

lemma transitions_nil_eq: "root =[]\<Rightarrow> root' = (root = root')"
proof
  assume "root =[]\<Rightarrow> root'"
  then show "root = root'" by cases simp_all
next
  assume "root = root'"
  then show "root =[]\<Rightarrow> root'" by (simp only: transitions.nil)
qed

lemma transitions_cons_eq:
  "root =(x # xs)\<Rightarrow> root'' = (\<exists>root'. root \<midarrow>x\<rightarrow> root' \<and> root' =xs\<Rightarrow> root'')"
proof
  assume "root =(x # xs)\<Rightarrow> root''"
  then show "\<exists>root'. root \<midarrow>x\<rightarrow> root' \<and> root' =xs\<Rightarrow> root''"
    by cases auto
next
  assume "\<exists>root'. root \<midarrow>x\<rightarrow> root' \<and> root' =xs\<Rightarrow> root''"
  then show "root =(x # xs)\<Rightarrow> root''"
    by (blast intro: transitions.cons)
qed

text {*
  The next two rules show how to ``destruct'' known transition
  sequences.  Note that the second one actually relies on the
  uniqueness property of the basic transition system (see
  \secref{sec:unix-single-trans}).
*}

lemma transitions_nilD: "root =[]\<Rightarrow> root' \<Longrightarrow> root' = root"
  by (simp add: transitions_nil_eq)

lemma transitions_consD:
  assumes list: "root =(x # xs)\<Rightarrow> root''"
    and hd: "root \<midarrow>x\<rightarrow> root'"
  shows "root' =xs\<Rightarrow> root''"
proof -
  from list obtain r' where r': "root \<midarrow>x\<rightarrow> r'" and root'': "r' =xs\<Rightarrow> root''"
    by cases simp_all
  from r' hd have "r' = root'" by (rule transition_uniq)
  with root'' show "root' =xs\<Rightarrow> root''" by simp
qed

text {*
  \medskip The following fact shows how an invariant @{term Q} of
  single transitions with property @{term P} may be transferred to
  iterated transitions.  The proof is rather obvious by rule induction
  over the definition of @{term "root =xs\<Rightarrow> root'"}.
*}

lemma transitions_invariant:
  assumes r: "\<And>r x r'. r \<midarrow>x\<rightarrow> r' \<Longrightarrow> Q r \<Longrightarrow> P x \<Longrightarrow> Q r'"
    and trans: "root =xs\<Rightarrow> root'"
  shows "Q root \<Longrightarrow> \<forall>x \<in> set xs. P x \<Longrightarrow> Q root'"
  using trans
proof induct
  case nil
  show ?case by (rule nil.prems)
next
  case (cons root x root' xs root'')
  note P = `\<forall>x \<in> set (x # xs). P x`
  then have "P x" by simp
  with `root \<midarrow>x\<rightarrow> root'` and `Q root` have Q': "Q root'" by (rule r)
  from P have "\<forall>x \<in> set xs. P x" by simp
  with Q' show "Q root''" by (rule cons.hyps)
qed

text {*
  As an example of applying the previous result, we transfer the basic
  type-safety property (see \secref{sec:unix-single-trans}) from
  single transitions to iterated ones, which is a rather obvious
  result indeed.
*}

theorem transitions_type_safe:
  assumes "root =xs\<Rightarrow> root'"
    and "\<exists>att dir. root = Env att dir"
  shows "\<exists>att dir. root' = Env att dir"
  using transition_type_safe and assms
proof (rule transitions_invariant)
  show "\<forall>x \<in> set xs. True" by blast
qed


section {* Executable sequences *}

text {*
  An inductively defined relation such as the one of @{text "root \<midarrow>x\<rightarrow>
  root'"} (see \secref{sec:unix-syscall}) has two main aspects.  First
  of all, the resulting system admits a certain set of transition
  rules (introductions) as given in the specification.  Furthermore,
  there is an explicit least-fixed-point construction involved, which
  results in induction (and case-analysis) rules to eliminate known
  transitions in an exhaustive manner.

  \medskip Subsequently, we explore our transition system in an
  experimental style, mainly using the introduction rules with basic
  algebraic properties of the underlying structures.  The technique
  closely resembles that of Prolog combined with functional evaluation
  in a very simple manner.

  Just as the ``closed-world assumption'' is left implicit in Prolog,
  we do not refer to induction over the whole transition system here.
  So this is still purely positive reasoning about possible
  executions; exhaustive reasoning will be employed only later on (see
  \secref{sec:unix-bogosity}), when we shall demonstrate that certain
  behavior is \emph{not} possible.
*}


subsection {* Possible transitions *}

text {*
  Rather obviously, a list of system operations can be executed within
  a certain state if there is a result state reached by an iterated
  transition.
*}

definition "can_exec root xs = (\<exists>root'. root =xs\<Rightarrow> root')"

lemma can_exec_nil: "can_exec root []"
  unfolding can_exec_def by (blast intro: transitions.intros)

lemma can_exec_cons:
    "root \<midarrow>x\<rightarrow> root' \<Longrightarrow> can_exec root' xs \<Longrightarrow> can_exec root (x # xs)"
  unfolding can_exec_def by (blast intro: transitions.intros)

text {*
  \medskip In case that we already know that a certain sequence can be
  executed we may destruct it backwardly into individual transitions.
*}

lemma can_exec_snocD: "can_exec root (xs @ [y])
    \<Longrightarrow> \<exists>root' root''. root =xs\<Rightarrow> root' \<and> root' \<midarrow>y\<rightarrow> root''"
proof (induct xs arbitrary: root)
  case Nil
  then show ?case
    by (simp add: can_exec_def transitions_nil_eq transitions_cons_eq)
next
  case (Cons x xs)
  from `can_exec root ((x # xs) @ [y])` obtain r root'' where
      x: "root \<midarrow>x\<rightarrow> r" and
      xs_y: "r =(xs @ [y])\<Rightarrow> root''"
    by (auto simp add: can_exec_def transitions_nil_eq transitions_cons_eq)
  from xs_y Cons.hyps obtain root' r' where xs: "r =xs\<Rightarrow> root'" and y: "root' \<midarrow>y\<rightarrow> r'"
    unfolding can_exec_def by blast
  from x xs have "root =(x # xs)\<Rightarrow> root'"
    by (rule transitions.cons)
  with y show ?case by blast
qed


subsection {* Example executions \label{sec:unix-examples} *}

text {*
  We are now ready to perform a few experiments within our formal
  model of Unix system-calls.  The common technique is to alternate
  introduction rules of the transition system (see
  \secref{sec:unix-trans}), and steps to solve any emerging side
  conditions using algebraic properties of the underlying file-system
  structures (see \secref{sec:unix-file-system}).
*}

lemmas eval = access_def init_def

theorem "u \<in> users \<Longrightarrow> can_exec (init users)
    [Mkdir u perms [u, name]]"
  apply (rule can_exec_cons)
    -- {* back-chain @{term can_exec} (of @{term [source] Cons}) *}
  apply (rule mkdir)
    -- {* back-chain @{term Mkdir} *}
  apply (force simp add: eval)+
    -- {* solve preconditions of @{term Mkdir} *}
  apply (simp add: eval)
    -- {* peek at resulting dir (optional) *}
  txt {* @{subgoals [display]} *}
  apply (rule can_exec_nil)
    -- {* back-chain @{term can_exec} (of @{term [source] Nil}) *}
  done

text {*
  By inspecting the result shown just before the final step above, we
  may gain confidence that our specification of Unix system-calls
  actually makes sense.  Further common errors are usually exhibited
  when preconditions of transition rules fail unexpectedly.

  \medskip Here are a few further experiments, using the same
  techniques as before.
*}

theorem "u \<in> users \<Longrightarrow> can_exec (init users)
   [Creat u perms [u, name],
    Unlink u [u, name]]"
  apply (rule can_exec_cons)
  apply (rule creat)
  apply (force simp add: eval)+
  apply (simp add: eval)
  apply (rule can_exec_cons)
  apply (rule unlink)
  apply (force simp add: eval)+
  apply (simp add: eval)
  txt {* peek at result: @{subgoals [display]} *}
  apply (rule can_exec_nil)
  done

theorem "u \<in> users \<Longrightarrow> Writable \<in> perms\<^isub>1 \<Longrightarrow>
  Readable \<in> perms\<^isub>2 \<Longrightarrow> name\<^isub>3 \<noteq> name\<^isub>4 \<Longrightarrow>
  can_exec (init users)
   [Mkdir u perms\<^isub>1 [u, name\<^isub>1],
    Mkdir u' perms\<^isub>2 [u, name\<^isub>1, name\<^isub>2],
    Creat u' perms\<^isub>3 [u, name\<^isub>1, name\<^isub>2, name\<^isub>3],
    Creat u' perms\<^isub>3 [u, name\<^isub>1, name\<^isub>2, name\<^isub>4],
    Readdir u {name\<^isub>3, name\<^isub>4} [u, name\<^isub>1, name\<^isub>2]]"
  apply (rule can_exec_cons, rule transition.intros,
    (force simp add: eval)+, (simp add: eval)?)+
  txt {* peek at result: @{subgoals [display]} *}
  apply (rule can_exec_nil)
  done

theorem "u \<in> users \<Longrightarrow> Writable \<in> perms\<^isub>1 \<Longrightarrow> Readable \<in> perms\<^isub>3 \<Longrightarrow>
  can_exec (init users)
   [Mkdir u perms\<^isub>1 [u, name\<^isub>1],
    Mkdir u' perms\<^isub>2 [u, name\<^isub>1, name\<^isub>2],
    Creat u' perms\<^isub>3 [u, name\<^isub>1, name\<^isub>2, name\<^isub>3],
    Write u' ''foo'' [u, name\<^isub>1, name\<^isub>2, name\<^isub>3],
    Read u ''foo'' [u, name\<^isub>1, name\<^isub>2, name\<^isub>3]]"
  apply (rule can_exec_cons, rule transition.intros,
    (force simp add: eval)+, (simp add: eval)?)+
  txt {* peek at result: @{subgoals [display]} *}
  apply (rule can_exec_nil)
  done


section {* Odd effects --- treated formally \label{sec:unix-bogosity} *}

text {*
  We are now ready to give a completely formal treatment of the
  slightly odd situation discussed in the introduction (see
  \secref{sec:unix-intro}): the file-system can easily reach a state
  where a user is unable to remove his very own directory, because it
  is still populated by items placed there by another user in an
  uncouth manner.
*}

subsection {* The general procedure \label{sec:unix-inv-procedure} *}

text {*
  The following theorem expresses the general procedure we are
  following to achieve the main result.
*}

theorem general_procedure:
  assumes cannot_y: "\<And>r r'. Q r \<Longrightarrow> r \<midarrow>y\<rightarrow> r' \<Longrightarrow> False"
    and init_inv: "\<And>root. init users =bs\<Rightarrow> root \<Longrightarrow> Q root"
    and preserve_inv: "\<And>r x r'. r \<midarrow>x\<rightarrow> r' \<Longrightarrow> Q r \<Longrightarrow> P x \<Longrightarrow> Q r'"
    and init_result: "init users =bs\<Rightarrow> root"
  shows "\<not> (\<exists>xs. (\<forall>x \<in> set xs. P x) \<and> can_exec root (xs @ [y]))"
proof -
  {
    fix xs
    assume Ps: "\<forall>x \<in> set xs. P x"
    assume can_exec: "can_exec root (xs @ [y])"
    then obtain root' root'' where
        xs: "root =xs\<Rightarrow> root'" and y: "root' \<midarrow>y\<rightarrow> root''"
      by (blast dest: can_exec_snocD)
    from init_result have "Q root" by (rule init_inv)
    from preserve_inv xs this Ps have "Q root'"
      by (rule transitions_invariant)
    from this y have False by (rule cannot_y)
  }
  then show ?thesis by blast
qed

text {*
  Here @{prop "P x"} refers to the restriction on file-system
  operations that are admitted after having reached the critical
  configuration; according to the problem specification this will
  become @{prop "uid_of x = user\<^isub>1"} later on.  Furthermore,
  @{term y} refers to the operations we claim to be impossible to
  perform afterwards, we will take @{term Rmdir} later.  Moreover
  @{term Q} is a suitable (auxiliary) invariant over the file-system;
  choosing @{term Q} adequately is very important to make the proof
  work (see \secref{sec:unix-inv-lemmas}).
*}


subsection {* The particular situation *}

text {*
  We introduce a few global declarations and axioms to describe our
  particular situation considered here.  Thus we avoid excessive use
  of local parameters in the subsequent development.
*}

locale situation =
  fixes users :: "uid set"
    and user\<^isub>1 :: uid
    and user\<^isub>2 :: uid
    and name\<^isub>1 :: name
    and name\<^isub>2 :: name
    and name\<^isub>3 :: name
    and perms\<^isub>1 :: perms
    and perms\<^isub>2 :: perms
  assumes user\<^isub>1_known: "user\<^isub>1 \<in> users"
    and user\<^isub>1_not_root: "user\<^isub>1 \<noteq> 0"
    and users_neq: "user\<^isub>1 \<noteq> user\<^isub>2"
    and perms\<^isub>1_writable: "Writable \<in> perms\<^isub>1"
    and perms\<^isub>2_not_writable: "Writable \<notin> perms\<^isub>2"
  notes facts = user\<^isub>1_known user\<^isub>1_not_root users_neq
    perms\<^isub>1_writable perms\<^isub>2_not_writable
begin

definition
  "bogus =
     [Mkdir user\<^isub>1 perms\<^isub>1 [user\<^isub>1, name\<^isub>1],
      Mkdir user\<^isub>2 perms\<^isub>2 [user\<^isub>1, name\<^isub>1, name\<^isub>2],
      Creat user\<^isub>2 perms\<^isub>2 [user\<^isub>1, name\<^isub>1, name\<^isub>2, name\<^isub>3]]"
definition
  "bogus_path = [user\<^isub>1, name\<^isub>1, name\<^isub>2]"

text {*
  The @{term bogus} operations are the ones that lead into the uncouth
  situation; @{term bogus_path} is the key position within the
  file-system where things go awry.
*}


subsection {* Invariance lemmas \label{sec:unix-inv-lemmas} *}

text {*
  The following invariant over the root file-system describes the
  bogus situation in an abstract manner: located at a certain @{term
  path} within the file-system is a non-empty directory that is
  neither owned nor writable by @{term user\<^isub>1}.
*}



definition
  "invariant root path =
    (\<exists>att dir.
      access root path user\<^isub>1 {} = Some (Env att dir) \<and> dir \<noteq> empty \<and>
      user\<^isub>1 \<noteq> owner att \<and>
      access root path user\<^isub>1 {Writable} = None)"

text {*
  Following the general procedure (see
  \secref{sec:unix-inv-procedure}) we will now establish the three key
  lemmas required to yield the final result.

  \begin{enumerate}

  \item The invariant is sufficiently strong to entail the
  pathological case that @{term user\<^isub>1} is unable to remove the
  (owned) directory at @{term "[user\<^isub>1, name\<^isub>1]"}.

  \item The invariant does hold after having executed the @{term
  bogus} list of operations (starting with an initial file-system
  configuration).

  \item The invariant is preserved by any file-system operation
  performed by @{term user\<^isub>1} alone, without any help by other
  users.

  \end{enumerate}

  As the invariant appears both as assumptions and conclusions in the
  course of proof, its formulation is rather critical for the whole
  development to work out properly.  In particular, the third step is
  very sensitive to the invariant being either too strong or too weak.
  Moreover the invariant has to be sufficiently abstract, lest the
  proof become cluttered by confusing detail.

  \medskip The first two lemmas are technically straight forward ---
  we just have to inspect rather special cases.
*}

lemma cannot_rmdir:
  assumes inv: "invariant root bogus_path"
    and rmdir: "root \<midarrow>(Rmdir user\<^isub>1 [user\<^isub>1, name\<^isub>1])\<rightarrow> root'"
  shows False
proof -
  from inv obtain "file" where "access root bogus_path user\<^isub>1 {} = Some file"
    unfolding invariant_def by blast
  moreover
  from rmdir obtain att where
      "access root [user\<^isub>1, name\<^isub>1] user\<^isub>1 {} = Some (Env att empty)"
    by cases auto
  then have "access root ([user\<^isub>1, name\<^isub>1] @ [name\<^isub>2]) user\<^isub>1 {} = empty name\<^isub>2"
    by (simp only: access_empty_lookup lookup_append_some) simp
  ultimately show False by (simp add: bogus_path_def)
qed

lemma
  assumes init: "init users =bogus\<Rightarrow> root"
  notes eval = facts access_def init_def
  shows init_invariant: "invariant root bogus_path"
  using init
  apply (unfold bogus_def bogus_path_def)
  apply (drule transitions_consD, rule transition.intros,
      (force simp add: eval)+, (simp add: eval)?)+
    -- "evaluate all operations"
  apply (drule transitions_nilD)
    -- "reach final result"
  apply (simp add: invariant_def eval)
    -- "check the invariant"
  done

text {*
  \medskip At last we are left with the main effort to show that the
  ``bogosity'' invariant is preserved by any file-system operation
  performed by @{term user\<^isub>1} alone.  Note that this holds for
  any @{term path} given, the particular @{term bogus_path} is not
  required here.
*}

lemma preserve_invariant:
  assumes tr: "root \<midarrow>x\<rightarrow> root'"
    and inv: "invariant root path"
    and uid: "uid_of x = user\<^isub>1"
  shows "invariant root' path"
proof -
  from inv obtain att dir where
      inv1: "access root path user\<^isub>1 {} = Some (Env att dir)" and
      inv2: "dir \<noteq> empty" and
      inv3: "user\<^isub>1 \<noteq> owner att" and
      inv4: "access root path user\<^isub>1 {Writable} = None"
    by (auto simp add: invariant_def)

  from inv1 have lookup: "lookup root path = Some (Env att dir)"
    by (simp only: access_empty_lookup)

  from inv1 inv3 inv4 and user\<^isub>1_not_root
  have not_writable: "Writable \<notin> others att"
    by (auto simp add: access_def split: option.splits)

  show ?thesis
  proof cases
    assume "root' = root"
    with inv show "invariant root' path" by (simp only:)
  next
    assume changed: "root' \<noteq> root"
    with tr obtain opt where root': "root' = update (path_of x) opt root"
      by cases auto
    show ?thesis
    proof (rule prefix_cases)
      assume "path_of x \<parallel> path"
      with inv root'
      have "\<And>perms. access root' path user\<^isub>1 perms = access root path user\<^isub>1 perms"
        by (simp only: access_update_other)
      with inv show "invariant root' path"
        by (simp only: invariant_def)
    next
      assume "path_of x \<le> path"
      then obtain ys where path: "path = path_of x @ ys" ..

      show ?thesis
      proof (cases ys)
        assume "ys = []"
        with tr uid inv2 inv3 lookup changed path and user\<^isub>1_not_root
        have False
          by cases (auto simp add: access_empty_lookup dest: access_some_lookup)
        then show ?thesis ..
      next
        fix z zs assume ys: "ys = z # zs"
        have "lookup root' path = lookup root path"
        proof -
          from inv2 lookup path ys
          have look: "lookup root (path_of x @ z # zs) = Some (Env att dir)"
            by (simp only:)
          then obtain att' dir' file' where
              look': "lookup root (path_of x) = Some (Env att' dir')" and
              dir': "dir' z = Some file'" and
              file': "lookup file' zs = Some (Env att dir)"
            by (blast dest: lookup_some_upper)

          from tr uid changed look' dir' obtain att'' where
              look'': "lookup root' (path_of x) = Some (Env att'' dir')"
            by cases (auto simp add: access_empty_lookup lookup_update_some
              dest: access_some_lookup)
          with dir' file' have "lookup root' (path_of x @ z # zs) =
              Some (Env att dir)"
            by (simp add: lookup_append_some)
          with look path ys show ?thesis
            by simp
        qed
        with inv show "invariant root' path"
          by (simp only: invariant_def access_def)
      qed
    next
      assume "path < path_of x"
      then obtain y ys where path: "path_of x = path @ y # ys" ..

      obtain dir' where
        lookup': "lookup root' path = Some (Env att dir')" and
        inv2': "dir' \<noteq> empty"
      proof (cases ys)
        assume "ys = []"
        with path have parent: "path_of x = path @ [y]" by simp
        with tr uid inv4 changed obtain "file" where
            "root' = update (path_of x) (Some file) root"
          by cases auto
        with lookup parent have "lookup root' path = Some (Env att (dir(y\<mapsto>file)))"
          by (simp only: update_append_some update_cons_nil_env)
        moreover have "dir(y\<mapsto>file) \<noteq> empty" by simp
        ultimately show ?thesis ..
      next
        fix z zs assume ys: "ys = z # zs"
        with lookup root' path
        have "lookup root' path = Some (update (y # ys) opt (Env att dir))"
          by (simp only: update_append_some)
        also obtain file' where
          "update (y # ys) opt (Env att dir) = Env att (dir(y\<mapsto>file'))"
        proof -
          have "dir y \<noteq> None"
          proof -
            have "dir y = lookup (Env att dir) [y]"
              by (simp split: option.splits)
            also from lookup have "\<dots> = lookup root (path @ [y])"
              by (simp only: lookup_append_some)
            also have "\<dots> \<noteq> None"
            proof -
              from ys obtain us u where rev_ys: "ys = us @ [u]"
                by (cases ys rule: rev_cases) simp
              with tr path
              have "lookup root ((path @ [y]) @ (us @ [u])) \<noteq> None \<or>
                  lookup root ((path @ [y]) @ us) \<noteq> None"
                by cases (auto dest: access_some_lookup)
              then show ?thesis 
                by (fastforce dest!: lookup_some_append)
            qed
            finally show ?thesis .
          qed
          with ys show ?thesis using that by auto
        qed
        also have "dir(y\<mapsto>file') \<noteq> empty" by simp
        ultimately show ?thesis ..
      qed

      from lookup' have inv1': "access root' path user\<^isub>1 {} = Some (Env att dir')"
        by (simp only: access_empty_lookup)

      from inv3 lookup' and not_writable user\<^isub>1_not_root
      have "access root' path user\<^isub>1 {Writable} = None"
        by (simp add: access_def)
      with inv1' inv2' inv3 show ?thesis unfolding invariant_def by blast
    qed
  qed
qed


subsection {* Putting it all together \label{sec:unix-main-result} *}

text {*
  The main result is now imminent, just by composing the three
  invariance lemmas (see \secref{sec:unix-inv-lemmas}) according the the
  overall procedure (see \secref{sec:unix-inv-procedure}).
*}

corollary
  assumes bogus: "init users =bogus\<Rightarrow> root"
  shows "\<not> (\<exists>xs. (\<forall>x \<in> set xs. uid_of x = user\<^isub>1) \<and>
    can_exec root (xs @ [Rmdir user\<^isub>1 [user\<^isub>1, name\<^isub>1]]))"
proof -
  from cannot_rmdir init_invariant preserve_invariant
    and bogus show ?thesis by (rule general_procedure)
qed

end

end
