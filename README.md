Cosa
=====

A thing about Coq-verified Shape Analysis

### Licence ###

Cosa and all of its files are distributed under the CeCILL v2.1 licence. It is a licence in the spirit of Gnu's GPL maintained by three French academic institutes. See the `LICENCE` file for details.

Xisa
----

Cosa is a Coq-verified implementation of (part of) the Xisa abstract interpretation based shape analysis by Bor-Yuh Evan Chang and Xavier Rival.

### Principles ###

Xisa (and Cosa) is an abstract domain construction which transforms a value analysis into a shape analysis. The unbounded regions of memory are represented as inductive shapes. Xisa is parametrised by the set of inductive shapes it can use to represent regions.

Xisa also has a built-in notion of inductive segments. Basically they are inductive shapes with one hole. Segments are inductive shapes which can be derived from the version without hole. However, Cosa has no notion of syntax of inductive shapes at this point, so segments are hand-coded.

### Papers ###

References to the relevant Xisa papers:

* [_Relational inductive shape analysis_](http://dl.acm.org/citation.cfm?id=1328469), Bor-Yuh Evan Chang & Xavier Rival.
* [_Abstract Domains for the Analysis of Programs Manipulating Complex Data-Structures_](http://www.di.ens.fr/~rival/hdr.pdf), Xavier Rival, Habilitation Thesis.


Design
------

On the concrete side, Cosa uses [Compcert](http://compcert.inria.fr/). The code is meant to interface with the value analysis described [here](http://link.springer.com/chapter/10.1007/978-3-642-38856-9_18). As such it will analyse the control-flow graph language which was designed as part of this analysis, and closely corresponds to Compcert's Cminor intermediate language. Currently Cosa doesn't use code from the value analysis (whose up to date version, developed for the [Verasco](http://verasco.imag.fr/wiki/Main_Page) project, hasn't been released yet).

### Interaction structures ###

Xisa is design as rule-sets which can be applied with any strategy. The correctness of the analysis does not depend on the chosen strategy. To represent rule-sets, Cosa uses _Interaction Structures_ introduced by Peter Hancock (see [_Programming interfaces and basic topology_](http://www.sciencedirect.com/science/article/pii/S0168007205000710) by Peter Hancock and Pierre Hyvernat for an overview).

Interaction structures represent processes which involve the interaction of two agents. In the case of Cosa, we can see the agent as the strategy (or _oracle_) and a provider of rules concerned by correctness. Interaction structures support forward refinement — as in [refinement calculus](http://en.wikipedia.org/wiki/Refinement_calculus) — which Arnaud Spiwack noticed is sufficient to encode the abstract interpretation framework in which Xisa is expressed (set [Abstract interpretation as anti-refinement](http://arxiv.org/abs/1310.4283)).

Cosa, being based on a pre-existing design on the concrete side, does not fully leverage the correspondance between abstract interpretation and forward refinement. However, thanks to the correspondence, it is possible to refine interaction structures leading, step-wise, to a realistic analysis. As refinement is going towards the abstract, we must strengthen the pre-conditions and weaken the post-conditions.

Refinement is leveraged, in particular, in the design of inductive types where new names are being generated. In the first step, we just assume that the oracle can provide us with new names. Later we change the type of graphs to include a name of a new node, which we can increase as we go, removing the need for the oracle to traverse the graph to figure a new name ( _work in progress_ ).

Interaction structures can also be used to represent proof systems. We use that property to define a generic notion of certificate that the oracle can provide to help the analysis check the correctness of its choice. Inclusion checking is designed to check a certificate ( _work in progress_ ).

Working with interaction structure is the main structuring choice of Cosa. It allows to describe the interaction with an external oracle in a systematic way, and allows to delay the calls to an actual oracle to a superficial layer completely separated from the correctness proof. The data structures manipulated by the algorithm do not need to be used in the correctness proofs either.

### Nominal sets ###

Summarised edges in a Xisa graph represent inductive shapes. Throughout an analysis they are unfolded (for instance a list at address `α` will be unfolded as the disjunction of `α=0` and `α.0=β`m `α.1=γ` for some value `β` and a list at address `γ`). This procedure of unfolding creates new names.

The correctness property of the concretisation asserts that we can always _fold back_ an edge, thus removing names. Creating new names is not justified directly by the usual properties of abstract interpretation.

To address this issue, Cosa uses a technology based on Andrew Pitts's _nominal sets_ (see [_Nominal Sets_ (course notes)](http://www.cs.nott.ac.uk/~vxc/mgs/MGS2011_nominal_sets.pdf). One way to see Xisa graph, from the point of view of unfolding, is a structure with an infinite amount of implicit binders. Nominal set handle infinite amounts of binders gracefully, which is not the case of other representations of binders.

The basic idea of nominal set is to consider a set of names (a.k.a. _atoms_), and the finite permutations of atoms. Permutations of atoms act on sets as a group. With such an action it is possible to define usual notions like α-equivalence and freshness. But more importantly for Cosa, it comes with a _composable_ notion of functions which do not create names (namely the _equivariant functions_, _i.e._ those functions which preserve the action of the finite permutations of atoms).


Overview
--------

Cosa is currently being developed, it does not provide a full-fledged analysis yet. However, it proves correct a significant proportion of the Xisa domain. Some parts of the development are being rewritten so some of the files will not compile at the moment. Here is a description of the directories and Coq files involved in the proofs:

### Lib ###

In the `Lib` directory, one can find generic types and proofs.

* `Axiom.v` assumes functional and propositional extensionality. It allows the development to be up equivalence of predicates. These axioms are not strictly necessary, but as predicates are ubiquitous in Cosa, including in datastructures, it would be quite a hassle to manipulate predicate equivalence explicitly.
* `Tactics.v` defines various tactics used throughout the development.
* `Extra.v` provides miscellaneous lemmas which could be part of Coq's standard library or Compcert.
* `Bracket.v` defines a squashing operators and properties about _choice_ (in the sense of the axiom of choice)
* `Algebra.v` defines type classes for associativity and commutativity.
* `MapReduce.v` proves properties about `List.fold_left` when the folded function is associative and commutative. It also provides a corresponding map-then-fold operation for `Ptree` (a association structure on positive from Compcert, see the `Map` therein)
* `CompleteLattice.v` defines the complete lattice structure of n-ary predicates.
* `Predicate.v` is essentially a notation layer atop `CompleteLattice.v` for unary predicates.
* `Relation.v` describes how a relation can be lifted to a function on predicates ( _monadic extension_ ).
* `Finite.v` describes (skeletal) finite types as well as there relation to lists. Finite types are in particular instrumental in the design of _generic proof certificates_.

### Interaction ###

In the `Interaction` directory, one can find everything pertaining specifically to interaction structures.

* `Transition.v` defines transition structures, interaction structures which involve a single agent. _They may not be useful in the final design._
* `Interaction.v` defines interaction structures together with their main constructors (such as _sequence_, _product_ and _iteration_).
* `Simulation.v` defines (forward) refinement for interaction structures. This file hinges on a _relation transformer_ whereby two interaction structures act jointly on a relation yielding a _weakest pre-relation_ which necessarily relates initial states in order for the final state to be related through the original (post)-relation. Just like the _weakest pre-condition_ reduces the proof of a Hoare triple to a single inclusion, this relation transformer reduces the proof of forward refinement to a single relation inclusion. The interaction between interaction structure constructors and refinement is, then, expressed in term of the relation transformer, such that the proofs of refinement do not require additional data to destruct constructors.
* `Rule.v` describes the use of interaction structures as rule systems, especially proof systems. The type [Rule.t] defines a specialised version of interaction structures, where the applicability of rules is _decidable_ and rules generate a _finite_ number of subgoals. From such a system, we derive two interaction structures.
    + An interaction structure `deductive` where only the applicable rules can be used, and which is well-suited to show what is proven by the proofs of this rule system.
    + An interaction structure `checker` where using inapplicable rules is permitted by the type checker, but leads to a junk state. It comes with a generic notion of certificate: a regular (non-dependent) datatype which can be read back as a proof of `checker`.
* `InteractionLib.v` describes interaction structures which do not fit in the core files.

### Nominal ###

The `Nominal` directory defines the primitives for the nominal set technology which is used to ensure the correctness of unfolding. Most everything in the `Nominal` directory is defined as type classes.

* `Atom.v` defines the basic properties of nominal atoms and permutations. The most important is the data of a type of finite decidable sets of atoms (which we arrange to be up to equality).
* `Set.v` defines the basic logic of nominal sets. A typeclass `Action` is defined to represent the sets on which finite permutations of atoms act as a group. A typeclass `Nominal` is then defined to represent nominal sets (in addition to the action each element has a (decidable) finite support). This file also defines the notion of equivariant functions (morphisms of the category of nominal sets) and some automatin to infer that a function is, indeed, equivariant.

### Concrete ###

The `Concrete` directory contains objects involved in the description of the concrete domain. The concrete domain being essentially described in Compcert, this directory is pretty small.

* `ConcreteFragment.v` complements the heaps of Compcert with a disjoint composition. This is achieved by adjoining a set of addresses to a heap. Only these addresses are considered to be in the _heap fragment_. Two fragments can then be composed if they have the same underlying heap, and disjoint address sets. This sits well, philosophically, with the idea of the composition of heaps: a fragment is part of a larger heap, of which it knows nothing (this approach is due to Xavier Rival, in unpublished previous works).

### Abstract ###

The `Abstract` directory contains objects involved in the description of the abstract domain but which are not part of the Xisa domain _per se_.

* `Valuation.v` gives helpers to manipulate valuations (functions relating graph nodes to concrete values). In particular, it defines the symmetry property which will be use to prove the correctness of picking fresh names arbitrarily.
* `Lang.v` describes the expressions used by the analysis. `Lang.expr` is essentially the expressions from Compcert's Cminor, except that `Lang.expr` is parametrised by the type of its variables.
* `NumericalDomain.v` defines an abstract type of numerical domain which will be used as an argument for the shape analysis. The type is meant to resemble that of Verasco's value analysis, except that it uses `Lang.expr` as expression whereas Verasco's value analysis has its own brand of expression, which doesn't have a _load_ (pointer dereferencing) expression. In `NumericalDomain.v` the load expression is essentially interpreted as top, though.

### Shape ###

The `Shape` directory contains the heart of Cosa's domain, where most correction proofs are done, but where types are sometimes still idealised.

* `Graph.v` describes the graphs which holds the pure shape part of the analysis. Graphs have point-to edges, which represent a single pointer in the concretisation, and summarised edges, which represent regions. Summaries are purely abstract as far as this file is concerned.
* `Summary.v` is arguably the most central file of Cosa: it describes summarised edges, and in particular, how they are unfolded. In this file, a summary is described by a process (an interaction structure) which takes a set of existing nodes as an input and outputs a pair of a graph and a `Lang.expr`. The idea is that inductive summaries will be given as in Xisa as a list (a finite product) of rules each of which creates some new nodes and yields a pure shape part and a pure numerical part. But in `Summary.v` these details are not touched upon. Given a set of summaries defined each by a (single) process, we can define the concretisation of summaries as a least fixed point (of complete lattice). We can then provide additional unfolding processes for each summary (such as backwards unfolding of segments). Given sufficient properties we show that unfolding a summary is always correct. The intention is that any summary derived from Xisa's schema will verify these assumptions, but at the time there is no generic schema in Cosa, inductive (as well as segments) are hand-coded.
* `ShapeDomainSig.v` gives the type and concretisation for combined domains: graphs with numerical analysis, then with an environment for program variables.
* `Inclusion.v` rules for inclusion checking. _work in progress._
* `ShapeDomain.v` provides the shape abstract domain. The shape abstract domain is given as a function taking dependent records and returning a dependent record (it can be seen as an ocaml functor). At this point, the domain operation are still presented as rule sets (given as interaction structures). _work in progress_

### Analysis ###

The `Analysis` directory is dedicated to turning the abstract domain from the `Shape` directory into an effective analysis.

* `Inductives.v` defines the inductive summaries that can be used for the analysis. _work in progress_


Installing Compcert
-------------------

To browse Cosa with Coq, Compcert's Coq development must be installed. Then you a recent Proof general (from the cvs), which uses the _CoqProject file to pass the appropriate arguments to Coq.

Cosa runs atop Compcert 2.0. As far as we know, there is no installing rules for Coq files in Compcert's Makefile, so here is a procedure to get the file at the right place:

* open a terminal in Compcert's source directory
* run `make proof` to build the proofs (this is pretty long, but it can run in parallel using `make`'s `-j` option).
* run `mkdir -p "$(coqtop -where)/user-contrib/compcert"` you probably need to run it as superuser.
* run `cp --parents $(find . -name "*.vo") "$(coqtop -where)/user-contrib/compcert"` you probably need to run it as superuser.
