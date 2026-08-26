Proxy-based small inversions (PBSI) are an alternative to the `inversion` and `dependent elimination` tactics in Rocq.
They are designed to minimize the size of terms.
In particular, the latter are not cluttered by additional equality constraints.

They are especially useful for defining programs with dependent types and developing formal proofs about them.


Proxy-based small inversions derive specialised versions of an inductive type $T$ according to the values (more precisely, the patterns) of the inductive indices of $T$, so that filtering on a term of type $T$ takes into account its particular form, i.e., the constructors used in its indices.

They work in two steps:

- First, defining suitable partial inductive types, which mimic the original inductive type $T$ depending on constructors used for one or more of its indices. A mapping from $T$ to the new partial inductive types is also defined. The partial inductive types together with this mapping act as a proxy for $T$.
This step only needs to be performed once.

- Second, inverting a object. It consists in decomposing a relevant proxy for it, using the `destruct` tactic (in interactive mode) or a pattern matching (when defining a dependently typed functional program).

Both of those steps are supported by automated tools, the first by various commands that customise the specialisation of the original inductive type into partial inductive types, the second in the form of tactics to be called in interactive mode.


To learn more about proxy-based small inversions, see [here](https://hal.science/hal-05469909).

# Installation and compilation
This plugin works with Rocq version 9.1, and MetaRocq version 1.4.1+9.1.
Should opam be installed, the following command should compile and install the plugin.
```bash
opam pin git+https://github.com/BasileGros/proxy-based-small-inversions
```

``` bash
opam pin git+ssh://git@github.com/BasileGros/proxy-based-small-inversions.git
```

For more details, see [INSTALL.md](./INSTALL.md).

# Usage
Import the plugin with the command

```coq
From SmallInversion Require Import small_inversion.
```

Proxy-based small inversions are used in two steps.
First, for each inductive type $T$ on which inversions will be performed,
call the preliminary command:  
`Derive InvProxy for T.`  
This command derives custom-made definitions (partial inductive types and a function called $T$`_proxy`).
It is good practice to perform this command before stating a lemma whose proof uses PBSI.

Then, in proof mode, you can call the tactic `sinv x` where x is the assumption
(more generally: the term) to invert.

For an introduction, you can find many more details in
[tutorial_PBSI](./Examples/tutorial_PBSI.v) .

The [Examples](./Examples) folder illustrates various use cases of proxy-based small inversions.

- [matrices](./Examples/matrices.v)
showcases the use of proxy-based small inversions to manipulate the notably finicky size-indexed vectors of Rocq, using transposition of matrices as an example.

- [map2_around](./Examples/map2_around.v)
expands on the use for vectors with different map functions.
A co-inductive version of vectors is also briefly considered.

- [comparison](./Examples/comparison.v)
presents several approaches to define a given function on a dependent data-structure
a given lemma on it: 
small inversions of Monin and Shi, ITP13; the tactic `inversion`;
and the `Equations` package of Sozeau.

- [Fin_t](./Examples/Fin_t.v)
presents how to use proxy-based small inversions to manipulate the `Fin.t` bounded natural numbers which are notoriously impractical to use.

- [bounded_even_handcrafted](./Examples/bounded_even_handcrafted.v)
presents an example similar to even, in the tutorial, where natural numbers are replaced by bounded natural numbers.
In this example, we have an indexed index.

- [list_position](./Examples/list_position.v)
uses proxy-based small inversions to prove properties on a custom inductive type representing the position of elements within a list.

- [stlc_Poulsen](./Examples/stlc_Poulsen.v)
presents an adaptation in Rocq of some of the material given in
"Intrinsically-Typed Definitional Interpreters for Imperative Languages"
by Poulsen et al., POPL 2018.

- [stlc_viewleft_handcrafted](./Examples/stlc_viewleft_handcrafted.v)
presents the "extended example" developed in the last section of
   "The view from the left" by McBride & McKinna, JFP 2004.

# Authors
Pierre Corbineau  
Basile Gros  
Jean-François Monin
