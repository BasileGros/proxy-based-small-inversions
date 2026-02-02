Proxy-based small inversions are an alternative to the `inversion` and `dependent elimination` tactics in Rocq.
They are designed to minimize the size of terms.
In particular, the latter are not cluttered by additional equality constraints.

They are especially useful for defining programs with dependent types and developing formal proofs about them.


Proxy-based small inversions derive specialised versions of an inductive type according to the values (more precisely, the patterns) of the inductive indices of that type, so that filtering on a term of that inductive type takes into account its particular form, i.e., the constructors used in its indices.

They work in two steps:
- First, defining suitable partial inductive types, which mimic the original inductive type depending on constructors used for one or more of its indices. A mapping from the original inductive type to the new partial inductive types is also defined. The partial inductive types together with this mapping act as a proxy for the original inductive type.
This step only needs to be performed once.

- Second, inverting a object consists in decomposing a relevant proxy for it, using the `destruct` tactic (in interactive mode) or a pattern matching (when defining a dependtly typed functional program).

Both of those steps are supported by automated tools, the first by various commands that customise the specialisation of the original inductive type into partial inductive types, the second in the form of tactics to be called in interactive mode.


To learn more about proxy-based small inversions, see [here](https://hal.science/hal-05469909).

# Installation and compilation
This plugin works with Rocq version 9.1, and MetaRocq version 1.4.1+9.1.
Should opam be installed, the call to `opam pin git+https://github.com/DeLectionnes/proxy-based-small-inversions` should compile and install the plugin.  
For more details, see [INSTALL.md](./INSTALL.md).

# Usage
Import the plugin with the command

```coq
From SmallInversion Require Import small_inversion.
```

Proxy-based small inversions are used in two steps.
First, for each inductive type, custom-made projections and eliminators are automatically defined
by calling the preliminary command  
`Derive InvProxy for name_inductive.` in the general environment, i.e. __not in interactive mode__.

Then, you can call the tactic `sinv x` where x is the object to invert performs inversion in proof mode.

Below are all the variants of the preliminary command that can be used to customise the inversion.
<details>
<summary> The Examples folder holds various usecases of proxy-based small inversions and of this library. </summary>

- [matrices](./Examples/matrices.v)
showcases the use of proxy-based small inversions to manipulate the notably finicky size-indexed vectors of Rocq, using transposition of matrices as an example.

- [map3](./Examples/map3.v)
expands on the use for vectors with different map functions.

- [Fin_t](./Examples/Fin_t.v)
presents how to use proxy-based small inversions to manipulate the `Fin.t` bounded natural numbers which are notoriously impractical to use.

- [even](./Examples/even.v)
present a simpler examples of proxy-based small inversions used in proofs rather than functions.

- [next_color](./Examples/even.v)
uses the toy example of the colors of a trafic light to present inversion of multiple indices.

- [list_position](./Examples/list_position.v)
uses proxy-based small inversions to prove properties on a custom inductive type representing the position of elements within a list.

- [patterns](./Examples/patterns.v)
Showcases the commands used to invert an inductive type according either to a user-given pattern, or a pattern custom-made for a specific inductively typed object.
</details>

## The possible commands to specialise an inductive type
### Specialising over all possible indices
As said earlier, proxy-based small inversions work by specialising an inductive type over the possible constructors its inductively-typed indices can take.

The general command `Derive InvProxy for name_inductive.` specialises the inductive type over every useful indices, i.e. every index that takes the form of a constructor in the conclusion of the constructors of the inductive type.

This can often be too general, with the object to invert having one or more of those indices in the form of variables.
In those cases the following error will appear:
```coq
Error: Not an inductive definition.
```

In those cases, the following sections will show how to generate more precise partial inductive types.

### Specialising over a single index

To specialise on a single given pilot index only, use  
`Derive InvProxy for name_inductive with index n.`  
Where `n` is the (0-indexed) position of the index to invert.
Do not take parameters into account while computing this position.


### Specialising over a pattern of indices
If you wish to specialise according to a specific pattern, you use the following inductive type to define your pattern:

```coq
Inductive inversion_pattern :=
| noInversion
| pilotInversion : nat -> list inversion_pattern -> inversion_pattern
```
For our example, if we want to invert an inductive type on the second index, then invert the second partial inductive type on the first of its index, we would write  
`Definition pattern_inv := pilotInversion 1 [noInversion; pilotInversion 0 [noInversion;noInversion]].`  
Note that we assume that at each inversion, we get two partial inductive types, the length of the sublists must match the number of partial inductive types generated (i.e. the number of constructors of the type of the index to invert on).
Then, we use this pattern with the following command:  
`Derive InvProxy for name_inductive with pattern pattern_inv.`  

It is possible to automatically generate this pattern and the associated command.
To do so, while in proof mode at the step where you want to invert, execute `create_sinv_call x` where `x` is the object you want to invert. This will print in the Rocq message buffer the command that you have to enter before the current proof/definition to invert the given object `x`. (It is possible to use `create_sdinv_call x` for dependent inversion)

In the specific case where you have an equality between two inductively typed terms, and you want to invert them (see for example [`list_position.v#45`](./Examples/list_position.v#L45)), use the tactic `create_sinv_call_eq`.


### Dependent inversion
Dependent inversion is needed in cases where the term to invert also appears in the goal and needs to be substituted.
To get a dependent inversion, add `Dependent` in front of `InvProxy` in any of the commands described above: `Derive Dependent InvProxy for name_inductive.`
The tactic to call for dependent inversion is `sdinv`.

### Prefix to avoid name collistions
For any of the above cases, adding `with prefix str` to the command will add the prefix `str` to all of the generated Rocq objects. This is necessary to sometimes avoid name collisions.  
`Derive InvProxy for name_inductive with prefix str.`

### Making the display clearer
Proxy-based small inversions proceed by defining auxiliary inductive types.
By default, Rocq automatically generates additional elimination principles which are not used here and produce undesirable output.
For comfort, it is better to surround the `Derive InvProxy` calls by `Unset Elimination Schemes.` and `Set Elimination Schemes.` so that only useful names generated by the plugin will be displayed.

## Using small inversions in definition mode rather than proof mode
Once you've generated the partial inductive types and proxy, it is possible invert an object of the inductive type by either `match invproxy name_object with` in a definition body, or `sinv name_object` or `destruct (invproxy name_object)` in interactive mode.
In the first case, you also need to know the constructors of the auxiliary inductive types generated, which can be obtained
using the `Print` command.

Dependent inversion can be performed by respectively using `match dinvproxy name_object with`, `sdinv name_object` or `destruct (dinvproxy name_object)`

## Making your development independent of the plugin (and MetaRocq)
To remove the need for the plugin in a code, you only need the `typeclass.v` file.
You can copy it or its content into your project.
Then, `Print` and copy the code of the generated function and inductive types, and for each `R_proxy` (or `R_dproxy`) object for an initial type `R`, create a declaration of the instance to the typeclass.
