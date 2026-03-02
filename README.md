Proxy-based small inversions are an alternative to the `inversion` and `dependent elimination` tactics in Rocq.
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
`Derive InvProxy for`$~T$`.`  
This command derives custom-made definitions (partial inductive types and a function called $T$`_proxy`).
You need to be in the global environment, i.e., __not inside a proof__.

Then, you can call the tactic `sinv x` where x is the object to invert.
It performs a small inversion in proof mode.

<!--- <details> -->
<summary> The [Examples](./Examples) folder illustrates various use cases of proxy-based small inversions. </summary>

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
showcases the commands used to invert an inductive type according either to a user-given pattern, or a pattern custom-made for a specific inductively typed object.
<!--- </details> -->

## The commands to derive the intermediate definitions.
### Specialising over all possible indices
As said earlier, proxy-based small inversions work by specialising an inductive type over the possible constructors its inductively-typed indices can take.

The general command "`Derive InvProxy for `$~T$" specialises the inductive type over all *useful* indices -- technically: all indices that take the form of a constructor in the conclusion of the constructors of $T$.

This strategy may be not suitable when, in the type of the object to be inverted, some of those indices are just variables.
In those cases the following error will appear:
```coq
Error: Not an inductive definition.
```

The following sections will show how to deal with this situation by generating more precise partial inductive types.

### Specialising over a single index

To specialise on a single given pilot index only, use  
`Derive InvProxy for `$~T~~$` with index n.`  
Here, `n` is the (0-indexed) position of the index to invert.
Do not take parameters into account while computing this position.


### Specialising over a pattern of indices
If you wish to specialise according to a specific pattern, you use the following inductive type to define your pattern:

```coq
Inductive inversion_pattern :=
| noInversion
| pilotInversion : nat -> list inversion_pattern -> inversion_pattern
```

It is possible to automatically generate this pattern and the associated command.
To do so, while in proof mode at the step where you want to invert, execute `create_sinv_call x` where `x` is the object you want to invert.
This will print in the Rocq message buffer the command that you have to enter before the current proof/definition to invert the given object `x`.
(If you need dependent inversion, use `create_sdinv_call x`.)

For our example, if we want to invert an inductive type on its second index, then invert the second partial inductive type on the first of its indices, we would write  
`Definition pattern_inv := pilotInversion 1 [noInversion; pilotInversion 0 [noInversion;noInversion]].`  
Note that we assume that at each inversion, we get two partial inductive types, the length of the sublists must match the number of partial inductive types generated (i.e. the number of constructors of the type of the index to invert on).
Then, we use this pattern with the following command:  
`Derive InvProxy for `$~T~\:$` with pattern pattern_inv.`  

In the specific case where you have an equality between two inductively typed terms, and you want to invert them (see for example [`list_position.v#45`](./Examples/list_position.v#L45)), use the tactic `create_sinv_call_eq`.


### Dependent inversion
Dependent inversion is needed in the cases where the term to invert also appears in the goal and needs to be substituted.
To get a dependent inversion, add `Dependent` in front of `InvProxy` in any of the commands described above: `Derive Dependent InvProxy for `$~T~$`.`
The tactic to call for dependent inversion is `sdinv`.

### Adding a prefix to avoid name collisions
For any of the above cases, adding `with prefix str` at the end of the command will add the prefix `str` to all of the generated Rocq objects. This is useful to avoid avoid accidental name collisions.  
`Derive InvProxy for `$~T~$` with prefix str.`

### Making the display clearer
Proxy-based small inversions proceed by defining auxiliary inductive types.
By default, Rocq automatically generates additional elimination principles which are not used here and produce undesirable output.
For comfort, it is better to surround the `Derive InvProxy` calls by `Unset Elimination Schemes.` and `Set Elimination Schemes.` so that only useful names generated by the plugin will be displayed.

## Using small inversions in definition mode and in interactive proof mode
Once you've generated the partial inductive types and proxy, it is possible invert an object of the inductive type by either "`match invproxy name_object with`" in a definition body, or `sinv name_object` or `destruct (invproxy name_object)` in interactive mode.
In the first case, you also need to know the constructors of the auxiliary inductive types generated, which can be obtained
using the `Print` command.

Dependent inversion can be performed by respectively using `match dinvproxy name_object with`, `sdinv name_object` or `destruct (dinvproxy name_object)`

## Making your development independent of the plugin (and MetaRocq)
It is possible to keep using the generated terms and the `sinv` tactic without having the plugin installed.
Basically, you only have to copy and paste the useful Rocq code generated by each `Derive InvProxy for `$~T$, taking care of the class mechanism.
The "useful Rocq code" corresponds to the objects whose names are displayed by a `Derive InvProxy for `$~T$ when you use `Unset Elimination Schemes`: the names of the partial inductive types and then the name of the proxy, typically $~T$`_proxy`.
First, display the code of each generated partial inductive type using `Print` and copy-paste the result in your source file without change.
Next, display the code of the proxy using `Print `$~T$`_proxy.`, resulting in something like

```coq
T_proxy =
fun ... =>
{|
  proxy_type := bbb...;
  invproxy := ccc...
|}
     : forall (ddd...), InvProxy (T aaa...)
```
In the last line, the parentheses around `ddd...` may be missing if there is only one variable.
Then by copy-paste and small adjustments, make it an instance of the class `InvProxy` along the following scheme:
```coq
Instance T_proxy (ddd...) : InvProxy (T aaa...) :=
{|
  proxy_type := bbb...;
  invproxy := ccc...
|}.
```

### Example
In the case of inversion for the [Fin.t](https://github.com/rocq-prover/stdlib/blob/master/theories/Vectors/Fin.v) inductive type, the commands
```coq
Unset Elimination Schemes.
Derive InvProxy for t.
```
tell you that `t_O`, `t_S` and `t_proxy` were generated.

Then type:
```coq
Print t_O.
Print t_S.
Print t_proxy.
```

You get:

```coq
Inductive t_O : Set :=  .
Inductive t_S (n : nat) : Set :=  F1_S : t_S n | FS_S : t n → t_S n.

t_proxy =
fun _nat2 : nat =>
{|
  proxy_type := match _nat2 with
                | 0 => t_O
                | S x => t_S x
                end;
  invproxy :=
    fun _t_r : t _nat2 =>
    match _t_r in (t _nat3) return match _nat3 with
                                   | 0 => t_O
                                   | S x => t_S x
                                   end with
    | @F1 n => F1_S n
    | @FS n x => FS_S n x
    end
|}
     : forall _nat2 : nat, InvProxy (t _nat2)
```

Then add in your source file:

```coq
Inductive t_O : Set :=  .
Inductive t_S (n : nat) : Set :=  F1_S : t_S n | FS_S : t n → t_S n.

Instance t_proxy (_nat2 : nat) : InvProxy (t _nat2) :=
{|
  proxy_type := match _nat2 with
                | 0 => t_O
                | S x => t_S x
                end;
  invproxy :=
    fun _t_r : t _nat2 =>
    match _t_r in (t _nat3) return match _nat3 with
                                   | 0 => t_O
                                   | S x => t_S x
                                   end with
    | @F1 n => F1_S n
    | @FS n x => FS_S n x
    end
|}.
```

Then, in your source file, remove the `Derive InvProxy for t`,
replace `Require Import small_inversion` by `Require Import typeclass`,
and add the file [`typeclass.v`](./SmallInversion/typeclass.v) in your project.

Detailed algorithm:

* on the first line,
  + add `Instance` at the beginning;
  + after $~T$`_proxy`, insert the text of the last line after the `forall`, that is, `(ddd...) : InvProxy (`$~T~$` aaa...)`;
  the comma just before `InvProxy` is replaced by a colon;
  + end the line by "`:=`" instead of "`=`";
* remove the second line;
* add a period after `|}` in the penultimate line;
* remove the last line.
