(** A tutorial on automated proxy-based small inversions (PBSI) *)

(** First, get the plugin for PBSI *)

From SmallInversion Require Import small_inversion.

(* ================================================================== *)
(** * Basics *)

(** We assume a (co)inductively defined type T, that is, a type defined
using the keywords `Inductive`, `CoInductive` or just `Variant`.
In what follows, we use the term “algebraic type” to encompass these
possibilities.
Proxy-based small inversions (PBSI) are based on specialised versions
of T according to the patterns of the algebraic indices of T.
Those specialised versions of T are called partial algebraic types (PAT).

PBSI work in two steps:

- First, defining partial algebraic types and a mapping from T to those
  PATs, so that we get a proxy for T.
  This step only needs to be performed once.

- Second, inverting a term. It consists in decomposing a relevant
  proxy for it by pattern-matching. In interactive mode, this
  can be achieved using the "destruct" tactic or our "sinv" tactic.
  In the case of dependent PBSI, the relevant tactic is "sdinv".
*)

(* ==================================================================*)
(** * Cheat sheet
  - Commands:
    Derive [Dependent] InvProxy for YourType.
    Derive [Dependent] InvProxy for YourType [with index 0,1, ...]
                                             [with prefix String].

    Create_sinv_call YourTerm
    Create_sdinv_call YourTerm

  - Tactics:
    sinv YourAssumption.
    sinv YourAssumption as [ ... | ... ].
    sdinv YourAssumption.
    sinv YourAssumption as [ ... | ... ].

  - Programming constructs (where PAT means partial algebraic type)
    match YourType_proxy expr with
    let ( , ... ) := YourType_proxy expr in
    let 'ConstructorPAT... := YourType_proxy expr in
    let 'ConstructorPAT... in PAT... x return ... x ... := YourType_proxy expr in

  - Programming constructs (OBSOLETE, TODO to be removed)
    match invproxy expr with
    let (... ) := (invproxy expr : ExpectedPartialAlgebraicType) in
    let (... ) := (YourType _ _).(invproxy) expr in
    let 'YourConsructor ... := invproxy expr in

    match (YourType _ _).(invproxy) expr with

    match my_YourType_proxy expr with
    let (... ) := my_YourType_proxy expr in

*)

(* ==================================================================*)
(** Summary

For a basic introduction to PBSI, Chapters 1, 2 and the first
part of Chapter 3 "Selecting an index" are enough.

Chapter 1: using PBSI in interactive proof mode
Chapter 2: using PBSI in dependently typed programs
Chapter 3: simple tuning of PBSI
Chapter 4: making your development independent from our plugin
Chapter 5: on the relevance of parameters
Chapter 6: more advanced example(s)
Chapter 7: advanced tuning of PBSI

*)

(* ==================================================================*)
(** * Chapter 1: using PBSI in interactive proof mode *)

(** Here, PBSI is used as an alternative to the well-known inversion
    tactic *)

(** ** An explainable inversion of even *)

Inductive even : nat -> Prop :=
| even0 : even O
| even2 : forall (n : nat), even n -> even (S (S n)).

(** Inversion is needed when we have assumptions (even X), where X is
    not a variable but constructed, for instance O, (S O), (S (S ...)) *)

(** The following command is required to make PBSI available for even.
    Its effect is to define some auxiliary algebraic predicates (or types),
    that we call "partial algebraic types" (PAT).  They are derived from the
    definition of even, as well as a proxy function for even called even_proxy
    (by default).
 *)

(** "Unset/Set Elimination Schemes" is not mandatory, it justs makes the
    output cleaner -- the keyword for the PATs should actually
    be "Variant" instead of "Inductive", because they are not recursive,
    even though the original algebraic relation (even, here) is itself recursive.
    This issue comes from MetaRocq <= 1.5.1+9.1 and it should be fixed in the
    next release.
*)

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for even.
(** This defines:
    - a number of PATs for even.
      Here: even_O, even_S_O and even_S_S.
    - a proxy function that gather them, here even_proxy
    - an instance of the class InvProxy, here even_instance,
      to be used internally by our generic tactic "sinv".
    It is instructive -- and recommended -- to see the contents
    of the PATs. *)
Print even_O.
Print even_S_O.
Print even_S_S.
Set Elimination Schemes (* For comfort *).

(** You can then replace "inversion" by our tactic "sinv". *)
Lemma even_cancel_S_S_draft n : even (S (S n)) -> even n.
Proof. intro e. sinv e. exact H. Qed.

(** As for the tactic destruct, it is good practice is to have an explicit name for
    the H above, so that your script does not depend on the algorithm used by
    Rocq for generating names.
    The syntax is the same as for destruct.
    In order to understand how many cases and, in each case, how many
    components you get, you shoud guess what is the relevant PAT.
    Looking at e, we guess that this is even_S_S, that contains only one case
    with one component, of type (even n).
    We give more details below in Lemma even_cancel_S_S_explanation.
*)
Lemma even_cancel_S_S n : even (S (S n)) -> even n.
Proof. intro e. sinv e as [e']. exact e'. Qed.

(** An absurd hypothesis. The PAT for e will be even_S_O, with zero cases. *)
Lemma no_even_1 : even 1 -> False.
Proof. intro e. sinv e. Qed.

(** A more interesting lemma, where an induction on even is followed
    by an inversion *)
Lemma even_plus_cancel n m : even n -> even (n + m) -> even m.
Proof.
  induction 1 as [ | n en Hen]; cbn; intro enm.
  - exact enm.
  - (* inversion needed, using even_S_S *)
    sinv enm as [enm']. exact (Hen enm').
Qed.

(** Explanation *)
(** Reminder on the vocabulary : the argument of even is called an index.
    Indeed, in a proof-as-types setting, an inductive predicate like even
    is seen as an indexed family of types. *)
Lemma even_cancel_S_S_explanation n : even (S (S n)) -> even n.
Proof.
  intro e.
  (** We have the assumption   e : even (S (S n)).
      By pattern-matching on the *index*, we know that only
      the second constructor of even is possible.
      The special cases of even x where x has the shape (S (S n))
      are precisely gathered in even_S_S, one of the partial algebraic
      types generated by the above command "Derive InvProxy for even." *)
  Print even_S_S.
  (** Result (up to a renaming, possibly; the keyword Variant is
      more accurate):
  Variant even_S_S (n : nat) : Prop :=
  | even2_S_S : even n -> even_S_S n. *)

  (** We also have (see below) :  even (S (S n) -> even_S_S n.
      A proof term for this implication is provided by even_proxy. *)
  Check (even_proxy (S (S n)) : even (S (S n)) -> even_S_S n).
  (** As a consequence: *)
  Check (even_proxy _ e : even_S_S n).
  (** (even_proxy _ e) can be decomposed as defined in even_S_S. *)
  destruct (even_proxy _ e) as [e'].

  (** We can also use invproxy e, because even_proxy and its type are gathered
      in a Rocq class, so that invproxy e is convertible with (even_proxy _ e).
      Indeed, "sinv e" is nothing else than "destruct (invproxy e)".
   *)
  Check eq_refl : invproxy e = even_proxy _ e.
  Undo.
  destruct (invproxy e) as [e'].
  exact e'.
Qed.

(** A more technical remark:
    as n is a parameter of even_S_S, it is not a component of
    even2_S_S, in contrast with even2; we then did not write
    "as [n' e']" but just "as [e']"; more importantly, this is
    why the link with other occurrences of n in the goal is kept.
    The interested reader will find more details on this aspect in Chapter 5.
*)

(** Some explanations regarding Lemma no_even_1 above. *)
Lemma no_even_1_explanation : even 1 -> False.
Proof.
  intro e.
  (** Here, we have no case of even x where x has the shape (S O) *)
  Print even_S_O.
  (** We also have :  even (S O) -> even_S_O. *)
  Check (even_proxy (S O) : even (S O) -> even_S_O).
  Check (invproxy e : even_S_O).
  (** Consistently, destruct (invproxy e) generates no case to consider *)
  destruct (invproxy e).
Qed.

(** You can also print the type of even_proxy. *)
Check even_proxy.

(** The key is the definition of even_proxy_type, that is based on the
    three PATS of even presented above. *)
Print even_proxy_type.

(** You could even print even_proxy and make it somewhat
    more beautiful. *)
Print even_proxy.

(** Handcrafted version of even_proxy *)
Definition my_even_proxy {n} (e : even n) : even_proxy_type n :=
  match e with
  | even0 => even0_O
  | even2 n x => even2_S_S n x
  end.

(** Then observe on the following scenario that you get a
    reasonably explicit controllable and explainable proof
    of even_cancel_S_S, in contrast with what you would get
    with "inversion". *)
Lemma even_cancel_S_S_handcrafted n : even (S (S n)) -> even n.
Proof.
  intro e.
  (* We can directly go to the "destruct" command below,
     but let us proceed slowly. *)
  Check (my_even_proxy e).
  Eval cbn in (even_proxy_type (S (S n))).
  Check (my_even_proxy e : even_S_S n).
  destruct (my_even_proxy e) as [e'].
  exact e'.
Qed.

(** You get a small proof term. *)
Print even_cancel_S_S_handcrafted.

(** See the constrast with what you get using the tactic inversion. *)
Lemma even_cancel_S_S_inversion n : even (S (S n)) -> even n.
Proof.
  intro e. inversion e. assumption.
Qed.

Print even_cancel_S_S_inversion.

(* ----------------------------------------------------------------- *)
(** In the above example, even is a unary predicate.
    In the presence of n-ary relations, some tuning is generally
    needed.  This is considered below in Chapter 3 for simple situations,
    then in Chapter 7 for more demanding cases.
*)


(* ================================================================== *)
(** * Chapter 2: using PBSI in dependently typed programs *)

(** An emblematic dependent type is length-indexed lists, aka vectors.
    Here is its definition, with parameter A (the type of the elements)
    and an index of type nat.
    Remind that parameters have to be uniformly used in each
    constructor, in contrast with indices.
    We provide more details in Chapter 5 on the distinction between
    parameters and indices.
    Here, the type of nil is (vect A O), whereas the type of (cons... )
    is (vect A (S n)) *)

Module Chapters_2_3.


Inductive vect (A : Type) : nat -> Type :=
| nil : vect A O
| cons : forall n, A -> vect A n -> vect A (S n).

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for vect.
Set Elimination Schemes (* For comfort *).

(** vect_proxy will be used below in programs *)
About vect_proxy.
(** We see that its main argument is a vector, preceded by its
    parameter and its index.  It is more convenient for these last two
    to be declared as implicit. *)
Arguments vect_proxy {_ _} _.


(** The head and tail function make sense only for vectors with
     a strictly positive length. *)

(** In pattern-matching, only indices are relevant -- they are bound
    in the "in" clause, in constrast with parameters, represented
    by a wilcard "_" . Note that n is a component of cons,
    whereas it is a parameter of vect_S, and then no longer
    a component of cons_S. *)

Print cons_S.

(** Therefore, we have two wildcards for cons_S in the following
    pattern matching. *)

Definition hd {A n} (u : vect A (S n)) : A :=
  match vect_proxy u with
  | cons_S _ _ x u' => x
  end.


(** For the record, the class mechanism mentioned above can
    also be used, using the generic name "invproxy". *)

Definition hd_gen {A n} (u : vect A (S n)) : A :=
  match invproxy u with
  | cons_S _ _ x u' => x
  end.


(* ---------------------------------------------------------------------- *)
(** ** Deconstructing let *)

(** This section can be skipped at first reading *)

(** Equivalently, you can use a deconstructing let.
     You can use one of the 2 following methods. *)

(** Method 1: agnostic in the name of the constructor,
    completely generic, by specifying the proxy instance to be used,
    here vect_proxy, the name printed by "Derive InvProxy for vect". *)
Definition hd_let {A n} (u : vect A (S n)) : A :=
  let (x, u') := vect_proxy u in x.

(** Method 2: deconstructing let that uses the name of the expected
      constructor, here cons_S, as in the above "match vect_proxy u". *)
Definition hd_let_cons {A n} (u : vect A (S n)) : A :=
  let 'cons_S _ _ x u' := vect_proxy u in x.

(** An additional possibility is to set "asymmetric patterns",
    so that the above wildcards are removed from patterns. *)

Set Asymmetric Patterns.
Definition hd_asym {A n} (u : vect A (S n)) : A :=
  match vect_proxy u with
  | cons_S x u' => x
  end.

Definition hd_cons_asym {A n} (u : vect A (S n)) : A :=
  let 'cons_S x u' := vect_proxy u in x.

(** Back to the default option of Rocq. *)
Unset Asymmetric Patterns.

(* ---------------------------------------------------------------------- *)
(** ** Defining map2 *)

(** We now define our favorite example: map2.  It is similar to map
    but, instead of a unary function, it applies a BINARY function
    to the elements of TWO vectors indexed by the SAME length. *)

Fixpoint map2 {A B C} (f : A -> B -> C) {n} (u : vect A n) :
  vect B n -> vect C n :=
  match u with
  | nil _         => fun v => nil C
  | cons _ n x u' => fun v =>
      let (y, v') := vect_proxy v in
      cons _ _ (f x y) (map2 f u' v')
  end.

(* ---------------------------------------------------------------------- *)
(** ** Formal proofs about dependently typed programs *)

(** For the tail, we pick one of the above methods. *)
Definition tl {A n} (u : vect A (S n)) : vect A n :=
  let (x, u') := vect_proxy u in u'.

(** However, sinv is not strong enough for *reasoning* about
    dependently typed programs such as hd and tl. *)
Lemma make_hd_tl {A n} (u : vect A (S n)) : u = cons A n (hd u) (tl u).
Proof.
  sinv u as [x u'].
  (** We see that, in the conclusion, u is not changed to (cons A n x u'). *)
Abort.

(** The technical reason is that the return clause of the corresponding
    pattern-matching construct references n but not the original vector.
    What is needed is called dependent PBSI.
 *)

Unset Elimination Schemes (* For comfort *).
Derive Dependent InvProxy for vect.
Set Elimination Schemes (* For comfort *).

(** The tactic to be used is "sdinv" instead of "sinv". *)
Lemma make_hd_tl {A n} (u : vect A (S n)) : u = cons A n (hd u) (tl u).
Proof.
  sdinv u as [x u']. cbn. reflexivity.
Qed.

(** Dependent PBSI is actually a slight modification of PBSI,
    that uses partial algebraic types containing an additional index
    that reflects the original vector.
    Additional explanations can be found in our LPAR-26 paper,
    but the idea can be caught by looking at the definitions generated
    by the above commands.
    It is instructive to see:
    - the basic partial algebraic types generated
    - the corrresponding dependent partial algebraic types
 *)

Print vect_O.
Print vect_O_dep.
Print vect_S.
Print vect_S_dep.

(** The code of the dependent proxy itself looks more complicated,
    but its computational contents is actually the same as before. *)

Print vect_proxy.
Print vect_dproxy.
Print vect_dproxy_type.

(** The above defnitions can be beautified. *)

Definition my_vect_proxy_type A n : Type :=
  match n with
  | O   => vect_O A
  | S n => vect_S A n
  end.

Definition my_vect_proxy {A n} (u : vect A n) : my_vect_proxy_type A n :=
  match u with
  | nil _         => nil_O A
  | cons _ n x u' => cons_S A n x u'
  end.

Definition my_vect_dproxy_type A n : vect A n -> Type :=
  match n with
  | O   => vect_O_dep A
  | S n => vect_S_dep A n
  end.

Definition my_vect_dproxy {A n} (u : vect A n) : my_vect_dproxy_type A n u :=
  match u with
  | nil _         => nil_O_dep A
  | cons _ n x u' => cons_S_dep A n x u'
  end.

(* ================================================================== *)
(** * Chapter 3: simple tuning of PBSI *)

(** Vectors have only one index, for their length.  Given a vector u to
    be analyzed by pattern matching, its index is in general an expression
    of type nat.  If this expression is a variable, CIC pattern matching
    is designed for this situation, just use it without making things any
    more complicated.  This is exactly the case for the first argument
    in the map2 function above.
    Indeed, trying to use PBSI in this situation does not make sense,
    because the type of (my_vect_proxy u), that is,
    vect_proxy_type A n, does not reduce further than
    match n with  0 => vect_O A  |  S n => vect_S A n  end.
    Then you don't know if you should a pattern for vect_O or for vect_S.
    This is rather clear if you write directly your program.
    If you are in interactive mode, either because you are designing your
    program, or because your target is not a program, but a proof,
    you may try our tactic sinv.  This will result in a typical error
    message "Not an inductive definition", as in the following scenario,
    followed by a small number of additional explanatory commands.
 *)

#[refine]
Fixpoint map2_stupid {A B C} (f : A -> B -> C) {n} (u : vect A n) :
  vect B n -> vect C n := _.
Fail sinv u. (* the promised error message *)
Fail destruct (invproxy u). (* The effect of "sinv u" *)
(** Similarly to what was shon on even, invproxy u is convertible with vect_proxy u. *)
Check eq_refl : invproxy u = vect_proxy u.
(** Here is its type *)
Check vect_proxy u : vect_proxy_type A n.
(** However, this type is not converitble to an inductive type. *)
Compute vect_proxy_type A n.
(** Hence the error message *)
Abort.

(** In other words, you don't have relevant information on n to be used
    by PBSI.

    Now, if the index of u is "constructed", that is, if it O or (S n)
    for some n -- or if it is convertible to one ot those two shapes --
    the type of (invproxy u) will reduce to vect_O or to vect_S n,
    respectively (with an implicit parameter, say A)
    and in either case, it can be properly decomposed.

    In summary, the relevant pattern matching expression to be used is
    match u with..., if the index of u if a variable, and
    match vect_proxy u with ..., if the index of u is constructed.
*)

(* ---------------------------------------------------------------------- *)
(** ** Selecting an index *)

(** For types or relations with 2 indices, the same binary question should be
    asked for each index, so that we have 4 possibilities, that is
    3 possibilities for a proxy, that could expect:
    - 2 constructed indices
    - or 1 constructed index only (2 possibilities)
    In theory, all possibilities can make sense. In practice, we derive
    the desired proxy only for the needed situation.
    Let us illustrate this on the following binary relation nextcolor.
*)

Inductive color := Red | Orange | Green.

Inductive nextcolor : color -> color -> Prop :=
| ncGO : nextcolor Green Orange
| ncOR : nextcolor Orange Red
| ncRG : nextcolor Red Green.

(** By default, the Derive InvProxy command build proxies for the
    situations where all indices (2, here) are constructed. *)

Definition FAKE := Prop.

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for nextcolor.
Set Elimination Schemes (* For comfort *).

(** However this is not relevant in the next lemma. *)

Lemma between_Green_Red c : nextcolor Green c -> nextcolor c Red.
Proof.
  intro nc. Fail sinv nc.
  (* We get the infamous "Not an inductive definition" explained above,
     because the second index of nc is a variable. *)
Abort.

(** Let us the tune our proxy, using "with index 0" :
    Indices are numbered 0, 1... (n-1) for an n-ary relation or type. *)

Reset FAKE.

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for nextcolor with index 0.
Set Elimination Schemes (* For comfort *).

Lemma between_Green_Red c : nextcolor Green c -> nextcolor c Red.
Proof.
  intro nc.
  sinv nc.
  (** Let us go slowly. *)
  Undo.
  Check (invproxy nc : nextcolor_Green c).
  Print nextcolor_Green.
  destruct (invproxy nc).
  constructor.
Qed.

(** Here is a lemma with an ordinary destruct followed by two PBSI. *)

Theorem nextcolor3 : forall c1 c2 c3 c4,
    nextcolor c1 c2 -> nextcolor c2 c3 ->  nextcolor c3 c4 ->
    c4 = c1.
Proof.
  intros c1 c2 c3 c4 nc1 nc2 nc3.
  (* We have 3 cases for the first assumption, forcing c2 to
  have a fixed value. *)
  destruct nc1 as [ | | ].
  - (* Only 1 case is left for nc2, provided we use (small) inversion;
       in turn, c3 becomes constrained to be a specific value *)
    sinv nc2.
    (* Similarly for nc3 *)
    sinv nc3. reflexivity.
   (* The remaining subgoals are proved in the same way *)
  - sinv nc2; sinv nc3; reflexivity.
  - sinv nc2; sinv nc3; reflexivity.
Qed.

(** The general command "Derive InvProxy for T" specialises the
algebraic type over all *useful* indices -- technically: all indices
that take the form of a constructor in the conclusion of at least
one of the constructors of T.
*)

(* ---------------------------------------------------------------------- *)
(** ** Using different proxies for the same relation *)

(** This section can be skipped at first reading.
    It is not a prerequisite for the following chapters. *)

(** Suppose that we aim at a theorem similar to nextcolor3,
    but using nextcolor in the opposite direction. *)

Definition FAKE := Prop.

Theorem prevcolor3_Red : forall c1 c2 c3,
    nextcolor c3 Red -> nextcolor c2 c3 -> nextcolor c1 c2 ->
    Red = c1.
Proof.
  intros c1 c2 c3 nc3 nc2 nc1.
  (* The next command fails because index 0 of nc3 is a variable *)
  Fail sinv nc3.
Abort.

(** We actually need "Derive InvProxy for nextcolor with index 1." *)
Unset Elimination Schemes (* For comfort *).
(** Unfortunately, we get a name conflict *)
Fail Derive InvProxy for nextcolor with index 1.
(** In this situation, just use the option "with prefix" completed
    by a string of your choice. *)
Derive InvProxy for nextcolor with index 1 with prefix "nc1".
Set Elimination Schemes (* For comfort *).

Theorem prevcolor3_Red : forall c1 c2 c3,
    nextcolor c3 Red -> nextcolor c2 c3 -> nextcolor c1 c2 ->
    Red = c1.
Proof.
  intros c1 c2 c3 nc3 nc2 nc1.
  (* Now sinv is working properly *)
  sinv nc3. sinv nc2. sinv nc1.
  reflexivity.
Qed.

(** Another possibility is to use the general option "with pattern" of
    "Derive InvProxy". Its syntax is rather technical, it is actually meant
    to be used in combination with a helper command called Create_sinv_call.
    For completeness, we illustrate this option for our current example,
    though "with index" is the most reasonable choice here.
    More relevant uses of "with pattern" are given in Chapter 7.
    First we go back to the state juste before the definition FAKE.
 *)

Reset FAKE.

Theorem prevcolor3_Red : forall c1 c2 c3,
    nextcolor c3 Red -> nextcolor c2 c3 -> nextcolor c1 c2 ->
    Red = c1.
Proof.
  intros c1 c2 c3 nc3 nc2 nc1.
  (* Generating a customized proxy for nc3 *)
  Create_sinv_call nc3.
  (* output :
  Derive InvProxy for nextcolor with pattern (pilotInversion 1 [noInversion; noInversion; noInversion]). *)
Abort.

(** As before, we add a prefix. *)

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for nextcolor with pattern (pilotInversion 1 [noInversion; noInversion; noInversion]) with prefix "csc".
Set Elimination Schemes (* For comfort *).

Theorem prevcolor3_Red_new : forall c1 c2 c3,
    nextcolor c3 Red -> nextcolor c2 c3 -> nextcolor c1 c2 ->
    Red = c1.
Proof.
  intros c1 c2 c3 nc3 nc2 nc1.
  sinv nc3. sinv nc2. sinv nc1.
  reflexivity.
Qed.

End Chapters_2_3.

(* ================================================================== *)
(** * Chapter 4: making your development independent from our plugin  *)

(** It is possible to keep using the generated terms and the "sinv"
    tactic without having the plugin installed and MetaRocq.

Basically, you only have to copy and paste the useful Rocq code
generated by each "Derive InvProxy for T", taking care of the class
mechanism if you need it (mainly for tactics sinv and sdinv).
The "useful Rocq code" corresponds to the objects whose
names are displayed by a "Derive InvProxy for T" when you use
"Unset Elimination Schemes", which are:
- the names of the partial algebraic types
- the name of the proxy and of its type, typically "T_proxy" and  "T_proxy_type".
- the name of the corresponding instance registered in the
  invproxy class.

 *)


(** ** Example *)

(** We consider again vect as defined in Chapter 2 above.
the command "Derive InvProxy for vect." displayed:
vect_O is defined
vect_S is defined
vect_proxy_type is defined
vect_proxy is defined
vect_instance is defined

Then get their contents.
The last one is only useful if you want to use the
class mechanism for tactics in scripts.
 *)

Inductive vect (A : Type) : nat -> Type :=
| nil : vect A O
| cons : forall n, A -> vect A n -> vect A (S n).

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for vect.
Set Elimination Schemes (* For comfort *).

Print vect_O.
Print vect_S.
Print vect_proxy_type.
Print vect_proxy.
Print vect_instance.

(** You get:

Inductive vect_O (A : Type) : Type :=  nil_O : vect_O A.
Inductive vect_S (A : Type) (n : nat) : Type :=
    cons_S : A -> vect A n -> vect_S A n.

vect_proxy_type =
fun (A : Type) (nat0 : nat) =>
match nat0 with
| 0 => vect_O A
| S x => vect_S A x
end
     : Type -> nat -> Type

vect_proxy =
fun (A : Type) (nat2 : nat) (vect_r : vect A nat2) =>
match vect_r in (vect _ nat3) return (vect_proxy_type A nat3) with
| nil _ => nil_O A
| cons _ n x x0 => cons_S A n x x0
end
     : forall (A : Type) (nat2 : nat), vect A nat2 -> vect_proxy_type A nat2

vect_instance =
fun (A : Type) (nat2 : nat) =>
{| invproxy_type := vect_proxy_type A nat2; invproxy := vect_proxy A nat2 |}
     : forall (A : Type) (nat2 : nat), InvProxy (vect A nat2)

 *)

(** In this demo we use a module only to avoid name clashes
    with previous definitions in this file. *)
Module ExampleIndependent.

(** You just copy the partial algebraic types in your source file.
    You can replace "Inductive" by "Variant". *)
Variant vect_O (A : Type) : Type :=  nil_O : vect_O A.
Variant vect_S (A : Type) (n : nat) : Type :=
    cons_S : A -> vect A n -> vect_S A n.

(** The proxy type and the proxy need obvious adjustments. *)

Definition vect_proxy_type (A : Type) (nat0 : nat) :=
  match nat0 with
  | 0 => vect_O A
  | S x => vect_S A x
  end.

Definition vect_proxy (A : Type) (nat2 : nat) (vect_r : vect A nat2) :=
  match vect_r in (vect _ nat3) return (vect_proxy_type A nat3) with
  | nil _ => nil_O A
  | cons _ n x x0 => cons_S A n x x0
  end.

(** You may want to beautity those definitions, for instance the last one *) 
Reset vect_proxy.
Definition vect_proxy A n (v : vect A n) :=
  match v in (vect _ nat3) return (vect_proxy_type A nat3) with
  | nil _ => nil_O A
  | cons _ n x v' => cons_S A n x v'
  end.

(** You can also make the type of the result more readable *)
Reset vect_proxy.
Definition vect_proxy A n (v : vect A n) : vect_proxy_type A n :=
  match v with
  | nil _ => nil_O A
  | cons _ n x v' => cons_S A n x v'
  end.

(** Finally, if you want to reuse what you wrote in your file without
    modification, in particular if you use "sinv" or "invproxy", 
    vect_instance needs to be declared as in instance
    of the class InvProxy.
    The type of the result is given at the end of the last line
    displayed above when printing vect_instance: InvProxy (vect A nat2) *)
Instance vect_instance (A : Type) (nat2 : nat) : InvProxy (vect A nat2) :=
  {| invproxy_type := vect_proxy_type A nat2; invproxy := vect_proxy A nat2 |}.

(** It is generally convenient have implicit arguments in vect_proxy. *)
Arguments vect_proxy {_ _} _.

(** It works as expected. *)
Definition hd_let {A n} (u : vect A (S n)) : A :=
  let (x, u') := vect_proxy u in x.

Definition hd_let_cons {A n} (u : vect A (S n)) : A :=
  let 'cons_S _ _ x u' := vect_proxy u in x.

Definition hd_class {A n} (u : vect A (S n)) : A :=
  let 'cons_S _ _ x u' := invproxy u in x.

End ExampleIndependent.

(** Then, in your source file, remove "Derive InvProxy for t",
replace "Require Import small_inversion" by "Require Import typeclass",
and add the file "./SmallInversion/typeclass.v" in your project.
 *)

(** For dependent PBSI, follow exactly the same instructions,
    looking at what is displayed by "Derive Dependent Proxy for T." *)

(* ================================================================== *)
(** * Chapter 5: on the relevance of parameters *)

(** The point to be detailed now is about distinguishing parameters and
indices.  Although this may seems a boring technical distinction,
it is behind one of the important design choices of PBSI, and it also
explains why PBSI sometimes yields better results than other approaches,
as illustrated in Chapter 6.

This chapter can be skipped if you are in a hurry or if you are
already familiar with parameters and indices.

First, compare the above definition of even with the definition
of the third PAT even_S_S :

Inductive even : nat -> Prop :=
| even0 : even O
| even2 : forall (n : nat), even n -> even (S (S n)).

Variant even_S_S (n : nat) : Prop :=
| even2_S_S : even n -> even_S_S n.

Here, even and even_S_S are both predicates on nat:
they take a nat as argument and return a Prop.
However, this argument is in index in the case of even,
whereas it is a parameter in the case of even_S_S.
The definition of even and even_S_S is made of constructors
and each of them, after full application to their components,
provides a term of type (even N) or (even_S_S N), respectively,
where N is an expression of type nat.
However, being an index or a parameter makes an important difference
about allowed expressions for N in the definition of even or even_S_S.
- As the argument of even is an index, this N can be any expression.
  Here they are O for the even0 and (S (S n)) for even2, respectively.
- in contrast, as the argument of even_S_S is a parameter named n, there
  is only one possibility for N: it must be n itself.

Indices are then more convenient at construction time.
But it is the opposite at destruction time.
To see this, consider the following alternative to even_S_S,
where an index is used instead of a parameter.

*)

Variant even_S_S' : nat -> Prop :=
| even2_S_S' : forall n, even n -> even_S_S' n.

(** We have an equivalence, so what is the point? *)
Lemma even_S_S'_equiv n : even_S_S n <-> even_S_S' n.
Proof. split; intro e; constructor; destruct e; assumption. Qed.

(** The point is that the meaning is not the same.
If we have an assumption (E: even_S_S EXP)
and a similar assuption (E' : even_S_S' EXP')
an analysis (by pattern matching) of the contents of
E does not provide the same information as for E'.

The information contained in E can be expressed as:
in the above definition of (even_S_S n), n is instantiated to EXP;
then E must have the shape (even2_S_S e) where the type of e is
(even EXP).

The information contained if E' can be roughly expressed as:
let us forget the argument of even_S_S in the type of E'; then E' must
have the shape (even2_S_S' n' e'), where n' is a fresh nat and the type
of e' is (even n').

The actual information contained if E' can me made more accurate,
so that other occurrences of EXP' can be bound to n',
but the important point is that we get an annoying fresh n'
that is unrelated to the other parts of an ongoing proof under construction.

Hence the well-known behavior that is observed in proofs such as the following.
 *)

Lemma demo_parameter_index
  (f f' g g' : nat -> nat) (n : nat)
  (H : forall x, even (f x) -> even (g x))
  (H' : forall x, even (f' x) -> even (g' x)):
  even_S_S (f n) -> even_S_S' (f' n) -> even (g n) /\ even (g' n).
Proof.
  intros E E'. split.
  - (* No problem if we first analyze the contents of E *)
    destruct E as [efn]. apply H. exact efn.
  - (* Problem if we first analyze the contents of E' *)
    destruct E' as [f'n ef'n]. apply H'.
    (* We are stuck because f'n is unrelated to (f' n) *)
    (* By chance here, backward reasoning would happen to work.
       This is left as a simple exercise. *)
Abort.

(** Forward reasoning is often more natural.
Indeed, it is also possible to use forward reasoning successfully
on the hypothesis E' in the above proof.
The general trick consists in adding a suitable additional
equality in the goal. It is sometimes called "Fording".
We see this as an unnecessary complication:
simply use even_S_S instead of even_S_S'!

In particular, the following proxy for even based on even_S_S'
in the place of even_S_S behaves badly.
*)

Definition even_proxy'_type n :=
  match n with
  | 0 => even_O
  | 1 => even_S_O
  | S (S n) => even_S_S' n
  end.

(** Another version of even_proxy *)
Definition my_even_proxy' {n} (e : even n) : even_proxy'_type n :=
  match e with
  | even0 => even0_O
  | even2 n x => even2_S_S' n x
  end.

(** The above issue illustrated above on Lemma demo_parameter_index
    can be adapted as follows. *)
Lemma demo_parameter_index_PBSI
  (f f' g g' : nat -> nat) (n : nat)
  (H : forall x, even (f x) -> even (g x))
  (H' : forall x, even (f' x) -> even (g' x)):
  even (S (S (f n))) -> even (S (S (f' n))) -> even (g n) /\ even (g' n).
Proof.
  intros E E'. split.
  - (* The PBSI proxy behaves well *)
    destruct (my_even_proxy E) as [efn]. apply H. exact efn.
 - (* Problem if we use the "bad" proxy *)
   destruct (my_even_proxy' E') as [f'n ef'n]. apply H'.
   Undo 2. (* The PBSI proxy behaves well *)
   destruct (my_even_proxy E') as [ef'n]. apply H'. exact ef'n.
Qed.

(** Another issue with even_S_S' is that its additional component n
conveys a data in Set (or Type).  This may raise issues with
the guard condition and Prop/Set elimination.

We do not go into details here, but just give a taste of
what is to come in Chapter 6 below.

Consider a correct-by-construction half function that is
expected to work on even numbers only.
It can be defined using my_even_proxy.
*)

Fixpoint twice n := match n with O => O | S n => S (S (twice n)) end.

Fixpoint half n : even n -> {y | twice y = n} :=
  match n with
  | O => fun _ => exist _ O eq_refl
  | 1 => fun e => match my_even_proxy e with end
  | S (S n) => fun e => let (e') := my_even_proxy e in
                        let (h, E) := half n e' in
                        exist _ (S h) (f_equal (fun x => S (S x)) E)
  end.

(** A similar code using my_even_proxy' could be:

Fixpoint half' n : even n -> {y | twice y = n} :=
  match n with
  | O => fun _ => exist _ O eq_refl
  | 1 => fun e => match my_even_proxy' e with end
  | S (S n) => fun e => let (n', e') := my_even_proxy' e in
                        let (h, E) := half' n' e' in
                        exist _ (S h) (f_equal (fun x => S (S x)) E)
  end.

However, we have an issue about Prop/Set elimination,
as shown by the next attempt.
 *)

#[refine]
Fixpoint half' n : even n -> {y | twice y = n} :=
  match n with
  | O => fun _ => exist _ O eq_refl
  | 1 => fun e => match my_even_proxy' e with end
  | S (S n) => fun e => _
  end.
Fail refine (let (n', e') := my_even_proxy' e in _).
Abort.

(** We could then try a weaker version with a result of sort Prop
    rather than Set.  We then see that the recursive call is not on n,
    but on the fresh n' provided by even_S_S', with two additional issues:
    - the guard condition would then be violated
    - the remaining proof obligation is about n instead of n'.
 *)

#[refine]
Fixpoint half' n : even n -> exists y, twice y = n :=
  match n with
  | O => fun _ => ex_intro _ O eq_refl
  | 1 => fun e => match my_even_proxy' e with end
  | S (S n) => fun e => let (n', e') := my_even_proxy' e in
                        let (h, E) := half' n' e' in
                        ex_intro _ (S h) _
  end.
Fail Guarded.
Check (f_equal (fun x => S (S x)) E : twice (S h) = S (S n')).
Abort.

(** Those issues could be managed by introducing "n = n'" in the return clause
    of the pattern matching of (my_even_proxy' e), and then using transport
    functions from (P n) to (P n'), or conversely, with suitable types P.
    All that effort is saved as soon as you use my_even_proxy instead of
    my_even_proxy'.
*)

(* ================================================================== *)
(** * Chapter 6: more advanced example(s) *)

(** In this chapter we consider a more interesting relation than the above
    nextcolor: the semantics of well-typed expressions.
    We use the source language provided in a seminal paper by Mc Carthy
    and Painter, 1967. *)

(** Internalized Basic Types *)
Variant ty : Set := Nat | Bool.

Definition value t : Set :=
  match t with
  | Bool => bool
  | Nat => nat
  end.

(** Untyped expressions, with
    constants, addition and if-then-else expressions *)
Inductive exp : Set :=
| Cst t (v : value t) : exp
| Plus (e1 e2 : exp) : exp
| Ifte (b : exp) (e1 e2 : exp) : exp.

(** A binary relation between expressions and types:
    (well_typed e t) means that expression e is weel-typed with type t *)
Inductive well_typed : exp -> ty -> Prop :=
| WTCst t (v : value t) : well_typed (Cst t v) t
| WTPlus (e1 e2 : exp) :
  well_typed e1 Nat -> well_typed e2 Nat ->
  well_typed (Plus e1 e2) Nat
| WTIfte (eb : exp) (e1 e2 : exp) (t : ty) :
  well_typed eb Bool -> well_typed e1 t -> well_typed e2 t ->
  well_typed (Ifte eb e1 e2) t.


(** As for nextcolor, we will need to perform case analyses
    on asssumptions of type (well_typed e t) where e is constructed,
    but t is a variable *)
Unset Elimination Schemes (* For comfort *).
Derive InvProxy for well_typed with index 0.
(** Making some arguments implicit for later usage *)
Arguments WTCst_Cst {_ _}.
Arguments WTPlus_Plus {_ _}.
Arguments well_typed_Plus {_ _} _.
Arguments well_typed_proxy {_ _} _.
Set Elimination Schemes (* For comfort *).

(** A semantics of well-typed expressions can be defined by recursion
    on expressions, then small inversion on well-typing.
    Note that here, both the tactic inversion and dependent
    elimination of Equations fail (complicated workarounds are
    possible, but PBSI behaves much better).
    For convenience, we first write a draft version in interactive mode,
    in order to highlight the effect of inversions.
    But it would be bad practice to consider this version as the definitive
    one, see below. *)

Module Script.

#[refine]
Fixpoint semE {t} (e : exp) : well_typed e t -> value t :=
  match e with
  | Cst t' v => fun w =>  _
  | Plus e1 e2 => fun w =>  _
  | Ifte eb e1 e2 => fun w => _
  end.
- (* we want to retun a (value t), which is essentially (v : value t');
  by inversion of w, we know that i is t'. *)
  sinv w. exact v.
- (* similarly, t is Nat by inversion of w, that also provides
     useful assumptions about e1 and e2 *)
  Fail inversion w (* standard inversion fails *).
  sinv w as [w1 w2].
  exact (semE _ e1 w1 + semE _ e2 w2).
- (* Here, by inversion of w, we get useful assumptions
     about eb, e1 and e2. *)
  Fail inversion w (* Once again, standard inversion fails *).
  sinv w as [wb w1 w2].
  exact (if semE _ eb wb then semE _ e1 w1 else semE _ e2 w2).
Defined.

End Script.

(** Note that defining a function that can be used later in the statement
    of theorems is BAD PRACTICE, because the meaning of such theorems
    comes from the very body of the program that defines the function.
    In this case, semE could be used to state the correctness of a compiler.
    But the above definition uses tactics, whereas the tactic language
    is NOT in the TCB of Rocq and does not have a properly defined semantic.
    Fortunately PBSI can be used directly.
    First, we can use "invproxy w" with additional information. *)



Unset Elimination Schemes (* For comfort *).
Derive Dependent InvProxy for well_typed with index 0.
(** Making some arguments implicit for later usage *)
Arguments well_typed_dproxy {_ _} _.
Set Elimination Schemes (* For comfort *).

(** Advanced usage of PBSI *)
Fixpoint semE {t} (e : exp) : well_typed e t -> value t :=
  match e with
  | Cst t' v => fun w =>
      let 'WTCst_Cst := well_typed_proxy w in v
  | Plus e1 e2 => fun w =>
      let 'WTPlus_Plus w1 w2 in well_typed_Plus t := well_typed_proxy w return value t
      in semE e1 w1 + semE e2 w2
  | Ifte eb e1 e2 => fun w =>
      let (wb, w1, w2) := well_typed_proxy w
      in if semE eb wb then semE e1 w1 else semE e2 w2
  end.

(* ================================================================== *)
(** * Chapter 7: advanced tuning of PBSI *)

(** Or: customizing proxies using "with pattern" *)

(** An alternative definition for the less or equal relation on natural numbers.
   As for nextcolor above, we have two interesting indices;
   but their type is nat, so that more patterns on could be considered. *)

Inductive le2 : nat -> nat -> Prop :=
| L0 : forall m, le2 0 m
| LS : forall n m, le2 n m -> le2 (S n) (S m).

Definition FAKE := Prop.

Unset Elimination Schemes.
Derive InvProxy for le2.
Set Elimination Schemes.

(** By default, the Derive InvProxy command build proxies for the
    situations where the two indices are constructed.
    However this is not relevant in the Lemma le2_n_1_small below,
    where, as in nextcolor3, only the second index is constructed.
    Additionally, the shape of the second index is very specific.
 *)


Lemma le2_n_1_small n : le2 n 1 -> n = 0 \/ n = 1.
Proof.
  intro l.
  Fail sinv l (*the default proxy is not relevant here *).
Abort.

(* Let us restart just before the definition of FAKE.*)
Reset FAKE.

(** We actually need an accurate proxy, that can be obtained using
    the algebraic type inversion_pattern that specifies a relevant pattern
    of indices. *)
Print inversion_pattern.

(* This is the type of the argument to be put after the keywords "with pattern"
   in the command "Derive InvProxy".
   The term (pilotInversion n l) indicates that we ask for an inversion on index
   number n, where l is a list that recursively specifies the kind of pattern matching
   to be performed deeper for this index. Note that the length of list must be exactly
   the nummber of partial algebraic types, and that the index position must take
   parameters into account.
   In our example, the desired proxy is generated by the following command.
   We indicate below how to get this command without effort.
 *)
Unset Elimination Schemes.
Derive InvProxy for le2
  with pattern(pilotInversion 1 [noInversion; pilotInversion 1 [noInversion; noInversion]]).
Set Elimination Schemes.

(** Now, sinv will work. *)
Lemma le2_n_1_small n : le2 n 1 -> n = 0 \/ n = 1.
Proof.
  intro l.
  sinv l as [ | n l'].
  - left; reflexivity.
  - right; sinv l'; reflexivity.
Qed.

(** As finding the correct pattern is not straightforward, we also provide the
    command "Create_sinv_call y" that, for a given algebraically typed term y,
    prints an invocation to "Derive InvProxy" with a suitable pattern for this y.
    It can only be used in interactive proof mode.
    Let us restart just before the definition of FAKE. *)

Reset FAKE.

Lemma le2_n_1_small n : le2 n 1 -> n = 0 \/ n = 1.
Proof.
  intro l.
  Create_sinv_call l.
  (* We get :
Derive InvProxy for le2 with pattern (pilotInversion 1 [noInversion; pilotInversion 1 [noInversion; noInversion]]).
  We just copy and paste it.
   *)

Unset Elimination Schemes.
Derive InvProxy for le2 with pattern (pilotInversion 1 [noInversion; pilotInversion 1 [noInversion; noInversion]]).
Set Elimination Schemes.
  sinv l as [ | n l'].
  - left; reflexivity.
  - right; sinv l'; reflexivity.
Qed.

(** It is better practice to define the proxy before its use in le2_n_1_small.
    The definitive script could be as follows. *)

Reset FAKE.

Unset Elimination Schemes.
Derive InvProxy for le2 with pattern (pilotInversion 1 [noInversion; pilotInversion 1 [noInversion; noInversion]]).
Set Elimination Schemes.

Lemma le2_n_1_small n : le2 n 1 -> n = 0 \/ n = 1.
Proof.
  intro l.
  sinv l as [ | n l'].
  - left; reflexivity.
  - right; sinv l'; reflexivity.
Qed.
