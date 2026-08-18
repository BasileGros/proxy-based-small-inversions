(** A tutorial on automated proxy-based small inversions (PBSI) *)

(** First, get the plugin for PBSI *)

From SmallInversion Require Import small_inversion.

(* ================================================================== *)
(** * Basics *)

(** Proxy-based small inversions derive specialised versions of an
inductive type $T$ according to the values (more precisely, the
patterns) of the inductive indices of $T$, so that filtering on a term
of type $T$ takes into account its particular form, i.e., the
constructors used in its indices.

They work in two steps:

- First, defining suitable partial inductive types, which mimic the
  original inductive type $T$ depending on constructors used for one
  or more of its indices. A mapping from $T$ to the new partial
  inductive types is also defined. The partial inductive types
  together with this mapping act as a proxy for $T$.  This step only
  needs to be performed once.

- Second, inverting a object. It consists in decomposing a relevant
  proxy for it, using the `destruct` tactic (in interactive mode) or a
  pattern matching (when defining a dependently typed functional
  program).

Both of those steps are supported by automated tools, the first by
various commands that customise the specialisation of the original
inductive type into partial inductive types, the second in the form of
tactics to be called in interactive mode.
*)

(* ==================================================================
*) (** * Chapter 1: using PBSI in interactive proof mode *)

(** Here, PBSI is used as an alternative to the well-known inversion
    tactic *)

(** A simple predicate on natural numbers *)

Inductive even : nat -> Prop :=
| even0 : even 0
| even2 : forall (n : nat), even n -> even (S (S n)).

(** Inversion is needed when we have assumptions (even X), where X is
    not a variable but, for instance O, (S O), (S (S ...)) *)

(** The following comand is needed in order to have PBSI for even.
    Its effect is to define some auxiliary inductive types derived
    from the definition of even, as well as a proxy function for even
    called even_proxy (by default).  "Unset/Set Elimination Schemes"
    is not mandatory, it justs makes the output cleaner.  *)

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for even.
Set Elimination Schemes (* For comfort *).

(** You can then replace "inversion" by our tactic "sinv". *)
Lemma even_cancel_S_S_draft n : even (S (S n)) -> even n.
Proof. intro e. sinv e. exact H. Qed.

(** A better practice is to have an explicit name for the H above.
    The syntax is the same as for destruct *)
Lemma even_cancel_S_S n : even (S (S n)) -> even n.
Proof. intro e. sinv e as [e']. exact e'. Qed.

(** An absurd hypothesis *) Lemma no_even_1 : even 1 -> False.
Proof. intro e. sinv e. Qed.

(** A more interesting lemma, where an induction on even is followed
    by an inversion *)
Lemma even_plus_cancel n m : even n -> even (n + m) -> even m.
Proof.
  induction 1 as [ | n en Hen]; cbn; intro enm.
  - exact enm.
  - (* inversion needed*) sinv enm as [enm']. exact (Hen enm').
Qed.

(** Explanation: sinv is actually a destruct on the proxy for
    even. This is hidden by using Rocq Classes, but we can show the
    explicit mechanism by defining a handcrafted version of
    even_proxy.  We remember the output of "Derive InvProxy for even."
    even_O is defined even_S_O is defined even_S_S is defined
    even_proxy is defined *)

Print even_O (* even x when x is O *).
Print even_S_O (* even x when x is (S O) *).
Print even_S_S (* even x when x is (S (S n) *).
(*
Inductive even_S_S (n : nat) : Prop :=
 even2_S_S : even n -> even_S_Sn. *)
Print even_proxy.

(** The latter can be made more readable as follows *)

(** Handcrafted version of the type of even_proxy *)
Definition even_proxy_type n :=
  match n with
  | 0 => even_O
  | 1 => even_S_O | S (S n) => even_S_S n
  end.

(** Handcrafted version of even_proxy *)
Definition my_even_proxy {n} (e : even n) : even_proxy_type n :=
  match e with
  | even0 => even0_O
  | even2 n x => even2_S_S n x
  end.

Lemma even_cancel_S_S_handcrafted n : even (S (S n)) -> even n.
Proof.
  intro e.
  Check (my_even_proxy e).
  Eval cbn in (even_proxy_type (S (S n))).
  Check (my_even_proxy e : even_S_S n).
  destruct (my_even_proxy e) as [e'].
  exact e'.
Qed.

(** An example with a binary relation R, with an assumption R x y
    where x is known but y is free.
    Indices are numbered from 0 : 0, 1, ...
    Then we will use Derive InvProxy for Rwith index 0.  *)

Inductive color := Red | Orange | Green.

Inductive nextcolor : color -> color -> Prop :=
| ncGO : nextcolor Green Orange
| ncOR : nextcolor Orange Red
| ncRG : nextcolor Red Green.

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for nextcolor with index 0.
Set Elimination Schemes (* For comfort *).

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
    sinv nc2.  (* Similarly for nc3 *)
    sinv nc3. reflexivity.
   (* The remaining subgoals are proved in the same way *)
  - sinv nc2; sinv nc3; reflexivity.
  - sinv nc2; sinv nc3; reflexivity.
Qed.

(* ================================================================== *)
(** * Chapter 2: using PBSI in dependtly typed functions *)

(* ================================================================== *)
(** * Chapter 3: tuning PBSI *)

(* ================================================================== *)
(** * Chapter 4: making your developement independent from our plugin *)
