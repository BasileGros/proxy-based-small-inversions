
Inductive even : nat -> Prop :=
| even0 :  even 0
| evenSS : forall (n : nat), even n -> even (S (S n)).

(* Handcrafted small inversions *)
Inductive even_O : Prop :=
| is_even0 : even_O.

Inductive even_S : nat -> Prop :=
| evenSS_S : forall (n:nat), even n -> even_S (S n).

Inductive even_SO : Prop :=.

Inductive even_SS (n : nat) : Prop :=
| is_evenSS : even n -> even_SS n.

Definition even_proxy_type (n : nat) : Prop :=
  match n with
  | 0 => even_O
  | S 0 => even_SO
  | S (S n) => even_SS n
  end.

Definition even_proxy (n : nat) (r : even n) :=
  match r in even n' return even_proxy_type n' with
  | even0 => is_even0
  | evenSS n r => is_evenSS n r
  end.

(* *)

(* Use case *)
Lemma add_2_even (n:nat) : even (2 + n) -> even n.
Proof.
  intro e.
  destruct (even_proxy _ e) as [en].
  exact en.
  Show Proof.
Qed.

(* Automated small inversions *)
From Examples Require Import examples_header.

Fail Derive InvProxy for even.
(* prefix to avoid name collision *)
Derive InvProxy for even with prefix "_".

Lemma add_2_even' (n:nat) : even (2 + n) -> even n.
Proof.
  intro e.
  sinv e as [en].
  exact en.
Show Proof.
Qed.

