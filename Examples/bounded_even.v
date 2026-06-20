(** Author: Jean-François Monin, Verimag, Université Grenoble Alpes *)

(** Even bounded natural numbers *)
(** Illustrates proxy-based small inversion with an indexed indice 
*)

From Stdlib Require Import Utf8.

(* ------------------------------------------ *)
(* Bounded natural numbers (as usual)         *)

Inductive bn : nat → Set :=
| BO : ∀ {n}, bn (S n)
| BS : ∀ {n}, bn n → bn (S n).

(* Proxy-based dependent samll inversion
  (Can be derived automatically)         *)     
Variant bn_O_dep : bn O → Set := .
Variant bn_S_dep n : bn (S n) → Set :=
| BO_S_dep : bn_S_dep n (@BO n)
| BS_S_dep (i : bn n) : bn_S_dep n (BS i).

Definition bn_sdinv_type {n} : bn n → Set :=
  match n with
  | O => bn_O_dep
  | S n => bn_S_dep n
  end.

Definition bn_sdinv {n} (i : bn n) : bn_sdinv_type i :=
  match i with
  | @BO n => BO_S_dep n
  | BS i => BS_S_dep _ i
  end.

(** ------------------------------------------------------------ *)
(** Addition on (bn n) and (bn m), to be used below in the
    statement of Lemma even_plus_left *)

(** An administrative transfer function (or coercion) *)

Definition bn_n_Sm {n m} (i: bn (S (m + n))) : bn (m + S n) :=
  match plus_n_Sm m n in (_ = n0) return (bn n0) with
  | eq_refl => i
  end.

Fixpoint transfer1 m {n} (i : bn n) : bn (m + n) :=
  match i in bn n return bn (m + n) with
  | BO => bn_n_Sm BO
  | BS i => bn_n_Sm (BS (transfer1 m i))
  end.

Fixpoint Fplus {n m : nat} (i : bn n) (j : bn m) : bn (n + m) :=
  match i with
  | @BO n => transfer1 (S n) j
  | BS i => BS (Fplus i j)
  end.

(** ------------------------------------------------------------ *)
(** * Inductive definition of even bounded numbers *)
Inductive even : ∀ {n}, bn n → Prop :=
| even_0 {n} :           even (@BO n)
| even_2 {n} (i: bn n) : even i → even (BS (BS i)).

(** Dependent small inversion *)
Variant even_BO_dep {n} : even (@BO n) → Prop :=
   | even_0_BO_dep : even_BO_dep even_0.
Variant even_BS_BO_dep {n} : even (BS (@BO n)) → Prop := .
Variant even_BS_BS_dep {n} (i: bn n) : even (BS (BS i)) → Prop :=
   | even_2_BS_BS_dep (e : even i) : even_BS_BS_dep i (even_2 i e).

(* We have two methods for the proxy type and then the proxy itself *)

(* Method 1, "index-first" : by pattern-matching on the first index n,
   and then by dependent inversion on the second index i.
   This is mainly for illustration, because when the second
   method works, the code is shorter. *)

Definition even_sdinv_idx1_type {n} : ∀ {i : bn n}, even i → Prop :=
  match n with
  | O => λ i, match bn_sdinv i with end

  | S O => λ i,
      match bn_sdinv i in bn_S_dep _ i return even i → Prop with
      | BO_S_dep _ => even_BO_dep
      | BS_S_dep _ i => match bn_sdinv i with end
      end

  | S (S n) => λ i,
      match bn_sdinv i in bn_S_dep _ i return even i → Prop with
      | BO_S_dep _ => even_BO_dep
      | BS_S_dep _ i =>
          match bn_sdinv i in bn_S_dep _ i return even (BS i) → Prop with
          | BO_S_dep _ => even_BS_BO_dep
          | BS_S_dep _ i => even_BS_BS_dep i
          end
      end
  end.

Definition even_sdinv_idx1 {n} {i : bn n} (e : even i) : even_sdinv_idx1_type e :=
  match e with
  | @even_0 n =>
      match n with
      | O => even_0_BO_dep
      | S n => even_0_BO_dep
      end
  | even_2 i e => even_2_BS_BS_dep i e
  end.

(* Method 2, directly by pattern-matching on the second index i *)

Definition even_sdinv_idx2_type {n} {i : bn n} : even i → Prop :=
  match i return even i → Prop with
  | @BO n => even_BO_dep
  | BS i =>
      match i return even (BS i) → Prop with
      | @BO n => even_BS_BO_dep
      | BS i => even_BS_BS_dep i
      end
  end.

Definition even_sdinv_idx2 {n} {i : bn n} (e : even i) : even_sdinv_idx2_type e :=
  match e with
  | even_0 => even_0_BO_dep
  | even_2 i e => even_2_BS_BS_dep i e
  end.

(* You can replace idx1 by idx2 on the next line. *)
Definition even_sdinv {n} {i : bn n} (e : even i) := even_sdinv_idx1 e.

(** ------------------------------------------------------------ *)
(** * Simple Applications *)

(** The basic one *)
Lemma even_2_inv : forall n (i: bn n), even (BS (BS i)) → even i.
Proof.
  intros n i e.
  destruct (even_sdinv e) as [e]. exact e.
Qed.

(** Additions and even numbers. *)

(** We show [even (i + j) → even i → even j] on bounded natural numbers.
 *)

Fixpoint even_transfer1 m {n} {i: bn n} : even (transfer1 m i) → even i.
Proof.
  intro e.
  destruct i as [ | n i]; simpl in e.
  - constructor 1.
  - destruct i as [ | n i]; cbn in e;
      unfold bn_n_Sm in e; repeat rewrite <- plus_n_Sm in e; cbn in e.
    + destruct (even_sdinv e).
    + destruct (even_sdinv e) as [e]. constructor 2. apply (even_transfer1 m n i e).
Qed.

Lemma even_plus_left n m (i: bn n) (j: bn m) : even (Fplus i j) → even i → even j.
Proof.
  intros eij ei.
  induction ei as [ | n i ei IHei]; simpl in eij.
  - apply (even_transfer1 (S n) eij).
  - destruct (even_sdinv eij) as [eij]. exact (IHei eij).
Qed.

(** Remark: another coercion function can be defined as well. *)

Fixpoint transfer2 {n} (i : bn n) m : bn (n + m) :=
  match i in bn n return bn (n + m) with
  | BO => BO
  | BS i => BS (transfer2 i m)
  end.

Fixpoint even_transfer2 {n} (i: bn n) : forall m, even (transfer2 i m) → even i :=
  match i with
  | @BO n => λ m e, even_0
  | BS i => match i with
            | @BO n => λ m e, match even_sdinv e with end
            | BS i =>  λ m e, let (e) := even_sdinv e in
                              even_2 i (even_transfer2 i m e)
            end
  end.

(* In interactive mode *)
Fixpoint even_transfer2_script {n} (i: bn n) : forall m, even (transfer2 i m) → even i.
Proof.
  intros m e.
  destruct i as [ | n i]; simpl in e.
  - constructor 1.
  - destruct i as [ | n i]; simpl in e.
    + destruct (even_sdinv e).
    + destruct (even_sdinv e) as [e]. constructor 2. apply (even_transfer2_script n i m e).
Qed.
