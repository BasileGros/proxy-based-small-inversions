(** Author: Jean-François Monin, Verimag, Université Grenoble Alpes *)

(** Even bounded natural numbers *)
(** Illustrates proxy-based small inversion with an indexed index
*)

From Stdlib Require Import Utf8.

(* ------------------------------------------ *)
(* Bounded natural numbers (as usual)         *)

Inductive bn : nat → Set :=
| BO : ∀ {n}, bn (S n)
| BS : ∀ {n}, bn n → bn (S n).

(* Proxy-based dependent small inversion
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

(* Method 1, "index-first" : by pattern-matching on the first index n
   (here we have a "second order" inversion)
   and then by dependent inversion on the second index i.
   This is mainly for illustration, because when the second
   method works, the code is shorter.
   However, a seemingly inocuous more precise typing of even
   changes many things: see even' below.
   In particular, a "second order" inversion becomes unavoidable.
 *)

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
    + destruct (even_sdinv e) as [e]. constructor 2.
      apply (even_transfer2_script n i m e).
Qed.

(* ====================================================================== *)
(* The following version of even with a more precise typing
   requires more work:
   - "second order inversions" in the proxy type are mandatory
   - in order to prove the transfer lemma, we use a general approach
     based on a bisimulation relation to be inverted as well.
 *)


Inductive even' : ∀ {n}, bn (S n) → Prop :=
| even'_0 {n} :           even' (@BO n)
| even'_2 {n} (i : bn (S n)) : even' i → even' (BS (BS i)).

(* We check that even and even' are equivalent on positive n *)

Lemma even'_even {n} (i : bn (S n)) (e : even' i) : even i.
Proof.
  induction e as [ n' | n' i e He].
  - constructor 1.
  - constructor 2. apply He.
Qed.

(* A proof by induction for the converse does not work,
   because the underlying pattern-matching is not accurate enough.
   We use the elaborated guard-safe PM based on 2010 small inversion *)
Fixpoint even_even' {n} (i : bn (S n)) (e : even i) : even' i :=
  match e with
  | even_0 => even'_0
  | @even_2 n i e =>
      match n return (∀ i : bn n, even i → even' (BS (BS i))) with
      | O => λ i e, match bn_sdinv i with end
      | S n => λ i e, even'_2 i (even_even' i e)
      end i e
  end.

(** Small inversion *)
Variant even'_BO_dep {n} : even' (@BO n) → Prop :=
   | even'_0_BO_dep : even'_BO_dep even'_0.
Variant even'_BS_BO_dep {n} : even' (BS (@BO n)) → Prop := .
Variant even'_BS_BS_dep {n} (i : bn (S n)) : even' (BS (BS i)) → Prop :=
   | even'_2_BS_BS_dep (e : even' i) : even'_BS_BS_dep i (even'_2 i e).

(* Pattern-matching on the second index i also requires
   "second order" inversions *)

Definition even'_sdinv_type {n} {i : bn (S n)} : even' i → Prop :=
  match bn_sdinv i with
  | BO_S_dep _ => even'_BO_dep
  | BS_S_dep _ i =>
      match n return ∀ i : bn n, even' (BS i) → Prop with
      | O => λ i, match bn_sdinv i in bn_O_dep i with end
      | S n => λ i,
          match bn_sdinv i with
          | BO_S_dep _ => even'_BS_BO_dep
          | BS_S_dep _ i =>
              match n return ∀ i : bn n, even' (BS (BS i)) → Prop with
              | O => λ i, match bn_sdinv i in bn_O_dep i with end
              | S n => even'_BS_BS_dep
              end i
          end
      end i
  end.

Definition even'_sdinv {n} {i : bn (S n)} (e : even' i) : even'_sdinv_type e :=
  match e with
  | even'_0 => even'_0_BO_dep
  | even'_2 i e => even'_2_BS_BS_dep i e
  end.


(** ------------------------------------------------------------ *)
(** * Simple Applications *)

(** The basic one *)
Lemma even'_2_inv : forall n (i : bn (S n)), even' (BS (BS i)) → even' i.
Proof.
  intros n i e.
  destruct (even'_sdinv e) as [e]. exact e.
Qed.

(** ------------------------------------------------------------ *)
(** bisimilarity relation on bn, useful in even'_transfer1|2 *)

Inductive bn_bisim : ∀ {n} (i : bn n) {m} (j : bn m), Prop :=
| bBO : ∀ n m, bn_bisim (@BO n) (@BO m)
| bBS : ∀ n (i : bn n) m (j : bn m), bn_bisim i j → bn_bisim (BS i) (BS j).

(* Small inversion on i *)
Variant bn_bisim_BO : ∀ m, bn m → Prop :=
  | bBO_BO m : bn_bisim_BO (S m) BO.
Variant bn_bisim_BS n (i : bn n) : ∀ m, bn m → Prop :=
  | bBS_BS m (j : bn m) : bn_bisim i j → bn_bisim_BS n i (S m) (BS j).

Definition bn_bisim_sinv2_type {n} (i : bn n) : ∀ m, bn m → Prop :=
  match i with
  | BO => bn_bisim_BO
  | BS i => bn_bisim_BS _ i
  end.
Definition bn_bisim_sinv2 {n m} {i : bn n} {j : bn m}
  (bb : bn_bisim i j) : bn_bisim_sinv2_type i _ j :=
  match bb with
  | bBO n m => bBO_BO m
  | bBS n i m j bb => bBS_BS n i m j bb
  end.

(* Small inversion on i and m *)
Variant bn_bisim_BO_S m : bn (S m) → Prop :=
  | bBO_BO_S : bn_bisim_BO_S m BO.
Variant bn_bisim_BS_S n (i : bn n) m : bn (S m) → Prop :=
  | bBS_BS_S (j : bn m) : bn_bisim i j → bn_bisim_BS_S n i m (BS j).
Definition bn_bisim_sinv23_type {n} (i : bn n) m : bn m → Prop :=
  match i with
  | BO =>
      match m with
      | O => λ j, False
      | S m => bn_bisim_BO_S m
      end
  | BS i =>
      match m with
      | O => λ j, False
      | S m => bn_bisim_BS_S _ i m
      end
  end.
Definition bn_bisim_sinv23 {n m} {i : bn n} {j : bn m}
  (bb : bn_bisim i j) : bn_bisim_sinv23_type i _ j :=
  match bb with
  | bBO n m => bBO_BO_S m
  | bBS n i m j bb => bBS_BS_S n i m j bb
  end.
(* *)

Lemma transfer1_bisim m {n} (i : bn n) : bn_bisim (transfer1 m i) i.
Proof.
  induction i as [ | n i Hi]; cbn.
  - unfold bn_n_Sm. rewrite <- plus_n_Sm. apply bBO.
  - unfold bn_n_Sm. rewrite <- plus_n_Sm. apply bBS. apply Hi.
Qed.


Lemma even'_bisim m {n} {i : bn (S n)} {j : bn (S m)} :
  even' j → bn_bisim j i → even' i.
Proof.
  intro e. revert n i. induction e as [ m | m j e He]; intros n i bb.
  - destruct (bn_bisim_sinv23 bb). constructor 1.
  - destruct (bn_bisim_sinv23 bb) as [i bb']; clear bb.
    destruct (bn_bisim_sinv2 bb') as [n i bb'']; clear bb'.
    destruct n as [ | n].
    + case (bn_sdinv i).
    + constructor 2. apply (He n i bb'').
Qed.

Corollary even'_transfer1 m {n} {i : bn (S n)} : even' (transfer1 (S m) i) → even' i.
Proof.
  intro e. apply (even'_bisim _ e). exact (transfer1_bisim (S m) i).
Qed.

Lemma even'_plus_left n m (i: bn (S n)) (j: bn (S m)) :
  even' (Fplus i j) → even' i → even' j.
Proof.
  intros eij ei.
  induction ei as [ | n i ei IHei]; simpl in eij.
  - apply (even'_transfer1 n eij).
  - destruct (even'_sdinv eij) as [eij]. exact (IHei eij).
Qed.

(* Easier than for transfer1 *)
Lemma transfer2_bisim m {n} (i : bn n) : bn_bisim (transfer2 i m) i.
Proof.
  induction i as [ | n i Hi]; cbn.
  - apply bBO.
  - apply bBS. apply Hi.
Qed.

Corollary even'_transfer2 m {n} {i : bn (S n)} : even' (transfer2 i m) → even' i.
Proof.
  intro e. apply (even'_bisim _ e). exact (transfer2_bisim m i).
Qed.
