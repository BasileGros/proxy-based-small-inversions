From Examples Require Import examples_header.
(* ====================================================================== *)

(* More advanced examples on vectors, matrices and bounded nats.
   In this exercise we define the transposition of matrices
   (in two ways), and prove that transposition is involutive. *)


(* In order to allow ∀ and λ notations *)
From Stdlib Require Import Utf8.



Inductive vect (A : Type) : nat -> Type :=
| nil : vect A 0
| cons : A -> forall n : nat, vect A n -> vect A (S n).

Unset Elimination Schemes (* For comfort *).

Derive InvProxy for vect.
(* vect_O vect_S *)
Derive Dependent InvProxy for vect.
(* vect_O_dep vect_S_dep *)
Set Elimination Schemes.



Arguments cons {A} _ {n}.
Arguments nil {A}.

Notation "[ ]" := nil (format "[ ]").
Notation "x :: v" := (cons x v).
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

(* ------------------------------------------ *)
(* Renaming finite sets into bounded nat : *)

Inductive bn : nat → Set :=
| BO : ∀ {n}, bn (S n)
| BS : ∀ {n}, bn n → bn (S n).


Derive InvProxy for bn.
(* bn_O bn_S *)
Derive Dependent InvProxy for bn.
(* bn_O_dep bn_S_dep *)


(* ------------------------------------------ *)

(* For convenience *)
Notation proxy_vectS u := (invproxy u : vect_S _ _).

Definition atVect {A n} (u : vect A n) : bn n → A :=
  λ i,
  (fix loop {n} (i : bn n) {struct i} :=
  match i in bn n return vect A n → A with
  | BO    => λ u, let (x, _) := proxy_vectS u in x
  | BS i' => λ u, let (_, u') := proxy_vectS u in loop i' u'
  end) n i u.

Definition mkVect {A} : ∀ {n}, (bn n → A) → vect A n :=
  fix loop n :=
    match n with
    | O => λ f, []
    | S n' => λ f, f BO :: loop n' (λ i, f (BS i))
    end.

Lemma atVect_mkVect {A n} (f : bn n → A) : ∀ i, f i = atVect (mkVect f) i.
Proof.
  induction n as [ | n Hn]; intro i.
  - sinv i.
  - sdinv i as [ | i'].
    + cbn. reflexivity.
    + cbn. exact (Hn _ i').
Qed.

Lemma atVect_extensional {A n} (u v : vect A n) :
  (∀ i, atVect u i = atVect v i) → u = v.
Proof.
  revert n u v.
  fix loop 2. intros n u v e.
  destruct u as [ | x n' u'].
  - sdinv v. reflexivity.
  - sdinv v as [y v'].
    generalize (e BO). cbn. intro e1. case e1. f_equal.
    apply (loop n' u' v'). intro i.
    generalize (e (BS i)). simpl (* better than cbn *).
    intro e'; exact e'.
Qed.

Corollary mkVect_atVect {A n} (v : vect A n) : v = mkVect (atVect v).
Proof.
  apply atVect_extensional; intro i. apply atVect_mkVect.
Qed.

Lemma mkVect_atVect_direct {A n} (v : vect A n) : v = mkVect (atVect v).
Proof.
  induction v as [ | x n v Hv].
  - cbn. reflexivity.
  - cbn [mkVect]. f_equal. simpl.
    apply Hv.
Qed.


(* Alternative definition, avoiding the use of simpl above *)
Fixpoint atVectV {A n} (u : vect A n) {struct u} :  bn n → A :=
  match u with
  | [] => λ i, match invproxy i in bn_O with end (* ballot : faut préciser SP_bn_O *)
  | x :: u' => λ i,
      match invproxy i with
      | BO_S _    => x
      | BS_S _ i' => atVectV u' i'
      end
  end.
(*
  refine
      match proxy i in SP_bn_S _ with
      | SP_BO_S => x
      | SP_BS_S i' => atVectV _ _ u' i' (* BUG AI *)
      end
  .
 *)

Lemma atVectV_mkVect {A n} (f : bn n → A) : ∀ i, f i = atVectV (mkVect f) i.
Proof.
  induction n as [ | n Hn]; intro i.
  - sinv i.
  - sdinv i as [ | i'].
    + cbn. reflexivity.
    + cbn.
      exact (Hn _ i').
Qed.

Lemma mkVect_atVectV {A n} (v : vect A n) : v = mkVect (atVectV v).
Proof.
  induction v as [ | x n v Hv]; cbn.
  - reflexivity.
  - f_equal. apply Hv.
Qed.

Lemma atVectV_extensional {A n} (u v : vect A n) : (∀ i, atVectV u i = atVectV v i) → u = v.
Proof.
  revert n u v. fix loop 2. intros n u v e.
  destruct u as [ | x n' u'].
  - sdinv v. reflexivity.
  - sdinv v as [y v'].
    generalize (e BO). cbn. intro e1. case e1. f_equal.
    apply (loop n' u' v'). intro i.
    generalize (e (BS i)). cbn.
    intro e'; exact e'.
Qed.

(* ====================================================================== *)
(* Matrices *)

(*
     | cW |  matE      |
  ---+----+------------+
  lN | NW |    NE      |
  ---+----+------------+
     |    |            |
     |    |            |
matS | SW |    SE      |
     |    |            |
     |    |            |
  ---+----+------------+

 *)

(* Matrix (m, n) : m lines of n elements (n columns) *)
Definition matrix (A : Type) : nat → nat → Type :=
  λ m n, vect (vect A n) m.

Definition atMat {A m n} (mat : matrix A m n) (i : bn m) (j : bn n) : A :=
  atVect (atVect mat i) j.

Definition mkMat {A m n} (f : bn m → bn n → A) : matrix A m n :=
  mkVect (λ i, mkVect (f i)).

Lemma atMat_mkMat {A m n} (f : bn m → bn n → A) : ∀ i j, f i j = atMat (mkMat f) i j.
Proof.
  intros i j.
  unfold atMat, mkMat.
  case atVect_mkVect.
  case atVect_mkVect.
  reflexivity.
Qed.

Lemma atMat_extensional {A m n} (mat mat' : matrix A m n) :
  (∀ i j, atMat mat i j = atMat mat' i j) → mat = mat'.
Proof.
  intros e.
  apply atVect_extensional; intro i.
  apply atVect_extensional; intro j.
  apply e.
Qed.

Corollary mkMat_atMat {A m n} (mat : matrix A m n) : mat = mkMat (atMat mat).
Proof.
  apply atMat_extensional; intros i j. apply atMat_mkMat.
Qed.


Definition swap {A B C} (f : A → B → C) : B → A → C := λ a b, f b a.

Definition swapMat {A m n} : matrix A m n → matrix A n m :=
  λ mat, mkMat (swap (atMat mat)).

Compute swapMat [[1; 2]; [3; 4]; [5; 6]].

Lemma swapMat_corr {A m n} (mat : matrix A m n) :
  ∀ j i, atMat mat i j = atMat (swapMat mat) j i.
Proof. exact (atMat_mkMat (swap (atMat mat))). Qed.

Corollary swapMat_invol {A m n} (mat : matrix A m n) :
  mat = swapMat (swapMat mat).
Proof.
  apply atMat_extensional; intros i j.
  case swapMat_corr.
  apply swapMat_corr.
Qed.

(* ---------------------------------------------------------------------- *)

Definition transpose_mn {A} : ∀ {m n}, matrix A m n → matrix A n m :=
  fix loopm m :=
    match m return ∀ n, matrix A m n → matrix A n m with
    | O    => λ n _, mkVect (λ _, [])
    | S m' => λ n mat,
        let (lN, matS) := proxy_vectS mat in
        let matS_ := loopm m' n matS in
        (fix loopn n  :=
           match n return
                 vect A n → matrix A n m' → matrix A n (S m') with
           | O    => λ lN matS_, []
           | S n' => λ lN matS_,
               let (NW, NE)   := proxy_vectS lN in
               let (SW_, SE_) := proxy_vectS matS_ in
               (NW :: SW_) :: loopn n' NE SE_
           end
        ) n lN matS_
    end.

Compute transpose_mn [[1; 2]; [3; 4]; [5; 6]].

(* -------------------------------------------------- *)

Definition cons_column {A n} :
  ∀ {m} (u : vect A m), matrix A m n → matrix A m (S n) :=
  fix loop {m} u {struct u} :=
    match u in vect _ m return matrix A m n → matrix A m (S n) with
    | []      => λ mat, []
    | x :: u' => λ mat,
        let (line, mat') := proxy_vectS mat in
        (x :: line) :: loop u' mat'
    end.

Definition transpose {A} : ∀ {m n}, matrix A m n → matrix A n m :=
  fix loop {m n} (mat : matrix A m n) {struct mat} : matrix A n m :=
    match mat in vect _ m return matrix A n m with
    | []       => mkVect (λ _, [])
    | lN :: matS => cons_column lN (loop matS)
    end.

Compute transpose [[1; 2]; [3; 4]; [5; 6]].

Definition at_cons_column {A m n} (u : vect A m) (mat : matrix A m n) :
  bn m → bn (S n) → A := λ i j,
    match j with
    | BO   => λ _, atVect u i
    | BS j' => λ mat, atMat mat i j'
    end mat.

Lemma cons_column_corr {A m n} (u : vect A m) (mat : matrix A m n) :
  ∀ i j, at_cons_column u mat i j = atMat (cons_column u mat) i j.
Proof.
  revert m u mat. fix loop 2. intros m u mat.
  destruct u as [ | x m' u']; intros i j.
  - sinv i.
  - sdinv mat as [line mat'].
    sdinv i as [ | i'].
    + sdinv j as [ | j']; reflexivity.
    + simpl.
      change (atMat (?a :: ?b) (BS ?i) ?j) with (atMat b i j).
      generalize (loop m' u' mat' i' j).
      sdinv j as [ | j']; intro e; exact e.
Qed.

Lemma transpose_corr {A m n} (mat : matrix A m n) :
  ∀ i j, atMat mat i j = atMat (transpose mat) j i.
Proof.
  revert n m mat. fix loop 3. intros n m mat.
  destruct mat as [ | lN m' matS]; intros i j.
  - sinv i.
  - cbn [transpose].
    case cons_column_corr.
    sdinv i as [ | i'].
    + reflexivity.
    + apply (loop _ _ matS).
Qed.

Corollary transpose_swap {A m n} (mat : matrix A m n) : swapMat mat = transpose mat.
Proof.
  apply atMat_extensional; intros i j. case swapMat_corr. apply transpose_corr.
Qed.

Corollary transpose_invol {A m n} (mat : matrix A m n) : mat = transpose (transpose mat).
Proof. do 2 case transpose_swap. apply swapMat_invol. Qed.
