From SmallInversion Require Import small_inversion.
(* ====================================================================== *)

(* More advanced examples on vectors, matrices and bounded nats.
   In this exercise we define the transposition of matrices
   (in two ways), and prove that transposition is involutive. *)


(* In order to allow ∀ and λ notations *)
From Stdlib Require Import Utf8.

(* ------------------------------------------ *)
(* Renaming finite sets into bounded nat : *)

Inductive bn : nat → Set :=
| BO : ∀ {n}, bn (S n)
| BS : ∀ {n}, bn n → bn (S n).


Derive InvProxy for bn.
(* bn_O bn_S *)
Derive Dependent InvProxy for bn.
(* bn_O_dep bn_S_dep *)


(* cons with n as first index is more convenient *)
Inductive vect (A : Type) : nat -> Type :=
| nil : vect A 0
| cons : ∀ n, A → vect A n → vect A (S n).

Unset Elimination Schemes (* For comfort *).

Derive InvProxy for vect.
(* vect_O vect_S *)
Derive Dependent InvProxy for vect.
(* vect_O_dep vect_S_dep *)
Set Elimination Schemes.

Arguments cons {A} {n} _.
Arguments nil {A}.

Notation "[ ]" := nil (format "[ ]").
Notation "x :: v" := (cons x v).
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

(* For convenience *)
Notation proxy_vectS u := (invproxy u : vect_S _ _).

(* ====================================================================== *)
(* Functional implementation of vectors *)

Definition fvect (A : Type) : nat -> Type := λ n, bn n → A.

(* From vectors to functional vectors... *)
Fixpoint ith {A n} (u : vect A n) : fvect A n :=
  match u with
  | []      => λ i, match invproxy i : bn_O with end
  | x :: u' => λ i, match invproxy i with
                    | BO_S _    => x
                    | BS_S _ i' => ith u' i'
                    end
  end.

Tactic Notation "simpl_ith" :=
  change (ith (?x :: ?u) BO) with x ||
  change (ith (?x :: ?u) (BS ?i')) with (ith u i').

Tactic Notation "simpl_ith_in" hyp(H) :=
  change (ith (?x :: ?u) BO) with x in H ||
  change (ith (?x :: ?u) (BS ?i')) with (ith u i') in H.

(* ... and conversely *)
Definition mkVect {A} : ∀ {n}, fvect A n → vect A n :=
  fix loop n :=
    match n with
    | O    => λ f, []
    | S n' => λ f, f BO :: loop n' (f ∘ BS)
    end.

Ltac simpl_mkVect :=
  change (mkVect ?f) with [] ||
  change (mkVect ?f) with (f BO :: mkVect (f ∘ BS)).

(* [ith] is extensionally the left inverse of [mkVect] *)
Lemma ith_mkVect {A n} (fv : fvect A n) : ∀ i, fv i = ith (mkVect fv) i.
Proof.
  induction n as [ | n Hn]; intro i.
  - sinv i.
  - sdinv i as [ | i']; simpl_mkVect; simpl_ith.
    + reflexivity.
    + exact (Hn _ i').
Qed.

(* Then [ith] is extensional *)
Lemma ith_extensional {A n} (u v : vect A n) :
  (∀ i, ith u i = ith v i) → u = v.
Proof.
  revert v; induction u as [ | x n u' Hu']; intros v e.
  - sdinv v. reflexivity.
  - sdinv v as [y v'].
    generalize (e BO). cbn. intro e1. f_equal; [ exact e1 | ].
    apply (Hu' v'); intro i. specialize (e (BS i)). simpl_ith_in e.
    exact e.
Qed.

(* Then mkVect is the left inverse of ith *)
Corollary mkVect_ith {A n} (v : vect A n) : v = mkVect (ith v).
Proof.
  apply ith_extensional; intro i. apply ith_mkVect.
Qed.

(* ====================================================================== *)

Definition vect_cst {A} (a : A) {n} : vect A n := mkVect (λ i, a).

(* Equivalent definition that produces more readable goals *)
Definition map0 {A} (a : A) : ∀ n, vect A n:=
  fix loop n :=  match n with  O => [] | S n' => a :: loop n' end.

Definition map2 {A B C} (f : A → B → C) :
  ∀ {n}, vect A n → vect B n → vect C n :=
  fix loop _ (u : vect A _) :=
    match u with
    | []      => λ v, []
    | x :: u' => λ v,
        let (y, v') := proxy_vectS v in
        f x y :: loop _ u' v'
    end.

Ltac simpl_map2 :=
  change (map2 ?op (?x :: ?u) (?y :: ?v)) with (op x y :: map2 op u v).

(* ====================================================================== *)
(* Matrices *)

(* Matrix (m, n) : m lines of n elements (n columns) *)
Definition matrix (A : Type) : nat → nat → Type :=
  λ m n, vect (vect A n) m.

(* ====================================================================== *)
(* Functional representation of matrices *)

Definition fmatrix (A : Type) (m n : nat) :=
  bn m → bn n → A.

(* From matrices to functional matrices... *)
Definition ijth {A m n} (mat : matrix A m n) : fmatrix A m n :=
  λ i j, ith (ith mat i) j.
Ltac fold_ijth := change (ith (ith ?mat ?i) ?j) with (ijth mat i j).
Ltac simpl_ijth :=
  change (ijth (?a :: ?b) BO ?j) with (ith a j) ||
  change (ijth (?a :: ?b) (BS ?i) ?j) with (ijth b i j).

(* ... and conversely *)
Definition mkMat {A m n} (f : bn m → bn n → A) : matrix A m n :=
  mkVect (λ i, mkVect (f i)).

(* [ijth] is extensionally the left inverse of [mkMat] *)
Lemma ijth_mkMat {A m n} (f : fmatrix A m n) :
  ∀ i j, f i j = ijth (mkMat f) i j.
Proof.
  intros i j. unfold ijth, mkMat.
  do 2 case ith_mkVect. reflexivity.
Qed.

(* Then [ijth] is extensional *)
Lemma ijth_extensional {A m n} (mat mat' : matrix A m n) :
  (∀ i j, ijth mat i j = ijth mat' i j) → mat = mat'.
Proof.
  intro e. do 2 (apply ith_extensional; intro). fold_ijth. apply e.
Qed.

(* Then mkMat is the left inverse of ijth *)
Corollary mkMat_ijth {A m n} (mat : matrix A m n) :
  mat = mkMat (ijth mat).
Proof. apply ijth_extensional, ijth_mkMat. Qed.

(* ====================================================================== *)

(* Transposition on a functional matrix, easy but quadratic complexity *)

Definition swap {X Y Z} (f : X → Y → Z) : Y → X → Z := λ x y, f y x.

Definition ftranspose {A m n} : matrix A m n → matrix A n m :=
  λ mat, mkMat (swap (ijth mat)).

Compute ftranspose [[1; 2]; [3; 4]; [5; 6]].

Lemma ftranspose_corr {A m n} (mat : matrix A m n) :
  ∀ j i, ijth mat i j = ijth (ftranspose mat) j i.
Proof. exact (ijth_mkMat (swap (ijth mat))). Qed.

Corollary ftranspose_invol {A m n} (mat : matrix A m n) :
  mat = ftranspose (ftranspose mat).
Proof.
  apply ijth_extensional; intros i j.
  case ftranspose_corr. apply ftranspose_corr.
Qed.

(* ---------------------------------------------------------------------- *)
(* Transposition on the implementation using vectors, linear complexity *)

Fixpoint transpose {A m n} (mat : matrix A m n) : matrix A n m :=
  match mat with
  | []        => map0 [] n
  | v :: mat' => map2 cons v (transpose mat')
  end.
Ltac simpl_transpose :=
  change (transpose (?v :: ?mat')) with (map2 cons v (transpose mat')).

Compute transpose [[1; 2]; [3; 4]; [5; 6]].

(* The following definition is for information (map2 cons will
   be directly used instead). However, in order to prove
   properties of transpose, a good strategy is to start with
   a corresponding lemma on cons_column *)
Definition cons_column {A n m} :
  ∀ (u : vect A m), matrix A m n → matrix A m (S n) :=
  map2 cons.

(* [u] represents a column on the left of [mat] *)
Definition ijth_colmat {A m n} (u : vect A m) (mat : matrix A m n) :
  fmatrix A m (S n) := λ i j,
    match j with
    | BO    => λ  _ , ith u i
    | BS j' => λ mat, ijth mat i j'
    end mat.

(* Correctness lemma on ijth_colmat *)
Lemma ijth_colmat_corr {A m n} (u : vect A m) (mat : matrix A m n) :
  ∀ i j, ijth_colmat u mat i j = ijth (map2 cons u mat) i j.
Proof.
  induction u as [ | x m u Hu]; intros i j.
  - sinv i.
  - sdinv mat as [line mat']. simpl_map2.
    sdinv i as [ | i'].
    + cbv [ijth]. sdinv j as [ | j'].
      all: cbv [ijth_colmat ijth]. all: repeat simpl_ith. all: reflexivity.
    + simpl_ijth. case (Hu mat'). sdinv j as [ | j'].
      all: cbv [ijth_colmat ijth]. all: simpl_ith. all: reflexivity.
Qed.

(* Correctness lemma on transpose *)
Lemma transpose_corr {A m n} (mat : matrix A m n) :
  ∀ i j, ijth mat i j = ijth (transpose mat) j i.
Proof.
  induction mat as [ | v m' mat' Hmat']; intros i j.
  - sinv i.
  - cbn [transpose]. case ijth_colmat_corr.
    sdinv i as [ | i']; cbn; simpl_ijth.
    + reflexivity.
    + apply Hmat'.
Qed.

(* Another correctness lemma on transpose, based on ftranspose
   seen as a functional specification of transpose *)
Corollary transpose_fctspec {A m n} (mat : matrix A m n) :
  ftranspose mat = transpose mat.
Proof.
  apply ijth_extensional; intros i j. case ftranspose_corr. apply transpose_corr.
Qed.

(* Then, transpose is involutive... *)
Corollary transpose_invol {A m n} (mat : matrix A m n) :
  mat = transpose (transpose mat).
Proof. do 2 case transpose_fctspec. apply ftranspose_invol. Qed.

(* ... and injective *)
Corollary transpose_injective {A m n} (ma mb : matrix A m n) :
  transpose ma = transpose mb → ma = mb.
Proof.
  intro e. rewrite (transpose_invol mb). case e. apply transpose_invol.
Qed.
