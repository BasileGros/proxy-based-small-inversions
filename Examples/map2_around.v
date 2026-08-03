From SmallInversion Require Import small_inversion.
(* ====================================================================== *)

(* The map function is easy to define on vectors.
   However, is is not that simple to define map2 (map3, ...)
   taking as arguments
   - a 2-ary (3-ary, ...) function
   - and 2 (3, ...) vectors of the *same* size, say n,
   and returning a vector of size n.

We provide here simple definitions using small inversion
and a possible generalisation to m-ary functions.

The end of the file contains related additional material.
- A version of map2 whose results depends on
  the two vectors in input, in order to illustrate
  dependent proxy-based small inversions.
- A version of map2 defined on co-inductive vectors
  indexed by co-inductive natural numbers using
  exactly the same algorithm.
  Approaches a la Agda based on first-order unification
  (including the Equations plugin) fail to support this,
  because their pattern-matching mechanism integrates the
  occur-check, compromising the separation of concerns
  between pattern-matching and induction.
*)

(* In order to allow ∀ and λ notations *)
From Stdlib Require Import Utf8.

Inductive vect (A : Type) : nat → Type :=
| nil : vect A 0
| cons : A → ∀ n : nat, vect A n → vect A (S n).


Unset Elimination Schemes (* For comfort *).
Derive InvProxy for vect.
(* vect_O vect_S vect_proxy *)
Derive Dependent InvProxy for vect.
(* vect_O_dep vect_S_dep vect_dproxy *)
Set Elimination Schemes.

Arguments cons {A} _ {n}.
Arguments nil {A}.

Notation "[ ]" := nil (format "[ ]").
Notation "x :: v" := (cons x v).
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

(* For convenient use of proxies in combination with the let construct *)
Notation inv_vectS u := (invproxy u : vect_S _ _).
Notation dinv_vectO u := (dinvproxy u : vect_O_dep _ _).
Notation dinv_vectS u := (dinvproxy u : vect_S_dep _ _ _).

Notation "'dinv_let' '()' := E 'in' F" :=
  (let 'nil_O_dep _ := dinv_vectO E in F)  (at level 200).
Notation "'dinv_let' ( A ,  B ) := E 'in' F" :=
  (let 'cons_S_dep _ _ A B := dinv_vectS E in F)  (at level 200, A binder, B binder).

(* ====================================================================== *)

(* Recursion can be performed on the first vector *)
Definition map2 {A B C : Type} (f : A → B → C) :
  ∀ n, vect A n → vect B n → vect C n :=
  fix loop n (u : vect A n) :=
    match u with
    | []      => λ v, []
    | x :: u' => λ v,
        let (y, v') := inv_vectS v in
        f x y :: loop _ u' v'
    end.

Definition swap {A B C} (f : A → B → C) : B → A → C :=
  λ b a, f a b.

(* The following lemma is simple to prove using dependent small inversion *)
Lemma swap_map2 {A B C : Type} (f : A → B → C) n u v :
  map2 (swap f) n u v = swap (map2 f n) u v.
Proof.
  induction u as [ | x n u' Hu'].
  - sdinv v. cbn. reflexivity.
  - sdinv v as [y v']. cbn. f_equal. apply Hu'.
Qed.
  
Definition map3 {A B C D : Type} (f : A → B → C → D) :
  ∀ n, vect A n → vect B n → vect C n → vect D n :=
  fix loop n (u : vect A n) :=
    match u with
    | []      => λ v w, []
    | x :: u' => λ v w,
        let (y, v') := inv_vectS v in
        let (z, w') := inv_vectS w in
        f x y z :: loop _ u' v' w'
    end.

(* Alternately, recursion can be performed on the common size of vectors *)
Definition map3_alt {A B C D : Type} (f : A → B → C → D) :
  ∀ n, vect A n → vect B n → vect C n → vect D n :=
  fix loop n :=
    match n with
    | O    => λ u v w, []
    | S n' => λ u v w,
        let (x, u') := inv_vectS u in
        let (y, v') := inv_vectS v in
        let (z, w') := inv_vectS w in
        f x y z :: loop n' u' v' w'
    end.

(* Those programming patterns can be extended to 4,... m-ary functions *)

(* ------------------------------------------ *)
(* Generalisation to m-ary functions *)

(* Homogeneous version : A → ... (n times) -> A *)
Definition An_to_A A :=
  fix loop n :=
    match n with
    | 0   => A
    | S n => A → loop n
    end.

(* Recursion performed on the size, so that we can include 0-ary functions. *)
Definition map_m {A : Type} m (f : An_to_A A m) :
  ∀ n, An_to_A (vect A n) m :=
  fix loopn n :=
    match n with
    | O    =>
        (fix loopm m :=
           match m return An_to_A (vect A 0) m with
           | 0   => []
           | S m => λ _, loopm m
           end) m
    | S n' =>
        (fix loopm m :=
           match m return
                 An_to_A A m → An_to_A (vect A n') m →
                 An_to_A (vect A (S n')) m
           with
           | 0   => λ (r : A) (u' : vect A n'), r :: u'
           | S m' => λ fx fu u,
               let (x, u') := inv_vectS u in
               loopm m' (fx x) (fu u')
           end)
          m f (loopn n')
    end.

(* We can then prove that (map3 f) and (map_m 3 f) are extensionally equal *)
Lemma map3_special_case A (f : A → A → A → A) n u v w :
  map3 f n u v w = map_m 3 f n u v w.
  induction n as [ | n Hn].
  - cbn. sdinv u. reflexivity.
  - sdinv u as [x u']. sdinv v as [y v']. sdinv w as [z w'].
    cbn. f_equal. apply Hn.
Qed.

(* ====================================================================== *)


(* A map2 function on vectors that remembers its inputs in its type *)
Inductive Remap2 {C A B} : ∀ {n}, vect A n → vect B n → Type :=
| Rmnil : Remap2 [] []
| Rmcons {a b n} {aa : vect A n} {bb : vect B n} :
  C → Remap2 aa bb → Remap2 (a :: aa) (b :: bb).
Arguments Remap2 C {A B n} _ _.

Fixpoint remap2 {A B C : Set} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []     => λ v, dinv_let () := v in Rmnil
  | x :: u => λ v, dinv_let (y, v) := v in Rmcons (f x y) (remap2 f u v)
  end.


From Equations Require Import Equations.

Equations eqmap2 {A B C} (f : A → B → C) {n} (u : vect A n) (v : vect B n) : vect C n :=
  eqmap2 f [] [] := [] ;
  eqmap2 f (a :: u) (b :: v) := (f a b) :: (eqmap2 f u v).

Equations eqremap2 {A B C} (f : A → B → C) {n} (u : vect A n) (v : vect B n) : Remap2 C u v :=
  eqremap2 f [] [] := Rmnil ;
  eqremap2 f (a :: u) (b :: v) := Rmcons (f a b) (eqremap2 f u v).

(* ====================================================================== *)
(* Co-inductive vectors *)

CoInductive conat : Set :=
| CO : conat
| CS : conat → conat.

CoInductive covec A : conat → Type :=
| cvnil : covec A CO
| cvcons : A → ∀ n, covec A n → covec A (CS n).
Arguments cvnil {_}.
Arguments cvcons {_} _ {_} _ .

Notation "[ ~ ]" := cvnil (format "[ ~ ]").
Notation "x ::~ v" := (cvcons x v) (at level 60, right associativity).

Lemma eq_decomp_covec {A n} (v : covec n A) :
  match v with [~] => [~] | x ::~ v => x ::~ v end = v.
Proof. destruct v; reflexivity. Qed.

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for covec.
(* covec_CO covec_CS *)
Derive Dependent InvProxy for covec.
(* covec_CO_dep covec_CS_dep *)
Set Elimination Schemes.

(* For convenience in let expressions *)
Notation sinv_covec u := (invproxy u : covec_CS _ _).

(* map2 on co-vectors *)
CoFixpoint cvmap2 {A B C} (f : A → B → C) {n} (v : covec A n) : covec B n → covec C n :=
  match v with
  | [~] => λ _, [~]
  | x ::~ v => λ w, let (y, w) := sinv_covec w in f x y ::~ cvmap2 f v w
  end.

Definition cvmap2_step {A B C} (f : A → B → C) {n} (v : covec A n) : covec B n → covec C n :=
  match v with
  | [~] => λ _, [~]
  | x ::~ v => λ w, let (y, w) := sinv_covec w in f x y ::~ cvmap2 f v w
  end.

Lemma cvmap2_step_eq {A B C} (f : A → B → C) {n} (v : covec A n) (w : covec B n) :
  cvmap2_step f v w = cvmap2 f v w.
Proof.
  case (eq_decomp_covec (cvmap2 f v w)). destruct v; sdinv w; cbn; reflexivity.
Qed.

(* Bisimilarity relation between co-vectors, to be used in correctness statementts *)
CoInductive covec_eq {A} : ∀ {n}, covec A n → covec A n → Prop :=
  | cvnil_eq : covec_eq [~] [~]
  | cvcons_eq x n (v w : covec A n) : covec_eq v w → covec_eq (x ::~ v) (x ::~ w).

(* Lemma similar to swap_map2 *)
Lemma swap_cvmap2 {A B C : Type} (f : A → B → C) : ∀ n u v,
  covec_eq (cvmap2 (swap f) u v) (swap (cvmap2 f (n:=n)) u v).
Proof.
  cofix loop. intros n u v.
  change (swap ?f ?x ?y) with (f y x). repeat case cvmap2_step_eq. 
  destruct u as [ | x n u'].
  - sdinv v. cbn. apply cvnil_eq.
  - sdinv v as [y v']. cbn. apply cvcons_eq. apply loop.
Qed.

(* Using Equations, an exception is raised *)
(*
Equations cvmap2 {A B C} (f : A → B → C) n (u : covec A n) (v : covec B n) : covec C n :=
  cvmap2 f _ [~] [~] := [~] ;
  cvmap2 f _ (a ::~ u) (b ::~ v) := cvcons (f a b) (cvmap2 f n u v).
*)
