(* Handcrafted proxy-based small inversions for vectors,
   used in map2 and remap2, a simple example of dependent inversion *)
From Stdlib Require Import Utf8.

Inductive vect (X : Type) : nat → Type :=
| nil : vect X O
| cons n : X → vect X n → vect X (S n).
Arguments nil {X}.
Arguments cons {X n}.

Notation "[ ]" := nil (format "[ ]").
Notation "x :: v" := (cons x v).
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

(* Partial inductive types *)
Variant vect_O (A : Set) : Set :=  nil_O : vect_O A.
Variant vect_S (A : Set) (n : nat) : Set :=  cons_S : A → vect A n → vect_S A n.
Arguments nil_O {A}.
Arguments cons_S {A n} _.

Definition sinv_vect_type A n : Set :=
  match n with  O => vect_O A  |  S n => vect_S A n  end.

Definition sinv_vect {A n} (u : vect A n) : sinv_vect_type A n :=
  match u with  nil => nil_O  |  cons x u => cons_S x u  end.

Variant vect_O_dep A : vect A 0 -> Set :=
  nil_O_dep : vect_O_dep A nil.
Variant vect_S_dep A n : vect A (S n) -> Set :=
  cons_S_dep x u : vect_S_dep A n (cons x u).
Arguments nil_O_dep {A}.
Arguments cons_S_dep {A n} _.

Definition sdinv_vect_type A n : vect A n -> Set :=
  match n with  O => vect_O_dep A  |  S n => vect_S_dep A n  end.

Definition sdinv_vect {A n} (u : vect A n) : sdinv_vect_type A n u :=
  match u with  nil => nil_O_dep  |  cons x u => cons_S_dep x u  end.


Notation "'let_nil' '()' := E 'in' F" :=  (let 'nil_O_dep := E in F)  (at level 200).
Notation "'let_cons' ( A ,  B ) := E 'in' F" :=
  (let 'cons_S_dep A B := E in F)  (at level 200, A binder, B binder).

(* ====================================================================== *)
(* Basic map2 function *)

Fixpoint map2 {A B C : Set} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []     => λ v, []
  | x :: u => λ v, let_cons (y, v) := sdinv_vect v in f x y :: map2 f u v
  end.

(* A map2 function on vectors that remembers its inputs in its type *)
Inductive Remap2 {C A B : Set} : ∀ {n}, vect A n → vect B n → Set :=
| Rmnil : Remap2 [] []
| Rmcons {a b n} {aa : vect A n} {bb : vect B n} :
  C → Remap2 aa bb → Remap2 (a :: aa) (b :: bb).
Arguments Remap2 C {A B n} _ _.

Fixpoint remap2 {A B C : Set} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []     => λ v, let_nil () := sdinv_vect v in Rmnil
  | x :: u => λ v, let_cons (y, v) := sdinv_vect v in Rmcons (f x y) (remap2 f u v)
  end.
