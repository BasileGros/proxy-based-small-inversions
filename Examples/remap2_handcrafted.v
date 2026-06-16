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
Variant vect_O (X : Type) : Type :=  nil_O : vect_O X.
Variant vect_S (X : Type) (n : nat) : Type :=  cons_S : X → vect X n → vect_S X n.
Arguments nil_O {X}.
Arguments cons_S {X n} _.

Definition sinv_vect_type X n : Type :=
  match n with  O => vect_O X  |  S n => vect_S X n  end.

Definition sinv_vect {X n} (u : vect X n) : sinv_vect_type X n :=
  match u with  nil => nil_O  |  cons x u => cons_S x u  end.

Variant vect_O_dep X : vect X 0 -> Type :=
  nil_O_dep : vect_O_dep X nil.
Variant vect_S_dep X n : vect X (S n) -> Type :=
  cons_S_dep x u : vect_S_dep X n (cons x u).
Arguments nil_O_dep {X}.
Arguments cons_S_dep {X n} _.

Definition sdinv_vect_type X n : vect X n -> Type :=
  match n with  O => vect_O_dep X  |  S n => vect_S_dep X n  end.

Definition sdinv_vect {X n} (u : vect X n) : sdinv_vect_type X n u :=
  match u with  nil => nil_O_dep  |  cons x u => cons_S_dep x u  end.


Notation "'let_nil' '()' := E 'in' F" :=  (let 'nil_O_dep := E in F)  (at level 200).
Notation "'let_cons' ( A ,  B ) := E 'in' F" :=
  (let 'cons_S_dep A B := E in F)  (at level 200, A binder, B binder).

(* ====================================================================== *)
(* Basic map2 function *)

Fixpoint map2 {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []     => λ v, []
  | x :: u => λ v, let '(cons_S y v) := sinv_vect v in f x y :: map2 f u v
  end.

(*For non-dependent inversion, the notation "let (y,v) := sinv_vect v in" is also possible*)

Fixpoint map2' {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []     => λ v, []
  | x :: u => λ v, let (y,v) := sinv_vect v in f x y :: map2' f u v
  end.

(* A map2 function on vectors that remembers its inputs in its type *)
Inductive Remap2 {C A B : Type} : ∀ {n}, vect A n → vect B n → Type :=
| Rmnil : Remap2 [] []
| Rmcons {a b n} {aa : vect A n} {bb : vect B n} :
  C → Remap2 aa bb → Remap2 (a :: aa) (b :: bb).
Arguments Remap2 C {A B n} _ _.

Fixpoint remap2 {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []     => λ v, let 'nil_O_dep := sdinv_vect v in Rmnil
  | x :: u => λ v, let '(cons_S_dep y v) := sdinv_vect v in Rmcons (f x y) (remap2 f u v)
  end.
