From SmallInversion Require Import small_inversion.
From Equations Require Import Equations.

(* ====================================================================== *)

(* Different approaches to dependent pattern-matching can be used in Rocq.
   Here is a comparison of them on the same programming problem :
   map2 and its dependent version remap2, taken in the sibling file map2_around.v
   In the experiments below, we use:
   - The Rocq Prover, version 9.1.0
   - The Equations plugin, opam package: rocq-equations 1.3.1+9.1
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

(* ---------------------------------------------------------------------- *)

(* Recursion can be performed on the first vector *)
Fixpoint map2 {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []      => λ v, []
  | x :: u' => λ v,
      let (y, v') := inv_vectS v in
      f x y :: map2 f u' v'
    end.

(*
Print map2.
map2 =
fix map2 (A B C : Type) (f : A → B → C) (n : nat) (u : vect A n) {struct u} : vect B n → vect C n :=
  match u in (vect _ n0) return (vect B n0 → vect C n0) with
  | [] => λ _ : vect B 0, []
  | @cons _ x n0 u' =>
      λ v : vect B (S n0), let (y, v') := inv_vectS v in f x y :: map2 A B C f n0 u' v'
  end
     : ∀ {A B C : Type}, (A → B → C) → ∀ {n : nat}, vect A n → vect B n → vect C n
 *)

Definition swap {A B C} (f : A → B → C) : B → A → C :=
  λ b a, f a b.

(* Using dependent small inversions, we can prove lemmas on programs defined
   with small inversions *)
Lemma swap_map2 {A B C : Type} (f : A → B → C) n u v :
  map2 (n:=n) (swap f) u v = swap (map2 f) u v.
Proof.
  induction u as [ | x n u' Hu'].
  - sdinv v. cbn. reflexivity.
  - sdinv v as [y v']. cbn. f_equal. apply Hu'.
Qed.

(* Another proof for comparison with inversion and Equations,
   where an early cbn exposes the contents of the program.
 *)
Lemma swap_map2_early_cbn {A B C : Type} (f : A → B → C) n u v :
  map2 (n:=n) (swap f) u v = swap (map2 f) u v.
Proof.
  induction u as [ | x n u' Hu']; cbn.
  - sdinv v. cbn. reflexivity.
  - sdinv v as [y v']. cbn. f_equal. apply Hu'.
Qed.

(* ---------------------------------------------------------------------- *)
(* Small inversions presented at ITP13 -- named si13 below *)

(* The focus of si13 was on proofs,
   not on programming using dependent types.
   In contrast with PBSI submitted to LPAR26, si13 does not consider:
   1/ programs such as map2;
   2/ reasoning on si13 terms, and programs such as remap2.
  Item 1/ raises no difficulty.  In order to compare PBSI and si13,
  the return clause named diag in si13 is defined explicitly here,
  and its named is suffixed by "_premises_type", since it provides the
  type of the inversion function itself suffixed by "_premises".
  It is clear that the inversion mechanism of si13 is the
  impredicative encoding of PBSI.
  In particular, "let (y, v') := inv_vectS v in RESULT" is translated by
  "vect_premises v _ (λ y v', RESULT)".
  The programs are of the same order of magnitude as for PBSI,
  however their CPS-like style make them more cryptic.
  This, combined with a lack of automation for generating
  the auxiliary definitions (like vect_premises here), and a missing single
  tactic like "sinv" (to be used in the place "inversion") may have hindered
  a wider usage of si13.

  Item 2/ is considered below.
 *)

Definition vect_premises_type A n : Type :=
  match n with 
  | 0   => ∀ X, X → X
  | S n => ∀ X, (A → vect A n → X) → X
  end.

Definition vect_premises {A n} (u : vect A n) : vect_premises_type A n :=
  match u with
  | []     => fun X k => k
  | e :: s => fun X k => k e s
  end.

Fixpoint map2_si13 {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []      => λ v, []
  | x :: u' => λ v, vect_premises v _  (λ y v', f x y :: map2_si13 f u' v')
  end.

(* (Item 2/) In order to prove properties of map2_si13,
   [ITP13] provides no clue.  We can use dependent PBSI. *)
Lemma swap_map2_si13_using_sdinv {A B C : Type} (f : A → B → C) n u v :
  map2_si13 (n:=n) (swap f) u v = swap (map2_si13 f) u v.
Proof.
  induction u as [ | x n u' Hu'].
  - sdinv v. cbn. reflexivity.
  - sdinv v as [y v']. cbn. f_equal. apply Hu'.
Qed.

(* We can also consider the impredicative encoding of dependent PBSI. *)

Definition vect_premises_dep_type A n : vect A n → Type :=
  match n with 
  | 0   => λ u, ∀ X, X [] → X u
  | S n => λ u, ∀ X, (∀ x (u' : vect A n), X (x :: u')) → X u
  end.

(* Same program as vect_premises, with a more complex typing *)
Definition vect_premises_dep {A n} (u : vect A n) : vect_premises_dep_type A n u :=
  match u with
  | []     => fun X k => k
  | e :: s => fun X k => k e s
  end.

(* In proof mode, the "destruct (dinv_vectS v)" that implements "sdinv v"
   is translated by an "apply (vect_premises_dep v)". *)
Lemma swap_map2_si13 {A B C : Type} (f : A → B → C) n u v :
  map2_si13 (n:=n) (swap f) u v = swap (map2_si13 f) u v.
Proof.
  induction u as [ | x n u' Hu'].
  - apply (vect_premises_dep v). cbn. reflexivity.
  - apply (vect_premises_dep v); intros y v'. cbn.
    f_equal. apply Hu'.
Qed.

(* ---------------------------------------------------------------------- *)
(* Tactic inversion *)

(* Using standard inversion in script mode and automatic programming *)
Definition map2_inv_eauto {A B C : Type} (f : A → B → C)
  {n} (u : vect A n) (v : vect B n) : vect C n.
Proof.
  induction u as [ | x n u' Hu'].
  - constructor.
  - inversion v; constructor; eauto.
Defined.

(* Are we sure that we get the desired program?
   Not at this point: tactics are not in the TCB.
   So we must look at the real CIC program.
 *)

Print map2_inv_eauto.

(*
map2_inv_eauto =
λ (A B C : Type) (f : A → B → C) (n : nat) (u : vect A n) (v : vect B n),
  vect_rect A (λ (n0 : nat) (_ : vect A n0), vect B n0 → vect C n0) (λ _ : vect B 0, [])
    (λ (x : A) (n0 : nat) (_ : vect A n0) (Hu' : vect B n0 → vect C n0) (v0 : vect B (S n0)),
       let X :=
         match v0 in (vect _ n1) return (n1 = S n0 → vect C (S n0)) with
         | [] =>
             λ H : 0 = S n0,
               (λ H0 : 0 = S n0,
                  let H1 : False :=
                    eq_ind 0 (λ e : nat, match e with
                                         | 0 => True
                                         | S _ => False
                                         end) I (S n0) H0
                    in
                  False_rect (vect C (S n0)) H1)
                 H
         | @cons _ x0 n1 x1 =>
             (λ (X : B) (n2 : nat) (X0 : vect B n2) (H : S n2 = S n0),
                (λ H0 : S n2 = S n0,
                   let H1 : n2 = n0 := f_equal (λ e : nat, match e with
                                                           | 0 => n2
                                                           | S n3 => n3
                                                           end) H0
                     in
                   (λ H2 : n2 = n0,
                      let H3 : n2 = n0 := H2 in
                      eq_rect_r (λ n3 : nat, B → vect B n3 → vect C (S n0))
                        (λ (X1 : B) (X2 : vect B n0), f x X1 :: Hu' X2) H3)
                     H1)
                  H X X0)
               x0 n1 x1
         end in
       X eq_refl)
    n u v
     : ∀ {A B C : Type}, (A → B → C) → ∀ {n : nat}, vect A n → vect B n → vect C n
*)

(* Using refine, in order to have more programming constructs in the body;
   but 'inversion' is still a tactic *)
#[refine]
Fixpoint map2_inv {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []      => λ v, []
  | x :: u' => λ v, _
  end.
inversion v as [ | y n' v' e].
refine (f x y :: map2_inv _ _ _ f _ u' v').
Defined.

Print map2_inv (* similar to the map2_inv_eauto, by the way *).

(*
fix map2_inv (A B C : Type) (f : A → B → C) (n : nat) (u : vect A n) {struct u} :
    vect B n → vect C n :=
  match u in (vect _ n0) return (vect B n0 → vect C n0) with
  | [] => λ _ : vect B 0, []
  | @cons _ x n0 u' =>
      λ v : vect B (S n0),
        let X :=
          match v in (vect _ n1) return (n1 = S n0 → vect C (S n0)) with
          | [] =>
              λ H : 0 = S n0,
                (λ e : 0 = S n0,
                   let H0 : False :=
                     eq_ind 0 (λ e0 : nat, match e0 with
                                           | 0 => True
                                           | S _ => False
                                           end) I (S n0) e
                     in
                   False_rect (vect C (S n0)) H0)
                  H
          | @cons _ x0 n1 x1 =>
              (λ (y : B) (n' : nat) (v' : vect B n') (H : S n' = S n0),
                 (λ e : S n' = S n0,
                    let H0 : n' = n0 :=
                      f_equal (λ e0 : nat, match e0 with
                                           | 0 => n'
                                           | S n2 => n2
                                           end) e
                      in
                    (λ e0 : n' = n0,
                       let H1 : n' = n0 := e0 in
                       eq_rect_r (λ n2 : nat, B → vect B n2 → vect C (S n0))
                         (λ (y0 : B) (v'0 : vect B n0), f x y0 :: map2_inv A B C f n0 u' v'0) H1)
                      H0)
                   H y v')
                x0 n1 x1
          end in
        X eq_refl
  end
     : ∀ {A B C : Type}, (A → B → C) → ∀ {n : nat}, vect A n → vect B n → vect C n
 *)

(* Unfortunately:
   - inversion is of no help in proofs
   - we can use dependent small inversions (tactic sdinv)!
     but are faced with terrible subgoals, illustrating an issue with the
     following coherence criterion:
       when calculations are performed, the link with the source code should be kept,
       so that the user can relate the output traces to the source code.
 *)
Lemma swap_map2_inv {A B C : Type} (f : A → B → C) n u v :
  map2_inv (n:=n) (swap f) u v = swap (map2_inv f) u v.
Proof.
  induction u as [ | x n u' Hu']; cbn (* look! *).
  - Fail reflexivity. Fail progress inversion v. Fail reflexivity.
    sdinv v. cbn. reflexivity.
  - inversion v. Fail progress f_equal. Undo.
    sdinv v as [y v'] (* let's have faith *). cbn (* yes! *).
    f_equal. apply Hu'.
Qed.

(* ---------------------------------------------------------------------- *)
(* Equations *)

Equations map2_eqn {A B C} (f : A → B → C)
  {n} (u : vect A n) (v : vect B n) : vect C n :=
  map2_eqn f [] [] := [] ;
  map2_eqn f (a :: u) (b :: v) := (f a b) :: (map2_eqn f u v).

Print map2_eqn.

(*
map2_eqn =
fix map2_eqn (A B C : Type) (f : A → B → C) (n : nat) (u : vect A n) (v : vect B n) {struct u} :
    vect C n :=
  match u in (vect _ n0) return (vect B n0 → vect C n0) with
  | [] =>
      λ v0 : vect B 0,
        match v0 in (vect _ n0) return (n0 = 0 → vect C 0) with
        | [] => apply_noConfusion 0 0 (λ _ : True, [])
        | @cons _ _ n0 _ => apply_noConfusion (S n0) 0 (False_rect (vect C 0))
        end eq_refl
  | @cons _ y n0 v0 =>
      λ v1 : vect B (S n0),
        match v1 in (vect _ n1) return (n1 = S n0 → vect C (S n0)) with
        | [] => apply_noConfusion 0 (S n0) (False_rect (vect C (S n0)))
        | @cons _ y0 n1 v2 =>
            apply_noConfusion (S n1) (S n0)
              (λ H : n1 = n0,
                 DepElim.solution_left n0 (λ v3 : vect B n0, f y y0 :: map2_eqn A B C f n0 v0 v3) n1 H
                   v2)
        end eq_refl
  end v
     : ∀ {A B C : Type}, (A → B → C) → ∀ {n : nat}, vect A n → vect B n → vect C n
 *)

(* By default, the above code is opaque:
   in proofs, you are supposed to use specific lemmas and tools provided by Equations.
   But if it does not work, you need to see the real thing,
   raising again an issue related to the aforementioned coherence criterion.
 *)

Lemma swap_map2_eqn {A B C : Type} (f : A → B → C) n u v :
  map2_eqn (n:=n) (swap f) u v = swap (map2_eqn f) u v.
Proof.
  induction u as [ | x n u' Hu']; cbn (* no effect*).
  - dependent elimination v. cbn (* no effect*). reflexivity (* lucky, fine *).
  - dependent elimination v. cbn. (* stuck, a deeper knowledge on Equations is required *)
Abort.

(* Let us now illustrate the coherence criterion *)

Transparent map2_eqn.
Lemma swap_map2_eqn {A B C : Type} (f : A → B → C) n u v :
  map2_eqn (n:=n) (swap f) u v = swap (map2_eqn f) u v.
Proof.
  induction u as [ | x n u' Hu']; cbn (* look! *).
  - dependent elimination v (* let's have faith *). cbn (* yes! *).
    reflexivity.
  - dependent elimination v (* let's have faith *). cbn (* yes! *).
    f_equal. apply Hu'.
Qed.

(* ====================================================================== *)
(* A dependent version of map2 *)

(* A map2 function on vectors that remembers its inputs in its type *)
Inductive Remap2 {C A B} : ∀ {n}, vect A n → vect B n → Type :=
| Rmnil : Remap2 [] []
| Rmcons {a b n} {aa : vect A n} {bb : vect B n} :
  C → Remap2 aa bb → Remap2 (a :: aa) (b :: bb).
Arguments Remap2 C {A B n} _ _.

Fixpoint remap2 {A B C} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []      => λ v, dinv_let () := v in Rmnil
  | x :: u' => λ v, dinv_let (y, v') := v in Rmcons (f x y) (remap2 f u' v')
  end.

(* In order to state a lemma similar to swap_map2, we need:
   - a dependent version of swap, named depswap
   - a conversion function from (Remap2 C u v) to (Remap2 C v u), named swRemap2.
*)

Definition depswap {A B} {C : A → B → Type} (f : ∀ a b, C a b) : ∀ b a, C a b :=
  λ b a, f a b.

Fixpoint swRemap2 {C A B n} {u : vect A n} {v : vect B n} (r : Remap2 C u v) : Remap2 C v u :=
  match r with
  | Rmnil => Rmnil
  | Rmcons c r => Rmcons c (swRemap2 r)
  end.

(* Using dependent PBSI, we can prove lemmas on programs defined
   with dependent PBSI *)
Lemma swap_remap2 {A B C : Type} (f : A → B → C) n u v :
  remap2 (n:=n) (swap f) u v = swRemap2 (depswap (remap2 f) u v).
Proof.
  induction u as [ | x n u' Hu'].
  - sdinv v. cbn. reflexivity.
  - sdinv v as [y v']. cbn. f_equal. apply Hu'.
Qed.

(* ---------------------------------------------------------------------- *)
(* Small inversions presented at ITP13 -- named si13 below *)

Fixpoint remap2_si13 {A B C} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []      => λ v, vect_premises_dep v _ Rmnil
  | x :: u' => λ v, vect_premises_dep v _ (λ y v', Rmcons (f x y) (remap2_si13 f u' v'))
  end.

(* Using dependent PBSI, we can prove lemmas on programs defined
   with the impredicative encoding of dependent PBSI *)
Lemma swap_remap2_si13_using_sdinv {A B C : Type} (f : A → B → C) n u v :
  remap2_si13 (n:=n) (swap f) u v = swRemap2 (depswap (remap2_si13 f) u v).
Proof.
  induction u as [ | x n u' Hu'].
  - sdinv v. cbn. reflexivity.
  - sdinv v as [y v']. cbn. f_equal. apply Hu'.
Qed.

(* The impredicative encoding of dependent PBSI can be sued as well *)
Lemma swap_remap2_si13 {A B C : Type} (f : A → B → C) n u v :
  remap2_si13 (n:=n) (swap f) u v = swRemap2 (depswap (remap2_si13 f) u v).
Proof.
  induction u as [ | x n u' Hu'].
  - apply (vect_premises_dep v). cbn. reflexivity.
  - apply (vect_premises_dep v); intros y v'. cbn.
    f_equal. apply Hu'.
Qed.

(* ---------------------------------------------------------------------- *)
(* Tactic inversion: failure *)

#[refine]
Fixpoint remap2_inv {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []      => λ v, _
  | x :: u' => λ v, _
  end.
- Fail progress inversion v (* Wrong goal, with v instead of [] *). admit.
- inversion v as [ | y n' v' e] (* Wrong goal, with v instead of (y :: v') *).
Abort.

(* ---------------------------------------------------------------------- *)
(* Equations *)

Equations remap2_eqn {A B C} (f : A → B → C) {n} (u : vect A n) (v : vect B n) : Remap2 C u v :=
  remap2_eqn f [] [] := Rmnil ;
  remap2_eqn f (a :: u) (b :: v) := Rmcons (f a b) (remap2_eqn f u v).

Print remap2_eqn.

(*
remap2_eqn =
fix remap2_eqn (A B C : Type) (f : A → B → C) (n : nat) (u : vect A n) (v : vect B n) {struct u} :
    Remap2 C u v :=
  match u as v0 in (vect _ n0) return (∀ v1 : vect B n0, Remap2 C v0 v1) with
  | [] =>
      λ v0 : vect B 0,
        match
          v0 as v1 in (vect _ n0)
          return ({| pr1 := n0; pr2 := v1 |} = {| pr1 := 0; pr2 := v0 |} → Remap2 C [] v0)
        with
        | [] =>
            DepElim.eq_simplification_sigma1_dep 0 0 [] v0
              (apply_noConfusion 0 0
                 (Logic.True_rect_dep
                    (λ H : True,
                       eq_rect 0 (λ n0 : nat, vect B n0) [] 0 (noConfusion H) = v0 → Remap2 C [] v0)
                    (λ H : eq_rect 0 (λ n0 : nat, vect B n0) [] 0 (noConfusion I) = v0,
                       DepElim.solution_right (eq_rect 0 (λ n0 : nat, vect B n0) [] 0 (noConfusion I))
                         Rmnil v0 H)))
        | @cons _ y n0 v1 =>
            DepElim.eq_simplification_sigma1_dep (S n0) 0 (y :: v1) v0
              (apply_noConfusion (S n0) 0
                 (Logic.False_rect_dep
                    (λ H : False,
                       eq_rect (S n0) (λ n1 : nat, vect B n1) (y :: v1) 0 (noConfusion H) = v0
                       → Remap2 C [] v0)))
        end eq_refl
  | @cons _ y n0 v0 =>
      λ v1 : vect B (S n0),
        match
          v1 as v2 in (vect _ n1)
          return ({| pr1 := n1; pr2 := v2 |} = {| pr1 := S n0; pr2 := v1 |} → Remap2 C (y :: v0) v1)
        with
        | [] =>
            DepElim.eq_simplification_sigma1_dep 0 (S n0) [] v1
              (apply_noConfusion 0 (S n0)
                 (Logic.False_rect_dep
                    (λ H : False,
                       eq_rect 0 (λ n1 : nat, vect B n1) [] (S n0) (noConfusion H) = v1
                       → Remap2 C (y :: v0) v1)))
        | @cons _ y0 n1 v2 =>
            DepElim.eq_simplification_sigma1_dep (S n1) (S n0) (y0 :: v2) v1
              (apply_noConfusion (S n1) (S n0)
                 (λ H : n1 = n0,
                    DepElim.solution_left_dep n0
                      (λ (v3 : vect B n0) (H0 : eq_rect (S n0) (λ n2 : nat, vect B n2)
                                                  (y0 :: v3) (S n0) (noConfusion eq_refl) =
                                                v1),
opyright (c) 2009-2021                         DepElim.solution_right
                           (eq_rect (S n0) (λ n2 : nat, vect B n2) (y0 :: v3)
                              (S n0) (noConfusion eq_refl))
                           (Rmcons (f y y0) (remap2_eqn A B C f n0 v0 v3)) v1 H0)
                      n1 H v2))
        end eq_refl
  end v
     : ∀ {A B C : Type}, (A → B → C) → ∀ {n : nat} (u : vect A n) (v : vect B n), Remap2 C u v

 *)

(* Note that a number of additional non-trivial stuff is needed
   in order to fully understand the pieces of CIC code generated
   by Equations.  *)
(*
Print DepElim.eq_simplification_sigma1_dep.
Print DepElim.solution_left.
Print DepElim.solution_right.
Print Logic.transport.
Print noConfusion. (* Here the Class mechanism is used, so that additional code
                      is under the carpet *)
 *)

(* Let us again illustrate the coherence criterion explained in [LPAR26]:
   same experiment as for map2_eqn, just more terrible *)
Transparent remap2_eqn.
Lemma swap_remap2_eqn {A B C : Type} (f : A → B → C) n u v :
  remap2_eqn (n:=n) (swap f) u v = swRemap2 (depswap (remap2_eqn f) u v).
Proof.
  induction u as [ | x n u' Hu']; cbn (* look!!! *).
  - dependent elimination v (* let's have more faith *). cbn (* yes! *).
    reflexivity.
  - dependent elimination v (* let's have more faith *). cbn (* yes! *).
    f_equal. apply Hu'.
Qed.

(* ====================================================================== *)
(* Co-inductive vectors: beyond the scope of Equations *)

CoInductive conat : Set :=
| CO : conat
| CS : conat → conat.

(* Shoud be useful for Equations *)
Derive NoConfusion for conat.

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
Set Elimination Schemes.

(* For convenience in let expressions *)
Notation sinv_covec u := (invproxy u : covec_CS _ _).

(* map2 on co-vectors *)
CoFixpoint cvmap2 {A B C} (f : A → B → C) {n} (v : covec A n) : covec B n → covec C n :=
  match v with
  | [~] => λ _, [~]
  | x ::~ v => λ w, let (y, w) := sinv_covec w in f x y ::~ cvmap2 f v w
  end.

(* -------------------------------------------------------- *)
(* Using the tactic 'inversion', in script mode with refine *)
#[refine]
CoFixpoint cvmap2_inv {A B C : Type} (f : A → B → C) {n} (u : covec A n) :
  covec B n → covec C n :=
  match u with
  | [~]      => λ v, [~]
  | x ::~ u' => λ v, _
  end.
inversion v as [ | y n' v' e].
refine (f x y ::~ cvmap2_inv _ _ _ f _ u' v').
Defined.

(* -------------------------------------------------------- *)
(* Using Equations, an exception is raised *)
(*
Equations cvmap2 {A B C} (f : A → B → C) n (u : covec A n) (v : covec B n) : covec C n :=
  cvmap2 f _ [~] [~] := [~] ;
  cvmap2 f _ (a ::~ u) (b ::~ v) := cvcons (f a b) (cvmap2 f n u v).
*)
