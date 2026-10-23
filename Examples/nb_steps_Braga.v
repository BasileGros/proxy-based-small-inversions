(* Jean-François Monin, Verimag
   CNRS, INP, University Grenoble Alpes
   2026 *)

(* We illustrate here how proxy-based small inversions (PBSI)
   can be used in combination with in the Braga method [Braga21].
   As a quick reminder, in order to write a partial recursive
   function f, this method starts from the "syntactic relational
   specification" Gf of f and derives from Gf a termination
   certificate Df that characterizes the domain of f.
   In the general case, if the type of the extracted version
   of f is X → Y, its complete CIC type will be

   ∀ x : X, Df x → {y : Y | Gf x y}.                        (1)

   Gf occurs in Df only when f is defined using embedded recursion.
   If that is not the case, it is no longer necessary to further burden
   the output CIC type of f and we can take instead the simpler type:

   ∀ x : X, Df x → Y.                                       (2)

   In version (1), partial correctness properties of f are better
   expressed using Gf.
   In version (2), it is possible to use a more direct approach,
   for example:
   ∀ x (δ : Df x), Pre x → Post x (f x δ).
   We can also start with the special case
   ∀ x (δ : Df x), Gf x (f x δ)
   and then, again, consider desired partial correctness properties of
   f as corollaries of properties of Gf.

   In this process, we typically get subgoals 

      δ : D e
      t : ... e ...
      ====================
      P e δ t (f e δ)

   where e is an expression given by a specific pattern of type X.
   Then, dependent PBSI turn out to be useful
   in order to reason by dependent inversion on δ.

   We also illustrate how (Boolean) reflection can be used
   for reasoning on Gf.

   As a simple example, we consider the introductory example ns
   of [Braga21: given a type X, a test function (b : X -> bool)
   a step function (g : X → X) and an initial value x : X,
   we want to compute the smaller number of steps n such that
   b (g^n x) is true, when such an n exists.
   The intended ocaml recursive program is
     let rec ns x = if b x then 0 else 1 + ns (g x)
   [Braga21] also considers a tail recursive version
     let rec nsa x a = if b x then a else nsa (g x) (1 + n)
   and proves:
     ∀ n, nsa x 0 = ns x

   [Braga21] The Braga Method: Extracting Certified Algorithms from
     Complex Recursive Schemes in Coq, D. Larchey-Wendling, JF. Monin,
     2021. https://doi.org/10.1142/9789811236488_0008

*)

From Stdlib Require Import Utf8 Extraction.
From SmallInversion Require Import small_inversion.

Section sec_ns.

Variable (X : Type) (g : X → X) (b : X → bool).

Unset Elimination Schemes.

(* In constrast  with [Braga21], we use a syntactic specification and
   a domain that does not use equality. The computation of (b x)
   introduces a control point that is modeled using mutual recursion. *)

Inductive Gns (x : X) : nat → Prop :=
| Gns_test n : Gnst x (b x) n → Gns x n
with Gnst (x : X) : bool → nat → Prop :=
| Gnst_tr : Gnst x true O
| Gnst_fa n : Gns (g x) n → Gnst x false (S n).

Inductive Dns (x : X) : Prop :=
| Dns_test : Dnst x (b x) → Dns x
with Dnst (x : X) : bool → Prop :=
| Dnst_tr : Dnst x true
| Dnst_fa : Dns (g x) → Dnst x false.

(* Any inhabitant of Gns provides a termination certificate *)
Fixpoint Gns_Dns {x n} (γ : Gns x n) : Dns x :=
  match γ with
  | Gns_test _ n γ => Dns_test x
      match γ in Gnst _ b n return Dnst _ b with
      | Gnst_tr _     => Dnst_tr x
      | Gnst_fa _ n γ => Dnst_fa x (Gns_Dns γ)
      end
  end.

Derive Dependent InvProxy for Dnst.

(* Small projection for Dnst_fa *)
Definition Dnst_fa_pi x (δ : Dnst x false) : Dns (g x) :=
  match δ in Dnst _ b return
        let sh := match b with false => True | _ => False end in
        sh → Dns (g x) with
  | Dnst_fa _ δ => λ sh, δ
  | _           => λ sh, match sh with end
  end I.

Fixpoint ns x (δ : Dns x) : nat :=
  let (δ) := δ in
  match b x as t return Dnst x t → nat with
  | true  => λ δ, 0
  | false => λ δ, let δ := Dnst_fa_pi x δ in
                  S (ns (g x) δ)
  end δ.

(* Auxiliary function that is used to express a convenient recursive equation *)
Definition nst x t : Dnst x t → nat :=
  match t with
  | true  => λ δ, 0
  | false => λ δ, let δ := Dnst_fa_pi x δ in
                  S (ns (g x) δ)
  end.

Lemma ns_eq x (δ : Dns x) : ns x δ = nst x (b x) (let (δ) := δ in δ).
Proof. destruct δ as [δ]. reflexivity. Qed.

(* Correctness: the output of ns satisfies Gns *)
Fixpoint ns_Gns {x} (δ : Dns x) : Gns x (ns x δ).
Proof.
  apply Gns_test.
  destruct δ as [δ]. cbn.
  destruct δ as [ | δ]; cbn.
  - apply Gnst_tr.
  - apply Gnst_fa, ns_Gns.
Qed.

(* Completeness: any output of Gns can be computed by ns,
   given an arbitrary termination certificate for ns *)
Fixpoint Gns_ns {x n} (γ : Gns x n) : ∀ δ, n = ns x δ.
Proof.
  intro δ.
  destruct γ as [n γ]. destruct δ as [δ]. cbn.
  destruct γ as [ | n γ].
  - reflexivity.
  - f_equal. apply Gns_ns, γ.
Qed.

(* The output of ns does not depend on δ.
   We use dependent PBSI. *)
Fixpoint ns_Dirr x (δ δ' : Dns x) : ns x δ = ns x δ'.
Proof.
  do 2 rewrite ns_eq.
  destruct δ as [δ]. destruct δ' as [δ'].
  destruct (b x).
  - cbn. reflexivity.
  - cbn. sdinv δ' as [δ']. cbn. rewrite (ns_Dirr (g x) _ δ'). reflexivity.
Qed.

(* Tail recursive version *)
Fixpoint nsa x (a : nat) (δ : Dns x) : nat :=
  let (δ) := δ in
  match b x as t return Dnst x t → nat with
  | true  => λ δ, a
  | false => λ δ, let δ := Dnst_fa_pi x δ in
                  nsa (g x) (S a) δ
  end δ.

Definition nsat x a t : Dnst x t → nat :=
  match t with
  | true  => λ δ, a
  | false => λ δ, let δ := Dnst_fa_pi x δ in
                  nsa (g x) (S a) δ
  end.

Lemma nsa_eq x a (δ : Dns x) : nsa x a δ = nsat x a (b x) (let (δ) := δ in δ).
Proof. destruct δ as [δ]. reflexivity. Qed.

(* As in [Braga21]. This result is easy because we use the same δ. *)
Fixpoint nsa_ns x a δ : nsa x a δ = ns x δ + a.
Proof.
  rewrite ns_eq. rewrite nsa_eq.
  destruct δ as [δ].
  destruct (b x).
  - cbn. reflexivity.
  - cbn. rewrite nsa_ns, plus_n_Sm. reflexivity.
Qed.

(* Additional partial correctness properties.
   We consider a decidable predicate P that is reflected by b. *)

Variable P : X → Prop.
Hypothesis rf : ∀ x, reflect (P x) (b x).

(* We then consider the following big-step semantics of ns

           P x                    ¬ P x    BSns (g x) n
        --------                 ----------------------
        BSns x 0                       BSns x (S n)
 *)

Inductive BSns (x : X) : nat → Prop :=
| BSns_stop : P x → BSns x O
| BSns_next : ~(P x) → ∀ n, BSns (g x) n → BSns x (S n).

(* However, in order to prove that Gns is included in BSns,
   reasoning by (small) inversion on reflect is needed.
 
   Remark: here we reason only on inductive relations. This kind of
   theorem can be proven independently of the presence of embedded
   recursion in f -- or Gf. *)

Derive InvProxy for reflect.

Fixpoint Gns_BSns x n (γ : Gns x n) : BSns x n.
Proof.
  destruct γ as [n γ].
  generalize (rf x).
  destruct γ as [ | n γ]; intro rfx.
  - sinv rfx as [yes]. apply (BSns_stop _ yes).
  - sinv rfx as [no]. apply (BSns_next _ no). apply Gns_BSns. exact γ.
Qed.

(* Remark: the simplest way to handle Boolean reflection would be
   to first reason by cases on (rf x), and then to proceed by inversion on γ.
   But the guard condition would then be violated. *)
Derive InvProxy for Gnst with index 1.

Fixpoint Gns_BSns_naive x n (γ : Gns x n) : BSns x n.
Proof.
  destruct γ as [n γ].
  destruct (rf x) as [yes | no].
  - sinv γ. apply (BSns_stop _ yes).
  - sinv γ as [n γ']. apply (BSns_next _ no). apply Gns_BSns_naive.
    Guarded. exact γ'. Fail Guarded.
Abort.

(* A corollary of previous lemmas *)
Corollary ns_BSns x δ : BSns x (ns x δ).
Proof. apply Gns_BSns, ns_Gns. Qed.

(* A direct proof of the previous corollary. *)
Fixpoint ns_BSns_direct x δ : BSns x (ns x δ).
Proof.
  rewrite ns_eq.
  destruct δ as [δ].
  generalize (rf x).
  destruct δ as [ | δ]; intro rfx; cbn.
  - sinv rfx as [yes]. apply (BSns_stop _ yes).
  - sinv rfx as [no]. apply (BSns_next _ no). apply ns_BSns_direct.
Qed.

(* Remark: here, the "naive" approach works as well. *)
Fixpoint ns_BSns_direct_naive x δ : BSns x (ns x δ).
Proof.
  rewrite ns_eq.
  destruct δ as [δ].
  destruct (rf x) as [yes | no].
  - cbn. apply (BSns_stop _ yes).
  - cbn. apply (BSns_next _ no). apply ns_BSns_direct_naive.
Qed.

End sec_ns.
