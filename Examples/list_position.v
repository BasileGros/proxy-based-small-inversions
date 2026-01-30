From Examples Require Import examples_header.

(** This file presents a case study on the use of (mainly dependent)
proxy-based small inversions.
The data structure considered represents positions in a polymorphic list.

We start with a program on dependent types using dependent inversion.
We then define a number of basic functions, and illustrate the use of
dependent inversions for proving their properties.

In all comments below, "inversion" refers to proxy-based small
inversions
 *)

(* ---------------------------------------------------------------------- *)
(* A number of programs below use the option type.
   The following basic fact turns out to be convenient. *)
Lemma Some_mono {A} (a1 a2: A) : Some a1 = Some a2 -> a1 = a2.
Proof using Type. congruence. Qed.

(* ====================================================================== *)
(* The  following inductive type encodes positions in a given list.
   We want to define a number of basic functions on this type. *)
Inductive list_position {A} : list A -> Type :=
| HeadPosition x l : list_position (x :: l)
| TailPosition x l (p:list_position l) : list_position (x :: l).

(* Generation of the proxies for non-dependent and dependent inversion *)
Unset Elimination Schemes (* For comfort *).
Derive InvProxy for list_position.
Derive Dependent InvProxy for list_position.
Set Elimination Schemes.

Arguments HeadPosition_cons {_ _ _}.
Arguments TailPosition_cons {_ _ _}.
Arguments HeadPosition_cons_dep {_ _ _}.
Arguments TailPosition_cons_dep {_ _ _}.
(* ---------------------------------------------------------------------- *)
(* The second constructor is injective.
   Note that using f_equal cannot be applied to the dependent proxy function,
   but we only need the non dependent version here. *)
Lemma TailPosition_mono {A:Type} {l:list A} {x} {p1 p2 : list_position l} :
  TailPosition x _ p1 = TailPosition x _ p2 -> p1 = p2.
Proof using Type.
  intro h. apply (f_equal invproxy) in h. simpl in h. congruence.
Qed.

(* ---------------------------------------------------------------------- *)
(* A typical use of dependent inversion. *)
(* Equality of positions is decidable.
   As usual, we proceed by induction on the first position
   followed by a case analysis on the second;
   but the latter requires a dependent inversion.
   We could also proceed by induction on the list,
   followed by two dependent inversions on the positions.
   We first present a script using dinv. *)
Definition list_position_dec :
  forall {A} {l:list A} (p1 p2 : list_position l),
    {p1 = p2} + {p1 <> p2}.
Proof.
  intros A l p1.
  induction p1 as [x l | x l p1 h1]; intros p2; sdinv p2 as [ | p2].
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (h1 p2) as [yes | no]; subst; [left | right].
    + reflexivity.
    + intro e. exact (no (TailPosition_mono e)).
Qed.

(* It can also be considered as a program on dependent types,
   which makes sense because the result is informative.
   Here is a version using programming constructs,
   only proof obligations are kept in interactive mode. *)
Fixpoint list_position_dec_prog {A} {l:list A} (p1 : list_position l) :
  forall p2, {p1 = p2} + {p1 <> p2}.
  refine
   match p1 with
    | HeadPosition x l    =>
        fun p2 =>
          match dinvproxy p2 in list_position_cons_dep _ _ _ p
          return {HeadPosition x l = p} + {HeadPosition x l <> p}
          with
          | HeadPosition_cons_dep   => left _
          | TailPosition_cons_dep p => right _
          end
    | TailPosition x l p1 =>
        fun p2 =>
          match dinvproxy p2 in list_position_cons_dep _ _ _ p
          return {TailPosition x l p1 = p} + {TailPosition x l p1 <> p}
          with
          | HeadPosition_cons_dep    => right _
          | TailPosition_cons_dep p2 =>
              match list_position_dec_prog _ _ p1 p2 with
              | left yes => left _
              | right no => right _
              end
          end
    end.
    + reflexivity.
    + discriminate.
    + discriminate.
    + f_equal; exact yes.
    + intro e. exact (no (TailPosition_mono e)).
Defined.

(* Small inversions can also be nicely combined with Boolean
   small-scale reflection style celebrated in mathcomp.
   We first define a program that returns a Boolean value,
   and then proof that its result reflects the equality
   between the two input list_positions.
   Advantage: the underlying computation is simpler and clearer.
   Small inversions are used both in the program and in the proof.
   Dependent inversion is required in the proof, whereas
   both kind of inversions can be used in the program
   (in contrast with list_position_dec_prog above).
 *)

Fixpoint list_position_bool {A} {l:list A} (p1 : list_position l) :
  forall (p2 : list_position l), bool :=
   match p1 with
    | HeadPosition x l    =>
        fun p2 => match invproxy p2 with
                  | HeadPosition_cons   => true
                  | TailPosition_cons p => false
                  end
    | TailPosition x l p1 =>
        fun p2 => match invproxy p2 with
                  | HeadPosition_cons    => false
                  | TailPosition_cons p2 => list_position_bool p1 p2
                  end
   end.

Lemma list_position_reflect {A} {l:list A} (p1 p2 : list_position l) :
  reflect (p1 = p2) (list_position_bool p1 p2).
Proof.
  induction p1 as [x l | x l p1 h1]; sdinv p2 as [ | p2]; cbn.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (h1 p2) as [yes | no]; [left | right].
    + apply f_equal, yes.
    + intro e. exact (no (TailPosition_mono e)).
Qed.

(* Trivial corollary (nothing is lost) *)
Corollary list_position_dec_alt {A} {l:list A} (p1 p2 : list_position l) :
  {p1 = p2} + {p1 <> p2}.
Proof.
  destruct (list_position_reflect p1 p2) as [yes | no];
    [left; exact yes | right; exact no].
Qed.


(* ====================================================================== *)
(* A propositional variant of the completion lemma described by C.Cornes
   and D.Terrasse. *)
Lemma list_position_split {A} {a: A} {l: list A} (P: list_position (a :: l) -> Prop) :
  P (HeadPosition a l) -> (forall p, P (TailPosition a l p)) ->
  forall p, P p.
Proof.
  intros hhd htl p.
  sdinv p as [ | p].
  - apply hhd.
  - exact (htl p).
Qed.

(* ====================================================================== *)
(* Basic functions on positions *)

Definition first_position {A} (l: list A) : option (list_position l) :=
  match l with
  | []     => None
  | x :: l => Some (HeadPosition x l)
  end.

Fixpoint last_position {A} (l: list A) : option (list_position l) :=
  match l with
  | []     => None
  | x :: l =>
      match last_position l with
      | None    => Some (HeadPosition x l)
      | Some lp => Some (TailPosition x l lp)
      end
  end.

(* The main function studied in this file *)
Fixpoint next_position {A} {l: list A} (p: list_position l) :
  option (list_position l) :=
  match p with
  | HeadPosition x l' =>
      match l' with
      | []       => None
      | x'::l''  => Some (TailPosition x (x' :: l'') (HeadPosition x' l''))
      end
  | TailPosition x l' p' =>
      match next_position p' with
      | None     => None
      | Some np' => Some (TailPosition x l' np')
      end
  end.

(* ---------------------------------------------------------------------- *)
(* Basic properties on position functions.*)

(* A first position cannot be a next position *)
Lemma first_xor_next_position {A} (l : list A) p :
  first_position l = next_position p -> False.
Proof using Type.
  destruct p as [ x l | x l p]; cbn.
  - destruct l as [ | x' l]; congruence.
  - destruct (next_position p); cbn; congruence.
Qed.

(* The proof can also be carried out using inversion,
   if we start with a case analysis on the list. *)
Lemma first_xor_next_position_alt {A} (l : list A) p :
  first_position l = next_position p -> False.
Proof using Type.
  destruct l as [|x [|x' l]]; cbn.
  - inv p.
  - sdinv p as [ | p]; cbn.
    + congruence.
    + destruct (next_position p); cbn; congruence.
  - sdinv p as [ | p]; cbn.
    + congruence.
    + destruct (next_position p); cbn; congruence.
Qed.

(* A helper for the main result *)
Lemma next_position_None {A} {x} {l: list A} (p: list_position l):
  next_position (TailPosition x l p) = None -> next_position p = None.
Proof.
  cbn. destruct (next_position p); congruence.
Qed.

(* ====================================================================== *)
(* This part is devoted to the main result of this file,
   saying that next_position is injective.
 *)

(* The following proof is carried out by induction on the first position,
   then dependent inversion on the second position. *)
Lemma last_position_unique {A}
  {l: list A} (p1 p2 : list_position l) :
  next_position p1 = None -> next_position p2 = None -> p1 = p2.
Proof.
  revert p2.
  induction p1 as [x l | x l p1 h1]; intros p2 e1 e2; sdinv p2 as [ | p2].
  - destruct l as [ | y l]; cbn; congruence.
  - destruct p2 as [y l | y l p2]; cbn in e1; congruence.
  - destruct p1; cbn in e2; congruence.
  - f_equal. apply next_position_None in e1, e2. exact (h1 _ e1 e2).
Qed.

(* The following proof is carried out by induction on the list
   followed by two dependent inversions on the positions
   but we could also proceed by induction on the first position,
   then dependent inversion on the second position *)
Lemma next_position_mono {A} {l: list A} (p1 p2: list_position l): 
  next_position p1 = next_position p2 ->
  p1 = p2.
Proof.
  intro e1.
  destruct (next_position p2) as [ np |] eqn:e2.
  {
    revert np e1 e2; 
      induction l as [| x l hl].
    - sdinv p1.
    - sdinv p1 as [ | p1]; sdinv p2 as [ | p2]; cbn; intro np.
      + destruct l as [|x' l']; cbn [next_position]; try congruence.
      + destruct l as [|x' l']; cbn [next_position]; try congruence.
        intros e1 e2; rewrite <- e2 in e1; clear np e2; exfalso.
        revert e1; case_eq (next_position p2); try congruence.
        intros l ee h; apply first_xor_next_position with _ p2.
        cbn; apply Some_mono, TailPosition_mono in h; congruence.
    + destruct l as [|x' l']; cbn [next_position]; try congruence.
      intros e1 e2; rewrite <- e2 in e1; clear np e2; exfalso.
      revert e1; case_eq (next_position p1); try congruence.
      intros l ee h; apply first_xor_next_position with _ p1.
      cbn; apply Some_mono, TailPosition_mono in h; congruence.
    + specialize (hl p1 p2).
      destruct (next_position p1) as [ np1 | ]; try congruence.
      destruct (next_position p2) as [ np2 | ]; try congruence.
      specialize (hl np1).
      intros e1 e2; f_equal; apply hl.
      ++ reflexivity.
      ++ rewrite <- e1 in e2; apply Some_mono, TailPosition_mono in e2; congruence.
  }
  {
    revert e1 e2; apply last_position_unique.
  }
Qed.

(* ====================================================================== *)
(* An induction principle saying how a property of positions propagates
   back from the last position to the first position in a list.
   As the base case and the step function are expressed on a given list l,
   the induction is carried out on l, and an inversion is required
   on the base case.
 *)
Lemma position_ind_list {A} {l: list A}: forall  P : list_position l -> Prop, 
    (forall p : list_position l, next_position p = None -> P p) ->
    (forall p np : list_position l, next_position p = Some np -> P np -> P p) ->
    forall fp : list_position l, first_position l = Some fp -> P fp.
Proof.
  induction l  as [ | a l hl]; intros P hlast hnext fp ep.
  - inv fp.
  - destruct l as [ | a' l]; apply Some_mono in ep; subst.
    + apply hlast; reflexivity.
    + specialize (hl (fun p => P (TailPosition a (a':: l) p))).
      pose (hh:= hnext (HeadPosition _ _) (TailPosition _ _ (HeadPosition _ _))); 
        apply hh; try reflexivity.
      apply hl; try reflexivity.
      * intros p ep; eapply hlast; simpl in ep |-*; rewrite ep; reflexivity.
      * intros p np ep; eapply hnext; simpl in ep |-*; rewrite ep; reflexivity.
Qed.
