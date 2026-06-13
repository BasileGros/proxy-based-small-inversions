From Stdlib Require Import Utf8.

From Stdlib Require Import List.
Import ListNotations.

(* ====================================================================== *)
(* The "extended example" developed in the last section of
   "The view from the left", McBride & McKinna 2004,
   refered to below as [viewleft04]
   Among other things, this paper illustrates number of subtle points
   on programming with dependent types.
   The framework used is a type theory close to the one that is
   implemented in Agda, with an advanced pattern-matching mechanism
   based on first-order unification, that is more powerful than
   the one available in CIC.
   Surprinsigly, all examples presented in [viewleft04] can be reproduced
   (without the specific syntax of the paper for views) in CIC without
   special care.
   There is only one exception, in the "advanced example" presented at the end,
   dedicated to a type-checker for simply-typed lambda calculs (STLC),
   where *dependent* proxy-based small inversion (PBSI) turns out to be useful.
 
   [viewleft04] uses only types that depend on the length of a list.
   We also experiment with vectors.
   PBSI is used only for 2 basic dependent data types : bounded natural numbers
   and vectors.  The other data structures of [viewleft04]are quite interesting
   by themselves, but can be handled by ordinary CIC.
 *)

(*  *)


(* NB. In this file, we can use Set everywhere in the place of Type *)

(* ================================================================================== *)
(* Bounded natural numbers, aka finite sets?
   Constructors refer to the notation of [viewleft04] *)

Inductive Fin : nat → Type :=
| bullet n : Fin (S n)
| up {n} (i : Fin n) : Fin (S n).

(* PBSI for Fin *)
Variant Fin_O : Type := .
Variant Fin_S (n : nat) : Type :=
| bullet_S : Fin_S n
| up_S (i : Fin n) : Fin_S n.
Definition Fin_proxy_type (n : nat) : Type :=
  match n with O => Fin_O | S n => Fin_S n end.
Definition Fin_proxy {n} (i: Fin n) : Fin_proxy_type n :=
  match i with bullet n => bullet_S n | up i => up_S _ i end.

(* Dependent small inversion for Fin.
   Turns out to be useful in the "find view below *)
Variant Fin_dep_O : Fin O → Type := .
Variant Fin_dep_S (n : nat) : Fin (S n) → Type :=
| bullet_dep_S : Fin_dep_S n (bullet n)
| up_dep_S (i : Fin n) : Fin_dep_S n (up i).
Definition Fin_proxy_type_dep (n : nat) : Fin n → Type :=
  match n with O => Fin_dep_O | S n => Fin_dep_S n end.
Definition Fin_proxy_dep {n} (i: Fin n) : Fin_proxy_type_dep n i :=
  match i with bullet n => bullet_dep_S n | up i => up_dep_S _ i end.

(* -------------------------------------------------- *)

Inductive vect (X : Type) : nat → Type :=
| vnil : vect X O
| vcons n : X → vect X n → vect X (S n).
Arguments vnil {X}.
Arguments vcons {X n}.

(* As we have lists in the file, we introduce a specific notation for vectors *)
Notation "[< >]" := (vnil) (format "[< >]").
Notation "x ::: v" := (vcons x v) (at level 60).
Notation "[< x >]" := (vcons x vnil).
Notation "[< x ; y ; .. ; z >]" :=  (vcons x (vcons y .. (vcons z vnil) ..)).

(* PBSI for vect *)
Variant vect_O (A : Type) : Type :=  vnil_O : vect_O A.
Variant vect_S (A : Type) (n : nat) : Type :=  vcons_S : A → vect A n → vect_S A n.
Arguments vnil_O {A}.
Arguments vcons_S {A n} _.

Definition sinv_vect_type A n : Type :=
  match n with  O => vect_O A  |  S n => vect_S A n  end.

Definition sinv_vect {A n} (u : vect A n) : sinv_vect_type A n :=
  match u with  vnil => vnil_O  |  vcons x u => vcons_S x u  end.

Variant vect_O_dep A : vect A 0 -> Type :=
  vnil_O_dep : vect_O_dep A vnil.
Variant vect_S_dep A n : vect A (S n) -> Type :=
  vcons_S_dep x u : vect_S_dep A n (vcons x u).
Arguments vnil_O_dep {A}.
Arguments vcons_S_dep {A n} _.

Definition sdinv_vect_type A n : vect A n -> Type :=
  match n with  O => vect_O_dep A  |  S n => vect_S_dep A n  end.

Definition sdinv_vect {A n} (u : vect A n) : sdinv_vect_type A n u :=
  match u with  vnil => vnil_O_dep  |  vcons x u => vcons_S_dep x u  end.

(* Convenient notations for (CIC dependent) let expressions *)
Notation "'let_vnil' '()' := E 'in' F" :=
  (let 'vnil_O_dep := E in F)  (at level 200).
Notation "'let_vcons' ( A ,  B ) := E 'in' F" :=
  (let 'vcons_S_dep A B := E in F)  (at level 200, A binder, B binder).

(* ================================================================================== *)
(* Section 7 of [viewleft04] *)

(* Internalized simple types *)
Inductive TExp : Type :=  o : TExp | arrow : TExp → TExp → TExp.

(* pre-terms = well-indexed -- not necessarily well-typed --  expressions *)
Inductive Expr (n : nat) : Type :=
| eVar (i : Fin n) : Expr n
| eApp (f s : Expr n) : Expr n
| eLam (T : TExp) (t : Expr (S n)) : Expr n.
Arguments eVar {n}.
Arguments eApp {n}.
Arguments eLam {n}.

(* 7.1 The find view *)
(* NB. x could be a parameter, but an index does not harm here. *)
Inductive In {X : Type} : list X → X → Type := 
| Ibullet xs x : In (x :: xs) x
| Iup xs x y (i : In xs y) : In (x :: xs) y.

Fixpoint len {X} (l : list X) : nat :=
  match l with [] => O | x :: l => S (len l) end.

Fixpoint forget {X : Type} {xs} {x : X} (ix : In xs x) : Fin (len xs) :=
  match ix with
  | Ibullet xs x => bullet _
  | Iup xs x y ix => up (forget ix)
  end.

(* find is just ith, as specified by the rich approprate type.
   NB. Failure is impossible because the deBruijn index i is bounded,
   therefore we have only one case.  *)
Variant Find {X : Type} (xs : list X) : Fin (len xs) → Type :=
  | found x (ix : In xs x) : Find xs (forget ix).
Arguments found {X xs}.

(* A dependent inverson on i is needed, because the type of the result
   depends on i.
*)

Fixpoint find {X : Type} (xs : list X) : ∀ i : Fin (len xs), Find xs i :=
  match xs with
  | [] => λ i, match Fin_proxy i with end
  | x :: xs => λ i,
      match Fin_proxy_dep i with
      | bullet_dep_S _ => found x (Ibullet xs x)
      | up_dep_S _ i =>
          match find xs i with found y iy => found y (Iup xs x y iy) end
      end
  end.

(* ---------------------------------------------------------------------- *)
(* Alternately, we can use vectors (not in the paper [viewleft04]  *)

(* Function of [viewleft04] defined using vectors *)
Fixpoint vlist {X n} (v : vect X n) : list X :=
  match v with
  | vnil => []
  | vcons x v => x :: vlist v
  end.

Fixpoint lvect {X} (l : list X) : vect X (len l) :=
  match l with
  | [] => vnil
  | x :: l => vcons x (lvect l)
  end.

Inductive vIn {X : Type} : ∀ {n}, vect X n → X → Type :=
| vIbullet {n} (xs : vect X n) x : vIn (vcons x xs) x
| vIup {n} (xs : vect X n) x y (i : vIn xs y) : vIn (vcons x xs) y.

Fixpoint vforget {X : Type} {n} {vxs : vect X n} {x : X} (ix : vIn vxs x) : Fin n :=
  match ix with
  | vIbullet xs x => bullet _
  | vIup xs x y ix => up (vforget ix)
  end.

Variant vFind {X : Type} {n} (xs : vect X n) : Fin n → Type :=
| vfound x (ix : vIn xs x) : vFind xs (vforget ix).
Arguments vfound {X n xs}.

(* For the find view, we still need dependent inversions, for the very same reason
   (the type of the result depends on inputs) bu we have an additional possible
   encoding of the Epigram dependent pattern-matching used in the paper:
   we can start with a pattern-matchin on i, because its actual index
   is a general n -- instead of the expression (len xs) 
*)
Fixpoint vfindi {X : Type} {n} (i : Fin n) : ∀ (xs : vect X n), vFind xs i :=
  match i with
  | bullet n => λ xs,
      let_vcons (x, xs) := sdinv_vect xs in vfound x (vIbullet xs x)
  | up i => λ xs,
      let_vcons (x, xs) := sdinv_vect xs in
      let 'vfound y iy := vfindi i xs in vfound y (vIup xs x y iy)
  end.

Fixpoint vfind {X : Type} {n} (xs : vect X n) : ∀ i : Fin n, vFind xs i :=
  match xs with
  | [<>] => λ i, match Fin_proxy i with end
  | x ::: xs => λ i,
      match Fin_proxy_dep i with
      | bullet_dep_S _ => vfound x (vIbullet xs x)
      | up_dep_S _ i =>
          let 'vfound y iy := vfindi i xs in vfound y (vIup xs x y iy)
      end
  end.

(* End of alternate definitions using vectors *)
(* ---------------------------------------------------------------------- *)

(* 7.2 The type of well-typed terms *)

Inductive Term (Γ : list TExp) : TExp → Type :=
| var {T : TExp} (iT : In Γ T) : Term Γ T
| app {T U} (f : Term Γ (arrow T U)) (s : Term Γ T) : Term Γ U
| lam T {U} (t : Term (T :: Γ) U) : Term Γ (arrow T U).

Fixpoint forgetxp {Γ T} (t : Term Γ T) : Expr (len Γ) :=
  match t with
  | var _ ix => eVar (forget ix)
  | app _ f s => eApp (forgetxp f) (forgetxp s)
  | lam _ T t => eLam T (forgetxp t)
  end.

(* Alternate definition Using vectors *)

Inductive vTerm {n} (Γ : vect TExp n) : TExp → Type :=
| vvar {T : TExp} (iT : vIn Γ T) : vTerm Γ T
| vapp {T U} (f : vTerm Γ (arrow T U)) (s : vTerm Γ T) : vTerm Γ U
| vlam T {U} (t : vTerm (T ::: Γ) U) : vTerm Γ (arrow T U).

Fixpoint vforgetxp {n Γ T} (t : vTerm Γ T) : Expr n :=
  match t with
  | vvar _ ix => eVar (vforget ix)
  | vapp _ f s => eApp (vforgetxp f) (vforgetxp s)
  | vlam _ T t => eLam T (vforgetxp t)
  end.

(* -------------------------------- *)
(* 7.3 The eq? view *)

(* We write testeq for `eq?` *)

Variant Isnt_sig (T : TExp) : Type :=
| isnt_sig U : (T = U → False) → Isnt_sig T.

Definition backsl_sig T (N : Isnt_sig T) : TExp := let (U, _) := N in U.

Inductive Isnt : TExp → Type :=
| isnto (T2 U2 : TExp) : Isnt o
| isntarr T1 U1 : Isnt (arrow T1 U1)
| isntR {T U} (NU : Isnt U) : Isnt (arrow T U)
| isntL {T U1} (NT : Isnt T) (U2 : TExp) : Isnt (arrow T U1).

Fixpoint backsl T (N : Isnt T) : TExp :=
  match N with
  | isnto T2 U2 => arrow T2 U2
  | isntarr T1 U1 => o
  | @isntR T U NU => arrow T (backsl U NU)
  | @isntL T U1 NT U2 => arrow (backsl T NT) U2
  end.

Variant Testeq (T : TExp) : TExp → Type :=
| same : Testeq T T
| diff (N : Isnt T) : Testeq T (backsl T N).

Fixpoint testeq T U : Testeq T U :=
  match T, U with
  | o, o => same _
  | o, arrow T2 U2 => diff o (isnto T2 U2)
  | arrow T1 U1, o => diff (arrow T1 U1) (isntarr T1 U1)
  | arrow T1 U1, arrow T2 U2 =>
      match testeq T1 T2 with
      | same _ =>
          match testeq U1 U2 with
          | same _ => same _
          | diff _ NU => diff _ (isntR NU) (* Testeq (arrow T U) (arrow T (backsl U NU)) *)
          end
      | diff _ NT => diff _ (isntL NT U2) (* Testeq (arrow T U1) (arrow (backsl T NT) U2) *)
       end
  end.

(* -------------------------------- *)
(* 7.4 The check view *)

(* Caveat: the argument of Expr MUST be a parameter
   for Γ and e to be propagated as desired in the pattern-matchin on e.
   This is no longer required if we use vectors instead of lists
   and dependeces on their length.
*)

(* We mimick the incremental interactive approach described in [viewleft04],
   providing an incremental design of Error and uExpr *)

(* We start with positive cases. Then holes are progressively
   refined using  "error (constructor args)";
   their respective signatures are provided by the current subgoal.
   First attempt: Error is empty and uExpr is trivial.  *)

Inductive Error (Γ : list TExp) : Type := .

Definition uExpr {Γ} (err : Error Γ) : Expr (len Γ) :=
  match err with
  end.

Variant Check Γ : Expr (len Γ) → Type :=
| term T (t : Term Γ T) : Check Γ (forgetxp t)
| error (err : Error Γ) : Check Γ (uExpr err).
Arguments term {Γ}.
Arguments error {Γ}.

#[refine]
Fixpoint check Γ (e : Expr (len Γ)) : Check Γ e :=
  match e with
  | eVar i => match find Γ i with found T iT => term T (var Γ iT) end
  | eApp f s =>
      match check Γ f with
      | term F f' =>
          match F return ∀ f', Check Γ (eApp _ s) with
          | o => λ f', _
          | arrow A B => λ f' : Term Γ (arrow A B),
              match check Γ s with
              | term S' s' =>
                 match testeq A S' return ∀ s', Check Γ (eApp (forgetxp f') (forgetxp s'))
                 with
                 | same _ => λ s', term B (app Γ f' s')
                 | diff _ N => λ s', _
                 end s'
              | error err => _
              end
          end f'
      | error err => _
      end
  | eLam T u =>
      match check (T :: Γ) u with
      | term U u' => term (arrow T U) (lam Γ T u')
      | error err => _
      end
  end.

(* The first subgoal is essentially:
  Γ : list TExp
  s : Expr (len Γ)
  f' : Term Γ o
  ============================
  Check Γ (eApp (forgetxp f') s)

This corresponds to trying to apply a term of type o.
We then introduce in Error a constructor `er_o_fct` dedicated to this case,
together with a reduction
   uExpr (er_o_fct Γ f' s)  ▷  eApp (forgetxp f') s
so that the type of `error (er_o_fct Γ f' s)` will match the conclusion
of the above goal.
*)

Abort.

(* -------------- *)
(* Next try *)

Reset Error.
Inductive Error (Γ : list TExp) : Type :=
| er_o_fct (f' : Term Γ o) (s : Expr (len Γ)) : Error Γ.

Definition uExpr {Γ} (err : Error Γ) : Expr (len Γ) :=
  match err with
  | er_o_fct _ f' s => eApp (forgetxp f') s
  end.

Variant Check Γ : Expr (len Γ) → Type :=
| term T (t : Term Γ T) : Check Γ (forgetxp t)
| error (err : Error Γ) : Check Γ (uExpr err).
Arguments term {Γ}.
Arguments error {Γ}.

#[refine]
Fixpoint check Γ (e : Expr (len Γ)) : Check Γ e :=
  match e with
  | eVar i => match find Γ i with found T iT => term T (var Γ iT) end
  | eApp f s =>
      match check Γ f with
      | term F f' =>
          match F return ∀ f', Check Γ (eApp _ s) with
          | o => λ f', error (er_o_fct Γ f' s)
          | arrow A B => λ f' : Term Γ (arrow A B),
              match check Γ s with
              | term S' s' =>
                 match testeq A S' return ∀ s', Check Γ (eApp (forgetxp f') (forgetxp s'))
                 with
                 | same _ => λ s', term B (app Γ f' s')
                 | diff _ N => λ s', _ (* nouveau premier sous-but *)
                 end s'
              | error err => _
              end
          end f'
      | error err => _
      end
  | eLam T u =>
      match check (T :: Γ) u with
      | term U u' => term (arrow T U) (lam Γ T u')
      | error err => _
      end
  end.

(* Similarly as before. Here we have a mismatch between the type of s
   and the type expected by f

  Γ : list TExp
  A, B : TExp
  f' : Term Γ (arrow A B)
  N : Isnt A
  s' : Term Γ (backsl A N)
  ============================
  Check Γ (eApp (forgetxp f') (forgetxp s'))
 *)
Abort.


Reset Error.
Inductive Error (Γ : list TExp) : Type :=
| er_o_fct (f' : Term Γ o) (s : Expr (len Γ)) : Error Γ
| er_mismatch {A B} (f' : Term Γ (arrow A B)) (N : Isnt A) (s' : Term Γ (backsl A N)) : Error Γ
.

Definition uExpr {Γ} (err : Error Γ) : Expr (len Γ) :=
  match err with
  | er_o_fct _ f' s => eApp (forgetxp f') s
  | er_mismatch _ f' N s' => eApp (forgetxp f') (forgetxp s')
  end.

(* And so on ... we get : *)

Reset Error.
Inductive Error (Γ : list TExp) : Type :=
| er_o_fct (f' : Term Γ o) (s : Expr (len Γ)) : Error Γ
| er_mismatch {A B} (f' : Term Γ (arrow A B)) (N : Isnt A) (s' : Term Γ (backsl A N)) :
  Error Γ
(*| er_appR_orig {A B} (f' : Term Γ (arrow A B)) (err : Error Γ) : Error Γ *)
| er_appR (f : Expr (len Γ)) (err : Error Γ) : Error Γ 
| er_appL (err : Error Γ) (s : Expr (len Γ)) : Error Γ 
| er_lam T (err : Error (T :: Γ)) : Error Γ 
.

Fixpoint uExpr {Γ} (err : Error Γ) : Expr (len Γ) :=
  match err with
  | er_o_fct _ f' s => eApp (forgetxp f') s
  | er_mismatch _ f' N s' => eApp (forgetxp f') (forgetxp s')
(*  | er_appR_orig _ f' err => eApp (forgetxp f') (uExpr err)*)
  | er_appR _ f err => eApp f (uExpr err)
  | er_appL _ err s => eApp (uExpr err) s
  | er_lam _ T err => eLam T (uExpr err)
  end.


Variant Check Γ : Expr (len Γ) → Type :=
| term T (t : Term Γ T) : Check Γ (forgetxp t)
| error (err : Error Γ) : Check Γ (uExpr err).
Arguments term {Γ}.
Arguments error {Γ}.

Fixpoint check Γ (e : Expr (len Γ)) : Check Γ e :=
  match e with
  | eVar i => match find Γ i with found T iT => term T (var Γ iT) end
  | eApp f s =>
      match check Γ f with
      | term F f' =>
          match F return ∀ f', Check Γ (eApp _ s) with
          | o => λ f', error (er_o_fct Γ f' s)
          | arrow A B => λ f' : Term Γ (arrow A B),
              match check Γ s with
              | term S' s' =>
                 match testeq A S' return ∀ s', Check Γ (eApp (forgetxp f') (forgetxp s'))
                 with
                 | same _ => λ s', term B (app Γ f' s')
                 | diff _ N => λ s', error (er_mismatch Γ f' N s')
                 end s'
              | error err => error (er_appR Γ _ err)
              end
          end f'
      | error err => error (er_appL Γ err _)
      end
  | eLam T u =>
      match check (T :: Γ) u with
      | term U u' => term (arrow T U) (lam Γ T u')
      | error err => error (er_lam Γ T err)
      end
  end.

(* ------------------------------------------------------------ *)
(* Using vectors *)

Inductive vError {n} (Γ : vect TExp n) : Type :=
| ver_o_fct (f' : vTerm Γ o) (s : Expr n) : vError Γ
| ver_mismatch {A B} (f' : vTerm Γ (arrow A B)) (N : Isnt A) (s' : vTerm Γ (backsl A N)) :
  vError Γ
(*| er_appR_orig {A B} (f' : Term Γ (arrow A B)) (err : vError Γ) : vError Γ *)
| ver_appR (f : Expr n) (err : vError Γ) : vError Γ 
| ver_appL (err : vError Γ) (s : Expr n) : vError Γ 
| ver_lam T (err : vError (T ::: Γ)) : vError Γ 
.

Fixpoint uvExpr {n} {Γ : vect TExp n} (err : vError Γ) : Expr n :=
  match err with
  | ver_o_fct _ f' s => eApp (vforgetxp f') s
  | ver_mismatch _ f' N s' => eApp (vforgetxp f') (vforgetxp s')
(*  | ver_appR_orig _ f' err => veApp (vforgetxp f') (uvExpr err)*)
  | ver_appR _ f err => eApp f (uvExpr err)
  | ver_appL _ err s => eApp (uvExpr err) s
  | ver_lam _ T err => eLam T (uvExpr err)
  end.

Variant vCheck {n} (Γ : vect TExp n) : Expr n → Type :=
| vterm T (t : vTerm Γ T) : vCheck Γ (vforgetxp t)
| verror (err : vError Γ) : vCheck Γ (uvExpr err).
Arguments vterm {n Γ}.
Arguments verror {n Γ}.

Fixpoint vcheck {n} (Γ : vect TExp n) (e : Expr n) : vCheck Γ e :=
  match e with
  | eVar i => match vfind Γ i with vfound T iT => vterm T (vvar Γ iT) end
  | eApp f s =>
      match vcheck Γ f with
      | vterm F f' =>
          match F return ∀ f', vCheck Γ (eApp _ s) with
          | o => λ f', verror (ver_o_fct Γ f' s)
          | arrow A B => λ f' : vTerm Γ (arrow A B),
              match vcheck Γ s with
              | vterm S' s' =>
                 match testeq A S' return ∀ s', vCheck Γ (eApp (vforgetxp f') (vforgetxp s'))
                 with
                 | same _ => λ s', vterm B (vapp Γ f' s')
                 | diff _ N => λ s', verror (ver_mismatch Γ f' N s')
                 end s'
              | verror err => verror (ver_appR Γ _ err)
              end
          end f'
      | verror err => verror (ver_appL Γ err _)
      end
  | eLam T u =>
      match vcheck (T ::: Γ) u with
      | vterm U u' => vterm (arrow T U) (vlam Γ T u')
      | verror err => verror (ver_lam Γ T err)
      end
  end.

(* Here we have the option to use iExpr (with n as an index instead of a parameter) *)

Reset vError.

Inductive iExpr : nat → Type :=
| ieVar {n} (i : Fin n) : iExpr n
| ieApp {n} (f s : iExpr n) : iExpr n
| ieLam {n} (T : TExp) (t : iExpr (S n)) : iExpr n.

Fixpoint ivforgetxp {n Γ T} (t : vTerm Γ T) : iExpr n :=
  match t with
  | vvar _ ix => ieVar (vforget ix)
  | vapp _ f s => ieApp (ivforgetxp f) (ivforgetxp s)
  | vlam _ T t => ieLam T (ivforgetxp t)
  end.

Inductive vError {n} (Γ : vect TExp n) : Type :=
| ver_o_fct (f' : vTerm Γ o) (s : iExpr n) : vError Γ
| ver_mismatch {A B} (f' : vTerm Γ (arrow A B)) (N : Isnt A) (s' : vTerm Γ (backsl A N)) :
  vError Γ
(*| er_appR_orig {A B} (f' : Term Γ (arrow A B)) (err : vError Γ) : vError Γ *)
| ver_appR (f : iExpr n) (err : vError Γ) : vError Γ 
| ver_appL (err : vError Γ) (s : iExpr n) : vError Γ 
| ver_lam T (err : vError (T ::: Γ)) : vError Γ 
.

Fixpoint uviExpr {n} {Γ : vect TExp n} (err : vError Γ) : iExpr n :=
  match err with
  | ver_o_fct _ f' s => ieApp (ivforgetxp f') s
  | ver_mismatch _ f' N s' => ieApp (ivforgetxp f') (ivforgetxp s')
(*  | ver_appR_orig _ f' err => veApp (vforgetxp f') (uviExpr err)*)
  | ver_appR _ f err => ieApp f (uviExpr err)
  | ver_appL _ err s => ieApp (uviExpr err) s
  | ver_lam _ T err => ieLam T (uviExpr err)
  end.

Variant vCheck {n} (Γ : vect TExp n) : iExpr n → Type :=
| vterm T (t : vTerm Γ T) : vCheck Γ (ivforgetxp t)
| verror (err : vError Γ) : vCheck Γ (uviExpr err).
Arguments vterm {n Γ}.
Arguments verror {n Γ}.


Fixpoint ivcheck {n} (e : iExpr n) : ∀ Γ : vect TExp n, vCheck Γ e :=
  match e with
  | ieVar i => λ Γ, match vfind Γ i with vfound T iT => vterm T (vvar Γ iT) end
  | ieApp f s => λ Γ,
      match ivcheck f Γ with
      | vterm F f' =>
          match F return ∀ f', vCheck Γ (ieApp _ s) with
          | o => λ f', verror (ver_o_fct Γ f' s)
          | arrow A B => λ f' : vTerm Γ (arrow A B),
              match ivcheck s Γ with
              | vterm S' s' =>
                 match testeq A S' return ∀ s', vCheck Γ (ieApp (ivforgetxp f') (ivforgetxp s'))
                 with
                 | same _ => λ s', vterm B (vapp Γ f' s')
                 | diff _ N => λ s', verror (ver_mismatch Γ f' N s')
                 end s'
              | verror err => verror (ver_appR Γ _ err)
              end
          end f'
      | verror err => verror (ver_appL Γ err _)
      end
  | ieLam T u => λ Γ,
      match ivcheck u (T ::: Γ) with
      | vterm U u' => vterm (arrow T U) (vlam Γ T u')
      | verror err => verror (ver_lam Γ T err)
      end
  end.


(* =========================================================================== *)
