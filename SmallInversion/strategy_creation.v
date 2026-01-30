From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.

From SmallInversion Require Import derecursivation.
From SmallInversion Require Import deparameterisation.
From SmallInversion Require Import dependent.
From SmallInversion Require Import parameterisation.
From SmallInversion Require Import strategy_engine.
From SmallInversion Require Import strategy_debug.
From SmallInversion Require Import specialisation.
From SmallInversion Require Import proxy0.
From utils Require Import utils.


Fixpoint sequence (l : list transfo)
  (strat_end : transformation_info ->  strategy) : transformation_info ->  strategy  :=
  match l with
  |[] => strat_end
  |hd::tl => fun _ => strat_Cons no_debug hd (sequence tl strat_end)
  end.

Fixpoint first_from_list {A}
  (l:list A) (param_transfo: A -> transfo)
  (on_success: transformation_info -> strategy)
  (on_failure: strategy)
  : strategy :=
  match l with
  | [] => on_failure
  | a :: q =>
      strat_Orelse
        (strat_Cons no_debug (param_transfo a) on_success)
        (first_from_list q param_transfo on_success on_failure)
  end.

CoFixpoint iter_choices_ {A}
  (genchoices:transformation_info -> list A)
  (choices: list A)
  (param_transfo: A -> transfo)
  (on_end: transformation_info -> strategy)
  (info : transformation_info):=
  match choices with
  | [] => on_end info
  | a :: remaining_choices =>
      strat_Orelse
        (strat_Cons no_debug (param_transfo a) (iter_choices_ genchoices (genchoices info) param_transfo on_end))
        (iter_choices_ genchoices remaining_choices param_transfo on_end info)
  end.

Definition iter_choices {A}
  (genchoices:transformation_info -> list A)
  (param_transfo: A -> transfo)
  (on_end: transformation_info -> strategy)
  (info : transformation_info):=
  iter_choices_  genchoices (genchoices info) param_transfo on_end info.

CoFixpoint debug_iter_choices_ {A}
  (genchoices:transformation_info -> list A)
  (choices: list A)
  (param_transfo: A -> transfo)
  (on_end: transformation_info -> strategy)
  (info : transformation_info):=
  match choices with
  | [] => on_end info
  | a :: remaining_choices =>
      strat_Orelse
        (strat_Cons later_debug (param_transfo a) (debug_iter_choices_ genchoices (genchoices info) param_transfo on_end))
        (debug_iter_choices_ genchoices remaining_choices param_transfo on_end info)
  end.

Definition debug_iter_choices {A}
  (genchoices:transformation_info -> list A)
  (param_transfo: A -> transfo)
  (on_end: transformation_info -> strategy)
  (info : transformation_info):=
   debug_iter_choices_  genchoices (genchoices info) param_transfo on_end info.

Definition strategy_identity  : strategy :=
  strat_Cons no_debug finalize_proxy (fun _ => strat_Fail).

Definition debug_strategy_identity  : strategy :=
  strat_Cons here_debug finalize_proxy (fun _ => strat_Fail).


Definition strategy_deparam : strategy :=
 strat_Cons no_debug transfo_deparameterisation (fun _ => strategy_identity).
Definition debug_strategy_deparam : strategy :=
 strat_Cons later_debug transfo_deparameterisation (fun _ => debug_strategy_identity).
Definition strategy_param : strategy :=
 strat_Cons no_debug transfo_parameterisation (fun _ => strategy_identity).
Definition debug_strategy_param : strategy :=
 strat_Cons later_debug transfo_parameterisation (fun _ => debug_strategy_identity).



Definition strategy_deparam_param : strategy :=
  strat_Cons no_debug transfo_deparameterisation (fun _ => strategy_param).
Definition debug_strategy_deparam_param : strategy :=
  strat_Cons later_debug transfo_deparameterisation (fun _ => debug_strategy_param).

Definition genchoices_specialisation
  (transfo_info : transformation_info)
  : list nat :=
  range_nat (length (poib transfo_info).(pseudo_indices)) 0.

Definition strategy_specialisation : strategy :=
  strat_Cons no_debug transfo_deparameterisation
    (iter_choices
       genchoices_specialisation
       (transfo_specialisation false)
       (fun _ => strategy_param)).

Definition precise_strategy_specialisation (n:nat) : strategy :=
  strat_Cons no_debug (transfo_specialisation true n) (fun _ => strategy_param).

Definition strategy_single_specialisation (n:nat) : strategy :=
  strat_Cons no_debug transfo_deparameterisation (fun _ => precise_strategy_specialisation n).


Definition debug_precise_strategy_specialisation (n:nat) : strategy :=
  strat_Cons later_debug (transfo_specialisation true n) (fun _ => debug_strategy_param).

Definition debug_strategy_single_specialisation (n:nat) : strategy :=
  strat_Cons later_debug transfo_deparameterisation (fun _ => debug_precise_strategy_specialisation n).

Definition debug_strategy_specialisation : strategy :=
  strat_Cons later_debug transfo_deparameterisation
    (debug_iter_choices
       genchoices_specialisation
       (transfo_specialisation false)
       (fun _ => debug_strategy_param)).

Inductive inversion_pattern :=
|noInversion
|pilotInversion : nat -> list inversion_pattern -> inversion_pattern.

Fixpoint create_branching_specialisation (patt:inversion_pattern) : strategy :=
  match patt with
  |noInversion => strategy_param
  |pilotInversion n lp =>
     let lstrats := map (fun p => (fun _ => create_branching_specialisation p)) lp in
     strat_Cons_Multiple no_debug (transfo_specialisation true n) lstrats
  end.

Definition strategy_pattern_specialisation (patt:inversion_pattern) : strategy :=
  strat_Cons no_debug transfo_deparameterisation (fun _ => create_branching_specialisation patt).

Fixpoint debug_create_branching_specialisation (patt:inversion_pattern) : strategy :=
  match patt with
  |noInversion => debug_strategy_param
  |pilotInversion n lp =>
     let lstrats := map (fun p => (fun _ => debug_create_branching_specialisation p)) lp in
     strat_Cons_Multiple later_debug (transfo_specialisation true n) lstrats
  end.

Definition debug_strategy_pattern_specialisation (patt:inversion_pattern) : strategy :=
  strat_Cons later_debug transfo_deparameterisation (fun _ => debug_create_branching_specialisation patt).
