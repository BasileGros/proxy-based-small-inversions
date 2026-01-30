From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
Import MRMonadNotation.

From SmallInversion Require Import MR_interface strategy_creation.


(** * Functions used by the OCaml UI of the plugin*)
Definition derive_proxy {T} (x : T) : TemplateMonad unit :=
  TmExecuteStrategy x strategy_specialisation "".

Register derive_proxy as small_inversion.derive_proxy.

Definition derive_dependent_proxy {T} (x : T) : TemplateMonad unit :=
  TmExecuteDependentStrategy x strategy_specialisation "".

Register derive_dependent_proxy as small_inversion.derive_dependent_proxy.

Definition derive_one_proxy {T} (x : T)(n:nat) : TemplateMonad unit :=
  TmExecuteStrategy x (strategy_single_specialisation n) "".

Register derive_one_proxy as small_inversion.derive_one_proxy.

Definition derive_dependent_one_proxy {T} (x : T)(n:nat) : TemplateMonad unit :=
  TmExecuteDependentStrategy x (strategy_single_specialisation n) "".

Register derive_dependent_one_proxy as small_inversion.derive_dependent_one_proxy.

Definition derive_pattern_proxy {T} (x : T)(patt:inversion_pattern) : TemplateMonad unit :=
  TmExecuteStrategy x (strategy_pattern_specialisation patt) "".

Register derive_pattern_proxy as small_inversion.derive_pattern_proxy.

Definition derive_dependent_pattern_proxy {T} (x : T)(patt:inversion_pattern) : TemplateMonad unit :=
  TmExecuteDependentStrategy x (strategy_pattern_specialisation patt) "".

Register derive_dependent_pattern_proxy as small_inversion.derive_dependent_pattern_proxy.

(*THe same, for a given prefix*)

Definition derive_proxy_prefix {T} (x : T)(prefix : string) : TemplateMonad unit :=
  TmExecuteStrategy x strategy_specialisation prefix.

Register derive_proxy_prefix as small_inversion.derive_proxy_prefix.

Definition derive_dependent_proxy_prefix {T} (x : T)(prefix : string) : TemplateMonad unit :=
  TmExecuteDependentStrategy x strategy_specialisation prefix.

Register derive_dependent_proxy_prefix as small_inversion.derive_dependent_proxy_prefix.

Definition derive_one_proxy_prefix {T} (x : T)(n:nat)(prefix : string) : TemplateMonad unit :=
  TmExecuteStrategy x (strategy_single_specialisation n) prefix.

Register derive_one_proxy_prefix as small_inversion.derive_one_proxy_prefix.

Definition derive_dependent_one_proxy_prefix {T} (x : T)(n:nat)(prefix : string) : TemplateMonad unit :=
  TmExecuteDependentStrategy x (strategy_single_specialisation n) prefix.

Register derive_dependent_one_proxy_prefix as small_inversion.derive_dependent_one_proxy_prefix.

Definition derive_pattern_proxy_prefix {T} (x : T)(patt:inversion_pattern)(prefix : string) : TemplateMonad unit :=
  TmExecuteStrategy x (strategy_pattern_specialisation patt) prefix.

Register derive_pattern_proxy_prefix as small_inversion.derive_pattern_proxy_prefix.

Definition derive_dependent_pattern_proxy_prefix {T} (x : T)(patt:inversion_pattern)(prefix : string) : TemplateMonad unit :=
  TmExecuteDependentStrategy x (strategy_pattern_specialisation patt) prefix.

Register derive_dependent_pattern_proxy_prefix as small_inversion.derive_dependent_pattern_proxy_prefix.




Declare ML Module "small-inversion.plugin".
