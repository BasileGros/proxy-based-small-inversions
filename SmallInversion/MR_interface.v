(** * Metarocq functions to call on the code. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.

From SmallInversion Require Import data_extraction.
From SmallInversion Require Import derecursivation.
From SmallInversion Require Import strategy_engine.
From SmallInversion Require Import strategy_debug.
From SmallInversion Require Import proxy0.

From SmallInversion Require Import strategy_creation.
From utils Require Import utils.

(** Different functions to access and use proxy0 as a standalone.*)
(*TODO tmExistingInstance pour proxy_0*)
Definition proxy0{X} (R:X) (suffix : string):=
  derec_transfo_info <-- data_extraction R "" false;;
  term_proxy <-- tmErrorReturn (create_proxy0 derec_transfo_info);;
  tmMkDefinition "Proxy0" term_proxy.

Definition print_proxy0{X} (R:X) (suffix : string):=
  derec_transfo_info <-- data_extraction R "" false;;
  term_proxy <-- tmErrorReturn (create_proxy0 derec_transfo_info);;
  tmPrint term_proxy.


(** MetaRocq calls to execute strategies in different modes.*)

(*The one you want, executes the strategy and defines in Rocq the resulting inductives and proxy instance in the context of Rocq.*)

Definition TmExecuteStrategy {X}(R : X) (strat: strategy) (prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix false;;
  '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- define_list_glob_def diffs;;
  let  name_proxy0 := prefix ^ (poib derec_transfo_info).(pseudo_name) ^"_proxy" in
  _ <-- tmMkDefinition name_proxy0 typeclass;;
  tmExistingInstance global (ConstRef (modpath_call derec_transfo_info,name_proxy0)).

Definition TmDebugStrategy {X}(R : X) (strat: strategy) (prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix false;;
  '(proxy_0, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- define_list_glob_def diffs;;
tmMkDefinition "Proxy0" proxy_0.

Definition TmPrintStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix false;;
  '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- print_list_glob_def (env_quote derec_transfo_info) diffs;;
  tmMsg (pTerm (env_quote derec_transfo_info) [] typeclass).

Definition TmPrintDebugStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix false;;
  '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- print_list_glob_def (env_quote derec_transfo_info) diffs;;
  tmMsg (pTerm (env_quote derec_transfo_info) [] typeclass).

Definition TmUglyPrintStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix false;;
  '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- ugly_print_list_glob_def (env_quote derec_transfo_info) diffs;;
  eval_print typeclass.

(** MetaRocq calls to execute strategies with depedendent inversion constructs in different modes.*)

(*The one you want, executes the strategy and defines in Rocq the resulting inductives and proxy instance in the context of Rocq.*)

Definition TmExecuteDependentStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
 derec_transfo_info <-- data_extraction R prefix true;;
 '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
 _ <-- define_list_glob_def diffs;;
  let  name_proxy0 := prefix ^ (poib derec_transfo_info).(pseudo_name) ^"_dproxy" in
  _ <-- tmMkDefinition name_proxy0 typeclass;;
tmExistingInstance global (ConstRef (modpath_call derec_transfo_info,name_proxy0)).

Definition TmDebugDependentStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix true;;
  '(proxy_0, diffs) <-- tmErrorReturn (debug_strategy_err strat derec_transfo_info);;
  _ <-- define_list_glob_def diffs;;
tmMkDefinition "Proxy0" proxy_0.

Definition TmPrintDependentStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix true;;
  '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- print_list_glob_def (env_quote derec_transfo_info) diffs;;
  tmMsg (pTerm (env_quote derec_transfo_info) [] typeclass).

Definition TmPrintDebugDependentStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix true;;
  '(typeclass, diffs) <-- tmErrorReturn (debug_strategy_err strat derec_transfo_info);;
  _ <-- print_list_glob_def (env_quote derec_transfo_info) diffs;;
  tmMsg (pTerm (env_quote derec_transfo_info) [] typeclass).

Definition TmUglyPrintDependentStrategy {X}(R : X) (strat: strategy)(prefix : string) :=
  derec_transfo_info <-- data_extraction R prefix true;;
  '(typeclass, diffs) <-- tmErrorReturn (execute_strategy_err strat derec_transfo_info);;
  _ <-- ugly_print_list_glob_def (env_quote derec_transfo_info) diffs;;
  eval_print typeclass.
