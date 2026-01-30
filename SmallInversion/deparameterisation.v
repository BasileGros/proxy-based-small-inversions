(** * Deparametrisation : transforms all parametres of an inductive into indices.*)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.

From SmallInversion Require Import strategy_engine.
From SmallInversion Require Import proxy_identity.

(*In the constructor of the inductive, changes the list of indices and arguments.
 The type telescope doesn't need to change.*)
Definition deparameterisation_constructor (transfo_info : transformation_info) (cons : constructor_body): constructor_body :=
  let new_arity := cons.(cstr_arity) + (pmib transfo_info).(pseudo_npars) in
  let new_indices := telescope_to_indices cons.(cstr_type) 0 in
   let new_args := telescope_to_args cons.(cstr_type) 0 new_arity in
  {|
    cstr_name := cons.(cstr_name);
    cstr_args := new_args;
    cstr_indices := new_indices;
    cstr_arity := new_arity;
    cstr_type := cons.(cstr_type);
  |}.

(*Changes the list of indices of the one_inductive_body.*)
Definition deparameterisation_oib  (transfo_info : transformation_info) : pseudo_oib :=
  let poib := poib transfo_info in
  let new_indices :=
    telescope_to_args
      (poib.(pseudo_type)) 0
      ((length poib.(pseudo_indices)) + (pmib transfo_info).(pseudo_npars))
  in
  {|
    pseudo_name := poib.(pseudo_name);
    pseudo_indices := new_indices;
    pseudo_sort := poib.(pseudo_sort);
    pseudo_type :=  poib.(pseudo_type);
    pseudo_kelim := poib.(pseudo_kelim);
    pseudo_projs := poib.(pseudo_projs);
    pseudo_relevance := poib.(pseudo_relevance)
  |}.

Definition deparameterisation_mib (transfo_info : transformation_info) : pseudo_mib :=
  
  let pmib := pmib transfo_info in
  {|
    pseudo_finite := pmib.(pseudo_finite);
    pseudo_npars :=  0;
    pseudo_params := [];
    pseudo_universes := pmib.(pseudo_universes);
    pseudo_variance := pmib.(pseudo_variance)
  |}.

(*Due to the fact that parameters and arguments are passed to constructors in the proxy,
the proxy itself is the identity.*)
Definition transfo_deparameterisation : transfo :=
  fun transfo_info : transformation_info =>
    let deparam_pmib := deparameterisation_mib transfo_info in
    let deparam_poib := deparameterisation_oib transfo_info in
    let deparam_cons :=
      map_list_options (deparameterisation_constructor transfo_info) (lctors transfo_info)
    in
    
    let new_transfo_info :=
      recreate_transfo_info transfo_info deparam_pmib deparam_poib deparam_cons
    in
    let proxy_adapter_identity := proxy_type_adapter_identity new_transfo_info in
    Success (proxy_adapter_identity, [new_transfo_info] , fun l => l).
