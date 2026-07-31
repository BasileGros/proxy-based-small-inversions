From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.
From SmallInversion Require Import strategy_engine.

Definition finalize_constructor
  (transfo_info: transformation_info) (index_constructor : nat) (c : constructor_body)
  : term :=
  let lambda_params := rev_params_into_lambdas (pmib transfo_info).(pseudo_params) in
  let lambda_args := rev_params_into_lambdas c.(cstr_args) in
  let dB_args := rev_range_deBruijn (length c.(cstr_args) + (pmib transfo_info).(pseudo_npars)) 0 in
  (lambda_params
     (lambda_args
        (tApp (tConstruct (inductive_transfo transfo_info) index_constructor []) dB_args))).

(*Adds the references to the partial inductive types and proxy type to the proxy, and add the prefix to the different names.*)
Definition finalize_proxy
  : transformation :=
  fun transfo_info =>
    let poib := poib transfo_info in
    let prefix := prefix transfo_info in
    let renamed_poib :=
      if isdep transfo_info
      then
        rename_poib prefix "_dep" poib
      else
        rename_poib prefix "" poib
    in
    let renamed_constructors :=
      if isdep transfo_info
      then
        map_list_options (rename_cstr prefix "_dep") (lctors transfo_info)
      else
        map_list_options (rename_cstr prefix "") (lctors transfo_info)
    in
    let renamed_mib := recreate_mib' (pmib transfo_info) renamed_poib renamed_constructors in
    let renamed_transfo_info :=
      recreate_transfo_info
        transfo_info
        (pmib transfo_info)
        renamed_poib
        renamed_constructors
    in
    let renamed_inductive :=
      if isdep transfo_info
      then
        rename_inductive prefix "_dep" (inductive_transfo transfo_info)
      else
        rename_inductive prefix "" (inductive_transfo transfo_info)
    in
    let list_ctors :=
      mapi_list_options'
        (fun n c => ( finalize_constructor renamed_transfo_info n c))
        renamed_constructors
    in
    Success ((tInd renamed_inductive [], list_ctors),[], (fun env => DefInductive "Finalize_proxy" transfo_info renamed_mib :: env) ).
