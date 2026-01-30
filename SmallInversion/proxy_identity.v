(** * The proxy adapters for transformations that do not change the order of arguemnts indices and parameters  *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.

(*The proxy adapter for a given constructor.*)
Definition proxy_adapter_identity
  (decl_disp : context_decl) (name_disp : string)
  (transfo_info : transformation_info)
  (cstr : constructor_body)
  : term :=
 (*The calls and context for the later dB and lambdas for the constructor, its parameters and arguments.*)
  let ctx_constructor :=
    [create_context_constructor name_disp cstr]
  in
  let named_params := name_context (pmib transfo_info).(pseudo_params) 1 in
  let calls_params := context_to_call named_params in
  let named_args := name_context cstr.(cstr_args) (S (length named_params)) in
  let call_args := context_to_call named_args in

  (*The inner call to the new constructor*)
  let call_constructor :=
    tApp (tVar ("_"^cstr.(cstr_name))) (calls_params ++ call_args)
  in

  (*Appending the lambdas for arguments, parameters, constructor, and type *)
  let env := (env_quote transfo_info) in
  let lamda_args :=
    append_context_vars_lambda env named_args call_constructor
  in
  let lambda_params := 
    append_context_vars_lambda env named_params lamda_args
  in
  let lambda_cons :=
    append_context_vars_lambda env ctx_constructor lambda_params
  in
  let proxy_adapter :=
    append_context_vars_lambda env [decl_disp] lambda_cons
  in
  proxy_adapter.

Definition proxy_type_adapter_identity (transfo_info : transformation_info)
  : term * list (option term) :=
  let poib := poib transfo_info in
  let name_disp := poib.(pseudo_name) in
  let decl_disp := vass (string_to_aname ("_" ^ name_disp)) poib.(pseudo_type) in
  (*The calls and context for the later dB and lambdas for the type, its parameters and indices.*)
  let named_indices := name_context poib.(pseudo_indices) 0 in
  let ctx_params_indices := named_indices ++ (pmib transfo_info).(pseudo_params) in
  let calls_params_indices := context_to_call ctx_params_indices in
  (*The inner call to the new type*)
  let call_disp := tApp (tVar ("_" ^ name_disp)) calls_params_indices in
  (*Appending the lambdas for arguments, parameters, constructor, and type *)
  let lambda_param_indices :=
    append_context_vars_lambda (env_quote transfo_info) ctx_params_indices call_disp
  in
  let adapter_identity :=
    append_context_vars_lambda (env_quote transfo_info) [decl_disp] lambda_param_indices
  in
  let adapters_cons :=
    map_list_options (proxy_adapter_identity decl_disp name_disp transfo_info) (lctors transfo_info)
  in
  (adapter_identity, adapters_cons).

