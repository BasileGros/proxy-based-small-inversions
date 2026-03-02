(** * Create the initial typeclass structure and pattern matching of the proxy.*)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.

From utils Require Import utils.
From SmallInversion Require Import derecursivation.
From SmallInversion Require Import dependent.
From SmallInversion Require Import typeclass.

(*Creates a branch of a case that calls the constructors of the inductive to proxy.*)
Definition create_call_constructor
  (calls_params : list term)(cstr : constructor_body)
  : branch term :=
  let call_args:= rev_range_deBruijn cstr.(cstr_arity) 0 in
  {| bcontext := map decl_name cstr.(cstr_args);
      bbody := tApp (tVar ("_"^cstr.(cstr_name))) (calls_params ++ call_args)
  |}.

Definition create_proxy0 (transfo_info : transformation_info) : ErrorMonad term :=
  
  (*Name and context of the inductive to proxy/the proxy of the inductive type to feed to proxy0*)
  let name_disp := (poib transfo_info).(pseudo_name) in
  let decl_disp := vass (string_to_aname name_disp) (poib transfo_info).(pseudo_type) in
                                                          
  (*Name the contexts of the inductive for the future variable uses. *)
  let ctx_constructors :=
    rev (map (create_context_constructor name_disp) (concat_options (lctors transfo_info)))
      ++
      name_context [decl_disp] 0
  in
  let named_indices := name_context (og_poib transfo_info).(pseudo_indices) (length (lctors transfo_info)) in
  let named_params := name_context (pmib transfo_info).(pseudo_params) (length (lctors transfo_info) + length (named_indices)) in
  let ctx_params_indices := named_indices ++ named_params in

  (*Create the variable calls to refer to the parameters and indices of the inductive.*)
  let calls_params_indices := context_to_call ctx_params_indices in
  let calls_params := context_to_call named_params in
  let calls_indices :=
    if isdep transfo_info
    then
      rev_range_deBruijn (length (poib transfo_info).(pseudo_indices)) 0
    else
      rev_range_deBruijn (length (og_poib transfo_info).(pseudo_indices)) 1 
  in
  (*The call to the proxy type.*)
  let proxy_type0 := tApp (tVar ("_" ^ name_disp)) calls_params_indices in

  (*The name and context declaration of the object to invert.*)
  let name_rel' :=
    {| binder_name := nNamed ("_" ^ (poib transfo_info).(pseudo_name) ^ "_r'"); binder_relevance := Relevant |}
  in

  let decl_rel :=
    {|
      decl_name := string_to_aname ("_" ^ (poib transfo_info).(pseudo_name) ^ "_r");
      decl_body := None;
      decl_type := tApp (term_og_inductive transfo_info) calls_params_indices
    |} in

  (*Create  the match construct.*)
  let proxy_body :=
    tCase
      {|
        ci_ind := og_inductive transfo_info;
        ci_npar := (pmib transfo_info).(pseudo_npars);
        ci_relevance := (poib transfo_info).(pseudo_relevance)
      |}
      {|
        puinst := [];
        pparams := calls_params;
        pcontext := name_rel'::(map decl_name named_indices);
        preturn := tApp (tVar ("_" ^ name_disp)) (calls_params ++ calls_indices)
      |}(tVar ("_" ^ (poib transfo_info).(pseudo_name) ^ "_r"))
      (map (create_call_constructor calls_params) (concat_options (og_lctors transfo_info)))
  in
  (*Creates the telescope by successively adding the different elements
and transforming the variabel references into De Bruijn indexes.*)
  let proxy0 :=  append_context_vars_lambda (env_quote transfo_info) [decl_rel] proxy_body in
  (*The original type of the inductive instanciated to be fed to the typeclass.*)
  let orig_type := tApp (term_og_inductive transfo_info) calls_params_indices in
  (*The typeclass construct of the proxy0*)
  let typeclass_proxy :=
    if isdep transfo_info
    then
      {| inductive_mind := (MPfile ["typeclass"; "SmallInversion"], "dInvProxy");
        inductive_ind := 0 |}
    else
      {| inductive_mind := (MPfile ["typeclass"; "SmallInversion"], "InvProxy");
        inductive_ind := 0 |}
  in
  let instance_proxy := tApp
                          (tConstruct typeclass_proxy 0 [])
                          [orig_type;proxy_type0;proxy0]
  in

  (*Adds the lambda terms of the parameters and indices of the inductive and converts the corresponding variables into deBruijn indices.*)
  let lambda_instance :=
    append_context_vars_lambda (env_quote transfo_info) ctx_params_indices instance_proxy
  in
  (*Adds the lambda terms of the type and constructors for the composition of the strategy results.*)
  let term_proxy0 :=
    append_context_vars_lambda (env_quote transfo_info) ctx_constructors lambda_instance
  in
  Success (term_proxy0 ).
