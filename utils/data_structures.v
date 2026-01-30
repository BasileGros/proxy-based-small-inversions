From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import term_functions.
From utils Require Import list_functions.
From utils Require Import error_monad.
From utils Require Import TM_functions.
From utils Require Import term_printer.
(*All information necessary to pass between transformations*)

Record pseudo_mib : Type :=
  Build_pseudo_mib
    { pseudo_finite : recursivity_kind;
      pseudo_npars : nat;
      pseudo_params : context;
      pseudo_universes : universes_decl;
      pseudo_variance : option (list Variance.t) }.

Definition pPseudo_mib
  (Σ : global_env)
  (Γ : context)
  (pmib : pseudo_mib)
  : string :=
"pmib :
" ^ "number of parameters : " ^ string_of_nat pmib.(pseudo_npars) ^ "
" ^ "parameters : " ^ pRevContext Σ Γ pmib.(pseudo_params).

Record pseudo_oib : Type :=
  Build_pseudo_oib
    { pseudo_name : ident;
    pseudo_indices : context;
    pseudo_sort : sort;
    pseudo_type : term;
    pseudo_kelim : allowed_eliminations;
    pseudo_projs : list projection_body;
    pseudo_relevance : relevance }.

Definition pPseudo_oib
  (Σ : global_env)
  (Γ : context)
  (poib : pseudo_oib)
  : string :=
  "poib " ^ poib.(pseudo_name) ^ " : " ^ pTerm Σ Γ poib.(pseudo_type).

Fixpoint pOptionConstructors
  (Σ : global_env)
  (Γ : context)
  (lctors : list (option constructor_body))
  : string :=
  match lctors with
  |[] => ""
  |None :: tl => "|None" ^ "
" ^ pOptionConstructors Σ Γ tl
  |Some cstr :: tl => pConstructor Σ Γ cstr ^ "
" ^ pOptionConstructors Σ Γ tl
  end.

  
Definition rename_poib (prefix : string)(suffix: string)(poib : pseudo_oib)
  : pseudo_oib :=
  {|
    pseudo_name := prefix ^ poib.(pseudo_name) ^ suffix;
    pseudo_indices := poib.(pseudo_indices);
    pseudo_sort := poib.(pseudo_sort);
    pseudo_type := poib.(pseudo_type);
    pseudo_kelim := poib.(pseudo_kelim);
    pseudo_projs := poib.(pseudo_projs);
    pseudo_relevance := poib.(pseudo_relevance)
  |}.

Record transformation_info : Type :=
  mkTransformationInfo {
      inductive_transfo : inductive;
      term_transfo : term;
      index_oib : nat;
      prefix : string;
      pmib : pseudo_mib;
      poib : pseudo_oib;
      lctors : list (option constructor_body);
      og_poib : pseudo_oib;
      og_lctors : list (option constructor_body);
      env_quote : global_env;
      modpath_call : modpath;
      name_og_inductive : string;
      term_og_inductive : term;
      og_inductive : inductive;
      isdep : bool
    }.

(*Un pretty printer de certaines infos de transfo info, pour le reste, utiliser eval_print*)
Definition pTransfo_info
  (Σ : global_env)
  (Γ : context)
  (t : transformation_info)
  : string :=
  "inductive : " ^ pInd Σ t.(inductive_transfo) [] ^ "
" ^ "pmib : " ^ pPseudo_mib Σ Γ t.(pmib) ^ "
" ^ "poib : " ^ pPseudo_oib Σ Γ t.(poib) ^ "
" ^ "constructors : " ^ pOptionConstructors Σ Γ t.(lctors).
    
Definition pseudo_mib_of_mib
  (mib : mutual_inductive_body) : pseudo_mib :=
  {|
    pseudo_finite := mib.(ind_finite);
    pseudo_npars := mib.(ind_npars);
    pseudo_params := mib.(ind_params);
    pseudo_universes := mib.(ind_universes);
    pseudo_variance := mib.(ind_variance);
    |}.

Definition pseudo_oib_of_oib
  (oib : one_inductive_body) : pseudo_oib :=
  {|
    pseudo_name := oib.(ind_name);
    pseudo_indices := oib.(ind_indices);
    pseudo_sort := oib.(ind_sort);
    pseudo_type := oib.(ind_type);
    pseudo_kelim := oib.(ind_kelim);
    pseudo_projs := oib.(ind_projs);
    pseudo_relevance := oib.(ind_relevance);
    |}.

Definition recreate_mib'
  (ps_mib : pseudo_mib)
  (ps_oib : pseudo_oib)
  (lcons : list (option constructor_body))
  : mutual_inductive_body :=
  
  {|
    ind_finite := ps_mib.(pseudo_finite);
    ind_npars := ps_mib.(pseudo_npars);
    ind_params := ps_mib.(pseudo_params);
    ind_bodies := [{|
        ind_name := ps_oib.(pseudo_name);
        ind_indices := ps_oib.(pseudo_indices);
        ind_sort := ps_oib.(pseudo_sort);
        ind_type := ps_oib.(pseudo_type);
        ind_kelim := ps_oib.(pseudo_kelim);
        ind_ctors := concat_options lcons;
        ind_projs := ps_oib.(pseudo_projs);
        ind_relevance := ps_oib.(pseudo_relevance)
      |}];
    ind_universes := ps_mib.(pseudo_universes);
    ind_variance := ps_mib.(pseudo_variance)
  |}.
    
Definition recreate_mib (t : transformation_info) : mutual_inductive_body :=
  recreate_mib' t.(pmib) t.(poib) t.(lctors).

(*Extracts from a mutual_inductive_body and a previous transformation_info
the informations to create a new tranformation_info*)
Definition recreate_transfo_info
  (transfo_info : transformation_info)
  (ps_mib:pseudo_mib) (ps_oib : pseudo_oib)
  (lcons : list (option constructor_body))
  : transformation_info :=
  let name_inductive := ps_oib.(pseudo_name) in
  let modpath_call_partial := modpath_call transfo_info in
  let inductive_partial := mkInd (modpath_call_partial,name_inductive) 0 in
  let term_partial := tInd inductive_partial [] in
  let new_transfo_info :=
    {|
      inductive_transfo := inductive_partial;
      term_transfo := term_partial;
      index_oib := index_oib transfo_info;
      prefix := prefix transfo_info;
      pmib := ps_mib;
      poib := ps_oib;
      lctors := lcons;
      og_poib := og_poib transfo_info;
      og_lctors := og_lctors transfo_info;
      env_quote := env_quote transfo_info;
      modpath_call := modpath_call_partial;
      name_og_inductive := name_og_inductive transfo_info;
      term_og_inductive := term_og_inductive transfo_info;
      og_inductive := og_inductive transfo_info;
      isdep := isdep transfo_info
    |} in
  new_transfo_info.





(** Tree structure to aggregate then flatten info from different recursive subcalls*)
Inductive tree (A:Type) :Type  :=
| node: A -> list (tree A) -> tree A
| leaf: tree A.

Arguments node {A}.
Arguments leaf {A}.

