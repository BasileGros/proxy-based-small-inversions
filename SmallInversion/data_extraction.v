From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.
From SmallInversion Require Import dependent.
From SmallInversion Require Import derecursivation.

(*Extracts from the coq object to invert all information necessary for the inversion.*)
Definition data_extraction_error
  (prefix : string) (env_R : global_env) (term_R:term)
  (modpath_call : modpath)(isdep : bool)
  : ErrorMonad (transformation_info) :=

  (*Quote the term and if it's an inductive type, get its components*)
  extraction_inductive_R <-? inductive_from_term term_R ;;
  (*The position of the type in the mutually inductive type*)
  let index_R := inductive_ind extraction_inductive_R in
  (*The qualified name and the identifier of the mutually inductive type*)
  let (modpath_R,ident_R) := inductive_mind extraction_inductive_R in
  (*Get the AST of the mutually inductive type from the quoted environment.*)
  match lookup_mind_decl (modpath_R,ident_R) env_R.(declarations) with
  |None => Error "Anomaly : mib of relation not found in the environment"
  |Some mib_R =>
     (*TODO if necessary, change the universe levels in the AST*)
     let univ_mib_R := (*universalisation_mib*) mib_R in
     (*Get the AST of the inductive type from the AST of the MIT*)
     oib_R <-? one_inductive_body_from_mib univ_mib_R index_R;;
     (*A letin telescope of the different inductive types in the mutually inductive type, for derecursivation.*)
     let telescope_oib_R :=
       create_telescope_letin_mutual_inductive
         extraction_inductive_R (length mib_R.(ind_bodies))
     in
     (*Keeping the original ASTs to define proxy0 properly.*)
     let og_poib := pseudo_oib_of_oib oib_R in
     let og_lctors := map (fun c => Some c) oib_R.(ind_ctors) in
     (*Transformation of the ASTs for dependent inversion purpose*)
     let lctors :=
       if isdep
       then
         mapi (fun i c =>
                 Some (dependent_constructor extraction_inductive_R  mib_R.(ind_npars) i c)
           ) oib_R.(ind_ctors)
       else
          og_lctors
     in
     let poib :=
       if isdep
       then
         dependent_oib og_poib term_R mib_R.(ind_npars)
       else
         og_poib
     in
     
     let transfo_info :=
       {|
         inductive_transfo := extraction_inductive_R;
         term_transfo := term_R;
         index_oib := index_R;
         prefix := prefix;
         pmib := pseudo_mib_of_mib univ_mib_R;
         poib := poib;
         lctors := lctors;
         og_poib := og_poib;
         og_lctors := og_lctors;
         env_quote := env_R;
         modpath_call := modpath_call;
         name_og_inductive := oib_R.(ind_name);
         term_og_inductive := term_R;
         og_inductive := extraction_inductive_R;
         isdep := isdep
       |} in
     (*Derecursivation*)
     let derec_transfo_info :=
       derecursivation_mib transfo_info telescope_oib_R (length univ_mib_R.(ind_bodies))
     in
     Success (derec_transfo_info)
  end.

(*Wraps the extraction of the data necessary for the inversion in MetaCoq's TemplateMonad*)
Definition data_extraction{X}
  (R:X) (prefix : string)(isdep : bool)
  : TemplateMonad (transformation_info) :=
  '(env_R,term_R) <-- tmQuoteRec R;;
  modpath_call <-- tmCurrentModPath tt;;
  tmErrorReturn (data_extraction_error prefix env_R term_R modpath_call isdep).

(*Wraps the printing of the data necessary for the inversion in MetaCoq's TemplateMonad*)
Definition print_data_extraction{X}
  (R:X) (prefix : string)(isdep : bool)
  : TemplateMonad unit :=
  '(env_R,term_R) <-- tmQuoteRec R;;
  modpath_call <-- tmCurrentModPath tt;;
  tmErrorPrint (data_extraction_error prefix env_R term_R modpath_call isdep).

