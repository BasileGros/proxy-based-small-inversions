From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
(*
Change all universe type levels to fresh_universe levels
 *)

Fixpoint universalisation_term (t:term) : term :=
  match t with
  | tRel n => tRel n
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (map universalisation_term args)
  | tCast t kind v => tCast (universalisation_term t) kind (universalisation_term v)
  | tProd na ty body => tProd na (universalisation_term ty) (universalisation_term body)
  | tLambda na ty body => tLambda na (universalisation_term ty) (universalisation_term body)
  | tLetIn na def def_ty body => tLetIn na (universalisation_term def) (universalisation_term def_ty) (universalisation_term body)
  | tApp f args => tApp (universalisation_term f) (map universalisation_term args)
  | tConst c u => tConst c u
  | tInd ind u => tInd ind u
  | tConstruct ind idx u => tConstruct ind idx u
  | tCase ind p discr brs =>
      let p' := map_predicate id universalisation_term universalisation_term p in
      let brs' := map_branches universalisation_term brs in
      tCase ind p' (universalisation_term discr) brs'
  | tProj proj t => tProj proj (universalisation_term t)
  | tFix mfix idx => tFix (map (map_def universalisation_term universalisation_term) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def universalisation_term universalisation_term) mfix) idx
  | tInt i => tInt i
  | tFloat f => tFloat f
  | tArray lev l a b => tArray lev (map universalisation_term l) (universalisation_term a) (universalisation_term b)
  | tSort s => match s with
              |sType u => tSort (sType fresh_universe)
              |s' => tSort s'
              end
  |t' => t'
  end.


Definition universalisation_constructors (cons : constructor_body) : constructor_body :=
  {|
    cstr_name := cons.(cstr_name);
    cstr_args := map (fun decl => map_decl universalisation_term decl) cons.(cstr_args);
    cstr_indices := map universalisation_term cons.(cstr_indices);
    cstr_type := universalisation_term cons.(cstr_type);
    cstr_arity := cons.(cstr_arity)
  |}.

Definition universalisation_oib (oib:one_inductive_body) : one_inductive_body :=
  {|
    ind_name := oib.(ind_name);
    ind_indices := map (fun decl => map_decl universalisation_term decl) oib.(ind_indices);
    ind_sort := match oib.(ind_sort) with
                |sType t' => sType fresh_universe
                |s' => s'
                        end
                ;
    ind_type := universalisation_term oib.(ind_type);
    ind_kelim := oib.(ind_kelim);
    ind_ctors := map universalisation_constructors oib.(ind_ctors);
    ind_projs := oib.(ind_projs);
    ind_relevance := oib.(ind_relevance)
  |}.

Definition universalisation_mib (mib:mutual_inductive_body) : mutual_inductive_body :=
  {|
       ind_finite := mib.(ind_finite);
       ind_npars := mib.(ind_npars);
       ind_params := map (fun decl => map_decl universalisation_term decl) mib.(ind_params);
       ind_bodies := map universalisation_oib mib.(ind_bodies);
       ind_universes := mib.(ind_universes);
       ind_variance := mib.(ind_variance)
     |}.

