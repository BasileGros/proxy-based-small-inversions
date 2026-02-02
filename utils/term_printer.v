From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import term_functions.
From utils Require Import TM_functions.
From utils Require Import TM_notations.

Definition pRel (Γ : context) (n:nat) :=
  match nth_error Γ n with
  | Some cd => match cd.(decl_name).(binder_name) with
              | nAnon => "#anon#" ^ (string_of_nat n)
              | nNamed s => s
              end
  | None => "#unbound#" ^ (string_of_nat n)
  end.

Definition pAname (a:aname) :=
   match a.(binder_name) with
   | nAnon => "_"
   | nNamed s => s
   end.

Fixpoint pAname_list (la:list aname) :=
   match la with
   | nil => ""
   | a :: q => " " ^ pAname a ^ pAname_list q
   end.

Fixpoint p_list (n:nat) :=
   match n with
   | 0 => ""
   | S m => " _" ^ p_list m
   end.

Definition pVar (id:ident) := "#var#"^id.

Definition pEvar (ev:nat) (args:list term) := "?"^ (string_of_nat ev).

Definition pSort (s:sort) :=
  if Sort.is_prop s then "Prop" else
    if Sort.is_sprop s then "SProp" else
      if Sort.is_type_sort s then "Type" else
        "#sort#unknown".

Definition pConst (c:kername) (u:Instance.t) :=
  snd c.

Definition pInd (Σ:global_env) (ind:inductive) (u:Instance.t) :=
    match lookup_inductive Σ ind with
  | None => "#inductive#" ^ string_of_kername ind.(inductive_mind) ^ "#" ^ string_of_nat ind.(inductive_ind)
  | Some (mib,oib) => oib.(ind_name)
  end.

Definition pConstruct (Σ:global_env) (ind:inductive) (idx:nat) (u:Instance.t) :=
  match lookup_constructor Σ ind idx with
  | None => "#construct#" ^ pInd Σ ind u ^ "#" ^ string_of_nat idx
  | Some (mib,oib,cbody) => cbody.(cstr_name)
  end.

Fixpoint pTerm
  (Σ : global_env)
  (Γ : context) (t : term) {struct t}
  : string :=
  match t with
  | tRel n => pRel Γ n
  | tVar id => pVar id
  | tEvar ev args => pEvar ev args
  | tSort s => pSort s
  | tCast t kind v => "(" ^ pTerm Σ Γ t ^ ":" ^ pTerm Σ Γ v ^ ")"
  | tProd ({|binder_name:= nAnon |} as na) ty body =>
       "(" ^ pTerm Σ Γ ty ^ ") -> " ^ pTerm Σ (Γ ,, vass na ty) body (*^ ")"*)
  | tProd ({|binder_name:= nNamed s |} as na) ty body =>
      let fix pForall Γ0 body0 :=
        match body0 with
          tProd ({|binder_name:= nNamed s0 |} as na0) ty0 body0 =>
            " (" ^ s0 ^  ":" ^ pTerm Σ Γ0 ty0 ^ ")" ^ pForall (Γ0 ,, vass na0 ty0) body0
        | _ =>  ", " ^ pTerm Σ Γ0 body0
        end
      in
      "forall (" ^ s ^  ":" ^ pTerm Σ Γ ty ^ ")" ^ pForall (Γ ,, vass na ty) body
  | tLambda na ty body =>
      let fix pLambda Γ0 body0 :=
        match body0 with
          tLambda na0 ty0 body0 =>
            " (" ^ pAname na0 ^  ":" ^ pTerm Σ Γ0 ty0 ^ ")" ^ pLambda (Γ0 ,, vass na0 ty0) body0
        | _ =>  " => " ^ pTerm Σ Γ0 body0 ^ ")"
        end
      in
      "(fun (" ^ pAname na ^ ":" ^ pTerm Σ Γ ty ^ ")" ^ pLambda (Γ ,, vass na ty) body
  | tLetIn na def def_ty body =>
      "let (" ^ pAname na ^ ":" ^ pTerm Σ Γ def_ty ^ ") := " ^
        pTerm Σ Γ def ^ " in " ^ pTerm Σ (Γ ,, vdef na def def_ty) body
  | tApp u v =>
      let fix pTerm_list args :=
        match args with
        | arg0::args1 => " " ^ pTerm Σ Γ arg0 ^ pTerm_list args1
        | nil => ""
        end
      in
      "(" ^ pTerm Σ Γ u ^ pTerm_list v ^ ")"
  | tConst c u => pConst c u
  | tInd ind u => pInd Σ ind u
  | tConstruct ind idx u => pConstruct Σ ind idx u
  | tCase ci type_info discr branches =>
      let fix pTerm_list args :=
        match args with
        | arg0::args1 => " " ^ pTerm Σ Γ arg0 ^ pTerm_list args1
        | nil => ""
        end
      in
      let ind:=ci.(ci_ind) in
      let u:= type_info.(puinst) in
      let pctx := rebuild_case_predicate_ctx_with_context Σ ind type_info in
      let bctx idx br := rebuild_case_branch_ctx_with_context Σ ind idx type_info br in
      let in_clause :=
        let as_name := hd {|binder_name:=nAnon ; binder_relevance := Relevant |} type_info.(pcontext) in
        let in_names := tl type_info.(pcontext) in
        " as " ^ pAname as_name ^ " in @" ^ pInd Σ ind u ^
          pTerm_list type_info.(pparams) ^ p_list ci.(ci_npar) ^ pAname_list in_names in
      let return_clause := " return " ^ pTerm Σ (pctx ++ Γ) type_info.(preturn) in
      let pBranch idx br :=
        let bctx := rebuild_case_branch_ctx_with_context Σ ci.(ci_ind) idx type_info br in
        " | " ^ pConstruct Σ ind idx u ^ pAname_list br.(bcontext) ^ " => " ^ pTerm Σ (bctx++Γ) br.(bbody)
      in
      let fix pBranches idx br {struct br} :=
        match br with
        | nil => ""
        | br0::q => pBranch idx br0 ^ pBranches (S idx) q  end in
      "match " ^ pTerm Σ Γ discr ^ in_clause ^ return_clause ^ " with"
        ^ pBranches 0 branches ^ " end"
  | _ => "#OTHER#"
  end.



Fixpoint pContext
  (Σ : global_env)
  (Γ : context) (c : context)
  : string :=
  match c with
  |[] => ""
  |hd::tl =>
     let tlprint := pContext Σ (hd::Γ) tl in
     "("^pAname hd.(decl_name)^":" ^ pTerm Σ Γ hd.(decl_type)^")"^tlprint
  end.

Definition pRevContext
  (Σ : global_env)
  (Γ : context)
  (c : context)
  : string :=
  pContext Σ Γ (rev c).

  Definition pConstructor
  (Σ : global_env)
  (Γ : context)
  (cstr : constructor_body)
  : string :=
  "| " ^ cstr.(cstr_name) ^ " : " ^ pTerm Σ Γ cstr.(cstr_type).

Fixpoint pConstructors
  (Σ : global_env)
  (Γ : context)
  (lcstr : list constructor_body)
  : string :=
  match lcstr with
  |[] => ""
  |hd::tl =>
     let tlprint := pConstructors Σ Γ tl in
     pConstructor Σ Γ hd ^ "
" ^ tlprint
  end.


Definition pOib
  (Σ : global_env)
  (Γ : context)
  (params : context)
  (oib : one_inductive_body)
  : string :=
  "Inductive "^ oib.(ind_name) ^ " " ^ pRevContext Σ Γ params ^ " : "
  ^ pRevContext Σ (params ++ Γ) oib.(ind_indices)
  ^ " -> " ^ pSort oib.(ind_sort)
    
  ^  " :=
" ^ pConstructors Σ Γ oib.(ind_ctors).

Fixpoint pOibs
  (Σ : global_env)
  (Γ : context)
  (params : context)
  (oibs : list one_inductive_body)
  : string :=
  match oibs with
  |[] => ""
  |[oib] => pOib Σ Γ params oib
  |hd::tl =>
     let tlprint := pOibs Σ Γ params tl in
     let hdprint := pOib Σ Γ params hd in
     hdprint ^"
with
" ^ tlprint
  end.

Definition pMib
  (Σ : global_env)
  (Γ : context)
  (mib : mutual_inductive_body)
  : string :=
  let ctx_oibs := create_context_mutual_oibs mib.(ind_bodies) in
  pOibs Σ (ctx_oibs ++ Γ) mib.(ind_params) mib.(ind_bodies).

Definition TM_PP_term (t:term) : TemplateMonad unit :=
  '(Σ,_) <--  tmQuoteRec t ;; let Γ := nil in
  msg <-- tmEval all (pTerm Σ Γ t);;
  tmMsg msg.

Definition test_TM_PP_term {A:Type} (a:A) : TemplateMonad unit :=
  t <-- tmQuote (A:=A) a ;;
  TM_PP_term t.


MetaRocq Run (test_TM_PP_term (fun x y => match y with 0 => 0 | S m => m + x end)).
