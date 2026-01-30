From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.


Definition map_context_with_binders
  (f : context -> term -> term)
  (c : context)
  (Γ : list context_decl)
  : list context_decl :=
  fold_right
    (fun (decl : context_decl) (acc : list context_decl) =>
       map_decl (f (Γ,,, acc)) decl :: acc) c [].

Definition map_predicate_with_binders
  (Σ : global_env)
  (f : context -> term -> term)
  (Γ : list context_decl)
  (ind : inductive)
  (p : predicate term)
  : predicate term :=
  let pctx := rebuild_case_predicate_ctx_with_context Σ ind p in
  let Γparams := map_context_with_binders f pctx Γ in
  {|
    puinst := puinst p;
    pparams := map (f Γ) (pparams p);
    pcontext := pcontext p;
    preturn := f (Γparams  ++ Γ) (preturn p)
  |}.

Definition map_constr_with_binders
  (Σ : global_env) (f : context -> term -> term)
  (Γ : context) (t : term)
  : term :=
match t with
| tEvar ev args => tEvar ev (map (f Γ) args)
| tCast c kind t0 => tCast (f Γ c) kind (f Γ t0)
| tProd na A B =>
    let A' := f Γ A in
    tProd na A' (f (Γ,, vass na A') B)
| tLambda na T M =>
    let T' := f Γ T in
    tLambda na T' (f (Γ,, vass na T') M)
| tLetIn na b t0 c =>
    let b' := f Γ b in
    let t' := f Γ t0 in
    tLetIn na b' t' (f (Γ,, vdef na b' t') c)
| tApp u v => tApp (f Γ u) (map (f Γ) v)
| tCase ci p c brs =>
    let p' := map_predicate_with_binders Σ f Γ (ci_ind ci) p in
    let brs' :=
      mapi
        (fun (i : nat) (x : branch term) =>
           map_case_branch_with_context Σ (ci_ind ci) i f Γ p' x)
        brs
    in
    tCase ci p' (f Γ c) brs'
| tProj p c => tProj p (f Γ c)
| tFix mfix idx =>
    let Γ' := fix_decls mfix ++ Γ in
    let mfix' := map (map_def (f Γ) (f Γ')) mfix in
    tFix mfix' idx
| tCoFix mfix k =>
    let Γ' := fix_decls mfix ++ Γ in
    let mfix' := map (map_def (f Γ) (f Γ')) mfix
    in tCoFix mfix' k
| _ => t
end.
