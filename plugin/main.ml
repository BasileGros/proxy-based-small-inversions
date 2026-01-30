open Template_rocq

(** This module provides printf-style functions over the basic printing functions
    provided by Coq.  *)
module Log = struct
  (** [Log.printf] is a standard [printf] function, except it automatically adds
      a newline at the end. *)
  let printf fmt = Format.ksprintf (fun res -> Feedback.msg_notice (Pp.str res)) fmt

  (** Same as [Log.printf] except it generates an error instead. *)
  let error fmt = Format.ksprintf (fun res -> CErrors.user_err (Pp.str res)) fmt
end

(** * Main entry point of the plugin. *)

(*Small inversion on all possible indices.*)
let derive_proxy (ind_ref : Libnames.qualid)(is_dep : bool): unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_ref with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_ref)
    | IndRef ind_name -> ind_name
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_ref)
  in
  let ind = EConstr.UnsafeMonomorphic.mkInd ind in
  (* Get the type of the inductive. *)
  let ind_type = Retyping.get_type_of env sigma ind in
  (* Build the program of type [TemplateMonad unit]. *)
  let name_file = if is_dep then "small_inversion.derive_dependent_proxy" else "small_inversion.derive_proxy" in
  let f =
    match Rocqlib.lib_ref name_file with
    | ConstRef fname -> EConstr.UnsafeMonomorphic.mkConst fname
    | gref -> Log.error "Internal error: %s should be a constant." (Pp.string_of_ppcmds @@ Printer.pr_global gref)
  in
  let program = EConstr.mkApp (f, [| ind_type; ind |]) in
  (* Run the program using [MetaRocq Run ...]. Since [program] is not supposed
     to create new obligations, we discard the final obligation state. *)
  let _st =
    Run_template_monad.run_template_program_rec
      ~poly:false
      ~intactic:false
      (fun ~st _ _ _ -> st)
      ~st:Declare.OblState.empty
      env
      (sigma, EConstr.to_constr sigma program)
  in
  ()
 
(*Small inversion on all possible indices.*)
let derive_proxy_prefix (ind_ref : Libnames.qualid) prefix (is_dep : bool): unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_ref with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_ref)
    | IndRef ind_name -> ind_name
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_ref)
  in
  let ind = EConstr.UnsafeMonomorphic.mkInd ind in
  (* Get the type of the inductive. *)
  let ind_type = Retyping.get_type_of env sigma ind in
  (* Build the program of type [TemplateMonad unit]. *)
  let name_file = if is_dep then "small_inversion.derive_dependent_proxy_prefix" else "small_inversion.derive_proxy_prefix" in
  let f =
    match Rocqlib.lib_ref name_file with
    | ConstRef fname -> EConstr.UnsafeMonomorphic.mkConst fname
    | gref -> Log.error "Internal error: %s should be a constant." (Pp.string_of_ppcmds @@ Printer.pr_global gref)
  in
  let program = EConstr.mkApp (f, [| ind_type; ind; prefix|]) in
  (* Run the program using [MetaRocq Run ...]. Since [program] is not supposed
     to create new obligations, we discard the final obligation state. *)
  let _st =
    Run_template_monad.run_template_program_rec
      ~poly:false
      ~intactic:false
      (fun ~st _ _ _ -> st)
      ~st:Declare.OblState.empty
      env
      (sigma, EConstr.to_constr sigma program)
  in
  ()

(*Small inversion on one specific index.*)
let derive_one_proxy (ind_ref : Libnames.qualid) n (is_dep : bool) : unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_ref with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_ref)
    | IndRef ind_name -> ind_name
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_ref)
  in
  let ind = EConstr.UnsafeMonomorphic.mkInd ind in
  (* Get the type of the inductive. *)
  let ind_type = Retyping.get_type_of env sigma ind in
  (* Build the program of type [TemplateMonad unit]. *)
  let name_file = if is_dep then "small_inversion.derive_dependent_one_proxy" else "small_inversion.derive_one_proxy" in
  let f =
    match Rocqlib.lib_ref name_file with
    | ConstRef fname -> EConstr.UnsafeMonomorphic.mkConst fname
    | gref -> Log.error "Internal error: %s should be a constant." (Pp.string_of_ppcmds @@ Printer.pr_global gref)
  in
  let program = EConstr.mkApp (f, [| ind_type; ind; n |]) in
  (* Run the program using [MetaRocq Run ...]. Since [program] is not supposed
     to create new obligations, we discard the final obligation state. *)
  let _st =
    Run_template_monad.run_template_program_rec
      ~poly:false
      ~intactic:false
      (fun ~st _ _ _ -> st)
      ~st:Declare.OblState.empty
      env
      (sigma, EConstr.to_constr sigma program)
  in
  ()

let derive_one_proxy_prefix (ind_ref : Libnames.qualid) n prefix (is_dep : bool) : unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_ref with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_ref)
    | IndRef ind_name -> ind_name
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_ref)
  in
  let ind = EConstr.UnsafeMonomorphic.mkInd ind in
  (* Get the type of the inductive. *)
  let ind_type = Retyping.get_type_of env sigma ind in
  (* Build the program of type [TemplateMonad unit]. *)
  let name_file = if is_dep then "small_inversion.derive_dependent_one_proxy_prefix" else "small_inversion.derive_one_proxy_prefix" in
  let f =
    match Rocqlib.lib_ref name_file with
    | ConstRef fname -> EConstr.UnsafeMonomorphic.mkConst fname
    | gref -> Log.error "Internal error: %s should be a constant." (Pp.string_of_ppcmds @@ Printer.pr_global gref)
  in
  let program = EConstr.mkApp (f, [| ind_type; ind; n; prefix |]) in
  (* Run the program using [MetaRocq Run ...]. Since [program] is not supposed
     to create new obligations, we discard the final obligation state. *)
  let _st =
    Run_template_monad.run_template_program_rec
      ~poly:false
      ~intactic:false
      (fun ~st _ _ _ -> st)
      ~st:Declare.OblState.empty
      env
      (sigma, EConstr.to_constr sigma program)
  in
  ()

(*Small inversion on one specific index.*)
let derive_pattern_proxy (ind_ref : Libnames.qualid) patt (is_dep : bool) : unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_ref with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_ref)
    | IndRef ind_name -> ind_name
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_ref)
  in
  let ind = EConstr.UnsafeMonomorphic.mkInd ind in
  (* Get the type of the inductive. *)
  let ind_type = Retyping.get_type_of env sigma ind in
  (* Build the program of type [TemplateMonad unit]. *)
  let name_file = if is_dep then "small_inversion.derive_dependent_pattern_proxy" else "small_inversion.derive_pattern_proxy" in
  let f =
    match Rocqlib.lib_ref name_file with
    | ConstRef fname -> EConstr.UnsafeMonomorphic.mkConst fname
    | gref -> Log.error "Internal error: %s should be a constant." (Pp.string_of_ppcmds @@ Printer.pr_global gref)
  in
  let program = EConstr.mkApp (f, [| ind_type; ind; patt |]) in
  (* Run the program using [MetaRocq Run ...]. Since [program] is not supposed
     to create new obligations, we discard the final obligation state. *)
  let _st =
    Run_template_monad.run_template_program_rec
      ~poly:false
      ~intactic:false
      (fun ~st _ _ _ -> st)
      ~st:Declare.OblState.empty
      env
      (sigma, EConstr.to_constr sigma program)
  in
  ()

let derive_pattern_proxy_prefix (ind_ref : Libnames.qualid) patt prefix (is_dep : bool) : unit =
  (* Create the initial environment and evar map. *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Resolve the inductive name to an inductive. *)
  let ind =
    match Smartlocate.locate_global_with_alias ind_ref with
    | exception Not_found -> Log.error "Unknown reference %s" (Libnames.string_of_qualid ind_ref)
    | IndRef ind_name -> ind_name
    | _ -> Log.error "%s is not an inductive" (Libnames.string_of_qualid ind_ref)
  in
  let ind = EConstr.UnsafeMonomorphic.mkInd ind in
  (* Get the type of the inductive. *)
  let ind_type = Retyping.get_type_of env sigma ind in
  (* Build the program of type [TemplateMonad unit]. *)
  let name_file = if is_dep then "small_inversion.derive_dependent_pattern_proxy_prefix" else "small_inversion.derive_pattern_proxy_prefix" in
  let f =
    match Rocqlib.lib_ref name_file with
    | ConstRef fname -> EConstr.UnsafeMonomorphic.mkConst fname
    | gref -> Log.error "Internal error: %s should be a constant." (Pp.string_of_ppcmds @@ Printer.pr_global gref)
  in
  let program = EConstr.mkApp (f, [| ind_type; ind; patt; prefix |]) in
  (* Run the program using [MetaRocq Run ...]. Since [program] is not supposed
     to create new obligations, we discard the final obligation state. *)
  let _st =
    Run_template_monad.run_template_program_rec
      ~poly:false
      ~intactic:false
      (fun ~st _ _ _ -> st)
      ~st:Declare.OblState.empty
      env
      (sigma, EConstr.to_constr sigma program)
  in
  ()
