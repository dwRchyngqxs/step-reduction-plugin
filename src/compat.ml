module CVars = Vars
open EConstr
open Vars
open Declarations

let case_parameter_context_specif mib u pms =
  subst_of_rel_context_instance (subst_instance_context u (of_rel_context mib.mind_params_ctxt)) pms

let instantiate_context u (ps: substl) (nas: Names.Name.t binder_annot array) binds =
  let u = Unsafe.to_instance u in
  let (nas: Names.Name.t Constr.binder_annot array), (ps: Constr.t list) =
    match Unsafe.eq, Unsafe.relevance_eq with
    | Refl, Refl -> nas, ps
  in
  of_rel_context (Environ.instantiate_context u ps nas binds)

let case_branch_context_specif mip ps u nas i =
  let binds = CList.firstn (mip.mind_consnrealdecls.(i)) (fst mip.mind_nf_lc.(i)) in
  instantiate_context u ps nas binds

let case_arity_context_specif mip ps (ind, u) nas =
  let open Constr in
  let open Names in
  let realdecls = CList.firstn mip.mind_nrealdecls mip.mind_arity_ctxt in
  let self =
    let u = UVars.Instance.abstract_instance (EInstance.length u) in
    let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
    mkApp (mkIndU (ind, u), args)
  in
  let na = Context.make_annot Anonymous mip.mind_relevance in
  instantiate_context u ps nas (LocalAssum (na, self) :: realdecls)

let case_branch_context env (ind, u) pms nas i =
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let ps = case_parameter_context_specif mib u pms in
  case_branch_context_specif mip ps u nas i

let case_expand_contexts env (ind, u) pms nas bl =
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let ps = case_parameter_context_specif mib u pms in
  let build_one_branch i = case_branch_context_specif mip ps u (fst bl.(i)) i in
  let pctx = case_arity_context_specif mip ps (ind, u) nas in
  Array.init (Array.length bl) build_one_branch, pctx

let lookup_constant_opt kn env =
  match Names.Cmap_env.find_opt kn Environ.Internal.View.((view env).env_constants) with
  | None -> None
  | Some (cb, _) -> Some cb

let get_senv_side_effects eff =
  let open Evd in
  snd (Safe_typing.export_private_constants eff.seff_private (Global.safe_env ()))

let lookup_constant env sigma c =
  match lookup_constant_opt c env with
  | Some cb -> cb
  | None ->
    if Safe_typing.is_empty_private_constants Evd.((eval_side_effects sigma).seff_private) then
      CErrors.anomaly Pp.(str "Constant " ++ Names.Constant.print c ++ str" does not appear in the environment.")
    else
      let senv = get_senv_side_effects Evd.(eval_side_effects sigma) in
      Environ.lookup_constant c (Safe_typing.env_of_safe_env senv)

let constant_value_in env sigma (kn, u) =
  let u = Unsafe.to_instance u in
  let cb = lookup_constant env sigma kn in
  match cb.const_body with
  | Def l_body ->
    of_constr (CVars.subst_instance_constr u l_body)
  | OpaqueDef _ -> raise (Environ.NotEvaluableConst Opaque)
  | Undef _ -> raise (Environ.NotEvaluableConst NoBody)
  | Primitive p -> raise (Environ.NotEvaluableConst (IsPrimitive (u ,p)))
  | Symbol b ->
    let r = Environ.lookup_rewrite_rules kn env in
    raise (Environ.NotEvaluableConst (HasRules (u, b, r)))