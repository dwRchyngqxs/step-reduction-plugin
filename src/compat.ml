open Constr
open Vars
open Declarations

let contract_fix ((recindices,bodynum),(_,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    mkFix ((recindices,ind),typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

let contract_cofix (bodynum,(_,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let coind = nbodies-j-1 in
    mkCoFix (coind,typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

let expand_match_param_context (mib, _) u params =
  subst_of_rel_context_instance (subst_instance_context u mib.mind_params_ctxt) params

let expand_branch_context (_, mip) u params br i =
  let binds = CList.firstn (mip.mind_consnrealdecls.(i)) (fst mip.mind_nf_lc.(i)) in
  Environ.instantiate_context u params (fst br.(i)) binds

let expand_branch mind u params brs i =
  let _, br = brs.(i) in
  let paramsubst = expand_match_param_context mind u params in
  let ctx = expand_branch_context mind u paramsubst brs i in
  Term.it_mkLambda_or_LetIn br ctx

let expand_branch_contexts (_, mip) u params br =
  let build_one_branch i =
    let binds = CList.firstn (mip.mind_consnrealdecls.(i)) (fst mip.mind_nf_lc.(i)) in
    Environ.instantiate_context u params (fst br.(i)) binds
  in
  Array.init (Array.length br) build_one_branch

let expand_arity_context (_, mip) (ind, u) params nas =
  let realdecls = CList.firstn mip.mind_nrealdecls mip.mind_arity_ctxt in
  let self =
    let u = UVars.Instance.(abstract_instance (length u)) in
    let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
    mkApp (mkIndU (ind, u), args)
  in
  let na = Context.make_annot Names.Anonymous mip.mind_relevance in
  Environ.instantiate_context u params nas (LocalAssum (na, self) :: realdecls)

let expand_case_contexts mind (_, u as pind) params nas br =
  (* Γ ⊢ c : I@{u} params args *)
  (* Γ, indices, self : I@{u} params indices ⊢ p : Type *)
  let params = expand_match_param_context mind u params in
  expand_arity_context mind pind params nas, expand_branch_contexts mind u params br