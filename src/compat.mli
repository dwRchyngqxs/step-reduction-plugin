open Constr
open Declarations

val contract_fix : fixpoint -> constr
val contract_cofix : cofixpoint -> constr
val expand_match_param_context : mind_specif -> UVars.Instance.t -> Vars.instance -> Vars.substl
val expand_branch_context :
  mind_specif -> UVars.Instance.t -> Vars.substl -> case_branch array ->
  int -> rel_context
val expand_branch :
  mind_specif ->
  UVars.Instance.t -> Vars.instance -> case_branch array ->
  int -> constr
val expand_arity_context :
  mind_specif -> pinductive -> Vars.substl ->
  Names.Name.t binder_annot array -> rel_context
val expand_case_contexts :
  mind_specif -> pinductive -> constr array ->
  Names.Name.t binder_annot array -> case_branch array -> rel_context * rel_context array