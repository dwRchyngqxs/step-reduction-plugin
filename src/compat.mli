open EConstr
open Names
open Declarations

val case_parameter_context_specif: mutual_inductive_body -> EInstance.t -> constr array -> Vars.substl
val case_branch_context_specif: one_inductive_body -> Vars.substl -> EInstance.t -> Name.t binder_annot array -> int -> rel_context
val case_arity_context_specif: one_inductive_body -> Vars.substl -> inductive puniverses -> Name.t binder_annot array -> rel_context
val case_expand_contexts : Environ.env -> inductive puniverses -> t array -> Name.t binder_annot array -> case_branch array -> rel_context array * rel_context
val case_branch_context : Environ.env -> inductive puniverses -> t array -> Name.t binder_annot array -> int -> rel_context

val lookup_constant : Environ.env -> Evd.evar_map -> Constant.t -> Declarations.constant_body
val constant_value_in : Environ.env -> Evd.evar_map -> Constant.t * EInstance.t -> constr