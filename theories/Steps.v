Declare ML Module "rocq-steps.plugin".

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std. (* occurrences + clause *)

Ltac2 Type end_condition.
Ltac2 @external cond_for: int -> end_condition
  := "rocq-steps.plugin" "ecnat".
Ltac2 @external cond_local: unit -> end_condition
  := "rocq-steps.plugin" "eclocal".
Ltac2 @external cond_global: unit -> end_condition
  := "rocq-steps.plugin" "ecglobal".

Ltac2 Type eta_reduction_kind.
Ltac2 @external eta_both: eta_reduction_kind
  := "rocq-steps.plugin" "eboth".
Ltac2 @external eta_lambda: ident option -> eta_reduction_kind
  := "rocq-steps.plugin" "elambda".
Ltac2 @external eta_prim_proj: reference option -> eta_reduction_kind
  := "rocq-steps.plugin" "eprim".

Module Reduction.
  Ltac2 Type t.

  Ltac2 @external cast: occurrences -> t
    := "rocq-steps.plugin" "step_cast".
  Ltac2 @external beta: ident option -> occurrences -> t
    := "rocq-steps.plugin" "step_beta".
  Ltac2 @external zeta: ident option -> occurrences -> t
    := "rocq-steps.plugin" "step_zeta".
  Ltac2 @external zeta_match: reference -> int option -> occurrences -> t
    := "rocq-steps.plugin" "step_zm".
  Ltac2 @external delta: reference option -> occurrences -> t
    := "rocq-steps.plugin" "step_delta".
  Ltac2 @external eta: eta_reduction_kind -> occurrences -> t
    := "rocq-steps.plugin" "step_eta".
  Ltac2 @external evar: t
    := "rocq-steps.plugin" "step_evar".
  Ltac2 @external iota_fix: ident option -> occurrences -> t
    := "rocq-steps.plugin" "step_fix".
  Ltac2 @external iota_fix': ident option -> occurrences -> t
    := "rocq-steps.plugin" "step_fix'".
  Ltac2 @external iota_cofix: ident option -> occurrences -> t
    := "rocq-steps.plugin" "step_cofix".
  Ltac2 @external iota_cofix': ident option -> occurrences -> t
    := "rocq-steps.plugin" "step_cofix'".
  Ltac2 @external iota_match: reference option -> occurrences -> t
    := "rocq-steps.plugin" "step_match".
  Ltac2 @external root: t
    := "rocq-steps.plugin" "step_root".
  Ltac2 @external head: end_condition -> t
    := "rocq-steps.plugin" "step_head".
  Ltac2 @external cbv: end_condition -> t
    := "rocq-steps.plugin" "step_cbv".
  Ltac2 @external cbn: end_condition -> t
    := "rocq-steps.plugin" "step_cbn".
  Ltac2 @external lazy: end_condition -> t
    := "rocq-steps.plugin" "step_lazy".

  Ltac2 @external to_red: t -> Red.t
    := "rocq-steps.plugin" "to_red".
End Reduction.

Ltac2 @external steps_tac : Reduction.t -> clause -> unit
  := "rocq-steps.plugin" "steps_tac".
Ltac2 @external steps_on : Reduction.t -> constr -> constr
  := "rocq-steps.plugin" "steps_on".