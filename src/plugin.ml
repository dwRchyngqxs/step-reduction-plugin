open Proofview
open Notations
open Locus
open Step

let bind_occurence occs =
  map_reduction
    (fun _ -> if occs = AllOccurrences then AtLeastOneOccurrence else occs)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)

let step_tac a cl =
  ( match Redexpr.out_occurrences cl.concl_occs with
    | NoOccurrences -> tclUNIT ()
    | occs ->
      Tactics.reduct_in_concl
        ~cast:false
        ~check:false
        (step (bind_occurence occs a), Constr.DEFAULTcast)
  ) <*> Goal.enter (fun gl ->
    List.fold_left
      ( fun tcl (occs, hyp) ->
        tcl <*> Tactics.reduct_in_hyp
          ~check:false
          ~reorder:false
          (step (bind_occurence occs a))
          hyp
      )
      (tclUNIT ())
      ( match cl.onhyps with
        | None ->
          List.map
            (fun id -> AtLeastOneOccurrence, (id, InHyp))
            (Tacmach.pf_ids_of_hyps gl)
        | Some l -> List.map (fun ((occs, id), f) -> Redexpr.out_occurrences occs, (id, f)) l
      )
  )

let check_uint n = if n < 0 then CErrors.user_err (Pp.str "Negative value not allowed.")

open Ltac2_plugin
open Tac2dyn
open Tac2ffi
open Tac2externals

let define s = define { mltac_plugin = "rocq-steps.plugin"; mltac_tactic = s }
let repr_ext s = repr_ext (Val.create ("rocq-steps.plugin:" ^ s))

let end_condition = repr_ext "end_condition"
let () =
  define "ecnat" (int @-> ret end_condition) (fun n -> check_uint n; ECNat n);
  define "eclocal" (unit @-> ret end_condition) (fun () -> ECLocal ());
  define "ecglobal" (unit @-> ret end_condition) (fun () -> ECGlobal ())

let eta_reduction_kind = repr_ext "eta_reduction_kind"
let () =
  define "eboth" (ret eta_reduction_kind) EBoth;
  define "elambda" (option ident @-> ret eta_reduction_kind) (fun id -> ELambda id);
  define "eprim" (option reference @-> eret eta_reduction_kind)
    (fun r env _ -> EPrim (Option.map (interp_tycons env) r))

let to_occurrences = let open Tac2val in function
| ValInt 0 -> AllOccurrences
| ValBlk (0, [|vl|]) -> AllOccurrencesBut (to_list to_int vl)
| ValInt 1 -> NoOccurrences
| ValBlk (1, [|vl|]) -> OnlyOccurrences (to_list to_int vl)
| _ -> assert false

let step_reduction = repr_ext "step_reduction"
let () =
  define "step_cast" (to_occurrences @--> ret step_reduction) (fun o -> Cast o);
  define "step_beta" (option ident @-> to_occurrences @--> ret step_reduction)
    (fun id o -> Beta (id, o));
  define "step_zeta" (option ident @-> to_occurrences @--> ret step_reduction)
    (fun id o -> Zeta (id, o));
  define "step_zm" (reference @-> option int @-> to_occurrences @--> eret step_reduction)
    ( fun name bind o env _ ->
      Option.iter check_uint bind;
      ZetaMatch (interp_zeta env (name, Option.map (fun n -> ArgArg n) bind), o)
    );
  define "step_delta" (option reference  @-> to_occurrences @--> ret step_reduction)
    (fun name o -> Delta (Option.map Tacred.soft_evaluable_of_global_reference name, o));
  define "step_eta" (eta_reduction_kind @-> to_occurrences @--> ret step_reduction)
    (fun ek o -> Eta (ek, o));
  define "step_evar" (ret step_reduction) Evar;
  define "step_fix" (option ident @-> to_occurrences @--> ret step_reduction)
    (fun id o -> IotaFix (id, o));
  define "step_fix'" (option ident @-> to_occurrences @--> ret step_reduction)
    (fun id o -> IotaFixPrime (id, o));
  define "step_cofix" (option ident @-> to_occurrences @--> ret step_reduction)
    (fun id o -> IotaCofix (id, o));
  define "step_cofix'" (option ident @-> to_occurrences @--> ret step_reduction)
    (fun id o -> IotaCofixPrime (id, o));
  define "step_match" (option reference @-> to_occurrences @--> eret step_reduction)
    (fun name o env _ -> IotaMatch (Option.map (interp_tycons env) name, o));
  define "step_root" (ret step_reduction) Root;
  define "step_head" (end_condition @-> ret step_reduction) (fun ec -> Head ec);
  define "step_cbv" (end_condition @-> ret step_reduction) (fun ec -> Cbv ec);
  define "step_cbn" (end_condition @-> ret step_reduction) (fun ec -> Cbn ec);
  define "step_lazy" (end_condition @-> ret step_reduction) (fun ec -> Lazy ec)

let to_occurrences_expr = let open Tac2val in function
| ValInt 0 -> AllOccurrences
| ValBlk (0, [|vl|]) -> AllOccurrencesBut (to_list (fun x -> ArgArg (to_int x)) vl)
| ValInt 1 -> NoOccurrences
| ValBlk (1, [|vl|]) -> OnlyOccurrences (to_list (fun x -> ArgArg (to_int x)) vl)
| _ -> assert false

let to_hyp_location_flag v = match to_int v with
| 0 -> InHyp
| 1 -> InHypTypeOnly
| 2 -> InHypValueOnly
| _ -> assert false

let to_clause v = match to_tuple v with
| [|hyps; concl|] ->
  let cast v = match to_tuple v with
  | [|hyp; occ; flag|] ->
    (to_occurrences_expr occ, to_ident hyp), to_hyp_location_flag flag
  | _ -> assert false
  in
  let hyps = to_option (fun h -> to_list cast h) hyps in
  { onhyps = hyps; concl_occs = to_occurrences_expr concl; }
| _ -> assert false

(* TODO NEXT: requires stuff in g_steps.mlg
  Redexpr.User.create/make
*)
let () =
  define "to_red" (step_reduction @-> ret reduction)
    (fun _ -> CErrors.user_err (Pp.str "User reduction will be added in Rocq 9.2."))

let () =
  define "steps_tac" (step_reduction @-> to_clause @--> tac unit) step_tac;
  define "steps_on" (step_reduction @-> constr @-> eret constr)
    (fun r c env evm -> step r env evm c)