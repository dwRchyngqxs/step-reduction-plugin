open Pp
open CErrors
open Environ
open Names
open Constr
open Vars
open Primred
open Inductive
open Compat
open Context.Rel.Declaration

(* UTILITY *)

let id x = x

let map_left2 f1 f2 a1 a2 =
  let l = Array.length a1 in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f1 a1.(0)) in
    let s = Array.make l (f2 a2.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f1 a1.(i);
      s.(i) <- f2 a2.(i)
    done;
    r, s
  end

let array_with a n x = let a = Array.copy a in a.(n) <- x; a

let or_step f x g =
  match x with
  | Some x -> Some (f x)
  | None -> g ()

let rec first_step = function
| [] -> None
| h :: t ->
  match h () with
  | Some x -> Some x
  | None -> first_step t

let first_success msg l =
  let rec aux errs = function
  | [] -> Error errs
  | h :: t ->
    match h () with
    | Ok x -> Ok x
    | Error e -> aux (e :: errs) t
  in
  Result.map_error
    (fun l -> msg ++ pr_vertical_list id l)
    (aux [] l)

let opt_or x f =
  match x with
  | None -> f ()
  | Some x -> Some x

let for_step f e =
  let rec aux i =
    if i = e then None else opt_or (f i) (fun _ -> aux (i + 1))
  in aux

let array_step_n f a =
  for_step (fun i -> Option.map (array_with a i) (f a.(i))) (Array.length a)

let array_step f a = array_step_n f a 0

let slist_step f =
  let open SList in
  let rec aux = function
  | Nil -> None
  | Default (n, t) -> Option.map (defaultn n) (aux t)
  | Cons (h, t) -> or_step (fun h -> cons h t) (f h) (fun _ -> Option.map (cons h) (aux t))
  in aux

let to_result msg = function
| None -> Error msg
| Some x -> Ok x

let force msg = function
| Some x -> x
| None -> user_err (str msg)


(* ESSENTIALS *)

module KNativeEntries =
  struct
    type elem = constr
    type args = constr array
    type evd = unit
    type uinstance = UVars.Instance.t
    open UnsafeMonomorphic

    let get = Array.unsafe_get

    let get_int () e =
      match kind e with
      | Int i -> i
      | _ -> raise NativeDestKO

    let get_float () e =
      match kind e with
      | Float f -> f
      | _ -> raise NativeDestKO

    let get_string () e =
      match kind e with
      | String s -> s
      | _ -> raise NativeDestKO

    let get_parray () e =
      match kind e with
      | Array (_, t, def, _) -> Parray.of_array t def
      | _ -> raise NativeDestKO

    let mkInt _ = mkInt

    let mkFloat _ = mkFloat

    let mkString _ = mkString

    let mkBool env b =
      let ct, cf = get_bool_constructors env in
      mkConstruct (if b then ct else cf)

    let mkCarry env b e =
      let int_ty = mkConst @@ get_int_type env in
      let c0, c1 = get_carry_constructors env in
      mkApp (mkConstruct (if b then c1 else c0), [| int_ty; e |])

  let mkIntPair env e1 e2 =
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp (mkConstruct c, [| int_ty; int_ty; e1; e2 |])

  let mkFloatIntPair env f i =
    let float_ty = mkConst @@ get_float_type env in
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp (mkConstruct c, [| float_ty; int_ty; f; i |])

  let mkLt env =
    let _, lt, _ = get_cmp_constructors env in
    mkConstruct lt

  let mkEq env =
    let eq, _, _ = get_cmp_constructors env in
    mkConstruct eq

  let mkGt env =
    let _, _, gt = get_cmp_constructors env in
    mkConstruct gt

  let mkFLt env =
    let _, lt, _, _ = get_f_cmp_constructors env in
    mkConstruct lt

  let mkFEq env =
    let eq, _, _, _ = get_f_cmp_constructors env in
    mkConstruct eq

  let mkFGt env =
    let _, _, gt, _ = get_f_cmp_constructors env in
    mkConstruct gt

  let mkFNotComparable env =
    let _, _, _, nc = get_f_cmp_constructors env in
    mkConstruct nc

  let mkPNormal env =
    let pNormal, _, _, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pNormal

  let mkNNormal env =
    let _, nNormal, _, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct nNormal

  let mkPSubn env =
    let _, _, pSubn, _, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pSubn

  let mkNSubn env =
    let _, _, _, nSubn, _, _, _, _, _ = get_f_class_constructors env in
    mkConstruct nSubn

  let mkPZero env =
    let _, _, _, _, pZero, _, _, _, _ = get_f_class_constructors env in
    mkConstruct pZero

  let mkNZero env =
    let _, _, _, _, _, nZero, _, _, _ = get_f_class_constructors env in
    mkConstruct nZero

  let mkPInf env =
    let _, _, _, _, _, _, pInf, _, _ = get_f_class_constructors env in
    mkConstruct pInf

  let mkNInf env =
    let _, _, _, _, _, _, _, nInf, _ = get_f_class_constructors env in
    mkConstruct nInf

  let mkNaN env =
    let _, _, _, _, _, _, _, _, nan = get_f_class_constructors env in
    mkConstruct nan

  let mkArray env u t ty =
    let t, def = Parray.to_array t in
    mkArray (u, t, def, ty)

  end

module KredNative = RedNative(KNativeEntries)

let substn x =
  let rec aux n c =
    match kind c with
    | Rel i -> if Int.equal i n then x else c
    | _ -> map_with_binders succ aux n c
  in aux

let unlift c =
  let rec aux n c =
    match kind c with
    | Rel i -> (
      match () with
      | () when i < n -> c
      | () when i > n -> mkRel (i - 1)
      | () -> raise DestKO
    )
    | _ -> map_with_binders succ aux n c
  in try Some (aux 1 c) with DestKO -> None


(* COMMON REDUCTION PROCEDURES *)

(* No need to case on args, of_kind already ensures invariants *)
let beta_red head args = mkApp (subst1 args.(0) head, CArray.tl args)

let delta_prim_red env (op, u) args =
  let nargs = CPrimitives.arity op in
  let len = Array.length args in
  let fred args =
    to_result (str "cannot be reduced with provided arguments.")
      (KredNative.red_prim env () op u args)
  in
  match () with
  | () when len < nargs -> Error (str "applied to too few arguments.")
  | () when len > nargs ->
    Result.map
      (fun head -> mkApp (head, Array.sub args nargs (len - nargs)))
      (fred (Array.sub args 0 nargs))
  | () -> fred args

let delta_var_red env id =
  match lookup_named id env with
  | LocalDef (_, c, _) -> Ok c
  | LocalAssum _  ->
    Error (
      str "variable "
      ++ Id.print id
      ++ str " has no unfoldable definition."
    )

let delta_const_red env sp =
  try Ok (constant_value_in env sp)
  with NotEvaluableConst x -> Error x

let eta_lambda_red env evm t c =
  match kind c with
  | App (h, a) when isRelN 1 (CArray.last a) ->
    let nargs = Array.length a in
    ( match
        unlift (if nargs = 1 then h else mkApp (h, Array.sub a 0 (nargs - 1)))
      with
      | None -> Error (str "the variable bound by the abstraction is used more than once.")
      | Some c ->
        let tyc = Retyping.get_type_of env evm (EConstr.of_constr c) in
        let _, k, _ = EConstr.destProd evm tyc in
        if Reductionops.is_conv env evm (EConstr.of_constr t) k
        then Ok c
        else Error (str "performing an eta reduction would change the type of the term.")
    )
  | _ -> Error (str "the term under the abstraction must be an application with the bound variable appearing only as the last argument of this application.")

let fix_red env ((reci, i), (nas, _, _) as f) args =
  let argi = reci.(i) in
  let reducible =
    argi < Array.length args &&
    match kind args.(argi) with
    | Construct _ -> true
    | App (head, _) -> isConstruct head
    | Const (kn, _) -> (
      match (lookup_constant kn env).const_body with
      | Symbol true -> true (* Unholy rewrite get out of this kernel *)
      | _ -> false
    )
    | _ -> false
  in
  if reducible then Ok (mkApp (contract_fix f, args))
  else
    Error (
      pr_nth (argi + 1)
      ++ str "argument of fixpoint "
      ++ Name.print nas.(i).binder_name
      ++ str " is not an applied constructor."
    )

let proj_red pn args =
  let n = Projection.(npars pn + arg pn) in
  if n >= Array.length args then anomaly (str "Struct members missing.");
  args.(n)

let match_red env ci u c brs args =
  let nbrs = Array.length brs in
  if nbrs < c then anomaly (str "Not a constructor of the matched type.");
  let pms, args = CArray.chop ci.ci_npar args in
  let mind = lookup_mind_specif env ci.ci_ind in
  let br = expand_branch mind u pms brs (c - 1) in
  mkApp (br, args)

let match_uip_red_specif env evm (mib, mip) u pms indices = function
| [||] -> Error (str "cannot eliminate a type without constructors in SProp.")
| [| [||] , br |] ->
  let open Declarations in
  let expect_indices =
    try snd (destApp (snd mip.mind_nf_lc.(0)))
    with DestKO -> [||]
  in
  let nind = Array.length indices in
  let rec loop i =
    if Int.equal nind i then Ok br else
    let expected = expect_indices.(mib.mind_nparams + i) in
    let expected = Vars.substl pms expected in
    match Conversion.conv env expected indices.(i) with
    | Ok () -> loop (i + 1)
    | Error () ->
      Error (
        pr_nth (mib.mind_nparams + i)
        ++ str " parameter prevents elimination in SProp; expected "
        ++ quote (hov 0 (Printer.safe_pr_constr_env env evm expected))
        ++ str " got "
        ++ quote (hov 0 (Printer.safe_pr_constr_env env evm indices.(i)))
        ++ str "."
      )
  in loop 0
| _ -> anomaly (str "Cannot eliminate a type with several constructors in SProp.")

let match_uip_red env evm ci u pms iv brs =
  match iv with
  | CaseInvert {indices} ->
    let mind = lookup_mind_specif env ci.ci_ind in
    let ps = expand_match_param_context mind u pms in
    match_uip_red_specif env evm mind u ps indices brs
  | NoInvert -> Error (str "type cannot be eliminated in SProp.")

let bind_to_index =
  let rec aux k m = function
  | [] -> user_err (str "Invalid let binding for zeta_match.")
  | LocalAssum _ :: t -> aux (k + 1) m t
  | LocalDef (_, _, _) :: t -> if m != 1 then aux (k + 1) (m - 1) t else k
  in aux 0

(* Zeta in match bindings
  (breaks property of "one location = one reduction")
  and one-stepping now becomes harder
*)
let zeta_match_red br nas brs c brn n =
  let br' = substn c n br in
  if br == br' then Error (str "match let binding is already reduced.")
  else Ok (array_with brs brn (nas, br'))

(* primitive projection eta reduction *)
let eta_prim_red env ind args =
  let mib = lookup_mind (fst ind) env in
  Result.bind
    ( match mib.mind_record with
      | PrimRecord x -> let _, x, _, _ = x.(snd ind) in Ok x
      | _ ->
        Error (
          str "type "
          ++ Printer.pr_inductive env ind
          ++ str " is not a primitive record."
        )
    )
    ( fun projs ->
      let get_record n c =
        match kind c with
        | Proj (pn, _, bdy) ->
          if eq_ind_chk (Projection.inductive pn) ind
          then
            if Projection.arg pn = n then Ok bdy
            else
              Error (
                pr_nth (n + mib.mind_nparams + 1)
                ++ str " argument is the wrong projection; expected "
                ++ Label.print projs.(n)
                ++ str " got "
                ++ Projection.print pn
                ++ str "."
              )
          else
            Error (
              pr_nth n
              ++ str " argument is a projection of the wrong type; expected "
              ++ Printer.pr_inductive env (Projection.inductive pn)
              ++ str " got "
              ++ Printer.pr_inductive env ind
              ++ str "."
            )
        | _ -> Error (pr_nth n ++ str " argument is not a projection.")
      in
      let nproj = Array.length projs in
      let nargs = Array.length args in
      if mib.mind_nparams + nproj != nargs
      then
        Error (
          str "record constructor is not fully applied; expected "
          ++ int (mib.mind_nparams + nproj)
          ++ str " arguments, got "
          ++ int nargs
          ++ str "."
        )
      else
        Result.bind (get_record 0 args.(mib.mind_nparams)) (fun base_c ->
          let rec arg_loop n =
            let cn = n - mib.mind_nparams in
            if cn = 0 then Ok base_c else
            Result.bind (get_record cn args.(n)) (fun new_c ->
              if Constr.equal base_c new_c then arg_loop (n - 1)
              else
                Error (
                  str "term under the projection differ between the "
                  ++ pr_nth (mib.mind_nparams + 1)
                  ++ str " and "
                  ++ pr_nth (cn + 1)
                  ++ str " argument."
                )
            )
          in arg_loop (nargs - 1)
        )
    )

let evar_red evm (ev, sl) =
  to_result
    (str "evar " ++ Evar.print ev ++ str " has no unfoldable definition.")
    (Evd.existential_opt_value0 evm (ev, sl))


(* HEAD AND REDUCTION STRATEGY HELPERS *)

let app_head env head args =
  match kind head with
  | Lambda (_, _, c) -> Ok (beta_red c args)
  | Fix f -> fix_red env f args
  | Const (c, u) -> (
    match get_primitive env c with
    | Some op -> delta_prim_red env (op, u) args
    | None -> Error (str "No reduction applicable.")
  )
  | Construct ((ind, _), _) -> eta_prim_red env ind args
  | _ -> Error (str "No reduction applicable.")

let const_head env sp =
  let the_const () = str "constant " ++ Constant.print (fst sp) in
  Result.map_error
    ( function
      | NoBody -> the_const () ++ str " has no definition."
      | Opaque -> the_const () ++ str " is opaque."
      | IsPrimitive _ -> the_const () ++ str " is an unapplied primitive."
      | HasRules _ -> (* Rules should be removed from Rocq *)
        Feedback.msg_warning (str "Cannot reduce symbols.");
        the_const () ++ str " is a symbol with custom rewrite rules."
    )
    (delta_const_red env sp)

let iota_match_head env (ci, u, pms, bi, iv, c, brs) =
  match kind c with
  | Construct ((_, c), _) -> Ok (match_red env ci u c brs [||])
  | CoFix cf -> Ok (mkCase (ci, u, pms, bi, iv, contract_cofix cf, brs))
  | App (head, args) -> (
    match kind head with
    | Construct ((_, c), _) -> Ok (match_red env ci u c brs args)
    | CoFix cf -> Ok (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs))
    | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")
  )
  | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")

let zeta_match_step brn n env (ci, u, pms, bi, iv, c, brs) =
  let nas, br = brs.(brn) in
  let mind = lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  let binds = expand_branch_context mind u ps brs brn in
  let bind =
    match List.nth binds n with
    | LocalDef (_, c, _) -> c
    | _ -> assert false
  in
  Result.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
    (zeta_match_red br nas brs bind brn (n + 1))

let zeta_match_head env ci u pms brs =
  let mind = Inductive.lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  to_result
    (str "Failed zeta reduction: all the let bindings are already reduced")
    ( for_step
      ( fun i ->
        let nargs = ci.ci_cstr_nargs.(i) in
        let ndecls = ci.ci_cstr_ndecls.(i) in
        if nargs = ndecls then None else
        let ctx = expand_branch_context mind u ps brs i in
        let nas, br = brs.(i) in
        let rec bind_mapper n = function
        | [] -> None
        | LocalAssum _ :: t -> bind_mapper (n + 1) t
        | LocalDef (na, c, _) :: t ->
          opt_or (Result.to_option (zeta_match_red br nas brs c i n))
            (fun _ -> bind_mapper (n + 1) t)
        in
        bind_mapper 1 ctx
      )
      (Array.length brs)
      0
    )

let proj_head pn r c =
  match kind c with
  (* Construct impossible because `proj {||}` and `proj {| proj := |}` are not a thing *)
  | Construct _ -> anomaly (str "Projection on an empty struct.")
  | CoFix cf -> Ok (mkProj (pn, r, contract_cofix cf))
  | App (head, args) -> (
    match kind head with
    | Construct _ -> Ok (proj_red pn args)
    | CoFix cf -> Ok (mkProj (pn, r, mkApp (contract_cofix cf, args)))
    | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")
  )
  | _ -> Error (str "Failed iota reduction: scrutinee is not an applied constructor or cofix.")

  let proj_step pn r c =
  if Projection.unfolded pn then proj_head pn r c
  else Ok (mkProj (Projection.unfold pn, r, c))


(* MUTATOR *)

module TermMutator = struct
  type 't mutation =
  { trigger: 't -> bool;
    rewrite: 't -> (constr, Pp.t) Result.t
  }
  type t =
  { rel: (env * int) mutation option;
    var: (env * Id.t) mutation option;
    meta: metavariable mutation option;
    evar: existential mutation option;
    sort: Sorts.t mutation option;
    cast: (constr * cast_kind * types) mutation option;
    prod: (Name.t binder_annot * types * types) mutation option;
    lambda: (env * Name.t binder_annot * types * constr) mutation option;
    letin: (Name.t binder_annot * constr * types * constr) mutation option;
    app: (env * constr * constr array) mutation option;
    const: (env * Constant.t * UVars.Instance.t) mutation option;
    ind: (inductive * UVars.Instance.t) mutation option;
    construct: (constructor * UVars.Instance.t) mutation option;
    case: (env * case) mutation option;
    fix: fixpoint mutation option;
    cofix: cofixpoint mutation option;
    proj: (env * Projection.t * Sorts.relevance * constr) mutation option;
    int: Uint63.t mutation option;
    float: Float64.t mutation option;
    string: Pstring.t mutation option;
    array: (UVars.Instance.t * constr array * constr * types) mutation option
  }

  let idle_mutator = {
    rel = None;
    var = None;
    meta = None;
    evar = None;
    sort = None;
    cast = None;
    prod = None;
    lambda = None;
    letin = None;
    app = None;
    const = None;
    ind = None;
    construct = None;
    case = None;
    fix = None;
    cofix = None;
    proj = None;
    int = None;
    float = None;
    string = None;
    array = None
  }

  type occ_count =
  { mutable atleastone: bool;
    mutable occs: Locusops.occurrences_count
  }

  let mutate occs mutator env t =
    let count = {
      atleastone = occs != Locus.AtLeastOneOccurrence;
      occs = Locusops.initialize_occurrence_counter occs
    } in
    let update_cnt () =
      let ok, count' = Locusops.update_occurrence_counter count.occs in
      count.occs <- count';
      ok
    in
    let add_occ occ ft = function
    | Ok t -> count.atleastone <- true; t
    | Error e ->
      if Locusops.is_all_occurrences occs then ft ()
      else user_err (str "Error at " ++ pr_nth occ ++ str " occurence: " ++ e)
    in
    let f_leaf s d t =
      match s with
      | Some {trigger; rewrite} when trigger d && update_cnt () ->
        add_occ
          (Locusops.current_occurrence count.occs)
          (fun _ -> t)
          (rewrite d)
      | _ -> t
    in
    let prep_node s d =
      Option.bind s (fun {trigger; rewrite} ->
        if trigger d && update_cnt ()
        then Some (rewrite, Locusops.current_occurrence count.occs)
        else None
      )
    in
    let step_node ft d = function
    | Some (rw, occ) -> add_occ occ ft (rw d)
    | None -> ft ()
    in
    let array_phys_eq = Array.for_all2 (==) in
    let rec traverse env t =
      if Locusops.occurrences_done count.occs then (* Shortcut *) t else
      match kind t with
      | Rel i -> f_leaf mutator.rel (env, i) t
      | Var id -> f_leaf mutator.var (env, id) t
      | Meta m -> f_leaf mutator.meta m t
      | Evar (ev, sl) ->
        let rw = prep_node mutator.evar (ev, sl) in
        let sl' = SList.Smart.map (traverse env) sl in
        step_node
          (fun _ -> if sl == sl' then t else mkEvar (ev, sl'))
          (ev, sl')
          rw
      | Sort s -> f_leaf mutator.sort s t
      | Cast (c, k, ty) ->
        let rw = prep_node mutator.cast (c, k, ty) in
        let c' = traverse env c in
        step_node
          (fun _ -> if c == c' then t else mkCast (c', k, ty))
          (c', k, ty)
          rw
      | Prod (na, b, c) ->
        let rw = prep_node mutator.prod (na, b, c) in
        let b' = traverse env b in
        let c' = traverse (push_rel (LocalAssum (na, b')) env) c in
        step_node
          (fun _ -> if b == b' && c == c' then t else mkProd (na, b', c'))
          (na, b', c')
          rw
      | Lambda (na, ty, c) ->
        let rw = prep_node mutator.lambda (env, na, ty, c) in
        let ty' = traverse env ty in
        let c' = traverse (push_rel (LocalAssum (na, ty')) env) c in
        step_node
          (fun _ -> if ty == ty' && c == c' then t else mkLambda (na, ty', c'))
          (env, na, ty', c')
          rw
      | LetIn (na, b, ty, c) ->
        let rw = prep_node mutator.letin (na, b, ty, c) in
        let ty' = traverse env ty in
        let b' = traverse env b in
        let c' = traverse (push_rel (LocalDef (na, b', ty')) env) c in
        step_node
          ( fun _ ->
            if ty == ty' && b == b' && c == c' then t
            else mkLetIn (na, b', ty', c')
          )
          (na, b', ty', c')
          rw
      | App (h, a) ->
        let rw = prep_node mutator.app (env, h, a) in
        let h' = traverse env h in
        let a' = CArray.map_left (traverse env) a in
        step_node
          ( fun _ ->
            if h == h' && array_phys_eq a a' then t else mkApp (h', a')
          )
          (env, h', a')
          rw
      | Const (kn, u) -> f_leaf mutator.const (env, kn, u) t
      | Ind ind -> f_leaf mutator.ind ind t
      | Construct c -> f_leaf mutator.construct c t
      | Case (ci, u, pms, (p, r), iv, c, bl) ->
        let rw =
          prep_node mutator.case (env, (ci, u, pms, (p, r), iv, c, bl))
        in
        let c' = traverse env c in
        let pms' = CArray.map_left (traverse env) pms in
        let mind = lookup_mind_specif env ci.ci_ind in
        let p0, bl0 =
          expand_case_contexts mind (ci.ci_ind, u) pms (fst p) bl
        in
        let f_ctx (nas, c) ctx = nas, traverse (push_rel_context ctx env) c in
        let p' = f_ctx p p0 in
        let bl' = CArray.map2 f_ctx bl bl0 in
        step_node
          (fun _ ->
            if
              c == c'
              && array_phys_eq pms pms'
              && snd p == snd p'
              && Array.for_all2 (fun (_, x) (_, y) -> x == y) bl bl'
            then t
            else mkCase (ci, u, pms', (p', r), iv, c', bl')
          )
          (env, (ci, u, pms', (p', r), iv, c', bl'))
          rw
      | Fix (i, (nas, tl, bl)) ->
        let rw = prep_node mutator.fix (i, (nas, tl, bl)) in
        let env' = push_rec_types (nas, tl, bl) env in
        let tl', bl' = map_left2 (traverse env) (traverse env') tl bl in
        step_node
          ( fun _ ->
            if array_phys_eq tl tl' && array_phys_eq bl bl' then t
            else mkFix (i, (nas, tl', bl'))
          )
          (i, (nas, tl', bl'))
          rw
      | CoFix (i, (nas, tl, bl)) ->
        let rw = prep_node mutator.cofix (i, (nas, tl, bl)) in
        let env' = push_rec_types (nas, tl, bl) env in
        let tl', bl' = map_left2 (traverse env) (traverse env') tl bl in
        step_node
          ( fun _ ->
            if array_phys_eq tl tl' && array_phys_eq bl bl' then t
            else mkCoFix (i, (nas, tl', bl'))
          )
          (i, (nas, tl', bl'))
          rw
      | Proj (pn, r, c) ->
        let rw = prep_node mutator.proj (env, pn, r, c) in
        let c' = traverse env c in
        step_node
          (fun _ -> if c == c' then t else mkProj (pn, r, c'))
          (env, pn, r, c')
          rw
      | Int i -> f_leaf mutator.int i t
      | Float f -> f_leaf mutator.float f t
      | String s -> f_leaf mutator.string s t
      | Array (u, a, def, ty) ->
        let rw = prep_node mutator.array (u, a, def, ty) in
        let a' = CArray.map_left (traverse env) a in
        let def' = traverse env def in
        let ty' = traverse env ty in
        step_node
          ( fun _ ->
            if array_phys_eq a a' && def == def' && ty == ty' then t
            else mkArray (u, a', def', ty')
          )
          (u, a', def', ty')
          rw
    in
    let t = traverse env t in
    Locusops.check_used_occurrences count.occs;
    if count.atleastone then t else user_err (str "No occurence to rewrite.")
end


(* REDUCTION TACTICS *)

type 'e eta_kind =
| EBoth
| ELambda of Id.t option
| EPrim of 'e option

let match_binder b = function
| Name na -> Id.equal na b
| Anonymous -> false

let match_opt_binder na = function
| None -> true
| Some b -> match_binder b Context.(na.binder_name)

let cast_mutator = {
  TermMutator.idle_mutator with cast = Some {
    trigger = (fun _ -> true);
    rewrite = fun (c, _, _) -> Ok c
  }
}

let beta_mutator b = {
  TermMutator.idle_mutator with app =
    let rewrite (_, h, a) = let _, _, h = destLambda h in Ok (beta_red h a) in
    match b with
    | Some b ->
      Some {rewrite; trigger = fun (_, h, _) ->
        match kind h with
        | Lambda (na, _, _) -> match_binder b na.binder_name
        | _ -> false
      }
    | None -> Some {rewrite; trigger = fun (_, h, _) -> isLambda h}
}

let zeta_mutator b = {
  TermMutator.idle_mutator with letin =
    let rewrite (_, b, _, c) = Ok (subst1 b c) in
    match b with
    | Some b ->
      Some {rewrite;
        trigger = fun (na, _, _, _) -> match_binder b na.binder_name
      }
    | None -> Some {rewrite; trigger = fun (na, _, _, _) -> true}
}

let zeta_match_mutator ty brn n = {
  TermMutator.idle_mutator with case = Some {
    trigger = (fun (_, (ci, _, _, _, _, _, _)) -> eq_ind_chk ty ci.ci_ind);
    rewrite = fun (env, case) -> zeta_match_step brn n env case
  }
}

let delta_mutator e = let open Evaluable in {
  TermMutator.idle_mutator with
  var = (
    let rewrite (env, id) = delta_var_red env id in
    match e with
    | Some (EvalVarRef i) ->
      Some {rewrite; trigger = fun (_, id) -> Id.equal id i}
    | None -> Some {rewrite; trigger = fun _ -> true}
    | _ -> None
  );
  const = (
    let rewrite (env, c, u) =
      let the_const () = str "constant " ++ Constant.print c in
      Result.map_error
        ( function
          | NoBody -> the_const () ++ str " has no definition."
          | Opaque -> the_const () ++ str " is opaque."
          | IsPrimitive _ -> assert false
          | HasRules _ ->
            the_const () ++ str " is a symbol with custom rewrite rules."
        )
        (delta_const_red env (c, u))
    in
    match e with
    | Some (EvalConstRef cr) ->
      Some {rewrite; trigger = fun (env, c, _) ->
        QConstant.equal env cr c && not (is_primitive env c)
      }
    | None ->
      Some {rewrite; trigger = fun (env, c, _) -> not (is_primitive env c)}
    | _ -> None
  );
  proj = (
    let rewrite (_, pn, r, c) = Ok (mkProj (Projection.unfold pn, r, c)) in
    match e with
    | Some (EvalProjectionRef p) ->
      Some {rewrite; trigger = fun (env, pn, _, _) ->
        QProjection.Repr.equal env p (Projection.repr pn)
        && not (Projection.unfolded pn)
      }
    | None ->
      Some {rewrite;
        trigger = fun (_, pn, _, _) -> not (Projection.unfolded pn)
      }
    | _ -> None
  );
  app =
    let rewrite (env, h, a) =
      let c, u = destConst h in
      let p = Option.get (get_primitive env c) in
      Result.map_error
        (fun e -> str "primitive " ++ Constant.print c ++ spc () ++ e)
        (delta_prim_red env (p, u) a)
    in
    match e with
    | Some (EvalConstRef cr) ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind h with
        | Const (c, _) -> QConstant.equal env cr c && is_primitive env c
        | _ -> false
      }
    | None ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind h with
        | Const (c, _) -> is_primitive env c
        | _ -> false
      }
    | _ -> None
}

let eta_mutator evm ek = {
  TermMutator.idle_mutator with
  lambda = (
    let rewrite (env, na, t, c) = eta_lambda_red env evm t c in
    match ek with
    | ELambda (Some b) ->
      Some {rewrite; trigger = fun (_, na, _, c) ->
        match kind c with
        | App (_, a) ->
          isRelN 1 (CArray.last a) && match_binder b na.binder_name
        | _ -> false
      }
    | EPrim _ -> None
    | _ ->
      Some {rewrite; trigger = fun (_, na, _, c) ->
        match kind c with
        | App (_, a) -> isRelN 1 (CArray.last a)
        | _ -> false
      }
  );
  app =
    let rewrite (env, h, a) =
      let (ind, _), _ = destConstruct h in
      eta_prim_red env ind a
    in
    let is_primitive_record env ind =
      match (lookup_mind (fst ind) env).mind_record with
      | PrimRecord _ -> true
      | _ -> false
    in
    match ek with
    | EPrim (Some (ind, None)) ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind h with
        | Construct ((ind', _), _) ->
          eq_ind_chk ind ind' && is_primitive_record env ind'
        | _ -> false
      }
    | EPrim (Some (ind, Some n)) ->
        Some {rewrite; trigger = fun (env, h, _) ->
          match kind h with
          | Construct ((ind', n'), _) ->
            eq_ind_chk ind ind' && n = n' && is_primitive_record env ind'
          | _ -> false
      }
    | ELambda _ -> None
    | _ ->
      Some {rewrite; trigger = fun (env, h, _) ->
        match kind h with
        | Construct ((ind, _), _) -> is_primitive_record env ind
        | _ -> false
      }
}

let evar_mutator evm = {
  TermMutator.idle_mutator with evar = Some {
    trigger = (fun _ -> true);
    rewrite = evar_red evm
  }
}

let fix_prime_mutator b = {
  TermMutator.idle_mutator with fix = Some (
    let rewrite f = Ok (contract_fix f) in
    match b with
    | Some b ->
      { rewrite;
        trigger = fun ((_, i), (nas, _, _)) ->
          match_binder b nas.(i).binder_name
      }
    | None -> {rewrite; trigger = fun _ -> true}
  )
}

let fix_mutator b = {
  TermMutator.idle_mutator with app = Some (
    let rewrite (env, h, a) = fix_red env (destFix h) a in
    match b with
    | Some b ->
      { rewrite; trigger = fun (_, h, _) ->
        match kind h with
        | Fix ((_, i), (nas, _, _)) -> match_binder b nas.(i).binder_name
        | _ -> false
      }
    | None -> {rewrite; trigger = fun (_, h, _) -> isFix h}
  )
}

let cofix_prime_mutator b = {
  TermMutator.idle_mutator with cofix = Some (
    let rewrite cf = Ok (contract_cofix cf) in
    match b with
    | Some b ->
      { rewrite;
        trigger = fun (i, (nas, _, _)) -> match_binder b nas.(i).binder_name
      }
    | None -> {rewrite; trigger = fun _ -> true}
  )
}

let cofix_mutator b =
  let extract_cofix c =
    match kind c with
    | CoFix cf -> Some (cf, [||])
    | App (h, a) -> (
      match kind h with
      | CoFix cf -> Some (cf, a)
      | _ -> None
    )
    | _ -> None
  in
  { TermMutator.idle_mutator with
    case = Some (
      let rewrite (_, (ci, u, pms, bi, iv, c, bl)) =
        let cf, a = Option.get (extract_cofix c) in
        Ok (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, a), bl))
      in
      match b with
      | Some b ->
        { rewrite; trigger = fun (_, (_, _, _, _, _, c, _)) ->
          match extract_cofix c with
          | Some ((i, (nas, _, _)), _) -> match_binder b nas.(i).binder_name
          | None -> false
        }
      | None ->
        { rewrite; trigger = fun (_, (_, _, _, _, _, c, _)) ->
          Option.has_some (extract_cofix c)
        }
    );
    proj = Some (
      let rewrite (_, pn, r, c) =
        let cf, a = Option.get (extract_cofix c) in
        Ok (mkProj (pn, r, mkApp (contract_cofix cf, a)))
      in
      match b with
      | Some b ->
        { rewrite; trigger = fun (_, pn, _, c) ->
          match extract_cofix c with
          | Some ((i, (nas, _, _)), _) ->
            Projection.unfolded pn && match_binder b nas.(i).binder_name
          | None -> false
        }
      | None ->
        { rewrite; trigger = fun (_, pn, _, c) ->
          Projection.unfolded pn && Option.has_some (extract_cofix c)
        }
    )
  }

let match_mutator evm tyc =
  let extract_construct t =
    match kind t with
    | Construct c -> Some (c, [||])
    | App (h, a) -> (
      match kind h with
      | Construct c -> Some (c, a)
      | _ -> None
    )
    | _ -> None
  in
  { TermMutator.idle_mutator with
    case = Some (
      let rewrite (env, (ci, u, pms, _, iv, c, brs)) =
        match extract_construct c with
        | Some (((_, c), _), a) -> Ok (match_red env ci u c brs a)
        | None ->
          Result.map_error
            (fun e -> str "scrutinee is not an applied constructor and " ++ e)
            (match_uip_red env evm ci u pms iv brs)
      in
      match tyc with
      | Some (ind, Some n) ->
        { rewrite; trigger = fun (_, (_, _, _, _, _, c, _)) ->
          match extract_construct c with
          | Some (((ind', c), _), _) -> eq_ind_chk ind ind' && n == c
          | None -> false
        }
      | Some (ind, None) ->
        { rewrite;
          trigger = fun (_, (ci, _, _, _, _, _, _)) -> eq_ind_chk ind ci.ci_ind
        }
      | None -> {rewrite; trigger = fun _ -> true}
    );
    proj = Some (
      let rewrite (env, pn, _, c) =
        match extract_construct c with
        | Some (_, a) -> Ok (proj_red pn a)
        | None -> Error (str "scrutinee is not an applied constructor.")
      in
      match tyc with
      | Some (ind, _) ->
        { rewrite; trigger = fun (_, pn, _, _) ->
          Projection.unfolded pn && eq_ind_chk ind (Projection.inductive pn)
        }
      | None -> {rewrite; trigger = fun (_, pn, _, _) -> Projection.unfolded pn}
    )
  }

let root_step env evm c =
  match kind c with
  | Var id ->
    Result.map_error (fun e -> str "Failed delta reduction : " ++ e)
      (delta_var_red env id)
  | Evar ev ->
    Result.map_error (fun e -> str "Failed evar reduction: " ++ e)
      (evar_red evm ev)
  | Cast (ct, _, _) -> Ok ct
  | LetIn (na, b, u, c) -> Ok (subst1 b c)
  | App (head, args) -> app_head env head args
  | Const sp ->
    Result.map_error (fun e -> str "Failed delta reduction: " ++ e)
      (const_head env sp)
  | Case (ci, u, pms, bi, iv, c, brs) ->
    first_success (str "Failed reduction of match,") [
      (fun _ -> iota_match_head env (ci, u, pms, bi, iv, c, brs));
      ( fun _ ->
        Result.map_error (fun e -> str "SProp elimination: " ++ e)
          (match_uip_red env evm ci u pms iv brs)
      );
      fun _ ->
        Result.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
          (zeta_match_head env ci u pms brs)
    ]
  | Proj (pn, r, c) -> proj_step pn r c
  | Lambda (_, t, c) ->
    Result.map_error (fun e -> str "Failed eta reduction : " ++ e)
      (eta_lambda_red env evm t c)
  | Rel _ | Meta _ | Sort _ | Prod _ | Ind _
  | Construct _ | Fix _ | CoFix _ | Int _
  | Float _ | String _ | Array _ -> Error (str "No reduction applicable.")

let head_step evm _ec (* TODO *) env c =
  let rec aux c =
    match kind c with
    | Var id -> Result.to_option (delta_var_red env id)
    | Evar ev -> Evd.existential_opt_value0 evm ev
    | Cast (c, k, t) ->
      Some (
        match aux c with
        | Some c -> mkCast (c, k, t)
        | None -> c
      )
    | LetIn (na, b, u, c) -> Some (subst1 b c)
    | App (head, args) ->
      opt_or
        ( match kind head with
          | Fix ((reci, i), f) ->
            let i = reci.(i) in
            if i < Array.length args
            then
              Option.map (fun c -> mkApp (head, array_with args i c))
                (aux args.(i))
            else None
          | _ -> Option.map (fun h -> mkApp (h, args)) (aux head)
        )
        (fun _ -> Result.to_option (app_head env head args))
    | Const sp -> Result.to_option (const_head env sp)
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> Result.to_option (match_uip_red env evm ci u pms iv brs));
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c)
        );
        fun _ ->
          Result.to_option (iota_match_head env (ci, u, pms, bi, iv, c, brs))
      ]
    | Proj (pn, r, c) ->
      if Projection.unfolded pn
      then
        or_step (fun c -> mkProj (pn, r, c)) (aux c)
          (fun _ -> Result.to_option (proj_head pn r c))
      else Some (mkProj (Projection.unfold pn, r, c))
    | Rel _ | Meta _ | Sort _ | Prod _ | Lambda _
    | Ind _ | Construct _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> None
    in force "Term at head is not reducible." (aux c)

let cbv_reduce env evm =
  let rec aux c =
    match kind c with
    | Var id -> Result.to_option (delta_var_red env id)
    | Evar (evi, ev) -> (* Evar solving is not considered progress :( *)
      Evd.existential_opt_value0 evm (evi, ev)
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match aux ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux t)
        (fun _ -> Option.map (fun u -> mkProd (na, t, u)) (aux u))
    | LetIn (na, b, u, c) ->
      Some (
        match aux b with
        | Some b -> mkLetIn (na, b, u, c)
        | None -> subst1 b c
      )
    | App (head, args) ->
      first_step [
        (fun _ -> Option.map (fun head -> mkApp (head, args)) (aux head));
        (fun _ -> Option.map (fun hd -> mkApp (head, array_with args 0 hd)) (aux args.(0)));
        (fun _ -> Result.to_option (app_head env head args));
        fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step_n aux args 1)
      ]
    | Const sp -> Result.to_option (const_head env sp)
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c));
        (fun _ -> Result.to_option (iota_match_head env (ci, u, pms, bi, iv, c, brs)));
        (fun _ -> Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step aux pms));
        fun _ -> Result.to_option (match_uip_red env evm ci u pms iv brs)
      ]
    | Proj (pn, r, c) -> Result.to_option (proj_step pn r c)
    | Rel _ | Meta _ | Sort _ | Lambda _
    | Ind _ | Construct _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> None
  in aux

let cbv_normalize evm =
  let rec aux env c =
    let reduce_or_normalize f c =
      opt_or (cbv_reduce env evm c) (fun _ -> aux (f env) c)
    in
    match kind c with
    | Evar (evi, ev) ->
      Option.map (fun ev -> mkEvar (evi, ev))
        (slist_step (reduce_or_normalize id) ev)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t) (fun _ ->
        Option.map (fun u -> mkProd (na, t, u))
          (aux (push_rel (LocalAssum (na, t)) env) u)
      )
    | Lambda (na, t, c) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkLambda (na, t, c))
          (reduce_or_normalize (push_rel (LocalAssum (na, t))) c)
        );
        ( fun _ ->
          Option.map (fun t -> mkLambda (na, t, c)) (reduce_or_normalize id t)
        );
        fun _ -> Result.to_option (eta_lambda_red env evm t c)
      ]
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (aux env head) (fun _ ->
        Option.map (fun args -> mkApp (head, args)) (array_step (aux env) args)
      )
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c)
        );
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs))
            (array_step (aux env) pms)
        );
        ( fun _ ->
          match zeta_match_head env ci u pms brs with
          | Ok brs -> Some (mkCase (ci, u, pms, bi, iv, c, brs))
          | Error _ -> None
        );
        fun _ ->
          let mind = lookup_mind_specif env ci.ci_ind in
          let ps = expand_match_param_context mind u pms in
          or_step (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
            ( for_step
              ( fun i ->
                let nas, br = brs.(i) in
                let ctx = expand_branch_context mind u ps brs i in
                Option.map (fun br -> array_with brs i (nas, br))
                  (reduce_or_normalize (push_rel_context ctx) br)
              )
              (Array.length brs)
              0
            )
            ( fun _ ->
              let (nas, p), rp = bi in
              Option.map
                (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                ( reduce_or_normalize
                  ( push_rel_context
                    (expand_arity_context mind (ci.ci_ind, u) ps nas)
                  )
                  p
                )
            )
      ]
    | Fix (si, (nas, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (nas, tys, bds)))
        (array_step (reduce_or_normalize (push_rec_types (nas, tys, bds))) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (nas, tys, bds)))
            (array_step (reduce_or_normalize id) tys)
        )
    | CoFix (ri, (nas, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (nas, tys, bds)))
        (array_step (reduce_or_normalize (push_rec_types (nas, tys, bds))) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (nas, tys, bds)))
            (array_step (reduce_or_normalize id) tys)
        )
    | Proj (pn, r, c) -> Option.map (fun c -> mkProj (pn, r, c)) (aux env c)
    | Array (u, ts, def, ty) ->
      first_step [
        ( fun _ ->
          Option.map (fun def -> mkArray (u, ts, def, ty))
            (reduce_or_normalize id def)
        );
        ( fun _ ->
          Option.map (fun ts -> mkArray (u, ts, def, ty))
            (array_step (reduce_or_normalize id) ts)
        );
        fun _ ->
          Option.map (fun ty -> mkArray (u, ts, def, ty))
            (reduce_or_normalize id ty)
      ]
    | Var _ | Rel _ | Meta _ | Sort _
    | Cast _ | Const _ | Ind _ | Construct _
    | Int _ | Float _ | String _ -> None
    | LetIn _ -> assert false
  in aux

let cbv_step evm ec env c =
  force "Term is fully reduced."
    (opt_or (cbv_reduce env evm c) (fun _ -> cbv_normalize evm env c))

let global_step evm ec env c =
  let rec aux env c =
    match kind c with
    | Var id -> Result.to_option (delta_var_red env id)
    | Evar (evi, ev) ->
      (* Evar solving is not considered progress :( *)
      or_step (fun ev -> mkEvar (evi, ev)) (slist_step (aux env) ev)
        (fun _ -> Evd.existential_opt_value0 evm (evi, ev))
    | Cast (ct, k, ck) ->
      (* Cast might be useful for performance until term below is fully reduced
        but cast stripping is not considered progress :(
      *)
      Some (match aux env ct with Some ct -> mkCast (ct, k, ck) | None -> ct)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t) (fun _ ->
        Option.map (fun u -> mkProd (na, t, u))
          (aux (push_rel (LocalAssum (na, t)) env) u)
      )
    | Lambda (na, t, c) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkLambda (na, t, c))
            (aux (push_rel (LocalAssum (na, t)) env) c)
        );
        (fun _ -> Option.map (fun t -> mkLambda (na, t, c)) (aux env t));
        fun _ -> Result.to_option (eta_lambda_red env evm t c)
      ]
    | LetIn (na, b, u, c) ->
      Some (
        match aux env b with
        | Some b -> mkLetIn (na, b, u, c)
        | None ->
          match aux (push_rel (LocalDef (na, b, u)) env) c with
          | Some c -> mkLetIn (na, b, u, c)
          | None -> subst1 b c
      )
    | App (head, args) ->
      first_step [
        (fun _ -> Option.map (fun head -> mkApp (head, args)) (aux env head));
        ( fun _ ->
          Option.map (fun hd -> mkApp (head, array_with args 0 hd))
            (aux env args.(0))
        );
        (fun _ -> Result.to_option (app_head env head args));
        fun _ ->
          Option.map (fun args -> mkApp (head, args))
            (array_step_n (aux env) args 1)
      ]
    | Const sp -> Result.to_option (const_head env sp)
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c)
        );
        (fun _ -> Result.to_option (iota_match_head env (ci, u, pms, bi, iv, c, brs)));
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs))
            (array_step (aux env) pms)
        );
        fun _ ->
          let mind = lookup_mind_specif env ci.ci_ind in
          let ps = expand_match_param_context mind u pms in
          first_step [
            ( fun _ ->
              match iv with
              | CaseInvert {indices} ->
                Result.to_option
                  (match_uip_red_specif env evm mind u ps indices brs)
              | _ -> None
            );
            ( fun _ ->
              match zeta_match_head env ci u pms brs with
              | Ok brs -> Some (mkCase (ci, u, pms, bi, iv, c, brs))
              | Error _ -> None
            );
            ( fun _ ->
              Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
                ( for_step
                  ( fun i ->
                    let nas, br = brs.(i) in
                    let ctx = expand_branch_context mind u ps brs i in
                    Option.map (fun br -> array_with brs i (nas, br))
                      (aux (push_rel_context ctx env) br)
                  )
                  (Array.length brs)
                  0
                )
            );
            fun _ ->
              let (nas, p), rp = bi in
              Option.map
                (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                ( aux
                  ( push_rel_context
                    (expand_arity_context mind (ci.ci_ind, u) ps nas)
                    env
                  )
                  p
                )
          ]
      ]
    | Fix (si, (nas, tys, bds)) ->
      or_step (fun bds -> mkFix (si, (nas, tys, bds)))
        (array_step (aux (push_rec_types (nas, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkFix (si, (nas, tys, bds)))
            (array_step (aux env) tys)
        )
    | CoFix (ri, (nas, tys, bds)) ->
      or_step (fun bds -> mkCoFix (ri, (nas, tys, bds)))
        (array_step (aux (push_rec_types (nas, tys, bds) env)) bds)
        ( fun _ ->
          Option.map (fun tys -> mkCoFix (ri, (nas, tys, bds)))
            (array_step (aux env) tys)
        )
    | Proj (pn, r, c) ->
      or_step (fun c -> mkProj (pn, r, c)) (aux env c)
        (fun _ -> Result.to_option (proj_step pn r c))
    | Array (u, ts, def, ty) ->
      first_step [
        ( fun _ ->
          Option.map (fun def -> mkArray (u, ts, def, ty)) (aux env def)
        );
        ( fun _ ->
          Option.map (fun t -> mkArray (u, ts, def, ty))
            (array_step (aux env) ts)
        );
        fun _ -> Option.map (fun ty -> mkArray (u, ts, def, ty)) (aux env ty)
      ]
    | Rel _ | Meta _ | Sort _ | Ind _ | Construct _
    | Int _ | Float _ | String _ -> None
  in force "Term is fully reduced." (aux env c)

type 'c end_condition =
| ECNat of int
| ECLocal of 'c
| ECGlobal of 'c

type ('occ, 'endc, 'tycons, 'zeta, 'delta) reduction =
(*| SRRule (* Rewrite rules *)*)
| Cast of 'occ Locus.occurrences_gen (* Cast removal *)
| Beta of Id.t option * 'occ Locus.occurrences_gen
(* Beta: applied lambda to substitution *)
| Zeta of Id.t option * 'occ Locus.occurrences_gen
(* Zeta: letin to substitution *)
| ZetaMatch of 'zeta * 'occ Locus.occurrences_gen
(* Zeta-match: match-letin to substitution *)
| Delta of 'delta option * 'occ Locus.occurrences_gen
(* Delta: name resolution (including application of primitives) *)
| Eta of 'tycons eta_kind * 'occ Locus.occurrences_gen
(* Eta:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| Evar of 'occ Locus.occurrences_gen
(* Evar: evar resolution + context substitution, not sure about this one *)
| IotaFix of Id.t option * 'occ Locus.occurrences_gen
(* Iota-fix: push fixpoint inward when allowed to *)
| IotaFixPrime of Id.t option * 'occ Locus.occurrences_gen
(* Iota-fix-prime: push fixpoint inward, maybe unfold and refold too? *)
| IotaCofix of Id.t option * 'occ Locus.occurrences_gen
(* Iota-cofix: match or project a cofix *)
| IotaCofixPrime of Id.t option * 'occ Locus.occurrences_gen
(* Iota-cofix-prime: push cofix inward, maybe unfold and refold too? *)
| IotaMatch of 'tycons option * 'occ Locus.occurrences_gen
(* Iota-match: match or project on a constructor + inversion in SProp *)
| Root (* Any reduction applicable at the root of the whole term *)
| Head (* Any reduction at head *)
| Cbv of 'endc end_condition (* Next reduction step of a call-by-value strategy *)
| Cbn of 'endc end_condition (* Next reduction step of a call-by-name strategy *)
| Lazy of 'endc end_condition (* Next reduction step of a call-by-need / lazy strategy *)

let map_end_condition f = function
| ECNat n -> ECNat n
| ECLocal x -> ECLocal (f x)
| ECGlobal x -> ECGlobal (f x)

let map_eta_kind f = function
| EPrim x -> EPrim (Option.map f x)
| EBoth | ELambda _ as x -> x

let map_reduction focc fend ftyc fz fd = function
| Cast occ -> Cast (focc occ)
| Beta (b, occ) -> Beta (b, focc occ)
| Zeta (b, occ) -> Zeta (b, focc occ)
| ZetaMatch (z, occ) -> ZetaMatch (fz z, focc occ)
| Delta (d, occ) -> Delta (Option.map fd d, focc occ)
| Eta (tyc, occ) -> Eta (map_eta_kind ftyc tyc, focc occ)
| Evar occ -> Evar (focc occ)
| IotaFix (b, occ) -> IotaFix (b, focc occ)
| IotaFixPrime (b, occ) -> IotaFixPrime (b, focc occ)
| IotaCofix (b, occ) -> IotaCofix (b, focc occ)
| IotaCofixPrime (b, occ) -> IotaCofixPrime (b, focc occ)
| IotaMatch (tyc, occ) -> IotaMatch (Option.map ftyc tyc, focc occ)
| Cbv e -> Cbv (map_end_condition fend e)
| Cbn e -> Cbn (map_end_condition fend e)
| Lazy e -> Lazy (map_end_condition fend e)
| (Root | Head as s) -> s

let pr_tycons env (ind, opn) =
  Printer.pr_inductive env ind ++ pr_opt int opn

let pr_zeta_raw (sg, x) =
  let open Pputils in
  pr_or_by_notation Libnames.pr_qualid sg ++ pr_opt (pr_or_var int) x

let pr_zeta_glob env (gr, x) =
  Termops.pr_global_env env gr ++ pr_opt (Pputils.pr_or_var int) x

let pr_zeta env (ind, n, m) = (* TODO REDO *)
  let rec index_to_bind n m = function
  | LocalDef (na, _, _) :: t ->
    if m = 0 then na, n else index_to_bind (n + 1) (m - 1) t
  | LocalAssum _ :: t when m > 0 -> index_to_bind n (m - 1) t
  | _ -> anomaly (str "Invalid zeta_match index.")
  in
  let mib, oib = Inductive.lookup_mind_specif env ind in
  let na, m = index_to_bind 0 m (fst oib.mind_nf_lc.(n)) in
  if mib.mind_record = NotRecord
  then Id.print oib.mind_consnames.(n) ++ spc () ++ int m
  else
    match na.binder_name with
    | Name id -> Id.print id
    | Anonymous -> Printer.pr_inductive env ind ++ spc () ++ int m

let pr_end_condition pr = function
| ECNat n -> pr_arg int n
| ECLocal x -> pr_arg str "until_focused" ++ pr_arg pr x
| ECGlobal x -> pr_arg str "until_global" ++ pr_arg pr x

let pr_eta_kind pr = function
| EBoth -> mt ()
| EPrim x -> pr_arg str "prim" ++ pr_opt pr x
| ELambda s -> pr_arg str "lambda" ++ pr_opt Id.print s

let pr_reduction pr_occs pr_closure pr_tycons pr_zeta pr_delta = function
| Cast occ -> str "cast" ++ pr_occs occ
| Beta (b, occ) -> str "beta" ++ pr_opt Id.print b ++ pr_occs occ
| Zeta (b, occ) -> str "zeta" ++ pr_opt Id.print b ++ pr_occs occ
| ZetaMatch (z, occ) -> str "zeta_match" ++ pr_arg pr_zeta z ++ pr_occs occ
| Delta (t, occ) -> str "delta" ++ pr_opt pr_delta t ++ pr_occs occ
| Eta (tyc, occ) -> str "eta" ++ pr_eta_kind pr_tycons tyc ++ pr_occs occ
| Evar occ -> str "evar" ++ pr_occs occ
| IotaFix (b, occ) -> str "iota_fix" ++ pr_opt Id.print b ++ pr_occs occ
| IotaFixPrime (b, occ) -> str "iota_fix'" ++ pr_opt Id.print b ++ pr_occs occ
| IotaCofix (b, occ) -> str "iota_cofix" ++ pr_opt Id.print b ++ pr_occs occ
| IotaCofixPrime (b, occ) -> str "iota_cofix'" ++ pr_opt Id.print b ++ pr_occs occ
| IotaMatch (tyc, occ) -> str "iota_match" ++ pr_opt pr_tycons tyc ++ pr_occs occ
| Root -> str "root"
| Head -> str "head"
| Cbv e -> str "cbv" ++ pr_end_condition pr_closure e
| Cbn e -> str "cbn" ++ pr_end_condition pr_closure e
| Lazy e -> str "lazy" ++ pr_end_condition pr_closure e

let interp_tycons env gr =
  let open GlobRef in
  let fail () = user_err (Termops.pr_global_env env gr ++ str " does not describe a type, constructor nor projection.") in
  match gr with
  | ConstRef c -> (
    try
      let open Structures in
      let open Structure in
      (Structure.find_from_projection c).name, Some 1
    with Not_found -> fail ()
  )
  | IndRef ind -> ind, None
  | ConstructRef (ind, n) -> ind, Some n
  | _ -> fail ()

let interp_zeta env (gr, x) =
  let zmargs =
    let open GlobRef in
    match gr, x with
    | ConstRef _, Some _ -> user_err (str "Too many arguments to zeta_match.")
    | ConstRef c, None -> (
      try
        let open Structures in
        let open Structure in
        let s = Structure.find_from_projection c in
        let rec count_binds n = function
        | {proj_body = Some c'; proj_true = false; _} :: _ when QConstant.equal env c c' -> Some n
        | {proj_true = pt; _} :: l -> count_binds (if pt then n else n + 1) l
        | _ -> None
        in
        match count_binds 0 s.projections with
        | None -> user_err (str "Projection has no definition to delta reduce.")
        | Some n -> Some (s.name, Some 1, Some (Locus.ArgArg n))
      with Not_found -> None
    )
    | IndRef ind, x -> Some (ind, None, x)
    | ConstructRef (ind, n), x -> Some (ind, Some n, x)
    | _ -> None
  in
  ( match zmargs with
    | None -> user_err (str "Argument of zeta_match is neither a type, constructor, nor projection.")
    | Some ((ind, tyi), x, y) ->
      let oib = (lookup_mind ind env).mind_packets.(tyi) in
      let nbrs = Array.length oib.mind_nf_lc in
      let n =
        match x with
        | Some n -> n - 1
        | None ->
          if nbrs != 1 then user_err (str "Use of type as argument for zeta_match is only allowed for types with a single constructor.");
          0
      in
      if n >= nbrs then user_err (str "Invalid branch for zeta_match.");
      let rec no_binding n = function
      | [] -> ()
      | LocalAssum _ :: t -> no_binding n t
      | LocalDef (na, _, _) :: t ->
        if match_opt_binder na n
        then user_err (str "Non unique let binding for zeta_match.")
        else no_binding n t
      in
      let rec single_binding n k = function
      | [] -> user_err (str "No let binding for zeta_match.")
      | LocalAssum _ :: t -> single_binding n (k + 1) t
      | LocalDef (na, _, _) :: t ->
        if match_opt_binder na n then (no_binding n t; k)
        else single_binding n (k + 1) t
      in
      let m =
        let bindings = CList.firstn (oib.mind_consnrealdecls.(n)) (fst oib.mind_nf_lc.(n)) in
        match y with
        | Some (Locus.ArgArg m) -> bind_to_index m bindings
        | Some (Locus.ArgVar m) -> single_binding (Some m.v) 0 bindings
        | None -> single_binding None 0 bindings
      in
      (ind, tyi), n, m
  )

let step red env evm c =
  let f =
    match red with
    | Cast occ -> TermMutator.mutate occ cast_mutator
    | Beta (b, occ) -> TermMutator.mutate occ (beta_mutator b)
    | Zeta (b, occ) -> TermMutator.mutate occ (zeta_mutator b)
    | ZetaMatch ((ind, n, m), occ) ->
      TermMutator.mutate occ (zeta_match_mutator ind n m)
    | Delta (t, occ) -> TermMutator.mutate occ (delta_mutator t)
    | Eta (ek, occ) -> TermMutator.mutate occ (eta_mutator evm ek)
    | Evar occ -> TermMutator.mutate occ (evar_mutator evm)
    | IotaFix (b, occ) -> TermMutator.mutate occ (fix_mutator b)
    | IotaFixPrime (b, occ) -> TermMutator.mutate occ (fix_prime_mutator b)
    | IotaCofix (b, occ) -> TermMutator.mutate occ (cofix_mutator b)
    | IotaCofixPrime (b, occ) -> TermMutator.mutate occ (cofix_prime_mutator b)
    | IotaMatch (tyc, occ) -> TermMutator.mutate occ (match_mutator evm tyc)
    | Root ->
      ( fun env t ->
        match root_step env evm t with
        | Ok t -> t
        | Error e -> user_err (str "Term is not reducible at root: " ++ e)
      )
    | Head -> head_step evm (ECNat 1) (* TODO *)
    | Cbv ec -> cbv_step evm ec
    | Cbn ec -> global_step evm ec (* LATER *)
    | Lazy ec -> global_step evm ec (* LATER *)
  in
  EConstr.of_constr (f env (EConstr.Unsafe.to_constr c))
