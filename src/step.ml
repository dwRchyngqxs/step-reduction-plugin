open Pp
open CErrors
open Result
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

let rec first_step l =
  match l with
  | [] -> None
  | h :: t ->
    match h () with
    | Some x -> Some x
    | None -> first_step t

let or_else x f =
  match x with
  | None -> f ()
  | _ -> x

let for_step f e =
  let rec aux i = if i = e then None else or_else (f i) (fun _ -> aux (i + 1))
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

let force msg = function
| Some x -> x
| None -> user_err (str msg)
(*
let force' msg = function
| Some x -> x
| None -> anomaly (str msg)
*)

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
    | Rel i ->
      ( match () with
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
    match KredNative.red_prim env () op u args with
    | Some x -> Ok x
    | None -> Error "primitive cannot be reduced with provided arguments"
  in
  ( match () with
    | () when len < nargs -> Error "primitive applied to too few arguments"
    | () when len > nargs ->
      Result.map
        (fun head -> mkApp (head, Array.sub args nargs (len - nargs)))
        (fred (Array.sub args 0 nargs))
    | () -> fred args
  )

let delta_var_red env id =
  match lookup_named id env with
  | LocalDef (_, c, _) -> Some c
  | LocalAssum _  -> None

let delta_const_red env sp =
  try Ok (constant_value_in env sp)
  with NotEvaluableConst x -> Error x

let eta_lambda_red evm env t c =
  try
    let head, args = destApp c in
    let nargs = Array.length args in
    let arg = args.(nargs - 1) in
    if not (isRelN 1 arg)
    then Error "Argument of the application under abstraction is not the bound variable."
    else
      match unlift (if nargs = 1 then head else mkApp (head, Array.sub args 0 (nargs - 1))) with
      | None -> Error "Variable bound by the abstraction is used more than once."
      | Some c ->
        let tyc = Retyping.get_type_of env evm (EConstr.of_constr c) in
        let _, k, _ = EConstr.destProd evm tyc in
        if Reductionops.is_conv env evm (EConstr.of_constr t) k
        then Ok c
        else Error "Performing eta reduction would change type."
  with DestKO -> Error "Term under abstraction is not an application."

let is_fix_reducible env ((reci, i), _) args =
  let argi = reci.(i) in
  argi < Array.length args &&
    match kind args.(argi) with
    | Construct _ -> true
    | App (head, _) -> isConstruct head
    | Const (kn, _) ->
      ( match (lookup_constant kn env).const_body with
        | Symbol true -> true (* Unholy rewrite get out of this kernel *)
        | _ -> false
      )
    | _ -> false

let fix_red env f args =
  if is_fix_reducible env f args
  then Some (mkApp (contract_fix f, args))
  else None

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

let match_uip_red_specif env (mib, mip) u pms indices = function
| [||] -> None
| [| [||] , br |] ->
  let open Declarations in
  let expect_indices =
    try snd (destApp (snd mip.mind_nf_lc.(0)))
    with DestKO -> [||]
  in
  let nind = Array.length indices in
  let rec loop i =
    if Int.equal nind i then true else
    let expected = expect_indices.(mib.mind_nparams + i) in
    let expected = Vars.substl pms expected in
    match Conversion.conv env expected indices.(i) with
    | Ok () -> loop (i + 1)
    | Error () -> false
  in
  if loop 0 then Some br else None
| _ -> anomaly (str "UIP on a type which doesn't have a unique constructor.")

let match_uip_red env ci u pms indices brs =
  let mind = lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  match_uip_red_specif env mind u ps indices brs

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
  if br == br' then None else Some (array_with brs brn (nas, br'))

(* primitive projection eta reduction *)
let eta_prim_red env ind args =
  let get_record n c =
    let pn, _, bdy = destProj c in
    if not (eq_ind_chk (Projection.inductive pn) ind) || Projection.arg pn != n then raise DestKO;
    bdy
  in
  let mib = lookup_mind (fst ind) env in
  Result.bind
    ( match mib.mind_record with
      | PrimRecord x -> let _, x, _, _ = x.(snd ind) in Ok (Array.length x)
      | _ -> Error "Not a record constructor."
    )
    ( fun nproj ->
      let nargs = Array.length args in
      if mib.mind_nparams + nproj != nargs
      then Error "Record constructor applied to too few arguments."
      else try
        let base_c = get_record 0 args.(mib.mind_nparams) in
        let rec arg_loop n =
          let cn = n - mib.mind_nparams in
          if cn = 0 then Ok base_c else
          if Constr.equal (get_record cn args.(n)) base_c
          then arg_loop (n - 1)
          else Error "Terms under projections are not the same."
        in
        arg_loop (nargs - 1)
      with DestKO -> Error "Wrong projection."
    )

(* HEAD AND REDUCTION STRATEGY HELPERS *)

let app_head env head args =
  match kind head with
  | Lambda (_, _, c) -> Some (beta_red c args)
  | Fix f -> fix_red env f args
  | Const (c, u) ->
    Option.bind (get_primitive env c)
      (fun op -> Result.to_option (delta_prim_red env (op, u) args))
  | Construct ((ind, _), _) -> Result.to_option (eta_prim_red env ind args)
  | _ -> None

let const_head env sp =
  match delta_const_red env sp with
  | Ok x -> Some x
  | Error (HasRules _) -> Feedback.msg_warning (str "Cannot reduce symbols."); None (* Rules should be removed from Rocq *)
  | Error _ -> None

let iota_match_head env ci u pms bi iv c brs =
  match kind c with
  | Construct ((_, c), _) -> Some (match_red env ci u c brs [||])
  | CoFix cf -> Some (mkCase (ci, u, pms, bi, iv, contract_cofix cf, brs))
  | App (head, args) ->
    ( match kind head with
      | Construct ((_, c), _) -> Some (match_red env ci u c brs args)
      | CoFix cf -> Some (mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs))
      | _ -> None
    )
  | _ -> None

let zeta_match_step brn n (env, ci, u, pms, bi, iv, c, brs) =
  let nas, br = brs.(brn) in
  let mind = lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  let binds = expand_branch_context mind u ps brs brn in
  let bind = match List.nth binds n with LocalDef (_, c, _) -> c | _ -> assert false in
  let brs =
    force "Match let binding is already reduced."
      (zeta_match_red br nas brs bind brn (n + 1)) in
  mkCase (ci, u, pms, bi, iv, c, brs)

let zeta_match_head env ci u pms brs =
  let mind = Inductive.lookup_mind_specif env ci.ci_ind in
  let ps = expand_match_param_context mind u pms in
  for_step
    ( fun i ->
      let nargs = ci.ci_cstr_nargs.(i) in
      let ndecls = ci.ci_cstr_ndecls.(i) in
      if nargs = ndecls then None else
      let ctx = expand_branch_context mind u ps brs i in
      let nas, br = brs.(i) in
      let rec bind_mapper n = function
      | [] -> None
      | LocalAssum _ :: t -> bind_mapper (n + 1) t
      | LocalDef (_, c, _) :: t ->
        or_else (zeta_match_red br nas brs c i n) (fun _ -> bind_mapper (n + 1) t)
      in
      bind_mapper 1 ctx
    )
    (Array.length brs)
    0

let proj_head pn r c =
  if Projection.unfolded pn
  then
    ( match kind c with
      (* Construct impossible because `proj {||}` and `proj {| proj := |}` are not a thing *)
      | Construct _ -> anomaly (str "Projection on an empty struct.")
      | CoFix cf -> Some (mkProj (pn, r, contract_cofix cf))
      | App (head, args) ->
        ( match kind head with
          | Construct _ -> Some (proj_red pn args)
          | CoFix cf -> Some (mkProj (pn, r, mkApp (contract_cofix cf, args)))
          | _ -> None
        )
      | _ -> None
    )
  else Some (mkProj (Projection.unfold pn, r, c))

(* ZIPPERS

(* Evar context zipper *)
module TermSListZipper = struct
  open SList

  type t =
  { mutable left: constr SList.t;
    mutable right: constr SList.t;
    (* keep old term and slist to preserve sharing *)
    mutable cache: constr option
  }
  type t_const =
  { cleft: constr SList.t;
    cright: constr SList.t
  }

  let make =
    let rec aux acc = function
    | Nil -> None
    | Cons (h, t) -> Some ({left = acc; right = t; cache = Some h}, h)
    | Default (n, t) -> aux (SList.defaultn n acc) t
    in aux empty

  let to_const {left; right; _} = {cleft = left; cright = right}

  let update_cache cache old knew =
    Option.bind cache (fun h -> if h == old then Some knew else None)

  let update s old l r knew =
    s.left <- l;
    s.right <- r;
    s.cache <- update_cache s.cache old knew

  let rec rev_append acc = function
  | Nil -> acc
  | Cons (h, t) -> rev_append (cons h acc) t
  | Default (n, t) -> rev_append (defaultn n acc) t

  let unzip {left; right; cache} t =
    match cache with
    | Some h when t == h -> None
    | _ -> Some (rev_append (SList.cons t right) left)

  let rec unzip_one acc = function
  | SList.Nil -> Result.Error acc
  | SList.Cons (h, t) -> Result.Ok (t, h, acc)
  | SList.Default (n, t) -> unzip_one (SList.defaultn n acc) t

  let move s t =
    let use_cache sl =
      Result.Error
        ( match s.cache with
          | Some h when t == h -> None
          | _ -> Some sl
        )
    in function
    | Either.Left () ->
      ( match unzip_one (cons t s.right) s.left with
        | Result.Ok (left, h, right) -> update s t left right h; Result.Ok h
        | Result.Error sl -> use_cache sl
      )
    | Either.Right () ->
      match unzip_one (cons t s.left) s.right with
      | Result.Ok (right, h, left) -> update s t left right h; Result.Ok h
      | Result.Error sl -> use_cache sl

  let _ = make, to_const, unzip, move
end

module TermZipper = struct
  type 't tern_pos = TLeft of 't | TMiddle | TRight
  type case_pos = CMatchee | CParams of int | CArity | CBranch of int

  (* zipper keeping old term to preserve sharing *)
  type context =
  | CEvar   of Evar.t (* Looking at evar ctx zipper *)
  | CEvarC  of TermSListZipper.t (* Looking at part of the evar ctx *)
  | CCast   of constr * cast_kind * types (* Never touch cast type *)
  | CProd   of (unit, unit) Either.t * Name.t binder_annot * types * types
  | CLambda of (unit, unit) Either.t * Name.t binder_annot * types * constr
  | CLetIn  of unit tern_pos * Name.t binder_annot * constr * types * constr
  | CApp    of (unit, int) Either.t * constr * constr array
  | CCase   of case_pos * case
  | CFix    of (int, int) Either.t * fixpoint
  | CCoFix  of (int, int) Either.t * cofixpoint
  | CProj   of Projection.t * Sorts.relevance * constr
  | CArray  of int tern_pos * UVars.Instance.t * constr array * constr * types

  (* Aggressive cache: All superterms are trashed as soon as they are invalidated. *)
  type t =
  { mutable ctx: context list;
    mutable cache: constr list
  }
  type t_const =
  { cctx: context list
  }

  let make = {ctx = []; cache = []}

(* TODO LATER: seems very complicated
  let make_evar evm ctx (ev, sl) = Evd.existential_opt_value0 evm (ev, sl)
*)

  let to_const {ctx; _} = {cctx = ctx}

  let pop_cache tz =
    match tz.cache with
    | [] -> None
    | h :: t -> tz.cache <- t; Some h

  let unzip_evar ev z t =
    Option.map (fun sl -> mkEvar (ev, sl)) (TermSListZipper.unzip z t)

(* Unused, may be useful
  let unzip_cast c k t x = if x == c then None else Some (mkCast (x, k, t))

  let unzip_prod na k t x = function
  | Either.Left () -> if x == k then None else Some (mkProd (na, x, t))
  | Either.Right () -> if x == t then None else Some (mkProd (na, k, x))

  let unzip_lambda na t c x = function
  | Either.Left () -> if x == t then None else Some (mkLambda (na, x, c))
  | Either.Right () -> if x == c then None else Some (mkLambda (na, t, x))

  let unzip_letin na b t c x = function
  | TLeft () -> if x == t then None else Some (mkLetIn (na, b, x, c))
  | TMiddle -> if x == b then None else Some (mkLetIn (na, x, t, c))
  | TRight -> if x == c then None else Some (mkLetIn (na, b, t, x))

  let unzip_app head args x = function
  | Either.Left () -> if x == head then None else Some (mkApp (x, args))
  | Either.Right n ->
    if x == args.(n) then None else Some (mkApp (head, array_with args n x))

  let unzip_case (ci, u, pms, p, iv, c, brs) x = function
  | CMatchee ->
    if x == c then None else Some (mkCase (ci, u, pms, p, iv, x, brs))
  | CParams n ->
    if x == pms.(n) then None
    else Some (mkCase (ci, u, array_with pms n x, p, iv, c, brs))
  | CArity ->
    let p, r = p in
    if x == snd p then None
    else Some (mkCase (ci, u, pms, ((fst p, x), r), iv, c, brs))
  | CBranch n ->
    let na, b = brs.(n) in
    if x == b then None
    else Some (mkCase (ci, u, pms, p, iv, c, array_with brs n (na, x)))

  let unzip_fix (si, (nas, tys, bds)) x = function
  | Either.Left n ->
    if x == tys.(n) then None
    else Some (mkFix (si, (nas, array_with tys n x, bds)))
  | Either.Right n ->
    if x == bds.(n) then None
    else Some (mkFix (si, (nas, tys, array_with bds n x)))

  let unzip_cofix (ri, (nas, tys, bds)) x = function
  | Either.Left n ->
    if x == tys.(n) then None
    else Some (mkCoFix (ri, (nas, array_with tys n x, bds)))
  | Either.Right n ->
    if x == bds.(n) then None
    else Some (mkCoFix (ri, (nas, tys, array_with bds n x)))

  let unzip_proj pn r c x = if x == c then None else Some (mkProj (pn, r, x))

  let unzip_array u ts def ty x = function
  | TLeft n ->
    if x == ts.(n) then None else Some (mkArray (u, array_with ts n x, def, ty))
  | TMiddle -> if x == def then None else Some (mkArray (u, ts, x, ty))
  | TRight -> if x == ty then None else Some (mkArray (u, ts, def, x))

  let unzip_one_cache x = function
  | CEvar _ | CEvarC _ -> anomaly (str "Evar context must be unzipped separately.")
  | CCast (c, k, t) -> unzip_cast c k t x
  | CProd (p, na, k, t) -> unzip_prod na k t x p
  | CLambda (p, na, t, c) -> unzip_lambda na t c x p
  | CLetIn (p, na, b, t, c) -> unzip_letin na b t c x p
  | CApp (p, head, args) -> unzip_app head args x p
  | CCase (p, case) -> unzip_case case x p
  | CFix (p, fix) -> unzip_fix fix x p
  | CCoFix (p, cofix) -> unzip_cofix cofix x p
  | CProj (pn, r, c) -> unzip_proj pn r c x
  | CArray (p, u, ts, def, ty) -> unzip_array u ts def ty x p
*)

  let unzip_one_no_cache x = function
  | CEvar _ | CEvarC _ -> anomaly (str "Ill formed evar context.")
  | CCast (c, k, t) -> mkCast (x, k, t)
  | CProd (p, na, k, t) ->
    ( match p with
    | Either.Left () -> mkProd (na, x, t)
    | Either.Right () -> mkProd (na, k, x)
    )
  | CLambda (p, na, t, c) ->
    ( match p with
    | Either.Left () -> mkLambda (na, x, c)
    | Either.Right () -> mkLambda (na, t, x)
    )
  | CLetIn (p, na, b, t, c) ->
    ( match p with
    | TLeft () -> mkLetIn (na, b, x, c)
    | TMiddle -> mkLetIn (na, x, t, c)
    | TRight -> mkLetIn (na, b, t, x)
    )
  | CApp (p, head, args) ->
    ( match p with
    | Either.Left () -> mkApp (x, args)
    | Either.Right n -> mkApp (head, array_with args n x)
    )
  | CCase (pos, (ci, u, pms, p, iv, c, brs)) ->
    ( match pos with
    | CMatchee -> mkCase (ci, u, pms, p, iv, x, brs)
    | CParams n -> mkCase (ci, u, array_with pms n x, p, iv, c, brs)
    | CArity -> let p, r = p in mkCase (ci, u, pms, ((fst p, x), r), iv, c, brs)
    | CBranch n ->
      let na, b = brs.(n) in
      mkCase (ci, u, pms, p, iv, c, array_with brs n (na, x))
    )
  | CFix (p, (si, (nas, tys, bds))) ->
    ( match p with
    | Either.Left n -> mkFix (si, (nas, array_with tys n x, bds))
    | Either.Right n -> mkFix (si, (nas, tys, array_with bds n x))
    )
  | CCoFix (p, (ri, (nas, tys, bds))) ->
    ( match p with
    | Either.Left n -> mkCoFix (ri, (nas, array_with tys n x, bds))
    | Either.Right n -> mkCoFix (ri, (nas, tys, array_with bds n x))
    )
  | CProj (pn, r, c) -> mkProj (pn, r, x)
  | CArray (p, u, ts, def, ty) ->
    match p with
    | TLeft n -> mkArray (u, array_with ts n x, def, ty)
    | TMiddle -> mkArray (u, ts, x, ty)
    | TRight -> mkArray (u, ts, def, x)

  let unzip {ctx; cache} t =
    let rec aux_no_cache x = function
    | [] -> x
    | CEvarC z :: CEvar ev :: t ->
      aux_no_cache
        (mkEvar (ev, TermSListZipper.(rev_append (SList.cons x z.right) z.left)))
        t
    | h :: t -> aux_no_cache (unzip_one_no_cache x h) t
    in
    let rec aux x = function
    | CEvarC _ :: CEvar _ :: ctx, c :: cache
    | _ :: ctx, c :: cache -> aux c (ctx, cache)
    | ctx, [] -> aux_no_cache x ctx
    | _ -> anomaly (str "Ill formed context.")
    in aux t (ctx, cache)

  let move_up_evarc tz cz t =
    match tz.ctx with
    | CEvar ev :: ctx ->
      tz.ctx <- ctx;
      first_step [
        (fun _ -> pop_cache tz);
        (fun _ -> unzip_evar ev cz t);
        fun _ -> anomaly (str "Inconsistent cache.")
      ]
    | [] -> None
    | _ -> anomaly (str "Ill formed context.")

  let unzip_evarc tz cz t =
    match tz.ctx with
    | CEvar ev :: ctx ->
      unzip tz (
        force' "Inconsistent cache." (
          or_else (pop_cache tz) (fun _ -> unzip_evar ev cz t)
        )
      )
    | _ -> anomaly (str "Ill formed context.")

  type unzip_res = Fail | Term of constr | EvarContext of TermSListZipper.t
  let move_up tz t =
    match tz.ctx with
    | [] -> Fail
    | CEvar _ :: _ -> anomaly (str "Evar context must be unzipped with move_up_evarc.")
    | CEvarC cz :: ctx -> tz.ctx <- ctx; EvarContext cz
    | h :: ctx ->
      tz.ctx <- ctx;
      Term
        ( match pop_cache tz with
          | Some t -> t
          | None -> unzip_one_no_cache t h
        )

  let zip_evar tz ev sl = tz.ctx <- CEvar ev :: tz.ctx; TermSListZipper.make sl

  let zip_evarc tz cz t = tz.ctx <- CEvarC cz :: tz.ctx; t

  let zip_cast tz c k t = tz.ctx <- CCast (c, k, t) :: tz.ctx; c

  let zip_prod tz d na b c =
    tz.ctx <- CProd (d, na, b, c) :: tz.ctx;
    match d with
    | Either.Left () -> b
    | Either.Right () -> c

  let zip_lambda tz d na t c =
    tz.ctx <- CLambda (d, na, t, c) :: tz.ctx;
    match d with
    | Either.Left () -> t
    | Either.Right () -> c

  let zip_letin tz d na b u c =
    tz.ctx <- CLetIn (d, na, b, u, c) :: tz.ctx;
    match d with
    | TLeft () -> u
    | TMiddle -> b
    | TRight -> c

  let zip_app tz d head args =
    tz.ctx <- CApp (d, head, args) :: tz.ctx;
    match d with
    | Either.Left () -> Some head
    | Either.Right k when 0 <= k && k < Array.length args ->
      Some (Array.unsafe_get args k)
    | _ -> None

  let zip_case tz d (_, _, pms, ((_, p), _), _, c, brs as case) =
    tz.ctx <- CCase (d, case) :: tz.ctx;
    match d with
    | CMatchee -> Some c
    | CParams k when 0 <= k && k < Array.length pms ->
      Some (Array.unsafe_get pms k)
    | CArity -> Some p
    | CBranch k when 0 <= k && k < Array.length brs ->
      Some (snd (Array.unsafe_get brs k))
    | _ -> None

  let zip_fix tz d (_, (_, tys, bds) as f) =
    tz.ctx <- CFix (d, f) :: tz.ctx;
    match d with
    | Either.Left k when 0 <= k && k < Array.length tys ->
      Some (Array.unsafe_get tys k)
    | Either.Right k when 0 <= k && k < Array.length bds ->
      Some (Array.unsafe_get bds k)
    | _ -> None

  let zip_cofix tz d (_, (_, tys, bds) as cf) =
    tz.ctx <- CCoFix (d, cf) :: tz.ctx;
    match d with
    | Either.Left k when 0 <= k && k < Array.length tys ->
      Some (Array.unsafe_get tys k)
    | Either.Right k when 0 <= k && k < Array.length bds ->
      Some (Array.unsafe_get bds k)
    | _ -> None

  let zip_proj tz pn r c = tz.ctx <- CProj (pn, r, c) :: tz.ctx; c

  let zip_array tz d u ts def ty =
    tz.ctx <- CArray (d, u, ts, def, ty) :: tz.ctx;
    match d with
    | TLeft k when 0 <= k && k < Array.length ts ->
      Some (Array.unsafe_get ts k)
    | TMiddle -> Some def
    | TRight -> Some ty
    | _ -> None

  let _ =
    TLeft (),
    TMiddle,
    TRight,
    CMatchee,
    CParams 0,
    CArity,
    CBranch 0,
    make,
    (* make_evar, *)
    to_const,
    unzip,
    move_up_evarc,
    unzip_evarc,
    move_up,
    zip_evar,
    zip_evarc,
    zip_cast,
    zip_prod,
    zip_lambda,
    zip_letin,
    zip_app,
    zip_case,
    zip_fix,
    zip_cofix,
    zip_proj,
    zip_array
end

(* TODO HERE: rule reduction, check cclosure?
  Environ.lookup_rewrite_rules kn env -> rewrite_rule list
  check how they are applied in Reductionops.apply_rule
  (CClosure.match_elim is too complicated)

  write mutual recursive functions for PE PH PA?
*)

module TermReduction = struct
  open TermZipper
  type red_case = RIota | RZeta of int * int
  (* rewrite rule: constant.t + number ? *)

  (* TODO/LATER?
  let reduce_rel tz n =
    let rec aux n = function
    | [] -> None
    | (_, h) :: t ->
      match h with
      | CProd (Right (), _, _, _) -> if n > 0 then aux (n - 1) t else None
      | CLetIn (TRight, _, c, _, _) -> if n > 0 then aux (n - 1) t else Some c
      | CFix (Either.Right _, (_, (_, _, bds))) ->
        let k = n - Array.length bds in
        if k >= 0 then aux k t else Some bds.(n)
      | CCoFix (Either.Right _, (_, (_, _, bds))) ->
        let k = n - Array.length bds in
        if k >= 0 then aux k t else Some bds.(n)
      | CLambda (Right (), _, _, _) ->
        if n > 0 then aux (n - 1) t
        else ... (* TODO *)
      | CCase (*case_pos * case*) -> (* TODO *)
      | _ -> aux n t
    in
    aux n tz.ctx
    (* Option.bind (List.nth_opt tz.rel_ctx n)
      Context.Rel.Declaration.(function LocalDef (_, c, _) -> Some c | LocalAssum _ -> None)
    *)
  *)

  let reduce_helper tz =
    Option.map
      ( fun (ctx, t) ->
        tz.cache <- [];
        tz.ctx <- ctx;
        t
      )

  let reduce_lambda tz t =
    let (*rec*) aux t = function
    | CApp (Either.Left (), _, args) :: ctx ->
      Some (ctx, beta_red t args)
    | _ -> None (* LATER: traverse letin and other stuff like it *)
    in reduce_helper tz (aux t tz.ctx)

  let reduce_app tz env head args =
    let r =
      match kind head with
      | Lambda (_, _, c) -> Some (beta_red c args)
      | Fix f -> fix_red env f args
      | Const (c, u) -> (* TODO: rule reduction *)
        Option.bind (get_primitive env c)
          (fun op -> Result.to_option (delta_prim_red env (op, u) args))
      | Construct ((_, c), _) ->
        ( match tz.ctx with
          | CCase (CMatchee, (ci, u, _, _, _, _, brs)) :: ctx ->
            tz.ctx <- ctx;
            Some (match_red env ci u c brs args)
          | CProj (pn, _, _) :: ctx -> tz.ctx <- ctx; Some (proj_red pn args)
          | _ -> None
        )
      | CoFix cf ->
        ( match tz.ctx with
          | (CCase _ | CProj _) :: _ -> Some (contract_cofix cf)
          | _ -> None
        )
      | _ -> None
    in if Option.has_some r then tz.cache <- []; r

  (*
  let rule_red env evm kn u tz =
    let open Declarations in
    let rec aux = function
    | [] -> None
    | { lhs_pat = (pu, elims); nvars; rhs } :: t ->
      let psubst = Partial_subst.make nvars in
      match UVars.Instance.pattern_match pu (EInstance.kind evm u) psubst with
      | None -> aux t
      | Some psubst ->
        ...
        let subst, qsubst, usubst = Partial_subst.to_arrays psubst in
        let usubst = UVars.Instance.of_array (qsubst, usubst) in
        ...
        return new headterm
      
    in aux (lookup_rewrite_rules kn env)
  *)

  let reduce_const tz env (kn, u) =
    let r =
      match (lookup_constant kn env).const_body with
      | Def x -> Some (subst_instance_constr u x)
      | Primitive p ->
        ( match tz.ctx with
          | CApp (Either.Left (), _, args) :: ctx ->
            ( match delta_prim_red env (p, u) args with
              | Ok v -> tz.ctx <- ctx; Some v
              | Error _ -> None
            )
          | _ -> None
        )
      (* | Symbol b ->
        match rule_red env evm kn tz with
        | Some ... -> ...
        | None ->
          if b
          then ...
          else ...
      *)
      | Symbol b when b -> (* TODO: rule reduction (remove 'when b') *)
        ( match tz.ctx with
          | CApp (Either.Right k, head, args) :: ctx ->
            ( match kind head with
              | Fix ((reci, i), _ as f) when reci.(i) = k ->
                tz.ctx <- ctx; Some (mkApp (contract_fix f, args))
              | _ -> None
            )
          | _ -> None
        )
      | _ -> None
    in if Option.has_some r then tz.cache <- []; r

  let reduce_contruct tz env c =
    reduce_helper tz (
      match tz.ctx with
      | CCase (CMatchee, (ci, u, _, _, _, _, brs)) :: ctx ->
        Some (ctx, match_red env ci u c brs [||])
      | CApp (Either.Left (), _, args) :: CCase (CMatchee, (ci, u, _, _, _, _, brs)) :: ctx ->
        Some (ctx, match_red env ci u c brs args)
      | CApp (Either.Left (), _, args) :: CProj (pn, _, _) :: ctx ->
        Some (ctx, proj_red pn args)
      | CApp (Either.Right k, head, args) :: ctx ->
        ( match kind head with
          | Fix ((reci, i), _ as f) when reci.(i) = k ->
            Some (ctx, mkApp (contract_fix f, args))
          | _ -> None
        )
      | _ -> None
    )

  let reduce_case tz env (ci, u, pms, p, iv, c, brs) rd =
    let r =
      match rd with
      | RIota -> iota_match_head env ci u pms p iv c brs
      | RZeta (brn, lbn) ->
        let ind, tyi = ci.ci_ind in
        let oib = (lookup_mind ind env).mind_packets.(tyi) in
        let bindings = CList.firstn (oib.mind_consnrealdecls.(brn)) (fst oib.mind_nf_lc.(brn)) in
        Some (zeta_match_step brn (bind_to_index lbn bindings) (env, ci, u, pms, p, iv, c, brs))
    in if Option.has_some r then tz.cache <- []; r

  let reduce_fix tz env f =
    match tz.ctx with
    | CApp (Either.Left (), _, args) :: ctx ->
      let r = fix_red env f args in
      if Option.has_some r
      then begin
        tz.ctx <- ctx;
        tz.cache <- []
      end;
      r
    | _ -> None

  let reduce_cofix tz cf =
    match tz.ctx with
    | CApp (Either.Left (), _, _) :: CCase (CMatchee, _) :: _
    | CCase (CMatchee, _) :: _ ->
      tz.cache <- []; Some (contract_cofix cf)
    | _ -> None

  let _ =
    RIota,
    RZeta (0, 0),
    reduce_lambda,
    reduce_app,
    reduce_const,
    reduce_contruct,
    reduce_case,
    reduce_fix,
    reduce_cofix
end

let _ = TermReduction.RIota

module TermVisitor = struct
  type ('r, 'c) control = Stop of 'r | Act of 'c | Up
  type ('m, 'r) action_kind = Down of 'm | Reduce of 'r
  type action =
  | ARel of red_rel
  | AVar
  | AEvar of (unit, unit) action_kind
  | ACast of (unit, unit) action_kind
  | AProd of (unit, unit) Either.t
  | ALambda of ((unit, unit) Either.t, unit) action_kind
  | ALetIn of (unit tern_pos, unit) action_kind
  | AApp of ((unit, int) Either.t, unit) action_kind
  | AConst of unit
  | AConstruct of unit
  | ACase of (case_pos, red_case) action_kind
  | AFix of ((int, int) Either.t, unit) action_kind
  | ACofix of ((int, int) Either.t, unit) action_kind
  | AProj of (unit, unit) action_kind
  | AArray of int tern_pos

  class type ['t] t = object
    method term: TermZipper.t -> constr -> ('t, action) control
    method evarc: TermZipper.t -> TermSListZipper.t -> constr -> ('t, unit tern_pos) control
  end

  (* TODO HERE: finish this maybe *)
  let visit env evm cb t =
    let tz = TermZipper.make t in
    let rec aux_term t =
      match cb#term tz t of
      | Stop v -> v, TermZipper.unzip tz t
      | Up ->
        ( match TermZipper.move_up tz t with
          | Either.Left t -> aux_term t
          | Either.Right cz -> aux_evarc cz t
        )
      | Act a ->
        (* TODO: use reductions from TermReduction
        match a, kind t with
        | ARel r, Rel i -> (* TODO *)
        | AVar, Var id -> aux_term (delta_var_red env id)
        | AEvar a, Evar (ev, sl) ->
          ( match a with
            | Move () ->
              tz.ctx <- (t, CEvar ev) :: tz.ctx;
              (* TODO *)
              aux_evarc (TermSListZipper.make sl)
            | Reduce () -> aux_term (Evd.existential_opt_value0 evm ev)
          )
        | ACast a, Cast (c, k, ct) ->
          ( match a with
            | Move () -> tz.ctx <- (t, CCast c k ct) :: tz.ctx; aux_term c
            | Reduce () -> aux_term c
          )
        | AProd d, Prod (na, t, b) -> (* TODO *) 
        | ALambda a, Lambda (na, t, b) ->
          ( match a with
            | Move
            | Reduce
          )
        | ALetIn a, LetIn (na, b, u, c) ->
          ( match a with
            | Move
            | Reduce () -> aux_term (subst1 b c)
          )
        | AApp a, App (h, al) ->
          ( match a with
            | Move
            | Reduce
          )
        | AConst r, Const sp ->
        | AConstruct r, Construct c ->
        | ACase a, Case (ci, u, pms, p, iv, b, bl) ->
          ( match a with
            | Move
            | Reduce
          )
        | AFix a, Fix f ->
          ( match a with
            | Move
            | Reduce () -> fix_red env f ...
          )
        | ACoFix a, CoFix cf ->
          ( match a with
            | Move
            | Reduce () -> contract_cofix
          )
        | AProj a, Proj (p, r, b) ->
          ( match a with
            | Move () -> aux_term b
            | Reduce () -> aux_term (proj_head)
          )
        | AArray d, Array (u, t, def, ty) ->
        | _ -> anomaly (str "Not an anomaly? rather a dev error? depends on the reduction fonction provided")
        *)
    and aux_evarc cz t =
      match cb#evarc tz cz t of
      | Stop v -> v, TermZipper.unzip_evarc tz cz t
      | Up -> aux_term (TermZipper.move_up_evarc tz cz t)
      | Act a ->
        let move d =
          match TermSListZipper.move cz t d with
          | Result.Error _ -> anomaly (str "Forbidden zipper movement.")
          | Result.Ok t -> aux_evarc cz t
        in
        match a with
        | TLeft () -> move (Either.Left ())
        | TRight -> move (Either.Right ())
        | TMiddle -> tz.ctx <- EvarC cz :: tz.ctx; aux_term t
    in aux_term t
end
*)

(* TREE WALKER *)

let map_constr_with_binders_left_to_right env g f acc c =
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> c
  | Cast (b, k, t) ->
    let b' = f acc b in
    if b' == b then c else mkCast (b', k, t)
  | Prod (na, t, b) ->
    let t' = f acc t in
    let b' = f (g (LocalAssum (na,t)) acc) b in
    if t' == t && b' == b then c else mkProd (na, t', b')
  | Lambda (na, t, b) ->
    let t' = f acc t in
    let b' = f (g (LocalAssum (na,t)) acc) b in
    if t' == t && b' == b then c else mkLambda (na, t', b')
  | LetIn (na, bo, t, b) ->
    let t' = f acc t in (* I swapped the first two, I believe I am correct and the other version is wrong *)
    let bo' = f acc bo in
    let b' = f (g (LocalDef (na,bo,t)) acc) b in
    if bo' == bo && t' == t && b' == b then c else mkLetIn (na, bo', t', b')
  | App (h, al) ->
    let h' = f acc h in
    let al' = CArray.map_left (f acc) al in
    if h == h' && Array.for_all2 (==) al al' then c else mkApp (h', al')
  | Proj (p, r, b) ->
    let b' = f acc b in
    if b' == b then c else mkProj (p, r, b')
  | Evar (ev, ctx) ->
    let ctx' = SList.Smart.map (fun c -> f acc c) ctx in
    if ctx' == ctx then c else mkEvar (ev, ctx')
  | Case (ci, u, pms, (p, r), iv, b, bl) ->
	let mind = lookup_mind_specif env ci.ci_ind in
    let p0, bl0 = expand_case_contexts mind (ci.ci_ind, u) pms (fst p) bl in
    let f_ctx (nas, c as r) ctx =
      let c' = f (List.fold_right g ctx acc) c in
      if c' == c then r else (nas, c')
    in
    let b' = f acc b in
    let pms' = CArray.map_left (f acc) pms in
    let p' = f_ctx p p0 in
    let bl' = CArray.map_left (fun (c, c0) -> f_ctx c c0) (Array.map2 (fun x y -> (x, y)) bl bl0) in
    if b' == b && pms' == pms && p' == p && bl' == bl then c
    else mkCase (ci, u, pms', (p', r), iv, b', bl')
  | Fix (ln, (lna, tl, bl)) ->
    let ctxt = CArray.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna tl in
    let acc' = Array.fold_left (fun e assum -> g assum e) acc ctxt in
    let tl', bl' = map_left2 (f acc) (f acc') tl bl in
    if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl' then c
    else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln, (lna, tl, bl)) ->
    let ctxt = CArray.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna tl in
    let acc' = Array.fold_left (fun e assum -> g assum e) acc ctxt in
    let tl', bl' = map_left2 (f acc) (f acc') tl bl in
    if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl' then c
    else mkCoFix (ln, (lna, tl', bl'))
  | Array(u, t, def, ty) ->
    let t' = CArray.map_left (f acc) t in
    let def' = f acc def in
    let ty' = f acc ty in
    if def' == def && t' == t && ty' == ty then c
    else mkArray (u, t', def', ty')

(* based on e_contextually, prep does matching and pre-processing, f does the reduction *)
let reduce_with_context occs prep f env t =
  let count = ref (
    Locusops.initialize_occurrence_counter occs,
    match occs with Locus.AtLeastOneOccurrence -> false | _ -> true
  ) in
  let rec traverse nested env t =
    if Locusops.occurrences_done (fst !count) then (* Shortcut *) t else
    let cont nested = map_constr_with_binders_left_to_right env push_rel (traverse nested) env t in
    match prep env t with
    | None -> cont nested
    | Some payload ->
      let ok, count' = Locusops.update_occurrence_counter (fst !count) in
      count := count', snd !count || ok;
      if not ok then cont nested else
      match nested with
      | Some n ->
        user_err
          ( str "The subterm at occurrence "
            ++ int n
            ++ str " overlaps with the subterm at occurrence "
            ++ int (Locusops.current_occurrence (fst !count))
            ++ str "."
          )
      | None -> (* Skip inner occurrences for stable counting of occurrences *)
        if Locusops.more_specific_occurrences (fst !count)
        then ignore (cont (Some (Locusops.current_occurrence (fst !count))));
        f payload
  in
  let t = traverse None env t in
  Locusops.check_used_occurrences (fst !count);
  if snd !count then t else user_err (str "No occurence to rewrite.")


(* REDUCTION TACTICS *)

type 'e eta_kind =
| EBoth
| ELambda of Id.t option
| EPrim of 'e option

let match_binder na = function
| None -> true
| Some b ->
  match Context.(na.binder_name) with
  | Name na when Id.equal na b -> true
  | _ -> false

let process_tycons head tyc =
  match kind head with
  | Construct ((ind, n as c), _) ->
    ( match tyc with
      | None -> Some c
      | Some (ind', None) when eq_ind_chk ind ind' -> Some c
      | Some (ind', Some n') when eq_ind_chk ind ind' && n = n' -> Some c
      | _ -> None
    )
  | _ -> None

let cast_prep _ c =
  match kind c with
  | Cast (ct, _, _) -> Some ct
  | _ -> None

let cast_step c = c

let beta_prep b env c =
  try
    let head, args = destApp c in
    let na, _, c = destLambda head in
    if match_binder na b then Some (c, args) else None
  with DestKO -> None

let beta_step (head, args) = beta_red head args

let zeta_prep b _ c =
  match kind c with
  | LetIn (na, p, _, c) -> if match_binder na b then Some (p, c) else None
  | _ -> None

let zeta_step (b, c) = subst1 b c

let zeta_match_prep ty brn n env c =
  match kind c with
  | Case (ci, u, pms, bi, iv, c, brs) when eq_ind_chk ty ci.ci_ind ->
    Some (env, ci, u, pms, bi, iv, c, brs)
  | _ -> None

type delta_kind =
| DeltaVar of variable
| DeltaConst of (constr, const_evaluation_result) result
| DeltaPrim of (CPrimitives.t * UVars.Instance.t) * constr array
| DeltaProj of Projection.t * Sorts.relevance * constr

(* reduction in prep to avoid matching a primitive *)
let delta_const_accept_prim env c =
  match delta_const_red env c with
  | Error (IsPrimitive _) -> None
  | x -> Some (env, DeltaConst x)

(* primitive resolution in prep to avoid counting constants twice *)
let delta_prim_reject_const env c u args =
  Option.map (fun op -> env, DeltaPrim ((op, u), args)) (get_primitive env c)

let delta_prep e env c =
  let open Evaluable in
  match kind c, e with
  | Var id, Some (EvalVarRef i) when Id.equal id i -> Some (env, DeltaVar id)
  | Var id, None -> Some (env, DeltaVar id)
  | Const (c, u), Some (EvalConstRef cr) when QConstant.equal env cr c ->
    delta_const_accept_prim env (c, u)
  | Const (c, u), None -> delta_const_accept_prim env (c, u)
  | Proj (pn, _, _), _ when Projection.unfolded pn -> None
  | Proj (pn, r, c), Some (EvalProjectionRef p)
    when QProjection.Repr.equal env p (Projection.repr pn) ->
    Some (env, DeltaProj (pn, r, c))
  | Proj (pn, r, c), None -> Some (env, DeltaProj (pn, r, c))
  | App (head, args), Some (EvalConstRef cr) ->
    ( match kind head with
      | Const (c, u) when QConstant.equal env cr c ->
        delta_prim_reject_const env c u args
      | _ -> None
    )
  | App (head, args), None ->
    ( match kind head with
      | Const (c, u) -> delta_prim_reject_const env c u args
      | _ -> None
    )
  | _ -> None

let delta_step = function
| env, DeltaVar id -> force "Variable has no unfoldable definition." (delta_var_red env id)
| _, DeltaConst (Ok c) -> c
| _, DeltaConst (Error Opaque) -> user_err (str "Constant is opaque.")
| _, DeltaConst (Error NoBody) -> user_err (str "Constant has no definition.")
| _, DeltaConst (Error (HasRules _)) ->
  user_err (str "Constant is a symbol with custom rewrite rules.")
| _, DeltaConst (Error (IsPrimitive _)) -> assert false (* don't try to unfold unapplied primitive *)
| env, DeltaPrim (p, args) ->
  ( match delta_prim_red env p args with
    | Ok x -> x
    | Error x -> user_err (str ("Could not reduce primitive: " ^ x ^ "."))
  )
| env, DeltaProj (pn, r, c) -> mkProj (Projection.unfold pn, r, c)

let eta_prep ek env c =
  let process_prim args ind =
    match (lookup_mind (fst ind) env).mind_record with
    | PrimRecord _ -> Some (env, Either.Right (ind, args))
    | _ -> None
  in
  match ek, kind c with
  | EBoth, Lambda (_, t, c) -> Some (env, Either.Left (t, c))
  | ELambda b, Lambda (na, t, c) when match_binder na b ->
    Some (env, Either.Left (t, c))
  | EBoth, App (head, args) ->
    ( match kind head with
      | Construct ((ind, _), _) -> process_prim args ind
      | _ -> None
    )
  | EPrim tyc, App (head, args) ->
    Option.bind (process_tycons head tyc) (fun (ind, _) -> process_prim args ind)
  | _ -> None

let eta_step evm = function
| env, Either.Left (t, c) ->
  ( match eta_lambda_red evm env t c with
    | Ok x -> x
    | Error m -> user_err (str m)
  )
| env, Either.Right (ind, args) ->
  ( match eta_prim_red env ind args with
    | Ok x -> x
    | Error x -> user_err (str x)
  )

let evar_prep _ c =
  match kind c with
  | Evar ev -> Some ev
  | _ -> None

let evar_step evm ev =
  force "Evar has no unfoldable definition." (Evd.existential_opt_value0 evm ev)

let fix_prime_prep b _ c =
  match kind c with
  | Fix ((_, i), (nas, _, _) as f) -> if match_binder nas.(i) b then Some f else None
  | _ -> None

let fix_prep b env c =
  try
    let head, args = destApp c in
    let (_, i), (nas, _, _) as f = destFix head in
     if match_binder nas.(i) b then Some (env, f, args) else None
  with DestKO -> None

let fix_step (env, f, args) =
  force "Fixpoint is not reducible." (fix_red env f args)

let cofix_prime_prep b _ c =
  match kind c with
  | CoFix (i, (nas, _, _) as cf) -> if match_binder nas.(i) b then Some cf else None
  | _ -> None

let cofix_prep b _ c =
  let extract_cofix c =
    Option.bind
      ( match kind c with
        | CoFix cf -> Some (cf, [||])
        | App (head, args) ->
          ( match kind head with
            | CoFix cf -> Some (cf, args)
            | _ -> None
          )
        | _ -> None
      )
      ( fun (i, (nas, _, _) as cf, args) ->
        if match_binder nas.(i) b then Some (cf, args) else None
      )
  in
  match kind c with
  | Proj (pn, r, c) ->
    Option.map (fun (cf, args) -> Either.Left (pn, r, cf, args)) (extract_cofix c)
  | Case (ci, u, pms, bi, iv, c, brs) ->
    Option.map (fun (cf, args) -> Either.Right (ci, u, pms, bi, iv, cf, args, brs))
      (extract_cofix c)
  | _ -> None

let cofix_step = function
| Either.Left (pn, r, cf, args) -> mkProj (pn, r, mkApp (contract_cofix cf, args))
| Either.Right (ci, u, pms, bi, iv, cf, args, brs) ->
  mkCase (ci, u, pms, bi, iv, mkApp (contract_cofix cf, args), brs)

type match_kind =
| MatchProj of Projection.t * constr array
| MatchCase of env * case_info * UVars.Instance.t * int * case_branch array * constr array
| MatchUIP of env * case_info * UVars.Instance.t * constr array * constr array * case_branch array

let match_prep tyc env c =
  match kind c with
  | Proj (pn, r, c) when Projection.unfolded pn ->
    ( match kind c with
      (* Construct impossible because primitive have at least one projection *)
      | App (head, args) ->
        if Option.has_some (process_tycons head tyc)
        then Some (MatchProj (pn, args))
        else None
      | _ -> None
    )
  | Case (ci, u, pms, bi, iv, c, brs) ->
    first_step [
      ( fun _ ->
        Option.map (fun (_, c) -> MatchCase (env, ci, u, c, brs, [||]))
          (process_tycons c tyc)
      );
      ( fun _ ->
        match kind c with
        | App (head, args) ->
          Option.map (fun (_, c) -> MatchCase (env, ci, u, c, brs, args))
            (process_tycons head tyc)
        | _ -> None
      );
      ( fun _ ->
        match iv with
        | CaseInvert {indices} ->
          Some (MatchUIP (env, ci, u, pms, indices, brs))
        | _ -> None
      )
    ]
  | _ -> None

let match_step = function
| MatchProj (pn, args) -> proj_red pn args
| MatchCase (env, ci, u, c, brs, args) -> match_red env ci u c brs args
| MatchUIP (env, ci, u, pms, indices, brs) ->
  force "Matched type with UIP has wrong indices." (match_uip_red env ci u pms indices brs)

let root_step evm env c =
  match kind c with
  | Var id -> delta_var_red env id
  | Evar ev -> Evd.existential_opt_value0 evm ev
  | Cast (ct, _, _) -> Some ct
  | LetIn (na, b, u, c) -> Some (subst1 b c)
  | App (head, args) -> app_head env head args
  | Const sp -> const_head env sp
  | Case (ci, u, pms, bi, iv, c, brs) ->
    first_step [
      (fun _ -> iota_match_head env ci u pms bi iv c brs);
      ( fun _ ->
        match iv with
        | CaseInvert {indices} -> match_uip_red env ci u pms indices brs
        | _ -> None
      );
      fun _ ->
        Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
          (zeta_match_head env ci u pms brs)
    ]
  | Proj (pn, r, c) -> proj_head pn r c
  | Lambda (_, t, c) -> Result.to_option (eta_lambda_red evm env t c)
  | Rel _ | Meta _ | Sort _ | Prod _ | Ind _ | Construct _ | Fix _ | CoFix _
  | Int _ | Float _ | String _ | Array _ -> None

let head_step evm env c =
  let rec aux c =
    match kind c with
    | Var id -> delta_var_red env id
    | Evar ev -> Evd.existential_opt_value0 evm ev
    | Cast (c, k, t) -> Option.map (fun c -> mkCast (c, k, t)) (aux c)
    | LetIn (na, b, u, c) -> Some (subst1 b c)
    | App (head, args) ->
      first_step [
        (fun _ -> app_head env head args);
        ( fun _ ->
          match kind head with
          | Fix ((reci, i), f) ->
            let i = reci.(i) in
            Option.map (fun c -> mkApp (head, array_with args i c)) (aux args.(i))
          | _ -> None
        );
        fun _ -> Option.map (fun h -> mkApp (h, args)) (aux head)
      ]
    | Const sp -> const_head env sp
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> iota_match_head env ci u pms bi iv c brs);
        ( fun _ ->
          match iv with
          | CaseInvert {indices} -> match_uip_red env ci u pms indices brs
          | _ -> None
        );
        fun _ -> Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c)
      ]
    | Proj (pn, r, c) ->
      or_else (proj_head pn r c) (fun _ -> Option.map (fun c -> mkProj (pn, r, c)) (aux c))
    | Rel _ | Meta _ | Sort _ | Prod _ | Lambda _ | Ind _ | Construct _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> None
  in force "Term at head is not reducible." (aux c)

let cbv_reduce evm env =
  let rec aux c =
    match kind c with
    | Var id -> delta_var_red env id
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
        (fun _ -> app_head env head args);
        fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step_n aux args 1)
      ]
    | Const sp -> const_head env sp
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux c));
        (fun _ -> iota_match_head env ci u pms bi iv c brs);
        (fun _ -> Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step aux pms));
        fun _ ->
          match iv with
          | CaseInvert {indices} -> match_uip_red env ci u pms indices brs
          | _ -> None
      ]
    | Proj (pn, r, c) -> proj_head pn r c
    | Rel _ | Meta _ | Sort _ | Lambda _ | Ind _ | Construct _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> None
  in aux

let cbv_normalize evm =
  let rec aux env c =
    let reduce_or_normalize f c = or_else (cbv_reduce evm env c) (fun _ -> aux (f env) c) in
    match kind c with
    | Evar (evi, ev) ->
      Option.map (fun ev -> mkEvar (evi, ev)) (slist_step (reduce_or_normalize id) ev)
    | Prod (na, t, u) ->
      or_step (fun t -> mkProd (na, t, u)) (aux env t)
        ( fun _ ->
          Option.map (fun u -> mkProd (na, t, u)) (aux (push_rel (LocalAssum (na, t)) env) u)
        )
    | Lambda (na, t, c) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkLambda (na, t, c))
          (reduce_or_normalize (push_rel (LocalAssum (na, t))) c)
        );
        (fun _ -> Option.map (fun t -> mkLambda (na, t, c)) (reduce_or_normalize id t));
        (fun _ -> Result.to_option (eta_lambda_red evm env t c))
      ]
    | App (head, args) ->
      or_step (fun head -> mkApp (head, args)) (aux env head)
        (fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step (aux env) args))
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c));
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step (aux env) pms)
        );
        ( fun _ ->
          Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
          (zeta_match_head env ci u pms brs)
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
              Option.map (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                ( reduce_or_normalize
                  (push_rel_context (expand_arity_context mind (ci.ci_ind, u) ps nas))
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
        (fun _ -> Option.map (fun def -> mkArray (u, ts, def, ty)) (reduce_or_normalize id def));
        ( fun _ ->
          Option.map (fun ts -> mkArray (u, ts, def, ty)) (array_step (reduce_or_normalize id) ts)
        );
        fun _ -> Option.map (fun ty -> mkArray (u, ts, def, ty)) (reduce_or_normalize id ty)
      ]
    | Var _ | Rel _ | Meta _ | Sort _ | Cast _ | Const _ | Ind _ | Construct _
    | Int _ | Float _ | String _ -> None
    | LetIn _ -> assert false
  in aux

let cbv_step evm env c =
  force "Term is fully reduced." (or_else (cbv_reduce evm env c) (fun _ -> cbv_normalize evm env c))

let global_step evm env c =
  let rec aux env c =
    match kind c with
    | Var id -> delta_var_red env id
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
      or_step (fun t -> mkProd (na, t, u)) (aux env t)
        ( fun _ ->
          Option.map (fun u -> mkProd (na, t, u)) (aux (push_rel (LocalAssum (na, t)) env) u)
        )
    | Lambda (na, t, c) ->
      first_step [
        ( fun _ ->
          Option.map (fun c -> mkLambda (na, t, c)) (aux (push_rel (LocalAssum (na, t)) env) c)
        );
        (fun _ -> Option.map (fun t -> mkLambda (na, t, c)) (aux env t));
        fun _ -> Result.to_option (eta_lambda_red evm env t c)
      ]
    | LetIn (na, b, u, c) ->
      Some (
        match aux env b with Some b -> mkLetIn (na, b, u, c)
        | None ->
          match aux (push_rel (LocalDef (na, b, u)) env) c with Some c -> mkLetIn (na, b, u, c)
          | None -> subst1 b c
      )
    | App (head, args) ->
      first_step [
        (fun _ -> Option.map (fun head -> mkApp (head, args)) (aux env head));
        (fun _ -> Option.map (fun hd -> mkApp (head, array_with args 0 hd)) (aux env args.(0)));
        (fun _ -> app_head env head args);
        fun _ -> Option.map (fun args -> mkApp (head, args)) (array_step_n (aux env) args 1)
      ]
    | Const sp -> const_head env sp
    | Case (ci, u, pms, bi, iv, c, brs) ->
      first_step [
        (fun _ -> Option.map (fun c -> mkCase (ci, u, pms, bi, iv, c, brs)) (aux env c));
        (fun _ -> iota_match_head env ci u pms bi iv c brs);
        ( fun _ ->
          Option.map (fun pms -> mkCase (ci, u, pms, bi, iv, c, brs)) (array_step (aux env) pms)
        );
        fun _ ->
          let mind = lookup_mind_specif env ci.ci_ind in
          let ps = expand_match_param_context mind u pms in
          first_step [
            ( fun _ ->
              match iv with
              | CaseInvert {indices} -> match_uip_red_specif env mind u ps indices brs
              | _ -> None
            );
            ( fun _ ->
              Option.map (fun brs -> mkCase (ci, u, pms, bi, iv, c, brs))
              (zeta_match_head env ci u pms brs)
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
              Option.map (fun p -> mkCase (ci, u, pms, ((nas, p), rp), iv, c, brs))
                (aux (push_rel_context (expand_arity_context mind (ci.ci_ind, u) ps nas) env) p)
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
      or_step (fun c -> mkProj (pn, r, c)) (aux env c) (fun _ -> proj_head pn r c)
    | Array (u, ts, def, ty) ->
      first_step [
        (fun _ -> Option.map (fun def -> mkArray (u, ts, def, ty)) (aux env def));
        (fun _ -> Option.map (fun t -> mkArray (u, ts, def, ty)) (array_step (aux env) ts));
        fun _ -> Option.map (fun ty -> mkArray (u, ts, def, ty)) (aux env ty)
      ]
    | Rel _ | Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ | String _ -> None
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
| (EBoth | ELambda _ as x) -> x

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
| EBoth -> Pp.mt ()
| EPrim x -> pr_arg str "prim" ++ pr_opt pr x
| ELambda s -> pr_arg str "lambda" ++ pr_opt Names.Id.print s

let pr_reduction pr_occs pr_closure pr_tycons pr_zeta pr_delta = function
| Cast occ -> str "cast" ++ pr_occs occ
| Beta (b, occ) -> str "beta" ++ pr_opt Names.Id.print b ++ pr_occs occ
| Zeta (b, occ) -> str "zeta" ++ pr_opt Names.Id.print b ++ pr_occs occ
| ZetaMatch (z, occ) -> str "zeta_match" ++ pr_arg pr_zeta z ++ pr_occs occ
| Delta (t, occ) -> str "delta" ++ pr_opt pr_delta t ++ pr_occs occ
| Eta (tyc, occ) -> str "eta" ++ pr_eta_kind pr_tycons tyc ++ pr_occs occ
| Evar occ -> str "evar" ++ pr_occs occ
| IotaFix (b, occ) -> str "iota_fix" ++ pr_opt Names.Id.print b ++ pr_occs occ
| IotaFixPrime (b, occ) -> str "iota_fix'" ++ pr_opt Names.Id.print b ++ pr_occs occ
| IotaCofix (b, occ) -> str "iota_cofix" ++ pr_opt Names.Id.print b ++ pr_occs occ
| IotaCofixPrime (b, occ) -> str "iota_cofix'" ++ pr_opt Names.Id.print b ++ pr_occs occ
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
  | ConstRef c ->
    ( try
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
    | ConstRef c, None ->
      ( try
          let open Environ in
          let open Structures in
          let open Structure in
          let s = Structure.find_from_projection c in
          let rec count_binds n = function
          | { proj_body = Some c'; proj_true = false; _ } :: _ when QConstant.equal env c c' -> Some n
          | { proj_true = pt; _ } :: l -> count_binds (if pt then n else n + 1) l
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
      let open Environ in
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
        if match_binder na n
        then user_err (str "Non unique let binding for zeta_match.")
        else no_binding n t
      in
      let rec single_binding n k = function
      | [] -> user_err (str "No let binding for zeta_match.")
      | LocalAssum _ :: t -> single_binding n (k + 1) t
      | LocalDef (na, _, _) :: t ->
        if match_binder na n then (no_binding n t; k) else single_binding n (k + 1) t
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
    | Cast occ -> reduce_with_context occ cast_prep cast_step
    | Beta (b, occ) -> reduce_with_context occ (beta_prep b) beta_step
    | Zeta (b, occ) -> reduce_with_context occ (zeta_prep b) zeta_step
    | ZetaMatch ((ind, n, m), occ) ->
      reduce_with_context occ (zeta_match_prep ind n m) (zeta_match_step n m)
    | Delta (t, occ) -> reduce_with_context occ (delta_prep t) delta_step
    | Eta (tyc, occ) -> reduce_with_context occ (eta_prep tyc) (eta_step evm)
    | Evar occ -> reduce_with_context occ evar_prep (evar_step evm)
    | IotaFix (b, occ) -> reduce_with_context occ (fix_prep b) fix_step
    | IotaFixPrime (b, occ) -> reduce_with_context occ (fix_prime_prep b) contract_fix
    | IotaCofix (b, occ) -> reduce_with_context occ (cofix_prep b) cofix_step
    | IotaCofixPrime (b, occ) -> reduce_with_context occ (cofix_prime_prep b) contract_cofix
    | IotaMatch (tyc, occ) -> reduce_with_context occ (match_prep tyc) match_step
    | Root -> fun env x -> force "Term is not reducible at root." (root_step evm env x)
    | Head -> head_step evm
    | Cbv _ -> cbv_step evm
    | Cbn _ -> global_step evm (* LATER *)
    | Lazy _ -> global_step evm (* LATER *)
  in
  EConstr.of_constr (f env (EConstr.Unsafe.to_constr c))
