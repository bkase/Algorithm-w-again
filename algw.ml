open Core

(* definitions *)
module Make_var (Named : sig
  val name : string
end) : sig
  type t [@@deriving equal, sexp]

  include Comparable.S with type t := t

  val fresh : ?name:string -> unit -> t

  val to_string : t -> string
end = struct
  module T = struct
    type t = string [@@deriving sexp, equal, compare]
  end

  include T
  include Comparable.Make (T)

  let fresh =
    let count = ref 0 in
    fun ?name () ->
      let next = !count in
      count := next + 1 ;
      Option.value_map name ~default:"" ~f:(fun s -> s ^ "$")
      ^ sprintf "%s%d" Named.name next

  let to_string = Fn.id
end

module Var = Make_var (struct
  let name = "var"
end)

module TyVar = Make_var (struct
  let name = "alpha"
end)

module Type = struct
  type t = Alpha of TyVar.t | Int | Bool | List of t | Arrow of t * t
  [@@deriving sexp, equal]

  let free t =
    let rec go acc = function
      | Alpha v ->
          v :: acc
      | Int ->
          acc
      | Bool ->
          acc
      | Arrow (t1, t2) ->
          go acc t1 @ go acc t2
      | List t ->
          go acc t
    in
    go [] t
end

module Exp = struct
  type t =
    | Int of int
    | Bool of bool
    | List of t list
    | If of t * t * t
    | Var of Var.t
    | App of t * t
    | Lam of Var.t * t
    | Let of Var.t * t * t
  [@@deriving sexp, equal]
end

module Scheme = struct
  type t = Tau of Type.t | Forall of TyVar.t list * Type.t
  [@@deriving sexp, equal]
end

module Subst = struct
  type t = Type.t TyVar.Map.t [@@deriving equal]

  let singleton k v = TyVar.Map.singleton k v

  let identity = TyVar.Map.empty

  let union s1 s2 =
    TyVar.Map.merge s1 s2 ~f:(fun ~key:_ -> function
      | `Both (x, y) when Type.equal x y ->
          Some x
      | `Both (_, y) ->
          Some y
      | `Left x ->
          Some x
      | `Right x ->
          Some x )

  let union_all ss = List.fold ss ~init:identity ~f:union

  let rec apply_typ (t : t) (typ : Type.t) =
    match typ with
    | Type.Int ->
        typ
    | Bool ->
        typ
    | Arrow (a, b) ->
        Arrow (apply_typ t a, apply_typ t b)
    | List a ->
        List (apply_typ t a)
    | Alpha tyvar -> (
      match TyVar.Map.find t tyvar with Some typ -> typ | None -> typ )

  let apply (t : t) (scheme : Scheme.t) =
    match scheme with
    | Scheme.Tau typ | Forall (_, typ) ->
        Scheme.Tau (apply_typ t typ)
end

module Context = struct
  type t = Scheme.t Var.Map.t [@@deriving sexp]

  let subst (t : t) (s : Subst.t) : t =
    Var.Map.map t ~f:(fun scheme -> Subst.apply s scheme)
end

module Infer = struct
  let rec unify (s : Type.t) (t : Type.t) :
      (Subst.t, [> `Unification of string]) Result.t =
    match (s, t) with
    | Alpha a, _ ->
        Ok (Subst.singleton a t)
    | _, Alpha b ->
        Ok (Subst.singleton b s)
    | List s1, List t1 ->
        unify s1 t1
    | Arrow (s1, s2), Arrow (t1, t2) ->
        let open Result.Let_syntax in
        let%bind m1 = unify s1 t1 in
        let%map m2 = unify s2 t2 in
        Subst.union m1 m2
    | _, _ when Type.equal s t ->
        Ok Subst.identity
    | _ ->
        Error
          (`Unification
            (sprintf
               !"Unification of %{sexp: Type.t} and %{sexp: Type.t} failed"
               s t))

  let rec w (ctx : Context.t) (e : Exp.t) :
      ( Subst.t * Type.t
      , [> `Unification of string
        | `Unbound_var
        | `Inconsistent_types_in_list
        | `If_condition_not_bool
        | `If_inconsistent_branches ] )
      Result.t =
    match e with
    | Exp.Int _ ->
        Ok (Subst.identity, Type.Int)
    | Exp.Bool _ ->
        Ok (Subst.identity, Type.Bool)
    | List es -> (
      match es with
      | [] ->
          let a = TyVar.fresh ~name:"list" () in
          Ok (Subst.identity, Type.List (Alpha a))
      | e1 :: eis ->
          List.fold eis ~init:(w ctx e1) ~f:(fun acc ei ->
              let open Result.Let_syntax in
              let%bind si, ti = acc in
              let%bind si', ti' = w ctx ei in
              if Type.equal ti ti' then Ok (Subst.union si si', ti)
              else Error `Inconsistent_types_in_list ) )
    | If (b, e1, e2) ->
        let open Result.Let_syntax in
        let%bind sc, tc = w ctx b in
        let%bind sc' =
          unify tc Type.Bool
          |> Result.map_error ~f:(fun _ -> `If_condition_not_bool)
        in
        let%bind s1, t1 = w ctx e1 in
        let%bind s2, t2 = w ctx e2 in
        let%map s12' =
          unify t1 t2
          |> Result.map_error ~f:(fun _ -> `If_inconsistent_branches)
        in
        (Subst.union_all [sc; sc'; s1; s2; s12'], t1)
    | Var x -> (
      match Var.Map.find ctx x with
      | None ->
          Error `Unbound_var
      | Some scheme -> (
        match scheme with
        (* ignore the alphas, we want those free in the inferred typ *)
        | Scheme.Tau typ | Forall (_, typ) ->
            Ok (Subst.identity, typ) ) )
    | App (e1, e2) ->
        let open Result.Let_syntax in
        let%bind s1, t2 = w ctx e2 in
        let%bind s2, t1 = w (Context.subst ctx s1) e1 in
        let b = TyVar.fresh ~name:"app" () in
        let%map v = unify (Subst.apply_typ s2 t1) (Type.Arrow (t2, Alpha b)) in
        (Subst.union v (Subst.union s1 s2), Subst.apply_typ v (Alpha b))
    | Lam (x, e1) ->
        let open Result.Let_syntax in
        let b = TyVar.fresh ~name:"lam" () in
        let ctx' =
          Var.Map.add_exn ctx ~key:x ~data:(Scheme.Tau (Type.Alpha b))
        in
        let%map s1, t1 = w ctx' e1 in
        (s1, Type.Arrow (Subst.apply_typ s1 (Type.Alpha b), t1))
    (*    | Fix (x, e1) ->
            let open Result.Let_syntax in
          let a = TyVar.fresh ~name:"fix" () in
          let%bind (s1, t1) = w (Var.Map.add_exn ctx ~key:x ~data:(Type.Alpha a)) in
    *)
    | Let (x, e1, e2) ->
        let open Result.Let_syntax in
        let%bind s1, t1 = w ctx e1 in
        let ctx' =
          let s1a = Context.subst ctx s1 in
          let xTyp =
            (* TODO: Not sure about this... *)
            Scheme.Forall (Type.free t1, t1)
          in
          Var.Map.add_exn s1a ~key:x ~data:xTyp
        in
        let%map s2, t2 = w ctx' e2 in
        (Subst.union s2 s1, t2)
end

;;
let idId () =
  let i = Var.fresh ~name:"i" () in
  let a = TyVar.fresh ~name:"a" () in
  let ctx =
    Var.Map.singleton i (Scheme.Forall ([a], Type.Arrow (Alpha a, Alpha a)))
  in
  let e = Exp.(App (Var i, Var i)) in
  (e, ctx)
in
let simple () =
  (* f : alpha -> int |- let x = 0 in f x *)
  let f = Var.fresh ~name:"f" () in
  let a = TyVar.fresh ~name:"a" () in
  let ctx =
    Var.Map.singleton f (Scheme.Forall ([a], Type.Arrow (Alpha a, Int)))
  in
  let x = Var.fresh ~name:"x" () in
  let e = Exp.(Let (x, Int 0, App (Var f, Var x))) in
  (e, ctx)
in
let map_hd () =
  let null = Var.fresh ~name:"null" () in
  let hd = Var.fresh ~name:"hd" () in
  (*let tl = Var.fresh ~name:"tl" () in
  let cons = Var.fresh ~name:"cons" () in *)
  let ctx =
    Var.Map.of_alist_exn
      [ ( null
        , let a = TyVar.fresh ~name:"a" () in
          Scheme.Forall ([a], Type.(Arrow (List (Alpha a), Bool))) )
      ; ( hd
        , let a = TyVar.fresh ~name:"a" () in
          Scheme.Forall ([a], Type.(Arrow (List (Alpha a), Alpha a))) )
        (*      ; ( tl
        , let a = TyVar.fresh ~name:"a" () in
          Scheme.Forall ([a], Type.(Arrow (List (Alpha a), List (Alpha a)))) )
      ; ( cons
        , let a = TyVar.fresh ~name:"a" () in
          Scheme.Forall
            ( [a]
            , Type.(Arrow (Alpha a, Arrow (List (Alpha a), List (Alpha a)))) )
        ) *)
       ]
  in
  let l = Var.fresh ~name:"l" () in
  let f = Var.fresh ~name:"f" () in
  let e =
    Exp.(
      Lam
        ( f
        , Lam
            ( l
            , If
                ( App (Var null, Var l)
                , List []
                , App (Var f, App (Var hd, Var l)) ) ) ))
  in
  (e, ctx)
in
let solve (e, ctx) =
  printf
    !"Attempting to infer e: %{sexp: Exp.t} under context: %{sexp: Context.t} \n"
    e ctx ;
  match Infer.w ctx e with
  | Ok (_, typ) ->
      printf !"e has type: %{sexp: Type.t}\n" typ
  | Error e ->
      printf
        !"Failed with %{sexp: [`Unification of string | `Unbound_var | \
          `Inconsistent_types_in_list | `If_condition_not_bool | \
          `If_inconsistent_branches]}\n"
        e
in
(* This one doesn't work yet ... *)
solve (idId ()) ;
printf "\n" ;
(* these work *)
solve (simple ()) ;
printf "\n" ;
solve (map_hd ())
