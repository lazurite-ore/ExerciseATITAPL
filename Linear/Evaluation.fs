module Evaluation

open Syntax
open RuntimeData

exception NoRuleApply

let rec eval1 (s: Store) = function

    | ETmBool _ | ETmAbs _ | ETmPair (_, ETmPtr _, ETmPtr _) as v ->
        let (ptr, s') = Store.malloc v s
        (s', ETmPtr ptr)

    | ETmPair (q, ETmPtr x, t2) ->
        let (s', t2') = eval1 s t2
        (s', ETmPair (q, ETmPtr x, t2'))
    | ETmPair (q, t1, t2) ->
        let (s', t1') = eval1 s t1
        (s', ETmPair (q, t1', t2))

    | ETmApp (ETmPtr x1, ETmPtr x2) ->
        match Store.read x1 s with
        | ETmAbs (_, _, _, t) ->
            let t' = EvalTerm.substTop (ETmPtr x2) t
            let s' = Store.free x1 s
            (s', t')
        | _ -> failwith "expect function"
    | ETmApp (ETmPtr x1, t2) ->
        let (s', t2') = eval1 s t2
        (s', ETmApp (ETmPtr x1, t2'))
    | ETmApp (t1, t2) ->
        let (s', t1') = eval1 s t1
        (s', ETmApp (t1', t2))

    | ETmIfElse (ETmPtr x, t1, t2) ->
        let t =
            match Store.read x s with
            | ETmBool (_, true) -> t1
            | ETmBool (_, false) -> t2
            | _ -> failwith "expect bool"
        let s' = Store.free x s
        (s', t)
    | ETmIfElse (t1, t2, t3) ->
        let (s', t1') = eval1 s t1
        (s', ETmIfElse (t1', t2, t3))

    | ETmSplit (ETmPtr x, y, z, t) ->
        match Store.read x s with
        | ETmPair (_, y1, z1) -> (Store.free x s, EvalTerm.substTop y1 (EvalTerm.substTop z1 t))
        | _ -> failwith "expect pair"

    | ETmSplit (t1, z, y, t2) ->
        let (s', t1') = eval1 s t1
        (s', ETmSplit (t1', z, y, t2))

    | ETmPtr _ ->
        raise NoRuleApply

    | ETmVar _ ->
        raise NoRuleApply

let rec eval2 debug (s: Store) (t: EvalTerm) =
    try
        let (s', t') = eval1 s t

        if debug then

            t'
            |> Pretty.evalToString []
            |> printfn "debug: %s"

            s'
            |> Pretty.storeToString
            |> printfn "store:{\n%s}"

        eval2 debug s' t'
    with
    | NoRuleApply ->
        (s, t)

let rec eval debug (t: Term) = eval2 debug [] (EvalTerm.termToEval t)