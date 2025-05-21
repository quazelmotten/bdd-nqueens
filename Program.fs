open System
open System.Collections.Generic

type BddNode =
    | Terminal of bool
    | Node of int * BddNode * BddNode

let mutable mkCalls = 0
let mutable buildCalls = 0

let mutable mkReuseHits = 0
let mutable mkNewNodes = 0

let bTrue = Terminal true
let bFalse = Terminal false

let uniqueTable = Dictionary<(int * BddNode * BddNode), BddNode>()

let mk v low high =
    mkCalls <- mkCalls + 1
    if low = high then low
    else
        let key = (v, low, high)
        match uniqueTable.TryGetValue(key) with
        | true, node ->
            mkReuseHits <- mkReuseHits + 1
            node
        | false, _ ->
            let node = Node(v, low, high)
            uniqueTable.[key] <- node
            mkNewNodes <- mkNewNodes + 1
            node


let applyCache = Dictionary<(string * BddNode * BddNode), BddNode>()

let rec apply op u1 u2 =
    let key = (op, u1, u2)
    match applyCache.TryGetValue key with
    | true, res -> res
    | false, _ ->
        let res =
            match (u1, u2) with
            | Terminal b1, Terminal b2 ->
                match op with
                | "and" -> Terminal (b1 && b2)
                | "or"  -> Terminal (b1 || b2)
                | "xor" -> Terminal (b1 <> b2)
                | _ -> failwith "Unsupported op"
            | Node(v1, l1, h1), Node(v2, l2, h2) ->
                if v1 = v2 then
                    mk v1 (apply op l1 l2) (apply op h1 h2)
                elif v1 < v2 then
                    mk v1 (apply op l1 u2) (apply op h1 u2)
                else
                    mk v2 (apply op u1 l2) (apply op u1 h2)
            | Node(v, l, h), Terminal _ ->
                mk v (apply op l u2) (apply op h u2)
            | Terminal _, Node(v, l, h) ->
                mk v (apply op u1 l) (apply op u1 h)
        applyCache.[key] <- res
        res


let rec restrict (node: BddNode) (var: int) (value: bool) : BddNode =
    match node with
    | Terminal _ -> node
    | Node(v, low, high) ->
        if v = var then
            if value then high else low
        elif v > var then node
        else mk v (restrict low var value) (restrict high var value)

type Assignment = Map<int, bool>

let rec anysat (node: BddNode) : Assignment option =
    let rec go (n: BddNode) (acc: Map<int, bool>) : Assignment option =
        match n with
        | Terminal true -> Some acc
        | Terminal false -> None
        | Node(v, l, h) ->
            match go h (acc.Add(v, true)) with
            | Some res -> Some res
            | None -> go l (acc.Add(v, false))
    go node Map.empty


let buildCache = Dictionary<(int * bool[]), BddNode>()
let rec build (f: bool[] -> bool) (vars: int list) (env: bool[]) (i: int) : BddNode =
    buildCalls <- buildCalls + 1
    let key = (i, Array.copy env)
    match buildCache.TryGetValue(key) with
    | true, result -> result
    | false, _ ->
        let result =
            if i >= vars.Length then
                Terminal (f env)
            else
                let v = vars.[i]

                env.[v] <- false
                let low = build f vars env (i + 1)

                env.[v] <- true
                let high = build f vars env (i + 1)

                env.[v] <- false 
                mk v low high
        buildCache.[key] <- result
        result


let varIndex n row col = row * n + col

let generateNQueensBDD (n: int) : BddNode =
    let variables = [0 .. n * n - 1]

    let f (env: bool[]) : bool =
        let board =
            [ for row in 0 .. n-1 ->
                [ for col in 0 .. n-1 ->
                    env.[varIndex n row col] ] ]

        let queens =
            [ for row in 0 .. n-1 do
                for col in 0 .. n-1 do
                    if board.[row].[col] then yield (row, col) ]

        if List.length queens <> n then false
        else
            let rec noConflict qlist =
                match qlist with
                | [] -> true
                | (r1, c1) :: rest ->
                    rest |> List.forall (fun (r2, c2) ->
                        r1 <> r2 && c1 <> c2 && abs (r1 - r2) <> abs (c1 - c2))
                    && noConflict rest
            noConflict queens

    let env = Array.zeroCreate (n * n)
    build f variables env 0


let printAssignment n (assignment: Assignment) =
    for row in 0 .. n - 1 do
        for col in 0 .. n - 1 do
            let idx = varIndex n row col
            if Map.tryFind idx assignment = Some true then
                printf "Q "
            else
                printf ". "
        printfn ""

[<EntryPoint>]
let main _ =
    printf "Введите количество ферзей (n): "
    let n = Console.ReadLine() |> int

    let bdd = generateNQueensBDD n
    match anysat bdd with
    | Some solution ->
        printfn "\nРешение:"
        printAssignment n solution
        printfn "\nmk was called %d times." mkCalls
        printfn "Reused nodes: %d" mkReuseHits
        printfn "New unique nodes created: %d" mkNewNodes
        printfn "Build calls: %d" buildCalls
    | None ->
        printfn "Решений не найдено."
    0
