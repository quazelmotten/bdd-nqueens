open System
open System.Collections.Generic

// Определение BDDNode и нижних терминалов
type BddNode =
    | Terminal of bool
    | Node of int * BddNode * BddNode

// Переменные для дебага
let mutable mkCalls = 0
let mutable mkReuseHits = 0
let mutable mkNewNodes = 0
let mutable applyCalls = 0
let mutable buildCalls = 0

// Определение таблицы H из методички, которая используется в mk
let uniqueTable = Dictionary<(int * BddNode * BddNode), BddNode>()
// Определение таблицы G из методички, которая используется в apply
let applyCache = Dictionary<(string * BddNode * BddNode), BddNode>()

// Функция mk из методички
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

// Функция apply из методички
let rec apply op u1 u2 =
    applyCalls <- applyCalls + 1
    let normalize (a, b) = if a < b then (a, b) else (b, a)
    //раннее отсекание
    match u1, u2 with
    | Terminal false, _ when op = "and" -> Terminal false
    | _, Terminal false when op = "and" -> Terminal false
    | Terminal true, x when op = "and" -> x
    | x, Terminal true when op = "and" -> x
    | Terminal true, _ when op = "or" -> Terminal true
    | _, Terminal true when op = "or" -> Terminal true
    | Terminal false, x when op = "or" -> x
    | x, Terminal false when op = "or" -> x
    | _ -> // дальше по рекурсии

    let key =
        match op with
        | "and" | "or" ->
            let (a, b) = normalize (u1, u2)
            (op, a, b)
        | _ -> (op, u1, u2)

    match applyCache.TryGetValue key with
    | true, res -> res
    | false, _ ->
        let res =
            match u1, u2 with
            | Terminal b1, Terminal b2 ->
                Terminal (
                    match op with
                    | "and" -> b1 && b2
                    | "or"  -> b1 || b2
                    | _ -> failwith "Не поддерживаемая операция в apply"
                )
            | Node(v1, l1, h1), Node(v2, l2, h2) ->
                if v1 = v2 then mk v1 (apply op l1 l2) (apply op h1 h2)
                elif v1 < v2 then mk v1 (apply op l1 u2) (apply op h1 u2)
                else mk v2 (apply op u1 l2) (apply op u1 h2)
            | Node(v, l, h), Terminal _ ->
                mk v (apply op l u2) (apply op h u2)
            | Terminal _, Node(v, l, h) ->
                mk v (apply op u1 l) (apply op u1 h)
        applyCache.[key] <- res
        res

// Функция НЕ по BDD (логично, что достаточно поменять терминалы местами)
let rec bddNot node =
    match node with
    | Terminal b -> Terminal (not b)
    | Node(v, l, h) -> mk v (bddNot l) (bddNot h)

let varIndex n row col = row * n + col

// функция для получения массива диагональных клеток
let diagonalVars n =
    let posDiags =
        [ for r in 0 .. n - 1 do
            for c in 0 .. n - 1 ->
                (r + c, varIndex n r c) ]
        |> List.groupBy fst
        |> List.map (fun (_, lst) -> lst |> List.map snd)

    let negDiags =
        [ for r in 0 .. n - 1 do
            for c in 0 .. n - 1 ->
                (r - c, varIndex n r c) ]
        |> List.groupBy fst
        |> List.map (fun (_, lst) -> lst |> List.map snd)

    posDiags @ negDiags

// anysat - поиск любого одного решения из методички
let rec anysat (node: BddNode) : Map<int, bool> option =
    let rec go (n: BddNode) (acc: Map<int, bool>) : Map<int, bool> option =
        match n with
        | Terminal true -> Some acc
        | Terminal false -> None
        | Node(v, l, h) ->
            match go h (acc.Add(v, true)) with
            | Some res -> Some res
            | None -> go l (acc.Add(v, false))
    go node Map.empty

// функция вывода решения
let printAssignment n (assignment: Map<int, bool>) =
    for row in 0 .. n - 1 do
        for col in 0 .. n - 1 do
            let idx = varIndex n row col
            printf (if Map.tryFind idx assignment = Some true then "Q " else ". ")
        printfn ""

// функиця построения bdd по ограничению
let buildConstraint (vars: int list) (predicate: bool[] -> bool) =
    let env = Array.zeroCreate (vars |> List.max |> (+) 1)
    let buildCache = Dictionary<(int * bool[]), BddNode>()
    
    let rec build (i: int) : BddNode =
        buildCalls <- buildCalls + 1
        let key = (i, Array.copy env)
        match buildCache.TryGetValue(key) with
        | true, res -> res
        | false, _ ->
            let res =
                if i >= vars.Length then
                    Terminal (predicate env)
                else
                    let v = vars.[i]
                    env.[v] <- false
                    let low = build (i + 1)
                    env.[v] <- true
                    let high = build (i + 1)
                    env.[v] <- false
                    mk v low high
            buildCache.[key] <- res
            res

    build 0

// предикат по условию только один ферзь в массиве (ряд, колонка)
let exactlyOnePredicate (vars: int list) (assignment: bool[]) =
    let count = vars |> List.sumBy (fun v -> if assignment.[v] then 1 else 0)
    count = 1

// предикат по условию как максимум один ферзь в массиве (диагональ)
let atMostOnePredicate (vars: int list) (assignment: bool[]) =
    let count = vars |> List.sumBy (fun v -> if assignment.[v] then 1 else 0)
    count <= 1

// функция генерации общей robdd по всем условиям
let generateNQueensBDD n =
    // Helper to get variables per line
    let varsInRow row = [ for col in 0 .. n - 1 -> varIndex n row col ]
    let varsInCol col = [ for row in 0 .. n - 1 -> varIndex n row col ]

    // Exactly one queen per row
    let rowPredicates = 
        [ for row in 0 .. n - 1 -> 
            let vars = varsInRow row
            vars, fun a -> exactlyOnePredicate vars a ]

    let rowConstraints =
        rowPredicates
        |> List.map (fun (vars, pred) -> buildConstraint vars pred)
        |> List.reduce (apply "and")

    // At most one queen per column
    let colConstraints =
        [ for col in 0 .. n - 1 ->
            buildConstraint (varsInCol col) (exactlyOnePredicate (varsInCol col)) ]
        |> List.reduce (apply "and")

    // Diagonal variables
    let diagVars = diagonalVars n

    // At most one queen per diagonal
    let diagConstraints =
        diagVars
        |> List.map (fun vars -> buildConstraint vars (atMostOnePredicate vars))
        |> List.reduce (apply "and")

    // Combine all constraints with AND
    rowConstraints
    |> apply "and" (colConstraints |> apply "and" diagConstraints)

//main
[<EntryPoint>]
let main _ =
    printf "Введите количество ферзей (n): "
    let n = Console.ReadLine() |> int

    let stopwatch = System.Diagnostics.Stopwatch.StartNew() // Start timing

    let bdd = generateNQueensBDD n

    stopwatch.Stop() // Stop timing after computation

    match anysat bdd with
    | Some sol ->
        printfn "Решение:"
        printAssignment n sol
        printfn "mk calls: %d" mkCalls
        printfn "Нод переиспользовано: %d" mkReuseHits
        printfn "Создано уникальных нод: %d" mkNewNodes
        printfn "Apply calls: %d" applyCalls
        printfn "Build calls: %d" buildCalls
    | None -> printfn "Решений не найдено."

    // Print elapsed time
    printfn "Затраченное время: %f seconds" stopwatch.Elapsed.TotalSeconds

    0

