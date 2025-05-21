open System

// BDD NODE вершина binary decision diagram
type BddNode =
    | Terminal of bool // Терминальная нода (0, 1)
    | Node of int * BddNode * BddNode // Нода клетки

let bTrue = Terminal true
let bFalse = Terminal false

let nodeCache = System.Collections.Generic.Dictionary<(int * BddNode * BddNode), BddNode>()

let mk idx low high =
    if low = high then low
    else
        let key = (idx, low, high)
        match nodeCache.TryGetValue key with
        | true, existing -> existing
        | false, _ ->
            let newNode = Node(idx, low, high)
            nodeCache.[key] <- newNode
            newNode

// Функция для создания не терминальной ноды
let bddVar = mk

// Функция булевого не
let rec bNot a =
    match a with
    | Terminal true -> Terminal false
    | Terminal false -> Terminal true
    | Node(v, l, h) -> Node(v, bNot l, bNot h)// Рекурсивная функция если матчит ноду

// Логическое И
let rec bAnd a b =
    match (a, b) with
    | Terminal false, _ | _, Terminal false -> Terminal false
    | Terminal true, x -> x
    | x, Terminal true -> x
    | Node(v1, l1, h1), Node(v2, l2, h2) ->
        if v1 = v2 then
            Node(v1, bAnd l1 l2, bAnd h1 h2)
        elif v1 < v2 then
            Node(v1, bAnd l1 b, bAnd h1 b)
        else
            Node(v2, bAnd a l2, bAnd a h2)

let rec bOr a b =
    match (a, b) with
    | Terminal true, _ | _, Terminal true -> Terminal true
    | Terminal false, x -> x
    | x, Terminal false -> x
    | Node(v1, l1, h1), Node(v2, l2, h2) ->
        if v1 = v2 then
            Node(v1, bOr l1 l2, bOr h1 h2)
        elif v1 < v2 then
            Node(v1, bOr l1 b, bOr h1 b)
        else
            Node(v2, bOr a l2, bOr a h2)



printf "Введите количество ферзей (n): "
let n = Console.ReadLine() |> Int32.Parse
let varIdx row col = row * n + col
    
let cell row col = bddVar (varIdx row col) bFalse bTrue



// Функция проверки, что ТОЛЬКО одно значений из списка BDDNode равно True, возвращает 
let oneHot (vars: BddNode list) =
    if vars.Length = 1 then 
        vars.Head 
    else
        let rec pairs lst =
            match lst with
            | [] -> []
            | x::xs -> List.map (fun y -> (x, y)) xs @ pairs xs

        let atMostOne =
            pairs vars
            |> List.map (fun (a, b) -> bNot (bAnd a b))
            |> List.reduce bAnd
        
        let atLeastOne = List.reduce bOr vars

        bAnd atMostOne atLeastOne

// Ограничения по строкам
let rowConstraints =
    [0 .. n - 1]
    |> List.map (fun row ->
        [0 .. n - 1]
        |> List.map (cell row)
        |> oneHot
    )
    |> List.reduce bAnd 

// Ограничения по столбцам
let columnConstraints =
    [0 .. n - 1]
    |> List.map (fun col ->
        [0 .. n - 1]
        |> List.map (fun row -> cell row col)
        |> oneHot
    )
    |> List.reduce bAnd 

// новые диагонали
let generateDiagonals (coords: (int * int) list list) =
    coords
    |> List.choose (fun diag ->
        let vars = 
            diag 
            |> List.choose (fun (r, c) ->
                if r >= 0 && r < n && c >= 0 && c < n then
                    Some(cell r c)
                else None)
        if List.length vars < 2 then None
        else Some(oneHot vars)
    )

let majorDiagonals =
    [ for d in -n+1 .. n-1 ->
        [ for r in 0 .. n-1 do
            let c = r - d
            yield (r, c) ]
    ] |> generateDiagonals

let minorDiagonals =
    [ for d in 0 .. 2*n-2 ->
        [ for r in 0 .. n-1 do
            let c = d - r
            yield (r, c) ]
    ] |> generateDiagonals



let diagConstraints = List.reduce bAnd (majorDiagonals @ minorDiagonals)
// В итоге получаем общую BDD ограничений (Один ферзь в ряду И Один ферзь в столбце И Хотя бы один ферзь в ряду И Хотя бы один ферзь в колонке И То же самое с диагоналями)
let fullConstraint = bAnd (bAnd rowConstraints columnConstraints) diagConstraints

type Assignment = Map<int, bool>

// Рекурсивная функция anysat. Если достигаем Terminal True, то выводим получившееся решение, если достигли Terminal False, то рекурсивно ищем дальше, либо если рекурсия закончилась, то решения нет
// Сначала идём по high нодам (то есть правым, в случае когда нода = True, потом идём по левым low нодам) 
// В итоге заполняем Map ферзей на доске <1 клетка: Есть, 2 Клетка: Нету и тд>
let rec anySat (bdd: BddNode) : Assignment option =
    let rec helper (node: BddNode) (acc: Map<int, bool>) =
        match node with
        | Terminal true -> 
            printfn "Solution found!"
            Some acc // If terminal true, we've found a solution
        | Terminal false -> 
            printfn "Dead end (no solution)"
            None // No solution in this branch
        | Node(v, low, high) ->
            printfn "Trying var %d with value true" v // Debug: trying the high branch
            match helper high (acc.Add(v, true)) with
            | Some result -> 
                printfn "Found solution with var %d = true" v
                Some result // If true branch finds a solution, return it
            | None -> 
                printfn "Backtracking, trying var %d with value false" v // Debug: backtracking to low branch
                helper low (acc.Add(v, false)) // Try the low branch if the high branch failed
    
    helper bdd Map.empty

// функция вывода, идём по мапе и вывыодим либо Q либо точку
let printAssignment (n: int) (assignment: Assignment) =
    for row in 0 .. n - 1 do
        for col in 0 .. n - 1 do
            let idx = varIdx row col
            match Map.tryFind idx assignment with
            | Some true -> printf "Q "
            | _ -> printf ". "
        printfn ""


match anySat diagConstraints with
| Some solution -> 
    printfn "\nРешение::"
    printAssignment n solution
| None -> 
    printfn "Решений не существует."

