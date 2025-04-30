open System

// BDD NODE вершина binary decision diagram
type BddNode =
    | Terminal of bool // Terminal = true - нижняя точка 
    | Node of int * BddNode * BddNode // номер клетки

let bTrue = Terminal true
let bFalse = Terminal false

// Функция для создания не терминальной ноды
let bddVar idx low high = Node(idx, low, high)

// Функция булевого не
let rec bNot a =
    match a with
    | Terminal true -> Terminal false
    | Terminal false -> Terminal true
    | Node(v, l, h) -> Node(v, bNot h, bNot l) // Рекурсивная функция если матчит ноду

// Логическое И
let rec bAnd a b =
    match (a, b) with
    | Terminal false, _ | _, Terminal false -> Terminal false
    | Terminal true, _ -> b
    | _, Terminal true -> a
    | Node(v1, l1, h1), Node(v2, l2, h2) ->
        if v1 = v2 then
            Node(v1, bAnd l1 l2, bAnd h1 h2)
        else
            let low = bAnd l1 l2
            let high = bAnd h1 h2
            Node(v1, low, high)

// Логическое ИЛИ
let rec bOr a b =
    match (a, b) with
    | Terminal true, _ | _, Terminal true -> Terminal true
    | Terminal false, _ -> b
    | _, Terminal false -> a
    | Node(v1, l1, h1), Node(v2, l2, h2) ->
        if v1 = v2 then
            Node(v1, bOr l1 l2, bOr h1 h2)
        else
            let low = bOr l1 l2
            let high = bOr h1 h2
            Node(v1, low, high)

printf "Введите количество ферзей (n): "
let n = Console.ReadLine() |> Int32.Parse

let varIdx row col = row * n + col
let cell row col = bddVar (varIdx row col) bFalse bTrue

// Функция проверки, что ТОЛЬКО одно значений из списка BDDNode равно True, возвращает 
let oneHot (vars: BddNode list) =
    if vars.Length = 1 then 
        vars.Head // If there's only one variable, just return it
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

let rowConstraints =
    [0 .. n - 1]
    |> List.map (fun row ->
        [0 .. n - 1]
        |> List.map (cell row)
        |> oneHot
    )
    |> List.reduce bAnd // Ensure one queen per row

let columnConstraints =
    [0 .. n - 1]
    |> List.map (fun col ->
        [0 .. n - 1]
        |> List.map (fun row -> cell row col)
        |> oneHot
    )
    |> List.reduce bAnd // Ensure one queen per column

let majorDiagonals =
    [-(n - 1) .. n - 1]
    |> List.choose (fun d ->
        let cells = 
            [0 .. n - 1]
            |> List.choose (fun r ->
                let c = r - d
                if c >= 0 && c < n then Some(cell r c) else None)
        if List.isEmpty cells then None else Some(oneHot cells)
    )

let minorDiagonals =
    [0 .. 2 * (n - 1)]
    |> List.choose (fun d ->
        let cells =
            [0 .. n - 1]
            |> List.choose (fun r ->
                let c = d - r
                if c >= 0 && c < n then Some(cell r c) else None)
        if List.isEmpty cells then None else Some(oneHot cells)
    )

let diagConstraints = List.reduce bAnd (List.concat [majorDiagonals; minorDiagonals])
let fullConstraint = bAnd (bAnd rowConstraints columnConstraints) diagConstraints

let rec getAssignment node (env: Map<int, bool>) =
    match node with
    | Terminal true -> Some env
    | Terminal false -> None
    | Node(v, lo, hi) ->
        // Check if setting variable to true is valid
        if isValid hi then
            getAssignment hi (env.Add(v, true))
        else
            getAssignment lo (env.Add(v, false))

and isValid node =
    match node with
    | Terminal false -> false
    | _ -> true

let findQueens n =
    let isValid row col (queens: (int * int) list) =
        not (List.exists (fun (r, c) -> r = row || c = col || abs (r - row) = abs (c - col)) queens)

    let rec backtrack row queens =
        if row = n then
            Some queens
        else
            let rec checkCol col =
                if col = n then None
                elif isValid row col queens then
                    match backtrack (row + 1) ((row, col) :: queens) with
                    | Some _ as result -> result
                    | None -> checkCol (col + 1)
                else checkCol (col + 1)
            checkCol 0

    match backtrack 0 [] with
    | Some queens ->
        for row in 0 .. n - 1 do
            for col in 0 .. n - 1 do
                if List.exists (fun (r, c) -> r = row && c = col) queens then
                    printf "Q "
                else
                    printf ". "
            printfn ""
    | None -> printfn "No solution found."

findQueens n


