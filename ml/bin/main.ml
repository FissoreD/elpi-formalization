
open Ml.Src
open Unif
open Language

let rec fromn = function
  | 0 -> O
  | x -> S (fromn (x-1))

let xA = Data (fromn 0)
let xB = Data (fromn 1)
let xC = Data (fromn 2)
let xD = Data (fromn 3)
let xE = Data (fromn 4)
let reset = Data (fromn 1000)

let s = fun _ -> None


let p : program = { rules = []; modes = (fun _ -> []) ; coq_sig = fun _ -> Coq_b Exp }
let f x = (Goal (p, (Call x)))

let build_or l r = Or (l, s, r)
let (^|) = build_or

let build_and1 l res r = And (l, res, r)
let build_and l r = build_and1 l (f reset) r
let (^&) = build_and


let cut = Goal (p, Cut)

let tester ag = state_to_list ag []

let tester_pr ag =
  let s = tester ag in
  Format.eprintf "%a@." pp_alts s

let _ =
  tester_pr (
    let left = OK ^| f xB in
    let right = build_and1 (cut ^| f xD) (f xE) cut in
    build_and1 left (f xC) right)

let _ =
  tester_pr (
    let left = KO ^| f xA in
    let right = f xC ^| f xD in
    build_and1 left (f xC) right)


