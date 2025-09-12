
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

let s = fun _ -> None


let p : program = { rules = []; modes = (fun _ -> []) ; coq_sig = fun _ -> Coq_b Exp }
let f x = (Goal (p, (Call x)))


let _ =
  let s = state_to_list 
    (And ((Or (OK, s, (f xB))), (f xC), (And ((Or ((Goal (p, Cut)), s, (f xD))), (f xE), (Goal (p, Cut))))))  [] in
  Format.eprintf "%a@." pp_alts s


(* 
  (* (OK \/_{s1} B) /\_C ((! \/_{s2} D) /\_{E} !) *)
  state_to_list 
    (And (Or OK s1 (f B)) (f C) (And (Or (Goal p Cut) s2 (f D)) (f E) (Goal p Cut))) [::] = 
    [:: 
      [:: cut [:: [:: call p B; call p C]]; cut [::]];
      [:: call p D; call p E]; 
      [:: call p B; call p C]].
 *)
