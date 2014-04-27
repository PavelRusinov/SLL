open Ostap
open Util
open Matcher
open Sll

exception Translation_error of string

let is_PCtr = function
  | `PCtr(_,_) -> true
  | _ -> false 
    
let divide_by_name x =
  let rec divide_help x cl =
  match x with
  |[] -> cl
  |((`DPGRule(gn, (`PCtr(pn, _)::smth1), b) as grule)::smth) ->
    let is_eq = function
      |`DPGRule(gname, (`PCtr(pname, _)::smth2), _) ->(gname = gn && pname = pn)
      | _ -> raise (Translation_error("")) in
    let res = List.partition is_eq smth in 
    divide_help (snd res) ((grule::(fst res))::cl)
  | _ -> raise (Translation_error(""))
in divide_help x []

let get_names pat_l prev_name =
    let to_id x numb = 
      match x with
        | `PArg n -> n
        | `PCtr (n, p) -> prev_name ^ "_" ^ string_of_int numb
        | _ -> raise (Translation_error ("")) in
    let rec helper n l = 
      match l with
        | x :: xs -> (to_id x n) :: helper (n+1) xs
        | [] -> [] in
    helper 0 pat_l 

let get_PCtr_args = function
 | `PCtr(n, pa) -> pa
 | _ -> raise (Translation_error (""))

let get_pat_list = function
 |`DPGRule(n1, p, b1) -> p
 | _ ->  raise (Translation_error ("")) 

let move_constr x = 
  let rec move_help x n =
    let line = begin try 
      List.map List.hd x
    with (Failure "hd") ->
      [] 
    end
  in
  match line with
  | [] -> (-1)
  | _ ->
     match (List.for_all is_PCtr line) with
     | true  -> n
     | false -> move_help (List.map List.tl x) (n+1)
in move_help x 0

let move numb dp_l_l = 
  let rec del x n = 
  match x with
  |h::t -> if (n=numb) then t else (h::(del t (n+1)))
  |[]-> []  in
let m_help x = (List.nth x numb)::(del x 0) in
List.map m_help dp_l_l

let gen_dpgr_l dp_l_l dpgr_l name = 
let join dp_l x = 
 match x with 
 |`DPGRule (n, p, b) ->`DPGRule(name, dp_l, b) 
 | _ -> raise (Translation_error (""))
in
List.map2 join dp_l_l dpgr_l

let rec to_SLL dpgr_list =
  let dp_l_l = List.map get_pat_list dpgr_list in (*deep_pattern_list list*)
  let first_def = List.hd dpgr_list in
  match first_def with
  |`DPGRule(gn, (`PCtr(pn, pargs)::tail), body) -> 
    let new_gname = (gn) ^ "_" ^ (pn) in
    let new_pargs = get_names pargs "parg" in
    let new_gargs = get_names tail "arg" in
    let new_def = gn $ (pn +> new_pargs, new_gargs ) in
    let new_dp_l_l = List.map (fun dpl -> (get_PCtr_args (List.hd dpl)) @ (List.tl dpl)) dp_l_l in
    let numb_to_move = move_constr new_dp_l_l in
    begin match (numb_to_move > (-1)) with
    |true -> 
      let body_args = new_pargs @ new_gargs in
      let mo_body_args = List.hd (move numb_to_move [body_args]) in
      let new_body = `FCall (new_gname, (List.map (fun n -> `Var n) mo_body_args)) in
      let new_classes = divide_by_name (gen_dpgr_l (move numb_to_move new_dp_l_l) dpgr_list new_gname) in
      (`GRule(new_def => new_body))::(List.concat (List.map to_SLL new_classes))
    |false -> 
      match dpgr_list with
      | (x::[]) -> [(`GRule (new_def => body))]
      | _ -> raise (Translation_error ("conflict"))  end
  |_ -> raise (Translation_error (""))

let elim_deep_pat x =
  let rec helper defs fdefs dpgdefs =
  match defs with
  | (`DPGRule(gn, p, b)::smth) -> helper smth fdefs ((`DPGRule(gn, p, b))::dpgdefs)  
  | (`FRule (fn, b)::smth) -> helper smth ((`FRule(fn, b))::fdefs) dpgdefs
  | [] -> (fdefs, dpgdefs) in 
  let res = helper x [] [] in
  (fst res)@(List.concat (List.map to_SLL (divide_by_name (snd res))))

