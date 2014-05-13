open Printf
open Ostap
open Util
open Matcher
open Sll
open Parser
open List

exception Translation_error of string

let get_PCtr_args = function
  | `PCtr(n, pa) -> pa
  | _ -> raise (Translation_error (""))

let is_PArg = function
  | (`PCtr _) -> false
  | (`PArg _) -> true
    
let divide_by_name x =
  let module M = Map.Make (struct type t = string * string include Pervasives end) in
  let m = fold_left 
    (fun m -> 
       function 
       |(`DPGRule (g, `PCtr (p, _) :: _, _) as y) -> 
         let k = g, p in
         M.add k (y :: (try M.find k m with Not_found -> [])) m
       | _ -> raise (Translation_error "")
    ) 
    M.empty 
    x 
  in
  snd (split (M.bindings m))

let get_names pat_l name = 
  mapi (fun numb -> 
          function `PArg n -> n | `PCtr _ -> name ^ "_" ^ string_of_int numb
       ) pat_l

let get_mnumb x =
  let rec move_help x n =
    let line = begin try
      map hd x
    with (Failure "hd") ->
      []
    end
  in
  match line with
  | [] -> (-1)
  | _ ->
     if exists is_PArg line
     then move_help (map tl x) (n+1)
     else n
in move_help x 0

let move_constr_forward numb dp_l_l =
  let rec del x n =
  match x with
  |h::t -> if (n=numb) then t else (h::(del t (n+1)))
  |[]-> [] in
let m_help x = (nth x numb)::(del x 0) in
map m_help dp_l_l

let gen_dpgr_l dp_l_l dpgr_l name =
map2 (fun dp_l (`DPGRule (n, p, b)) -> `DPGRule(name, dp_l, b)) dp_l_l dpgr_l

let rec to_SLL dpgr_list =
  let dp_l_l = map (fun (`DPGRule(n1, p, b1)) -> p) dpgr_list in (*dp_l_l - deep pattern list list*)
  let first_def = hd dpgr_list in
  match first_def with
  |`DPGRule(gn, (`PCtr(pn, pargs) :: tail), body) ->
    let new_pargs = get_names pargs "parg" in
    let new_gargs = get_names tail "arg" in
    let new_def = gn $ (pn +> new_pargs, new_gargs ) in
    let new_dp_l_l = map (fun h::t -> (get_PCtr_args h) @ t) dp_l_l in
    let numb_to_move = get_mnumb new_dp_l_l in
    if numb_to_move > (-1)
    then
      let body_args = new_pargs @ new_gargs in
      let [mo_body_args] = move_constr_forward numb_to_move [body_args] in
      let new_gname = (gn) ^ "_" ^ (pn) in
      let new_body = `FCall (new_gname, map (fun n -> `Var n) mo_body_args) in
      let new_classes = divide_by_name (gen_dpgr_l (move_constr_forward numb_to_move new_dp_l_l) dpgr_list new_gname) in
      `GRule(new_def => new_body) :: concat (map to_SLL new_classes)
    else
      begin match dpgr_list with
      | (x::[]) -> [(`GRule (new_def => body))]
      | _ -> raise (Translation_error "conflict") end
  |_ -> raise (Translation_error "")

let elim_deep_pat x = 
  let fs, gs =
    fold_left (fun (fs, gs) -> 
                 function (`DPGRule _) as y -> fs, y::gs |(`FRule _) as y -> y::fs, gs 
              ) 
              ([], []) 
              x
  in
  (fs :: (map to_SLL (divide_by_name gs)))

let resolve_rule name pat body =
  let to_id = function
    | `PArg pn -> pn
    | _ -> raise (Translation_error "") in
  if List.for_all is_PArg pat
  then `FRule (name >$ (List.map to_id pat) >= body)
  else `DPGRule (name, [`PCtr ("AllArgs", pat)], body)

ostap (
  dp_g_rule[expr_parser][dp_parser]:
    name:ident -"(" pat:list0[dp_parser] -")"
        -"=" gbody:expr_parser
    { resolve_rule name pat gbody }
  ;
  deep_pat[dp_parser]: 
      name:ident { `PArg name }
    | pname:cnt pargs:dp_args[dp_parser]  { `PCtr (pname, pargs) }
  ;
  dp_args[dp_parser]: 
    pargs:(-"(" list0[dp_parser] -")")? { list_of_opt pargs }
  )

ostap (
  dp_decl[expr_parser][dp_parser]: 
    defs: (dp_g_rule[expr_parser][dp_parser])* {elim_deep_pat defs}
)

let rec dp_parser xs = deep_pat dp_parser xs
let rec dp_decl_parser = dp_decl pure_expr_parser dp_parser
let dp_program_parser = program_parser dp_decl_parser pure_term_pure_expr_parser

let rec to_AllArgs = function
  | `GCall (gname, parg, gargs) ->
       `GCall (gname, `Ctr ("AllArgs", ((to_AllArgs parg) :: (List.map to_AllArgs gargs))), [])
  | x -> x

let parse source_text cont =
  Combinators.unwrap (dp_program_parser (new lexer source_text))
    (fun program -> cont (resolve_gcalls to_AllArgs program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 5) `Acc reason))

let example =
 "g(K(S(x, y), o, S(z, S(z1, z2))), l, A(a))=F(x,y,o,z,z1,z2,l,a)\n"
  ^ "g(K(Z, l, b), a, M(o))=T(a,b,o)\n"
  ^ "g(Z, A, c)=T(c,c,c)\n"
  ^ "g(Z, Z, c)=T(c,c,c)\n"
  ^ "g(Z, H, C(A))=T(z,z,z)\n"
  ^ "lk(z, H, C(A))=T(z,z,z)\n"
  ^ "f()=K(S(X,Y),O,S(Z, S(Z1, Z2)))\n"
  ^ "f1()=K(Z,L,B)\n"
  ^ "f2(a)=K(Z,L,B)\n"
  ^ ".\n"
  ^ "g(f(), L, A(A))"

let verbose_test () =
  Combinators.unwrap (dp_program_parser (new lexer example))
    (fun program ->
      printf "Parsed program:\n%s\n" (string_of_program string_of_pure program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 3) `Acc reason))

let big_test () =
  Combinators.unwrap (dp_program_parser (new lexer example))
    (fun program ->
       let result = Interpret.run (resolve_gcalls to_AllArgs program) in
       printf "%s\n" (string_of_pure result))
    (fun _ -> ())
