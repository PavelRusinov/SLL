open Printf
open Ostap
open Util
open Matcher
open Sll

exception Translation_error of string

let ident = ostap (n:IDENT {Token.repr n})
let cnt = ostap (c:CNT {Token.repr c})

let list_of_opt = function
  | Some xs -> xs
  | None    -> []

let to_arg = function
  | Some x -> x
  | None   -> `Empty

let resolve_rule name pat args body =
  match pat with
  | `PArg pname          -> `FRule (name >$ (pname :: args) >= body)
  | `PCtr (pname, pargs) -> `DPGRule (name, pat, args, body)
  | `Empty -> `FRule (name >$ [] >= body)

let rec toSLL acc gn p gargs b =
  let to_id x = 
    match x with
    | `PArg n -> n
    | `PCtr (n, _) -> (String.lowercase n) ^ "_arg"
    | `Empty -> raise (Translation_error ("")) in
  let rec id_list x = List.map to_id x in
  let rec var_list x = List.map (fun n -> `Var (to_id n)) x in
    match p with
     | `PCtr (n, ((`PCtr (n1, l) :: xs) as pargs)) -> 
       let body_args = (var_list pargs) @ (List.map (fun n -> `Var n) gargs) in 
       let new_gname = (gn ^ "_" ^ n) in
       let new_def = `GRule (gn $ (n +> (id_list pargs), gargs) => (`FCall (new_gname, body_args))) in
         toSLL (new_def :: acc) new_gname (`PCtr (n1,l)) ((id_list xs) @ gargs) b
     | `PCtr (n, pargs)      -> `GRule (gn $ (n +> (id_list pargs), gargs) => b) :: acc
     | `PArg name            -> raise (Translation_error (""))
     | `Empty            -> raise (Translation_error (""))


let elim_deep_pat x =
  let elim_helper = function
    | `FRule (fn, b) -> [`FRule (fn, b)]
    | `DPGRule (gn, p, a, b) -> (toSLL [] gn p a b) in
List.concat (List.map elim_helper x)

let defs_splitter xs =
  let rec helper defs fdefs gdefs =
    match defs with
    | (`FRule (fn, b) :: smth)     -> helper smth ((fn, b) :: fdefs) gdefs
    | (`GRule (gn, pn, b) :: smth) -> helper smth fdefs ((gn, pn, b) :: gdefs)
    | []                           -> (fdefs, gdefs)
  in helper xs [] []

ostap (
  program_parser[e_parser][dp_parser]:
    defs:(fun_def[e_parser][dp_parser])* -"." term:expression[e_parser] {
      let (fdefs, gdefs) = defs_splitter (elim_deep_pat defs) in
      make_program fdefs gdefs term
    }
  ;
  fun_def[e_parser][dp_parser]:
    name:ident -"(" pat:(deep_pat[dp_parser])? gargs:(-"," ident)* -")"
        -"=" gbody:e_parser
    { resolve_rule name (to_arg pat) gargs gbody }
  ;
  args_list[e_parser]: -"(" list0[e_parser] -")"
  ;
  deep_pat[dp_parser]: 
      name:ident {`PArg name}
    | pname:cnt pargs:dp_args[dp_parser]  {`PCtr (pname, pargs)}
  ;
  dp_args[dp_parser]: 
    pargs:(-"(" list0[dp_parser] -")")? { list_of_opt pargs }
  ;
  expression[e_parser]:
      constructor[e_parser]
    | fun_call[e_parser]
    | v:ident  { `Var v }
  ;
  ident_ctr_args:
    pargs:(-"(" list0[ident] -")")? { list_of_opt pargs }
  ;
  constructor[e_parser]:
    cname:cnt  args:args_list[e_parser]?
    { `Ctr cname (list_of_opt args) }
  ;
  fun_call[e_parser]:
    name:ident args:args_list[e_parser]
    { `FCall (name, args) }
)

class lexer s =
  let skip  = Skip.create [Skip.whitespaces " \n\t\r"] in
  let ident = Str.regexp "[a-z][a-zA-Z0-9]*" in
  let cnt = Str.regexp "[A-Z][a-zA-Z0-9]*" in
  object (self)

    inherit t s

    method skip p c = skip s p c
    method getIDENT = self#get "identifier" ident
    method getCNT   = self#get "constructor" cnt

  end

let rec pure_parser xs = expression pure_parser xs
let rec dp_parser xs = deep_pat dp_parser xs
let program_parser = program_parser pure_parser dp_parser

let resolve_gcalls { fdefs = fdefs; gdefs = gdefs; term = term; } =
  let rec resolve_expr = function
    | `FCall (name, parg :: args) when not (Ident_map.mem name fdefs) ->
        `GCall (name, resolve_expr parg, List.map resolve_expr args)
    | `FCall (fname, fargs) -> `FCall (fname, List.map resolve_expr fargs)
    | `GCall (gname, pname, gargs) -> `GCall (gname, pname, gargs)
    | `Ctr (cname, cargs) -> `Ctr (cname, List.map resolve_expr cargs)
    | `Var name -> `Var name
  in
  let resolved_fdefs = Ident_map.map (fun { fargs = fargs; fbody = fbody; } ->
    { fargs = fargs; fbody = resolve_expr fbody } ) fdefs
  in
  let resolved_gdefs = Ident_map.map (fun gpdefs ->
    Ident_map.map (fun { pargs = pargs; gargs = gargs; gbody = gbody; } ->
      { pargs = pargs; gargs = gargs; gbody = resolve_expr gbody; })
      gpdefs) gdefs
  in
  { fdefs = resolved_fdefs; gdefs = resolved_gdefs; term = resolve_expr term; }

let parse source_text cont =
  Combinators.unwrap (program_parser (new lexer source_text))
    (fun program -> cont (resolve_gcalls program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 5) `Acc reason))

let example =
    "g(S(S(x, y),a))=F(x,y,a)\n"
  ^ "g(S(Z, b))=T\n"
  ^ "g(Z)=T\n"
  ^ "f()=S(S(X,Y),A)\n"
  ^ ".\n"
  ^ "g(f())"

let big_example = string_of_program string_of_pure Arithm.program

let verbose_test () =
  Combinators.unwrap (program_parser (new lexer example))
    (fun program ->
      printf "Parsed program:\n%s\n" (string_of_program string_of_pure program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 3) `Acc reason))

let big_test () =
  Combinators.unwrap (program_parser (new lexer example))
    (fun program ->
       let result = Interpret.run (resolve_gcalls program) in
       printf "%s\n" (string_of_pure result))
    (fun _ -> ())
