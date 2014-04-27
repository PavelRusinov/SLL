open Printf
open Ostap
open Util
open Matcher
open Sll
open Deep_pattern

let ident = ostap (n:IDENT {Token.repr n})
let cnt = ostap (c:CNT {Token.repr c})

let list_of_opt = function
  | Some xs -> xs
  | None    -> []

let resolve_rule name pat body =
  let to_id = function
    | `PArg pn -> pn
    | _ -> raise (Translation_error ("")) in
  let is_g = List.exists is_PCtr pat in
    match is_g with
      | true  -> `DPGRule (name, [`PCtr ("AllArgs", pat)], body)
      | false -> `FRule (name >$ (List.map to_id pat) >= body)
    
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
      let (fdefs, gdefs) = defs_splitter (Deep_pattern.elim_deep_pat defs) in
      make_program fdefs gdefs term
    }
  ;
  fun_def[e_parser][dp_parser]:
    name:ident -"(" pat:list0[dp_parser] -")"
        -"=" gbody:e_parser
    { resolve_rule name pat gbody }
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

let rec to_AllArgs = function
  | `GCall (gname, parg, gargs) -> 
       `GCall (gname, `Ctr ("AllArgs", ((to_AllArgs parg) :: (List.map to_AllArgs gargs))), [])
  | x -> x
  
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
  { fdefs = resolved_fdefs; gdefs = resolved_gdefs; term = to_AllArgs (resolve_expr term); }

let parse source_text cont =
  Combinators.unwrap (program_parser (new lexer source_text))
    (fun program -> cont (resolve_gcalls program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 5) `Acc reason))

let example =
    "g(K(S(x, y), o, S(z, S(z1, z2))), l, A(a))=F(x,y,o,z,z1,z2,l,a)\n"
  ^ "g(K(Z, l, b), a, M(o))=T(a,b,o)\n"
  ^ "g(Z, A, c)=T(c,c,c)\n"
  ^ "g(Z, Z, c)=T(c,c,c)\n"
  ^ "g(Z, H, C(A))=T(z,z,z)\n"
  ^ "f()=K(S(X,Y),O,S(Z, S(Z1, Z2)))\n"
  ^ "f1()=K(Z,L,B)\n"
  ^ ".\n"
  ^ "g(f(), L, A(A))" 

let big_example = string_of_program string_of_pure Arithm.program

let verbose_test () =
  Combinators.unwrap (program_parser (new lexer example))
    (fun program ->
      printf "Parsed program:\n%s\n" (string_of_program string_of_pure (resolve_gcalls program)))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 3) `Acc reason))

let big_test () =
  Combinators.unwrap (program_parser (new lexer example))
    (fun program ->
       let result = Interpret.run (resolve_gcalls program) in
       printf "%s\n" (string_of_pure result))
    (fun _ -> ())
