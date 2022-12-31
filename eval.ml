open Ast

exception TypeError
exception UndefinedVar
exception DivByZeroError

(* Remove shadowed bindings *)
let prune_env (env : environment) : environment =
  let binds = List.sort_uniq compare (List.map (fun (id, _) -> id) env) in
  List.map (fun e -> (e, List.assoc e env)) binds

(* Env print function to stdout *)
let print_env_std (env : environment): unit =
  List.fold_left (fun _ (var, value) ->
      match value with
        | Int_Val i -> Printf.printf "- %s => %s\n" var (string_of_int i)
        | Bool_Val b -> Printf.printf "- %s => %s\n" var (string_of_bool b)
        | Closure _ -> ()) () (prune_env env)

(* Env print function to string *)
let print_env_str (env : environment): string =
  List.fold_left (fun acc (var, value) ->
      match value with
        | Int_Val i -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_int i))
        | Bool_Val b -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_bool b))
        | Closure _ -> acc
      ) "" (prune_env env)


(***********************)
(****** Your Code ******)
(***********************)

let sub (x,y) =
  match (x,y) with 
  | Int_Val x, Int_Val y -> Int_Val (x-y)
  | _ -> raise (TypeError);;

let plus (x,y) =
  match (x,y) with 
  | Int_Val x, Int_Val y -> Int_Val (x+y)
  | _ -> raise (TypeError);;

let mult (x,y) =
  (match (x,y) with 
  | Int_Val x, Int_Val y -> Int_Val (x*y)
  | _ -> raise (TypeError));;

let div (x,y) =
  (match (x,y) with 
  | Int_Val x, Int_Val y -> if y!=0 then Int_Val (x/y) else raise (DivByZeroError)
  | _ -> raise (TypeError));;

let md (x,y) =
 match (x,y) with 
  | Int_Val x, Int_Val y -> Int_Val (x mod y)
  | _ -> raise (TypeError);;

let lt (x,y)=
  match (x,y) with
  | Int_Val x, Int_Val y -> if x<y then Bool_Val true else Bool_Val false
  | _ -> raise (TypeError);;

let lesseq (x,y)=
  match (x,y) with
  | Int_Val x, Int_Val y -> if x<=y then Bool_Val true else Bool_Val false
  | _ -> raise (TypeError);;

let equ (x,y) =
  match (x,y) with
  | Int_Val x, Int_Val y -> if x=y then Bool_Val true else Bool_Val false
  | Bool_Val x, Bool_Val y -> if x=y then Bool_Val true else Bool_Val false
  | _ -> raise (TypeError);; 

let not (x) =
  match x with
  | Bool_Val x -> if x = false then Bool_Val true else Bool_Val false
  | _-> raise (TypeError);;

let fand (x,y) =
  match x,y with
  |Bool_Val x, Bool_Val y -> Bool_Val (x&&y)
  | _-> raise (TypeError);;

let fOr (x,y) =
 match x,y with
  |Bool_Val x, Bool_Val y -> Bool_Val (x||y)
  | _-> raise (TypeError);;

let rec fvar (x) (env:environment) =
  (match env with  
  [] -> raise (UndefinedVar) 
  | (a,b)::t -> if a=x then b else fvar x t);;

 

(* evaluate an arithmetic expression in an environment *)
let rec eval_expr (e : exp) (env : environment) : value =
    match e with 
    | Number x-> Int_Val x
    | True -> Bool_Val true
    | False -> Bool_Val false
    | Var x -> fvar x env
    | Plus (x,y) -> plus (eval_expr x env, eval_expr y env)
    | Minus (x,y) -> sub (eval_expr x env, eval_expr y env)
    | Times (x,y) -> mult (eval_expr x env, eval_expr y env)
    | Div (x,y) -> div (eval_expr x env, eval_expr y env)
    | Mod (x,y) -> md (eval_expr x env, eval_expr y env)
    | Lt (x,y) -> lt (eval_expr x env, eval_expr y env)
    | Leq (x,y) -> lesseq(eval_expr x env, eval_expr y env)
    | Eq (x,y) -> equ (eval_expr x env, eval_expr y env)
    | Not (x) -> not (eval_expr x env)
    | And (x,y) -> fand (eval_expr x env, eval_expr y env)
    | Or (x,y) -> fOr (eval_expr x env, eval_expr y env)
    | Fun (x,y) -> Closure (env, x, y)
    | App (e1, e2) ->  let newFun= eval_expr e1 env in let newFun2 =  eval_expr e2 env in 
                      (match newFun with
                      | Closure (e, str, expr) -> let newEnv = (str, newFun2):: e in eval_expr expr newEnv);;
  


let fdeclare (x,y) env = 
  if x = Int_Type then (y, Int_Val 0) :: env
  else if x=Bool_Type then (y, Bool_Val false) :: env
  else (y, Closure(env, "x", Var "x")) :: env ;;


let fcond (x,(y:environment),(z:environment)) env =
  let a = eval_expr x env in 
  if a= Bool_Val true then y
  else if a=Bool_Val false then z
  else raise (TypeError);;


let rec fassg x e2val env =
 ( match env with
     [] -> raise UndefinedVar
    | (str, v) :: t -> 
       if x = str then
            match v, e2val with
           | Int_Val x, Int_Val y -> (str, e2val) :: t
           | Bool_Val x, Bool_Val y -> (str, e2val) :: t
           | Closure (e, s, expr), Closure(e2, s2, expr2) -> (str,e2val) :: t
           | _ -> raise TypeError
       else (str, v) :: fassg x e2val t);;


(* evaluate a command in an environment *)
let rec eval_command (c : com) (env : environment) : environment =
    match c with
    | Skip -> env 
    | Comp (x,y) -> let z = eval_command x env in eval_command y z
    | Declare (x,y) ->  fdeclare (x,y) env 
    | Cond (x,y,z) -> fcond (x, eval_command y env, eval_command z env) env
    | Assg (x,y) -> let e2val = eval_expr y env in fassg x e2val env 
    | While (x, y) -> let a = eval_expr x env in
                  (match a with
                  | Bool_Val true -> eval_command c (eval_command y env) 
                  | Bool_Val false -> env
                  | _ -> raise TypeError)
    | For (x,y) ->  let n = eval_expr x env in (match n with 
                    | Int_Val t -> if t > 0 then let nTimes = t - 1 in let newCom = For(Number nTimes, y) 
                    in let newEnv = eval_command y env in eval_command newCom newEnv
                    else env) ;;

   




  

