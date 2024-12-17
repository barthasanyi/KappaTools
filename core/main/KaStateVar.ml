
open Kappa_grammar.Ast

(* Random helpers and things *)

exception Internal_error;;

type agent_port = string * string

let compare_string = String.compare

module APMap = Map.Make(struct type t = string * string [@@deriving compare] end)

module StringMap = Map.Make(String)

let list_of_list_opt l =
  match l with
  | None -> []
  | Some l -> l

let list_opt_of_list l =
  match l with
  | [] -> None
  | (_:_) as l -> Some l

let combine_list_opts l1 l2 = (list_of_list_opt l1) @ (list_of_list_opt l2)
  
let list_to_map empty update i =
    List.fold_left 
      (fun m (k,v) -> update k (fun o -> list_opt_of_list (combine_list_opts (list_opt_of_list v) o)) m) 
      empty 
      i

(* Slow intersection implementation for list of lists*)

let bin_intersection l1 l2 = List.filter (fun e -> List.mem e l2) l1   
let list_intersection (sets : 'a list list) : 'a list =
    match sets with
    | [] -> raise Internal_error
    | (s::sets) -> List.fold_left bin_intersection s sets

(* Cartesian product for StringMap of lists *)

let cartesian_on_string_maps string_map =
  StringMap.fold
    (fun key vs partial_map_seq -> 
      List.concat_map 
        (fun partial_map ->
          List.map
            (fun v -> StringMap.add key v partial_map) 
            vs
        )
        partial_map_seq 
    ) 
    string_map 
    [StringMap.empty]
  
(* helpers end here *)

(* Collecting possible states for each agent/site froom signatures.
   Building a string * string -> string list map,
   mapping agent name * site name -> list of states. *)

let states_to_state_names states =
   List.filter_map 
    (function 
        | StateName name -> Some name 
        | StateVar _ -> None 
        | StateAny -> None) states
   
let rec states_of_site_list agent sites =  
    match sites with
    | [] -> []
    | (Port port::sites) -> 
      List.cons 
        ((agent,fst port.port_name), states_to_state_names (List.map fst port.port_int))
        (states_of_site_list agent sites)
    | (Counter _ :: sites) -> states_of_site_list agent sites

let rec collect_agent_sigs parsing_instructions =
    match parsing_instructions with
    | [] -> []
    | (pi::pis) ->
      match pi with 
      | SIG (Present ((agent,_),sites,_mods)) -> (states_of_site_list agent sites) @ (collect_agent_sigs pis)
      | SIG (Absent _) | 
        (TOKENSIG (_,_)|VOLSIG (_, _, _)|
        INIT ((_,_), _)|
        DECLARE
          ((_,_),
          (_,_))|
        OBS
          ((_,_),
          (_,_))|
        PLOT (_,_)|
        PERT ((_, _, _, _),_)|
        CONFIG ((_,_), _)|
        RULE (_, (_,_))) -> collect_agent_sigs pis

let create_agent_sig_map parsing_instructions =
  collect_agent_sigs parsing_instructions |> list_to_map APMap.empty APMap.update

(* Collect state vars for a rule together with its agent/site names. *)
let states_to_state_vars states =
  List.filter_map  
   (function 
      | StateName _ -> None
      | StateVar var -> Some var
      | StateAny -> None) states ;;

let state_vars_of_port agent_name port =
  let agent_port = (agent_name,fst port.port_name) in
  List.map (fun sv -> (sv,[agent_port])) (states_to_state_vars (List.map fst port.port_int))

let state_vars_of_site agent_name site =
    match site with
    | Port port -> state_vars_of_port agent_name port
    | Counter _ -> []

let state_vars_of_agent agent =
     match agent with
     | Present ((agent_name,_),site_list,_) -> List.concat (List.map (state_vars_of_site agent_name) site_list)
     | Absent _ -> []

let state_vars_of_mixture mixture =  List.concat_map state_vars_of_agent (List.concat mixture)

let rec state_vars_of_expr (expr : (mixture, string) Kappa_terms.Alg_expr.e) =
  match expr with
  | STATE_ALG_OP _ | ALG_VAR _| TOKEN_ID _ | CONST _ -> []
  | BIN_ALG_OP (_ , (expr1,_), (expr2,_)) -> 
    state_vars_of_expr expr1 @ 
    state_vars_of_expr expr2
  | UN_ALG_OP (_, (expr,_)) -> 
    state_vars_of_expr expr
  | KAPPA_INSTANCE mix -> state_vars_of_mixture mix    
  | IF ((b,_),(expr1,_),(expr2,_)) -> 
    state_vars_of_bool b @
    state_vars_of_expr expr1 @
    state_vars_of_expr expr2 
  | DIFF_TOKEN ((expr,_),_) -> state_vars_of_expr expr
  | DIFF_KAPPA_INSTANCE ((expr,_),mix) ->
    state_vars_of_expr expr @
    state_vars_of_mixture mix
and state_vars_of_bool b =
  match b with
  | TRUE | FALSE -> []      
  | BIN_BOOL_OP (_ ,(b1,_),(b2,_)) -> state_vars_of_bool b1 @ state_vars_of_bool b2
  | UN_BOOL_OP (_, (b,_)) -> state_vars_of_bool b
  | COMPARE_OP (_,(expr1,_),(expr2,_)) -> state_vars_of_expr expr1 @ state_vars_of_expr expr2
let state_vars_of_token_list tokens =
  List.concat_map (fun ((token,_),_) -> state_vars_of_expr token) tokens

let state_vars_of_rule_content rule_content =
    match rule_content with
    | Edit edit -> 
      state_vars_of_mixture edit.mix @
      state_vars_of_token_list edit.delta_token
    | Arrow arrow ->  
      state_vars_of_mixture (arrow.lhs @ arrow.rhs) @
      state_vars_of_token_list (arrow.rm_token @ arrow.add_token)

let state_vars_of_opt_expr opt_expr =
  match opt_expr with
  | None -> []
  | Some (expr,_) -> state_vars_of_expr expr

let state_vars_of_k_un k_un =
    match k_un with
    | None -> []
    | Some ((expr,_),opt_expr) -> 
      state_vars_of_expr expr @
      state_vars_of_opt_expr opt_expr
let state_vars_of_rule rule =
  state_vars_of_rule_content rule.rewrite @
  state_vars_of_expr (fst rule.k_def) @  
  state_vars_of_k_un rule.k_un @
  state_vars_of_opt_expr rule.k_op @
  state_vars_of_k_un rule.k_op_un

 (* Substitution *)   

let subst_on_rule rule substs =
  let subst_on_state state =
    match state with
    | StateName _ | StateAny -> state
    | StateVar v ->      
      match StringMap.find_opt v substs with
      | None -> assert false
      | Some n -> StateName n in
  let subst_on_internal internal =
    List.map (fun (state,loc) -> (subst_on_state state,loc)) internal in
  let subst_on_port port =
    {port with port_int = subst_on_internal port.port_int} in
  let subst_on_site site =
    match site with
    | Port port -> Port (subst_on_port port)
    | Counter _ as c -> c in
  let subst_on_agent agent = 
    match agent with
    | Present (name,sites,mods)-> Present (name,List.map subst_on_site sites,mods)    
    | Absent _ as abs -> abs
    in        
  let subst_on_mixture = List.map (List.map subst_on_agent) in
  let rec subst_on_expr (expr : (mixture, string) Kappa_terms.Alg_expr.e) =
    match expr with
    | STATE_ALG_OP _  | ALG_VAR _| TOKEN_ID _ | CONST _ ->
      expr
    | BIN_ALG_OP (op , expr1, expr2) ->
      BIN_ALG_OP (op, subst_on_expr_loc expr1, subst_on_expr_loc expr2)
    | UN_ALG_OP (op, expr) ->
      UN_ALG_OP (op, subst_on_expr_loc expr)
    | KAPPA_INSTANCE mix ->
      KAPPA_INSTANCE (subst_on_mixture mix)
    | IF (b,expr1,expr2) ->
      IF (subst_on_bool_loc b,subst_on_expr_loc expr1,subst_on_expr_loc expr2)
    | DIFF_TOKEN (expr,id) ->
      DIFF_TOKEN (subst_on_expr_loc expr,id)
    | DIFF_KAPPA_INSTANCE (expr,mix) ->
      DIFF_KAPPA_INSTANCE (subst_on_expr_loc expr, subst_on_mixture mix)
  and subst_on_expr_loc (expr,loc) = (subst_on_expr expr,loc)
  and subst_on_bool (b : (mixture,string) Kappa_terms.Alg_expr.bool) =
    match b with
    | TRUE | FALSE ->
      b
    | BIN_BOOL_OP (op ,b1,b2) ->
      BIN_BOOL_OP (op ,subst_on_bool_loc b1,subst_on_bool_loc b2)
    | UN_BOOL_OP (op, b) ->
      UN_BOOL_OP (op, subst_on_bool_loc b)
    | COMPARE_OP (op,expr1,expr2) ->
      COMPARE_OP (op,subst_on_expr_loc expr1,subst_on_expr_loc expr2) 
  and subst_on_bool_loc (b,loc) = (subst_on_bool b,loc) in
  let subst_on_token_list tokens =
    List.map (fun (expr_loc,id) -> ((subst_on_expr_loc expr_loc),id)) tokens in
  let subst_on_edit (edit : edit_notation) =
     {
      mix = subst_on_mixture edit.mix;
      delta_token = subst_on_token_list edit.delta_token
     } in
  let subst_on_arrow (arrow : arrow_notation) =      
      {
          lhs = subst_on_mixture arrow.lhs; 
          rm_token = subst_on_token_list arrow.rm_token;
          rhs = subst_on_mixture arrow.rhs; 
          add_token = subst_on_token_list arrow.add_token
      } in
  let subst_on_rule_content (rc : rule_content) =
    match rc with
    | Arrow arrow -> Arrow (subst_on_arrow arrow)
    | Edit edit -> Edit (subst_on_edit edit) in
  let subst_on_expr_loc_opt expr_opt =
    match expr_opt with
    | None -> None
    | Some expr -> Some (subst_on_expr_loc expr) in
  let subst_on_k_un k_un =
    match k_un with
    | None -> None
    | Some (expr,expr_opt) -> Some (subst_on_expr_loc expr,subst_on_expr_loc_opt expr_opt) in
  {
    rewrite = subst_on_rule_content rule.rewrite;
    bidirectional = rule.bidirectional;
    k_def = subst_on_expr_loc rule.k_def;
    k_un = subst_on_k_un rule.k_un;
    k_op = subst_on_expr_loc_opt rule.k_op;
    k_op_un = subst_on_k_un rule.k_op_un
  }  
let expand_rule ap_states_map rule =
  let var_aps_map : agent_port list StringMap.t = 
      state_vars_of_rule rule |> list_to_map StringMap.empty StringMap.update in
  let state_var_to_states = StringMap.map (fun ap_list ->
      list_intersection 
          (List.map (fun ap -> list_of_list_opt (APMap.find_opt ap ap_states_map)) ap_list)
    ) var_aps_map in
  let bindings_list = cartesian_on_string_maps state_var_to_states in
  List.map (subst_on_rule rule) bindings_list
  
let expand_parsing_instruction ap_map pi =  
    match pi with 
        | SIG _
        | TOKENSIG (_,_)
        | VOLSIG (_, _, _)
        | INIT (_, _)
        | DECLARE (_,_)
        | OBS (_,_)
        | PLOT (_,_)
        | PERT (_,_)
        | CONFIG (_, _)-> [pi]
        | RULE (name,(rule,loc)) -> 
            let convert_name name ix =
              match name with
              | None -> None
              | Some (name,loc) -> Some (name ^ "_" ^ (string_of_int ix),loc) in
         List.map 
            ( let counter = ref 0 in
              fun rule ->
                counter := !counter + 1 ;
                RULE (convert_name name !counter,(rule,loc))
            )
            (expand_rule ap_map rule) ;;
                  
(* Shell script for expanding site variables. 
   Reads a kappa file with site variables from stdin.
   Writes an expanded kappa file without site variables to stdout. *)

(* 1. Parsing *)
let lexbuf = Lexing.from_channel stdin in
let ast = Kappa_grammar.Kparser4.model Kappa_grammar.Klexer4.token lexbuf in
(* 2. Gathering list of states for each agent/port from signature. *)
let ap_map = create_agent_sig_map ast in
(* 3. Transform AST *)
let transformed_ast = List.concat_map (expand_parsing_instruction ap_map) ast in
(* 4. Pretty printing *)
let cst = Kappa_grammar.Cst.append_to_ast_compil transformed_ast empty_compil in
  print_parsing_compil_kappa Format.std_formatter cst