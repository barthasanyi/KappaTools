
open Kappa_grammar.Ast

(* Random helpers and things *)

exception Unsupported_language_construct;;
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

(* Collect list of state vars for a rule, adding agent/site names. *)

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

let state_vars_of_rule rule =
    match rule.rewrite with
    | Edit _ -> raise Unsupported_language_construct
    | Arrow arrow -> List.concat_map state_vars_of_agent (List.concat (arrow.lhs @ arrow.rhs))
  
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
  let subst_on_arrow
        (arrow : arrow_notation) =
      let () = assert (arrow.rm_token = [] && arrow.add_token = []) in
      {arrow with 
          lhs = subst_on_mixture arrow.lhs; 
          rhs = subst_on_mixture arrow.rhs 
      } in
  let subst_on_rule_content (rc : rule_content) =
    match rc with
    | Arrow arrow -> Arrow (subst_on_arrow arrow)
    | Edit _ -> raise Unsupported_language_construct in
  {rule with rewrite = subst_on_rule_content rule.rewrite}  
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