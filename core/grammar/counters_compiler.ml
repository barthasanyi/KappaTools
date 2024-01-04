(******************************************************************************)
(*  _  __ * The Kappa Language                                                *)
(* | |/ / * Copyright 2010-2020 CNRS - Harvard Medical School - INRIA - IRIF  *)
(* | ' /  *********************************************************************)
(* | . \  * This file is distributed under the terms of the                   *)
(* |_|\_\ * GNU Lesser General Public License Version 3                       *)
(******************************************************************************)

type 'a with_agent_counters = {
  agent: 'a;
  counters: (Ast.counter * LKappa.switching) option array;
}

type rule_mixture_with_agent_counters =
  LKappa.rule_agent with_agent_counters list

type raw_mixture_with_agent_counters =
  Raw_mixture.agent with_agent_counters list

(** [combinations_of_var_setup ls1 ls2]
 * Each element of [ls1] describes a setup of counter variables, with the first element of the tuple being the list of entities to be used in the model, where variables have been removed from counters, and the second one the mapping of variables to their values, that allows to know which instance of model entities would be chosen in this given setup.
 * [ls2] adds a new entity with different kinds according to the variable values given in the list as second member of the tuple, which is then combined in this function with the other setups, combining the different variable values which those already defined.
 * No check is done on the unicity of the described variables and their values *)
let combinations_of_var_setup (ls1 : ('a list * 'b list) list)
    (ls2 : ('a * 'b list) list) : ('a list * 'b list) list =
  if ls1 = [] then
    List.fold_left (fun acc (b, ds) -> ([ b ], ds) :: acc) [] ls2
  else
    List.fold_left
      (fun acc (a, cs) ->
        List.fold_left (fun acc' (b, ds) -> (b :: a, ds @ cs) :: acc') acc ls2)
      [] ls1

let update_rate counter_var_values (k, a) =
  let update_id s k =
    let counters_matching_s, _ =
      List.partition (fun (s', _) -> String.compare s s' = 0) counter_var_values
    in
    match counters_matching_s with
    | [ (_, x) ] -> Alg_expr.CONST (Nbr.I x)
    | [] -> k
    | _ :: _ ->
      raise
        (ExceptionDefn.Malformed_Decl
           ("Counter variable " ^ s ^ " appears twice in rule", Loc.dummy))
  in
  let rec update_bool_expr k =
    match k with
    | Alg_expr.TRUE | Alg_expr.FALSE -> k
    | Alg_expr.BIN_BOOL_OP (op, (k1, a1), (k2, a2)) ->
      Alg_expr.BIN_BOOL_OP
        (op, (update_bool_expr k1, a1), (update_bool_expr k2, a2))
    | Alg_expr.UN_BOOL_OP (op, (k, a)) ->
      Alg_expr.UN_BOOL_OP (op, (update_bool_expr k, a))
    | Alg_expr.COMPARE_OP (op, (k1, a1), (k2, a2)) ->
      Alg_expr.COMPARE_OP (op, (update_expr k1, a1), (update_expr k2, a2))
  and update_expr k =
    match k with
    | Alg_expr.BIN_ALG_OP (op, (k1, a1), (k2, a2)) ->
      Alg_expr.BIN_ALG_OP (op, (update_expr k1, a1), (update_expr k2, a2))
    | Alg_expr.UN_ALG_OP (op, (k1, a1)) ->
      Alg_expr.UN_ALG_OP (op, (update_expr k1, a1))
    | Alg_expr.IF ((k1, a1), (k2, a2), (k3, a3)) ->
      Alg_expr.IF
        ((update_bool_expr k1, a1), (update_expr k2, a2), (update_expr k3, a3))
    | Alg_expr.DIFF_TOKEN ((k1, a1), k2) ->
      Alg_expr.DIFF_TOKEN ((update_expr k1, a1), k2)
    | Alg_expr.DIFF_KAPPA_INSTANCE ((k, a), m) ->
      Alg_expr.DIFF_KAPPA_INSTANCE ((update_expr k, a), m)
    | Alg_expr.ALG_VAR id | Alg_expr.TOKEN_ID id -> update_id id k
    | Alg_expr.STATE_ALG_OP _ | Alg_expr.CONST _ | Alg_expr.KAPPA_INSTANCE _ ->
      k
  in
  update_expr k, a

let collect_ids expr_list : Mods.StringSet.t =
  let rec aux_expr expr acc =
    match expr with
    | Alg_expr.BIN_ALG_OP (_, (k1, _), (k2, _)) -> aux_expr k2 (aux_expr k1 acc)
    | Alg_expr.UN_ALG_OP (_, (k1, _))
    | Alg_expr.DIFF_TOKEN ((k1, _), _)
    | Alg_expr.DIFF_KAPPA_INSTANCE ((k1, _), _) ->
      aux_expr k1 acc
    | Alg_expr.IF ((k1, _), (k2, _), (k3, _)) ->
      aux_expr k3 (aux_expr k2 (aux_bool k1 acc))
    | Alg_expr.ALG_VAR id | Alg_expr.TOKEN_ID id -> aux_id id acc
    | Alg_expr.STATE_ALG_OP _ | Alg_expr.CONST _ | Alg_expr.KAPPA_INSTANCE _ ->
      acc
  and aux_id id acc = Mods.StringSet.add id acc
  and aux_bool expr acc =
    match expr with
    | Alg_expr.TRUE | Alg_expr.FALSE -> acc
    | Alg_expr.BIN_BOOL_OP (_, (k1, _), (k2, _)) ->
      aux_bool k2 (aux_bool k1 acc)
    | Alg_expr.UN_BOOL_OP (_, (k, _)) -> aux_bool k acc
    | Alg_expr.COMPARE_OP (_, (k1, _), (k2, _)) -> aux_expr k2 (aux_expr k1 acc)
  in
  List.fold_left
    (fun acc expr_opt ->
      match expr_opt with
      | None -> acc
      | Some (expr, _) -> aux_expr expr acc)
    Mods.StringSet.empty expr_list

let name_match (s, _) (s', _) = String.compare s s' = 0

let prepare_agent rsites lsites =
  let rec prepare_site sites c =
    match sites with
    | [] -> [ Ast.Counter c ]
    | hd :: tl ->
      (match hd with
      | Ast.Counter c' when name_match c.Ast.counter_name c'.Ast.counter_name ->
        Ast.Counter { c' with Ast.counter_delta = c.Ast.counter_delta } :: tl
      | Ast.Counter _ | Ast.Port _ -> hd :: prepare_site tl c)
  in
  let counters =
    List.fold_left
      (fun acc' rsite ->
        match rsite with
        | Ast.Port _ -> acc'
        | Ast.Counter c -> c :: acc')
      [] rsites
  in
  List.fold_left prepare_site lsites counters

(* - add in the lhs : (i) counters only mentioned in the rhs and (ii) the deltas
   - syntactic checks of no test in rhs; no modif in lhs *)
let prepare_counters rules =
  let check_syntax sites f error =
    List.iter
      (function
        | Ast.Port _ -> ()
        | Ast.Counter c ->
          if f c then
            raise
              (ExceptionDefn.Malformed_Decl
                 ( "Counter " ^ Loc.v c.Ast.counter_name ^ error,
                   Loc.get_annot c.Ast.counter_name )))
      sites
  in

  let rec prepare_lhs_rule rhs lhs =
    match rhs, lhs with
    | Ast.Present (rna, rsites, _) :: r, Ast.Present (lna, lsites, b) :: l ->
      check_syntax lsites
        (fun c -> not (Loc.v c.counter_delta = 0))
        " has a modif in the lhs";
      check_syntax rsites
        (fun c -> not (c.counter_test = None))
        " has a test in the rhs";
      if String.compare (Loc.v rna) (Loc.v lna) = 0 then (
        let lsites' = prepare_agent rsites lsites in
        Ast.Present (lna, lsites', b) :: prepare_lhs_rule r l
      ) else
        lhs
      (*TODO we stop our job here. LKappa_compiler will detect
        later that there is a problem *)
    | _ :: r, (Ast.Absent _ as lagent) :: l ->
      (*created agent*)
      (* TODO Maybe some syntax check on rhs are necessary here *)
      lagent :: prepare_lhs_rule r l
    | Ast.Absent _ :: r, (Ast.Present (_, lsites, _) as lagent) :: l ->
      (*deleted  agent*)
      check_syntax lsites
        (fun c -> not (Loc.v c.Ast.counter_delta = 0))
        " has a modif in the lhs";
      lagent :: prepare_lhs_rule r l
    | [], x ->
      x
      (* TODO x must be [] but it is for now LKappa_compiler
         duty to complain *)
    | _x, [] -> (*TODO let () = assert (_x = []) in*) []
  in

  let aux (rule : Ast.rule) : Ast.rule =
    match rule.rewrite with
    | Ast.Edit _ -> rule
    | Ast.Arrow content ->
      {
        rule with
        rewrite =
          Ast.Arrow
            {
              content with
              Ast.lhs =
                [
                  prepare_lhs_rule (List.flatten content.rhs)
                    (List.flatten content.lhs);
                ];
            };
      }
  in
  List.map (fun (s, (r, a)) -> s, (aux r, a)) rules

let counters_signature s agents =
  match
    List.find
      (function
        | Ast.Absent _ -> false
        | Ast.Present (s', _, _) -> name_match s s')
      agents
  with
  | Ast.Absent _ -> assert false
  | Ast.Present (_, sites', _) ->
    List.fold_left
      (fun acc s ->
        match s with
        | Ast.Counter c -> c :: acc
        | Ast.Port _ -> acc)
      [] sites'

(** [split_cvar_counter_in_rules_per_value var_name annot counter_delta counter_def] translates a counter CVAR whose value acts upon the rate expression into a rule per possible value, that are selected by a CEQ expression.
 * *)
let split_cvar_counter_in_rules_per_value (var_name : string) (annot : Loc.t)
    (counter_delta : int Loc.annoted) (counter_def : Ast.counter) :
    (Ast.site * (string * int) list) list =
  let max_value : int = Loc.v counter_def.counter_delta in
  let min_value : int =
    match counter_def.counter_test with
    | None | Some (Ast.CGTE _, _) | Some (Ast.CLTE _, _) | Some (Ast.CVAR _, _)
      ->
      raise
        (ExceptionDefn.Malformed_Decl
           ( "Invalid counter signature - have to specify min bound",
             Loc.get_annot counter_def.counter_name ))
    | Some (Ast.CEQ min_value, _) -> min_value
  in

  (* Make CEQ counters with all possible values of variable *)
  let rec make_ceq_counters_from_var_values (value : int) :
      (Ast.site * (string * int) list) list =
    if value > max_value then
      []
    else if
      value + Loc.v counter_delta <= max_value
      && value + Loc.v counter_delta >= 0
    then
      ( Ast.Counter
          {
            Ast.counter_name = counter_def.counter_name;
            counter_test = Some (Ast.CEQ value, annot);
            counter_delta;
          },
        [ var_name, value ] )
      :: make_ceq_counters_from_var_values (value + 1)
    else
      make_ceq_counters_from_var_values (value + 1)
  in
  make_ceq_counters_from_var_values min_value

let has_counters compil =
  List.exists
    (function
      | Ast.Absent _ -> false
      | Ast.Present (_, sites, _) ->
        List.exists
          (function
            | Ast.Counter _ -> true
            | Ast.Port _ -> false)
          sites)
    compil.Ast.signatures

(** [split_counter_variables_into_separate_rules] ~warning rules signatures] replaces counters with CVAR contraints with counters with CEQ contraints in [rules], in lists with the variable values associated, so that in simulation, correct counter conditions are being selected. The main operation happens in [split_cvar_counter_in_rules_per_value] *)
let split_counter_variables_into_separate_rules ~warning rules signatures =
  let split_for_each_counter_var_value_site ids counter_defs = function
    | Ast.Port p -> [ Ast.Port p, [] ]
    | Ast.Counter c ->
      let delta = Loc.v c.counter_delta in
      (match c.counter_test with
      | Some (Ast.CEQ value, _) ->
        if delta > 0 || abs delta <= value then
          [ Ast.Counter c, [] ]
        else
          raise
            (ExceptionDefn.Malformed_Decl
               ( "Counter " ^ Loc.v c.counter_name ^ " becomes negative",
                 Loc.get_annot c.counter_name ))
      | Some (Ast.CLTE _value, _annot) ->
        failwith "not implemented" (* TODO NOW *)
      | Some (Ast.CGTE value, annot) ->
        if value + delta < 0 then
          raise
            (ExceptionDefn.Malformed_Decl
               ( "Counter " ^ Loc.v c.counter_name ^ " becomes negative",
                 Loc.get_annot c.counter_name ));
        if value = 0 then (
          let error = "Counter " ^ Loc.v c.counter_name ^ ":>0 always holds" in
          warning ~pos:annot (fun f -> Format.pp_print_string f error)
        );
        [ Ast.Counter c, [] ]
      | Some (Ast.CVAR var_name, annot) when Mods.StringSet.mem var_name ids ->
        (* If the variable is present in an rate definition expression *)
        let counter_def : Ast.counter =
          List.find
            (fun counter ->
              name_match c.Ast.counter_name counter.Ast.counter_name)
            counter_defs
        in

        split_cvar_counter_in_rules_per_value var_name annot c.counter_delta
          counter_def
      | None | Some (Ast.CVAR _, _) ->
        if delta < 0 then (
          let counter_delta : Ast.counter =
            { c with counter_test = Some (Ast.CGTE (abs delta), Loc.dummy) }
          in
          [ Ast.Counter counter_delta, [] ]
        ) else
          [
            ( Ast.Counter { c with counter_test = Some (Ast.CGTE 0, Loc.dummy) },
              [] );
          ])
  in

  let rec split_for_each_counter_var_value_sites (ids : Mods.StringSet.t)
      (counter_defs : Ast.counter list) :
      Ast.site list -> (Ast.site list * (string * int) list) list = function
    | [] -> []
    | s :: t ->
      combinations_of_var_setup
        (split_for_each_counter_var_value_sites ids counter_defs t)
        (split_for_each_counter_var_value_site ids counter_defs s)
  in
  let split_for_each_counter_var_value_agent (ids : Mods.StringSet.t) :
      Ast.agent -> (Ast.agent * (string * int) list) list = function
    | Ast.Absent l -> [ Ast.Absent l, [] ]
    | Ast.Present (agent_name, sites, modif) ->
      let counter_defs = counters_signature agent_name signatures in
      let sites_for_each_counter_var_values =
        split_for_each_counter_var_value_sites ids counter_defs sites
      in
      List.map
        (fun (sites', var_values) ->
          Ast.Present (agent_name, sites', modif), var_values)
        sites_for_each_counter_var_values
  in
  let rec split_for_each_counter_var_value_mixture (ids : Mods.StringSet.t) :
      Ast.agent list -> (Ast.agent list * (string * int) list) list = function
    | [] -> []
    | ast_agent :: t ->
      combinations_of_var_setup
        (split_for_each_counter_var_value_mixture ids t)
        (split_for_each_counter_var_value_agent ids ast_agent)
  in

  let update_opt_rate counter_var_values = function
    | None -> None
    | Some r -> Some (update_rate counter_var_values r)
  in
  let update_pair_rate counter_var_values = function
    | None -> None
    | Some (r1, r2) ->
      Some
        ( update_rate counter_var_values r1,
          update_opt_rate counter_var_values r2 )
  in

  (* [split_for_each_counter_var_value_rule] rule evaluates for the rule in argument to a list of new rules set according to the value of a counter matching the value of a variable. This replaces tests of equality between a counter value and a variable with tests of equality between a counter value and integers in the counter value range *)
  let split_for_each_counter_var_value_rule
      (rule_name : string Loc.annoted option)
      ((rule, annot) : Ast.rule Loc.annoted) :
      (string Loc.annoted option * Ast.rule Loc.annoted) list =
    let mix_lhs =
      match rule.rewrite with
      | Ast.Edit content -> content.mix
      | Ast.Arrow content -> content.lhs
    in

    (* Fetch ids from rule rates *)
    let exprs_from_rates :
        (Ast.mixture, string) Kappa_terms.Alg_expr.e Loc.annoted option list =
      [ Some rule.k_def; rule.k_op ]
      @ (match rule.k_un with
        | None -> []
        | Some r_kun_rates -> [ Some (fst r_kun_rates); snd r_kun_rates ])
      @
      match rule.k_op_un with
      | None -> []
      | Some r_k_op_un_rates ->
        [ Some (fst r_k_op_un_rates); snd r_k_op_un_rates ]
    in
    let ids = collect_ids exprs_from_rates in

    let mixture_for_each_counter_var_value :
        (Ast.agent list * (string * int) list) list =
      split_for_each_counter_var_value_mixture ids (List.flatten mix_lhs)
    in
    List.map
      (fun (lhs, counter_var_values) ->
        (* Apply counter var values to rates *)
        let k_def = update_rate counter_var_values rule.k_def in
        let k_un = update_pair_rate counter_var_values rule.k_un in
        let k_op = update_opt_rate counter_var_values rule.k_op in
        let k_op_un = update_pair_rate counter_var_values rule.k_op_un in
        let lhs = [ lhs ] in
        let new_rule_name : string Loc.annoted option =
          if counter_var_values = [] then
            rule_name
          else (
            (* Build counters_ids_as_string, that will be used to build new rule names *)
            let counters_ids_as_string =
              List.fold_left
                (* TODO should we add a separator. maybe also add name of variable? *)
                  (fun acc (_, i) -> string_of_int i ^ acc)
                "" counter_var_values
            in

            match rule_name with
            | None -> None (* No rule name, new rules will have no name too *)
            | Some (rule_name_string, locality) ->
              (* Make a new name for new rule including counter_var_values info *)
              Some (rule_name_string ^ "__" ^ counters_ids_as_string, locality)
          )
        in

        ( new_rule_name,
          ( {
              Ast.rewrite =
                (match rule.rewrite with
                | Ast.Edit content -> Ast.Edit { content with Ast.mix = lhs }
                | Ast.Arrow content -> Ast.Arrow { content with Ast.lhs });
              bidirectional = rule.bidirectional;
              k_def;
              k_un;
              k_op;
              k_op_un;
            },
            annot ) ))
      mixture_for_each_counter_var_value
  in

  let rules = prepare_counters rules in

  List.fold_left
    (fun acc (rule_name, ((rule_content, _) as rule_annoted)) ->
      let new_rules_from_rule =
        if
          (* Per counter syntax, these rules cannot contain counter vars that need to be considered when removing CVAR counter tests *)
          match rule_content.Ast.rewrite with
          | Ast.Edit _ -> false
          | Ast.Arrow a -> a.lhs = []
        then
          [ None, rule_annoted ]
        else
          split_for_each_counter_var_value_rule rule_name rule_annoted
      in
      new_rules_from_rule @ acc)
    [] rules
  (* TODO: is rev relevant here? *)
  |> List.rev

let split_counter_variables_into_separate_rules ~warning ~debug_mode
    (compil : Ast.parsing_compil) =
  let rules =
    split_counter_variables_into_separate_rules ~warning compil.rules
      compil.signatures
  in
  (* Debug printing *)
  if debug_mode then (
    Format.printf "@.ast rules@.";
    List.iter
      (fun (s, (r, _)) ->
        let label =
          match s with
          | None -> ""
          | Some (l, _) -> l
        in
        Format.printf "@.%s = %a" label Ast.print_ast_rule r)
      rules
  );
  { compil with Ast.rules }

let make_rule_counter_agent sigs noted_as_erased link_with_switching_before
    link_with_switching_after loc : LKappa.rule_agent =
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b, port_a = counter_agent_info.ports in
  let ra_type = counter_agent_info.id in

  let ra_ports =
    Array.make counter_agent_info.arity
      (LKappa.LNK_FREE |> Loc.annotate loc, LKappa.Maintained)
  in
  ra_ports.(port_b) <- link_with_switching_before;
  ra_ports.(port_a) <- link_with_switching_after;
  let ra_ints = Array.make counter_agent_info.arity LKappa.I_ANY in
  {
    LKappa.ra_type;
    ra_erased = noted_as_erased;
    ra_ports;
    ra_ints;
    ra_syntax = Some (Array.copy ra_ports, Array.copy ra_ints);
  }

let make_raw_counter_agent (link_before : Raw_mixture.link)
    (link_after : Raw_mixture.link) (sigs : Signature.s) : Raw_mixture.agent =
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b, port_a = counter_agent_info.ports in
  let ports = Array.make counter_agent_info.arity Raw_mixture.FREE in
  let internals =
    Array.init counter_agent_info.arity (fun i ->
        Signature.default_internal_state counter_agent_info.id i sigs)
  in
  ports.(port_b) <- link_before;
  ports.(port_a) <- link_after;
  {
    Raw_mixture.a_type = counter_agent_info.id;
    Raw_mixture.a_ports = ports;
    Raw_mixture.a_ints = internals;
  }

let make_rule_agent_counter_test_chain (sigs : Signature.s) (nb : int)
    (first_link_type : int * int) (noted_as_erased : bool)
    (test_is_equality : bool) (link : int) (loc : Loc.t) (delta : int) :
    LKappa.rule_mixture =
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b, port_a = counter_agent_info.ports in
  let ra_type = counter_agent_info.id in

  let rec aux (i : int) =
    if i = nb + 1 then
      []
    else (
      let is_first = i = 0 in
      let is_last = i = nb in

      let link_type_before : int * int =
        if is_first then
          first_link_type
        else
          (* TODO *)
          (*           port_a, ra_type *)
          ra_type, port_a
      in
      let link_before : (int, int * int) LKappa.link Loc.annoted =
        LKappa.LNK_VALUE (link + i, link_type_before) |> Loc.annotate loc
      in
      let link_switching_before : LKappa.switching =
        if is_first && delta > 0 then
          (* TODO comment: delta > 0 testing for created *)
          LKappa.Linked (link + i)
        else
          LKappa.Maintained
      in
      let link_after : (int, int * int) LKappa.link Loc.annoted =
        (if is_last && test_is_equality then
           LKappa.LNK_FREE
         else if is_last then
           LKappa.LNK_ANY
         else
           (* TODO *)
           (*            LKappa.LNK_VALUE (link + i + 1, (port_b, ra_type))) *)
           LKappa.LNK_VALUE (link + i + 1, (ra_type, port_b)))
        |> Loc.annotate loc
      in

      let ra_agent =
        make_rule_counter_agent sigs noted_as_erased
          (link_before, link_switching_before)
          (link_after, LKappa.Maintained)
          loc
      in
      ra_agent :: aux (i + 1)
    )
  in
  aux 0

let make_new_raw_counter_agents_in_chain (first_link : int)
    (last_link_nb_opt : int option) (delta : int) (sigs : Signature.s) :
    Raw_mixture.agent list =
  let rec aux (i : int) =
    if i = delta then
      []
    else (
      let is_first = i = 0 in
      let is_last = i = delta - 1 in

      let link_before =
        if is_first then
          Raw_mixture.VAL first_link
        else
          Raw_mixture.VAL (first_link + i)
      in
      let link_after =
        if is_last then (
          match last_link_nb_opt with
          | None -> Raw_mixture.FREE
          | Some last_link_nb -> Raw_mixture.VAL last_link_nb
        ) else
          Raw_mixture.VAL (first_link + i + 1)
      in
      let raw_incr = make_raw_counter_agent link_before link_after sigs in
      raw_incr :: aux (i + 1)
    )
  in
  aux 0

let set_erased_rule_counter_agents_in_chain (sigs : Signature.s)
    (incrs : LKappa.rule_mixture) (delta : int) (link : int) :
    LKappa.rule_mixture =
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b = fst counter_agent_info.ports in
  let rec aux (i : int) (incr_l : LKappa.rule_agent list) =
    match incr_l with
    | incr :: incr_s ->
      if i < abs delta then (
        (* Erase agent: we erase [delta] agents at the start of the chain *)
        Array.iteri
          (fun i (a, _) -> incr.LKappa.ra_ports.(i) <- a, LKappa.Erased)
          incr.LKappa.ra_ports;
        let rule_agent = { incr with LKappa.ra_erased = true } in
        rule_agent :: aux (i + 1) incr_s
      ) else (
        (* Link first agent from the remaining of the chain back to the first link *)
        let before_link, _ = incr.LKappa.ra_ports.(port_b) in
        incr.LKappa.ra_ports.(port_b) <- before_link, LKappa.Linked link;
        incr :: incr_s
      )
    | [] -> []
  in
  aux 0 incrs

(** Returns mixtures for agent with site changed from counter to port, as well as new [link_nb] after previous additions
 * Used by [compile_counter_in_rule_agent]*)
let counter_becomes_port (sigs : Signature.s) (ra : LKappa.rule_agent)
    (port_id : int) (counter : Ast.counter) (start_link_nb : int) :
    (LKappa.rule_mixture * Raw_mixture.t) * int =
  (* Returns positive part of value *)
  let positive_part (i : int) : int =
    if i < 0 then
      0
    else
      i
  in

  let loc : Loc.t = Loc.get_annot counter.Ast.counter_name in
  let (delta, loc_delta) : int * Loc.t = counter.Ast.counter_delta in
  let counter_test : Ast.counter_test Loc.annoted =
    Option_util.unsome_or_raise
      ~excep:
        (ExceptionDefn.Internal_Error
           ( "Counter "
             ^ Loc.v counter.Ast.counter_name
             ^ " should have a test by now",
             loc ))
      counter.Ast.counter_test
  in
  let (test_value, test_is_equality) : int * bool =
    match Loc.v counter_test with
    | Ast.CVAR _ ->
      raise
        (ExceptionDefn.Internal_Error
           ( "Counter "
             ^ Loc.v counter.Ast.counter_name
             ^ " defines a variable, which should have been replaced by CEQ \
                conditions after rule splitting",
             Loc.get_annot counter_test ))
    | Ast.CEQ j -> j, true
    | Ast.CGTE j -> j, false
    | Ast.CLTE _j -> failwith "not implemented" (* TODO *)
  in

  (* There are two kinds of mixtures specified here in the rule: rule mixture and raw mixture.
   * Operations done to change the counter to a chain of agents:
   * - Add the test in the rule mixture as test in the chain of agent
   * - If delta < 0, remove agents in the rule mixture by setting them as Erased
   * - If delta > 0, add agents in the raw mixture *)

  (* Add test condition of counter value in rule_mixture:
   * specify counter agents that should be present and link value in the end of the chain *)
  (* TODO *)
  let first_link_type : int * int = port_id, ra.LKappa.ra_type in
  let rule_mix_with_counter_test : LKappa.rule_mixture =
    make_rule_agent_counter_test_chain sigs test_value first_link_type
      ra.LKappa.ra_erased test_is_equality start_link_nb loc delta
  in

  (* TODO: clarify why these link numbers *)
  let link_for_erased : int = start_link_nb + abs delta in
  let start_link_for_created : int = start_link_nb + test_value + 1 in
  let new_link_nb : int =
    start_link_nb + 1 + test_value + positive_part delta
  in
  (* Adjust delta in counter value:
   * - if delta < 0 set them as erased in the rule mixture
   * - if delta > 0 add them in the raw mixture *)
  let rule_mix_with_counter_test_and_delta : LKappa.rule_mixture =
    if delta < 0 then
      set_erased_rule_counter_agents_in_chain sigs rule_mix_with_counter_test
        delta link_for_erased
    else
      rule_mix_with_counter_test
  in
  let raw_mix_with_counter_delta : Raw_mixture.t =
    if delta > 0 then
      make_new_raw_counter_agents_in_chain start_link_for_created
        (Some start_link_nb) delta sigs
    else
      []
  in

  if test_value + delta < 0 then
    raise
      (ExceptionDefn.Internal_Error
         ("Counter test should be greater then abs(delta)", loc_delta));

  (* Update link to the rule agent with the counter *)
  let switch : LKappa.switching =
    if delta = 0 then
      LKappa.Maintained
    else if delta > 0 then
      LKappa.Linked start_link_for_created
    else
      LKappa.Linked link_for_erased
  in
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b : int = fst counter_agent_info.ports in
  ra.LKappa.ra_ports.(port_id) <-
    ( (LKappa.LNK_VALUE (start_link_nb, (port_b, counter_agent_info.id)), loc),
      switch );

  ( (rule_mix_with_counter_test_and_delta, raw_mix_with_counter_delta),
    new_link_nb )

(* TODO: fixes this comment as it also applies the delta to the counter *)

(** Compiles the counter precondition in a left hand side mixture of a rule into a mixture which tests dummy positions
 * rule_agent_ - agent with counters in a rule
   lnk_nb - the max link number used in the rule;
   sigs.counter_agent_info - info on the counter agent
   returns: agent with explicit counters; created incr agents;
            the next link number to use *)
let compile_counter_in_rule_agent (sigs : Signature.s)
    (rule_agent_ : LKappa.rule_agent with_agent_counters) (lnk_nb : int) :
    LKappa.rule_mixture * Raw_mixture.t * int =
  let (incrs, lnk_nb') : (LKappa.rule_mixture * Raw_mixture.t) list * int =
    Tools.array_fold_lefti
      (fun id (acc_incrs, lnk_nb) -> function
        | None -> acc_incrs, lnk_nb
        | Some (counter, _) ->
          let new_incrs, new_lnk_nb =
            counter_becomes_port sigs rule_agent_.agent id counter lnk_nb
          in
          new_incrs :: acc_incrs, new_lnk_nb
        (* JF: link ids were colliding after counter decrementations -> I do not think that we should add delta when negative *))
      ([], lnk_nb) rule_agent_.counters
  in
  let (als, bls) : LKappa.rule_mixture * Raw_mixture.t =
    List.fold_left (fun (als, bls) (a, b) -> a @ als, b @ bls) ([], []) incrs
  in
  als, bls, lnk_nb'

(** Compiles the counter value change in the right hand side of a rule into dummy chain changes *)
let compile_counter_in_raw_agent (sigs : Signature.s)
    (raw_agent_ : Raw_mixture.agent with_agent_counters) (lnk_nb : int) :
    Raw_mixture.agent list * int =
  let raw_agent : Raw_mixture.agent = raw_agent_.agent in
  let ports : Raw_mixture.link array = raw_agent.Raw_mixture.a_ports in
  Tools.array_fold_lefti
    (fun port_id (acc, lnk_nb) -> function
      | None -> acc, lnk_nb
      | Some (c, _) ->
        (match c.Ast.counter_test with
        | None ->
          let agent_name =
            Format.asprintf "@[%a@]"
              (Signature.print_agent sigs)
              raw_agent.Raw_mixture.a_type
          in
          LKappa.raise_not_enough_specified ~status:"counter" ~side:"left"
            agent_name c.Ast.counter_name
        | Some (test, _) ->
          (match test with
          | Ast.CGTE _ | Ast.CLTE _ | Ast.CVAR _ ->
            let agent_name =
              Format.asprintf "@[%a@]"
                (Signature.print_agent sigs)
                raw_agent.Raw_mixture.a_type
            in
            LKappa.raise_not_enough_specified ~status:"counter" ~side:"left"
              agent_name c.Ast.counter_name
          | Ast.CEQ j ->
            let p = Raw_mixture.VAL lnk_nb in
            let () = ports.(port_id) <- p in
            let incrs =
              make_new_raw_counter_agents_in_chain lnk_nb None (j + 1) sigs
            in
            acc @ incrs, lnk_nb + j + 1)))
    ([], lnk_nb) raw_agent_.counters

let raw_agent_has_counters (ag_ : 'a with_agent_counters) : bool =
  Array.fold_left (fun ok x -> x <> None || ok) false ag_.counters

let rule_agent_has_counters (rule_agent : LKappa.rule_agent)
    (sigs : Signature.s) : bool =
  Signature.has_counter (Signature.get sigs rule_agent.ra_type)

(** [compile_counter_in_rule sigs mix created] takes the intial mixture from a rule [mix],
 * and the mixture obtained from the application of the rule [created],
 * both with counter information, and returns two mixtures for a new rule without counters, having compiled the counter logic inside the rule.
 *
 * - adds increment agents to the rule_agent mixture
   - adds increment agents to the raw mixture
   - links the agents in the mixture(lhs,rhs,mix) or in the raw mixture(created)
     to the increments *)
let compile_counter_in_rule (sigs : Signature.s)
    (mix : rule_mixture_with_agent_counters)
    (created : raw_mixture_with_agent_counters) :
    LKappa.rule_mixture * Raw_mixture.t =
  let has_counters : bool =
    List.exists
      (fun rule_agent_ -> rule_agent_has_counters rule_agent_.agent sigs)
      mix
    || List.exists (fun raw_agent_ -> raw_agent_has_counters raw_agent_) created
  in
  if has_counters then (
    let lnk_nb : int =
      List.fold_left
        (fun (m : int) rule_agent_ ->
          max m (LKappa.max_link_id [ rule_agent_.agent ]))
        0 mix
    in

    let (incrs, incrs_created, lnk_nb') :
        LKappa.rule_mixture * Raw_mixture.t * int =
      List.fold_left
        (fun (mix_incr, created_incr, lnk_nb) rule_agent_ ->
          let mix_incr_new, created_incr_new, lnk_nb' =
            compile_counter_in_rule_agent sigs rule_agent_ lnk_nb
          in
          mix_incr_new @ mix_incr, created_incr_new @ created_incr, lnk_nb' + 1)
        ([], [], lnk_nb + 1)
        mix
    in
    let incrs_created' : Raw_mixture.t =
      List.fold_left
        (fun (created_incr, lnk_nb) raw_agent_ ->
          let created_incr_new, lnk_nb'' =
            compile_counter_in_raw_agent sigs raw_agent_ lnk_nb
          in
          created_incr_new @ created_incr, lnk_nb'')
        ([], lnk_nb' + 1)
        created
      |> fst
      (* We drop the lnk_nb as we don't need in the following *)
    in

    (* Return initial mixtures with new agents in rule from counter compilation *)
    let rule_agent_mix : LKappa.rule_mixture =
      List_util.rev_map_append (fun rule_agent_ -> rule_agent_.agent) mix incrs
    in
    let raw_mix : Raw_mixture.t =
      List_util.rev_map_append
        (fun raw_agent_ -> raw_agent_.agent)
        created
        (incrs_created @ incrs_created')
    in
    rule_agent_mix, raw_mix
  ) else
    ( List.rev_map (fun rule_agent_ -> rule_agent_.agent) (List.rev mix),
      List.rev_map (fun raw_agent_ -> raw_agent_.agent) (List.rev created) )

let rule_agent_with_max_counter sigs c ((agent_name, _) as ag_ty) :
    LKappa.rule_mixture =
  let ag_id = Signature.num_of_agent ag_ty sigs in
  let sign = Signature.get sigs ag_id in
  let arity = Signature.arity sigs ag_id in
  let ports =
    Array.make arity (Loc.annot_with_dummy LKappa.LNK_ANY, LKappa.Maintained)
  in
  let internals = Array.make arity LKappa.I_ANY in
  let c_na = c.Ast.counter_name in
  let c_id = Signature.num_of_site ~agent_name c_na sign in
  let max_val, loc = c.Ast.counter_delta in
  let max_val' = max_val + 1 in
  let incrs =
    make_rule_agent_counter_test_chain sigs max_val' (c_id, ag_id) false false 1
      loc (-1)
  in
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b = fst counter_agent_info.ports in
  let p = LKappa.LNK_VALUE (1, (port_b, counter_agent_info.id)), loc in
  ports.(c_id) <- p, LKappa.Maintained;
  let ra : LKappa.rule_agent =
    {
      LKappa.ra_type = ag_id;
      ra_ports = ports;
      ra_ints = internals;
      ra_erased = false;
      ra_syntax = Some (Array.copy ports, Array.copy internals);
    }
  in
  ra :: incrs

let counter_perturbation sigs c ag_ty =
  let annot = Loc.get_annot c.Ast.counter_name in
  let filename = [ Primitives.Str_pexpr ("counter_perturbation.ka", annot) ] in
  let stop_message =
    "Counter " ^ Loc.v c.Ast.counter_name ^ " of agent " ^ Loc.v ag_ty
    ^ " reached maximum"
  in
  let mods =
    [
      Ast.PRINT ([], [ Primitives.Str_pexpr ("", annot) ]);
      Ast.PRINT ([], [ Primitives.Str_pexpr (stop_message, annot) ]);
      Ast.STOP filename;
    ]
  in
  let val_of_counter =
    Alg_expr.KAPPA_INSTANCE (rule_agent_with_max_counter sigs c ag_ty)
  in
  let pre =
    Alg_expr.COMPARE_OP
      ( Operator.EQUAL,
        (val_of_counter, annot),
        (Alg_expr.CONST (Nbr.I 1), annot) )
  in
  ( None,
    Some (pre, Loc.get_annot ag_ty),
    mods,
    Some (Loc.annot_with_dummy Alg_expr.FALSE) )

let counters_perturbations sigs ast_sigs =
  List.fold_left
    (List.fold_left (fun acc -> function
       | Ast.Absent _ -> acc
       | Ast.Present (ag_ty, sites, _) ->
         List.fold_left
           (fun acc' site ->
             match site with
             | Ast.Port _ -> acc'
             | Ast.Counter c ->
               (counter_perturbation sigs c ag_ty, Loc.get_annot ag_ty) :: acc')
           acc sites))
    [] ast_sigs

let make_counter i name =
  {
    Ast.counter_name = Loc.annot_with_dummy name;
    counter_test = Some (Loc.annot_with_dummy (Ast.CEQ i));
    counter_delta = Loc.annot_with_dummy 0;
  }

let add_counter_to_contact_map sigs add_link_contact_map =
  let counter_agent_info = Signature.get_counter_agent_info sigs in
  let port_b, port_a = counter_agent_info.ports in
  add_link_contact_map counter_agent_info.id port_a counter_agent_info.id port_b

let raise_if_modification (delta, loc) =
  if delta != 0 then LKappa.raise_if_modification loc (Some delta)

let annotate_dropped_counters sign ast_counters ra arity agent_name aux =
  let ra_counters = Array.make arity None in
  let _ =
    List.fold_left
      (fun pset c ->
        let port_name = c.Ast.counter_name in
        let port_id = Signature.num_of_site ~agent_name port_name sign in
        let () =
          match Signature.counter_of_site_id port_id sign with
          | None -> LKappa.raise_counter_misused agent_name c.Ast.counter_name
          | Some _ -> ()
        in
        let pset' = Mods.IntSet.add port_id pset in
        let () =
          if pset == pset' then
            LKappa.raise_several_occurence_of_site agent_name c.Ast.counter_name
        in
        let () = raise_if_modification c.Ast.counter_delta in
        let () =
          match aux with
          | Some f -> f port_id
          | None -> ()
        in
        ra_counters.(port_id) <- Some (c, LKappa.Erased);
        pset')
      Mods.IntSet.empty ast_counters
  in
  { agent = ra; counters = ra_counters }

let annotate_edit_counters sigs ((agent_name, _) as ag_ty) counters ra
    add_link_contact_map =
  let ag_id = Signature.num_of_agent ag_ty sigs in
  let sign = Signature.get sigs ag_id in
  let arity = Signature.arity sigs ag_id in
  let ra_counters = Array.make arity None in
  let register_counter_modif c_id =
    let counter_agent_info = Signature.get_counter_agent_info sigs in
    let port_b = fst counter_agent_info.ports in
    add_link_contact_map ag_id c_id counter_agent_info.id port_b
  in
  let _ =
    List.fold_left
      (fun pset c ->
        let port_name = c.Ast.counter_name in
        let port_id = Signature.num_of_site ~agent_name port_name sign in
        let () =
          match Signature.counter_of_site_id port_id sign with
          | None -> LKappa.raise_counter_misused agent_name c.Ast.counter_name
          | Some _ -> ()
        in
        let pset' = Mods.IntSet.add port_id pset in
        let () =
          if pset == pset' then
            LKappa.raise_several_occurence_of_site agent_name c.Ast.counter_name
        in
        let () = register_counter_modif port_id in
        let () = ra_counters.(port_id) <- Some (c, LKappa.Maintained) in
        pset')
      Mods.IntSet.empty counters
  in
  { agent = ra; counters = ra_counters }

let annotate_counters_with_diff sigs ((agent_name, loc) as ag_ty) lc rc ra
    add_link_contact_map =
  let ag_id = Signature.num_of_agent ag_ty sigs in
  let sign = Signature.get sigs ag_id in
  let arity = Signature.arity sigs ag_id in
  let register_counter_modif c c_id =
    let counter_agent_info = Signature.get_counter_agent_info sigs in
    let port_b = fst counter_agent_info.ports in
    let () = add_link_contact_map ag_id c_id counter_agent_info.id port_b in
    c, LKappa.Maintained
  in
  let ra_counters = Array.make arity None in
  let rc_r, _ =
    List.fold_left
      (fun (rc, cset) c ->
        let ((na, _) as counter_name) = c.Ast.counter_name in
        let c_id = Signature.num_of_site ~agent_name counter_name sign in
        let cset' = Mods.IntSet.add c_id cset in
        let () =
          if cset == cset' then
            LKappa.raise_several_occurence_of_site agent_name counter_name
        in
        let c', rc' =
          List.partition
            (fun p -> String.compare (Loc.v p.Ast.counter_name) na = 0)
            rc
        in
        let c'' =
          match c' with
          | _ :: [] | [] -> register_counter_modif c c_id
          | _ :: _ ->
            LKappa.raise_several_occurence_of_site agent_name counter_name
        in
        let () = ra_counters.(c_id) <- Some c'' in
        rc', cset')
      (rc, Mods.IntSet.empty) lc
  in
  let _ =
    (* test if counter of rhs is in the signature *)
    List.map
      (fun c -> Signature.num_of_site ~agent_name c.Ast.counter_name sign)
      rc_r
  in
  if (not (rc = [])) && not (rc_r = []) then
    raise
      (ExceptionDefn.Internal_Error
         ("Counters in " ^ agent_name ^ " should have tests by now", loc));
  { agent = ra; counters = ra_counters }

let annotate_created_counters sigs ((agent_name, _) as ag_ty) counters
    add_link_contact_map ra =
  let ag_id = Signature.num_of_agent ag_ty sigs in
  let sign = Signature.get sigs ag_id in
  let arity = Signature.arity sigs ag_id in
  let ra_counters = Array.make arity None in

  (* register all counters (specified or not) with min value *)
  Array.iteri
    (fun port_id _ ->
      match Signature.counter_of_site_id port_id sign with
      | Some (min, _) ->
        let c_name = Signature.site_of_num port_id sign in
        (try
           let c =
             List.find
               (fun c' -> String.compare (Loc.v c'.Ast.counter_name) c_name = 0)
               counters
           in
           ra_counters.(port_id) <-
             Some
               ( {
                   Ast.counter_name = c.Ast.counter_name;
                   Ast.counter_test = c.Ast.counter_test;
                   Ast.counter_delta = 0, Loc.dummy;
                 },
                 LKappa.Maintained )
         with Not_found ->
           ra_counters.(port_id) <-
             Some
               ( {
                   Ast.counter_name = c_name, Loc.dummy;
                   Ast.counter_test = Some (Ast.CEQ min, Loc.dummy);
                   Ast.counter_delta = 0, Loc.dummy;
                 },
                 LKappa.Maintained ))
      | None -> ())
    ra_counters;

  let register_counter_modif c_id =
    let counter_agent_info = Signature.get_counter_agent_info sigs in
    let port_b = fst counter_agent_info.ports in
    add_link_contact_map ag_id c_id counter_agent_info.id port_b
  in
  let _ : Mods.IntSet.t =
    List.fold_left
      (fun pset c ->
        let port_name = c.Ast.counter_name in
        let port_id = Signature.num_of_site ~agent_name port_name sign in
        match Signature.counter_of_site_id port_id sign with
        | None -> LKappa.raise_counter_misused agent_name c.Ast.counter_name
        | Some _ ->
          ();
          let pset' = Mods.IntSet.add port_id pset in
          if pset == pset' then
            LKappa.raise_several_occurence_of_site agent_name c.Ast.counter_name;
          register_counter_modif port_id;
          ra_counters.(port_id) <- Some (c, LKappa.Maintained);
          pset')
      Mods.IntSet.empty counters
  in
  { agent = ra; counters = ra_counters }
