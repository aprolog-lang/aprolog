open Absyn;;
open Flags;;
open Solve;;
module P = Perm;;
open Printer;;
open Util;;
open Tcenv;;
open Config;;
open Types;;
module Dg = Dependency_graph;;  
module N = Negelim;;

Random.self_init();;

(* Some global variables for interpreter state *)
let version = "0.4";;
let interactive = ref false;;
let verbose = ref false;;
let log = ref false;;
let errors = ref 0;;
let dumpfile = ref "";;

(* It would be nice to get rid of this side-effecting state *)
let dump_ne = ref false;;
let depen_graph = ref Dg.empty;;

(* State for saving answers *)
let save_to_file_docs = ref [];;
let start_save_to_file () =
  save_to_file_docs := []

let do_save_to_file doc =
  save_to_file_docs := doc :: !save_to_file_docs

let stop_save_to_file filename fdoc =
  let oc = (open_out_gen [Open_wronly;Open_creat;Open_text] 0o666 filename) in
  Printer.doc_to_channel oc (fdoc (List.rev !save_to_file_docs));
  close_out oc

let parse_libs_var s = split (fun c -> c = ':') s;;
lib_dirs := 
   try (parse_libs_var (Sys.getenv "APROLOG_LIBS"))@ !lib_dirs
   with _ -> !lib_dirs

let log_msg msg = 
  print_string msg; 
  flush stdout;
  if !log then output_string stderr msg;
;;


let add_lib_dir s = 
  lib_dirs := s::!lib_dirs
;;

let set_depth_first_bound i = 
  Flags.depth_first_bound := Some i;;

let timer = ref 0.0;;
let start_timer () = 
  timer := Sys.time();;
let time_msg msg = 
  let diff = Sys.time() -. !timer in
  log_msg (msg^"\t"^(string_of_float diff)^"\n");
  flush stdout
;;


let timer2 = ref 0.0;;
let start_timer2 () = 
  timer2 := Sys.time();;
let time2 () = 
  Sys.time() -. !timer2
;;

let find_local file = 
  if Sys.file_exists file then Some file else None
;;


let find_lib file = 
  let rec find l = 
    match l with 
      [] -> None
    | d::ds -> 
	if Sys.file_exists (d^"/"^file) 
	then Some (d^"/"^file) 
	else find ds
  in find !lib_dirs
;;



let quit() = 
  print_string "\nGoodbye.\n";
  exit(0)
;;


exception Success;;


let succeed() = raise Success;;


let lexbuf = Lexing.from_channel stdin;;


let get_lineno () = 
  Lineno.lineno()
;;

let parse file = 
  let ic = open_in file in
  Lineno.reset();
  Lineno.enter_file file;
  Parser.parse Lexer.lex (Lexing.from_channel ic)
;;


let parse_input_line () = 
  Lineno.reset();
  Parser.parse_input_line Lexer.lex lexbuf
;;


let get_decls find_file file = 
  match find_file file with 
    Some file' -> 
      let decls = 
	try parse file'
	with Parsing.Parse_error -> 
	  Util.error("Syntax error near ["^Lineno.filename()^":"
		       ^(string_of_int (get_lineno()))^"]\n")
	| Lexer.LexFail msg -> 
	    Util.error("Error near line ["^Lineno.filename()^":"
			 ^(string_of_int (get_lineno()))^"]: "^msg^"\n") 
      in
      decls
  |  None -> print_string (file^": File not found\n"); []
;;
  

let forall f l = List.fold_left (&&) true (List.map f l);;
let rec mem x l = match l with
                    [] -> false
                  | y::ys -> x= y || mem x ys;;
let subset l m = forall (fun x -> mem x m) l;;

(* TODO: Solve any pi X # X constraints for X. *)
let rec solve_constrs sc ans = 
  if not(!Flags.consistency_check) then sc ans 
  else 
  let (subst,constrs) = ans in 
  let rec check_constrs constrs sc = 
      match constrs with 
        (Internal.Name a,x)::constrs' -> check_constrs constrs' sc
      | (Internal.Susp(pi,_,y) as v,x)::constrs' -> 
         if Var.eq x y 
         then (* TODO: This is unsafe if x is not a name-variable *)
	   let support = Perm.supp pi in
	   let rec try_all support sc = 
	     match support with 
	       [] -> ()
	     | (a::support') -> 
		 (Unify.unify Isym.term_sym_eq v (Internal.Name a) (solve_constrs sc) ans;
		  try_all support' sc)
	   in
	   if support = [] then sc ans else try_all support sc
	 else check_constrs constrs' sc
      | [] -> sc ans
      | _ -> impos "expected name or variable in constr"
  in check_constrs constrs sc
;;

let handleTcFail pos msg = 	
  (match pos with 
    None -> print_string ("***TYPE ERROR***\n"^msg^"\n")
  | Some p -> print_string ("***TYPE ERROR*** ["
			    ^Pos.pos2s p
			    ^"]: \n"^msg^"\n")
  );
  incr errors
;;


let help() = 
  let doc = text "Interpreter directives:" <:> newline
      <:> text "#quit.\t\t\tQuit AlphaProlog" <:> newline
      <:> text "#help.\t\t\tPrint this message" <:> newline
      <:> text "#use \"<filename>\".\tUse (read & execute) an external file" <:> newline
      <:> text "#open <id>.\t\tOpen a namespace (binding all its names locally)" <:> newline
      <:> text "#type <exp>.\t\tTypecheck an expression and display principal typing" <:> newline
      <:> text "#trace <num>.\t\tSet trace level to num = 0 (silent) to 3 (verbose)"<:> newline
      <:> text "#infix<dir> <id> <num>.\tMake identifier infix with associativity <dir> (l,r,n)"<:> newline
      <:> text "\t\t\tand precedence <num> (1..9)"<:>newline <:> newline
      <:> text "Keystroke commands:" <:> newline
      <:> text "<Control-C>\t\tInterrupt execution" <:> newline 
      <:> text "<Control-D>\t\tQuit AlphaProlog from prompt" <:> newline <:> newline
      <:> text "Queries:"<:> newline
      <:> text "<query>.\t\tPose a query." <:> newline<:> newline
(*      <:> text "Kinds of queries"<:> newline
      <:> text "<query>,<query> \tConjunction (\"and\") of queries" <:> newline
      <:> text "<query>;<query> \tDisjunction (\"or\") of queries" <:> newline
      <:> text "<exp> = <exp>\t\tUnification query" <:> newline
      <:> text "<exp> # <exp>\t\tFreshness query" <:> newline
      <:> text "<exp>\t\t\tAtomic query (e.g. \"List.append [1] [2] X\")"<:> newline <:> newline
*)
  in
  Printer.doc_to_channel stdout doc
  

let check_disjoint_vars vs = 
  let rec chk s vs = 
    match vs with 
      [] -> ()
    | v::vs -> 
	if Varset.mem v s 
	then raise (Tc.TcFail ("Repeated variable "^Var.to_string' v^" in type abbreviation"))
	else chk (Varset.add v s) vs
  in chk Varset.empty vs
;;
 
(* Preprocess declarations to check that #gen directives aren't present in 
source, #check directives aren't followed by ordinary declarations, and 
insert #gen directives before the first #check. *)

let preprocess_decls decls0 =

(* HACK: Sanity-check the declarations to ensure that there are no 
generate directives in the source, and there is no ordinary code 
after a #check directive. *)

  let rec sanity_check checks_only decls = 
    match decls with
      [] -> ()
    | {pos=pos;rdecl=GenerateDirective(x)}::_ -> 
	Util.impos "Generate directives not allowed in source programs"
    | {pos=pos;rdecl=CheckDirective(name,bound,t,_)}::decls -> 
	sanity_check true decls
    | {pos=pos;rdecl=QuitDirective}::decls -> 
	sanity_check true decls
    | decl::decls ->
	if checks_only 
	then  Util.impos "Ordinary code is not allowed after #check directives"
	else sanity_check checks_only decls
  in
  
(* HACK: Look for the first occurrence of a check directive 
   and insert the appropriate generators before it. 
*)
  let rec insert_generation decls = 
    match decls with
      [] -> []
    | {pos=pos;rdecl=CheckDirective(name,bound, t,_)}::_ -> 
	let mkdecl rdecl = {pos=pos; rdecl=rdecl} in
	let l1 = 
	  if(!generate_terms) 
          then [mkdecl (GenerateDirective("gen"))] 
          else [] in
	let l2 = 
	  if(!generate_negation) 
          then
            [mkdecl (GenerateDirective("eq"));
             mkdecl (GenerateDirective("fresh"));
             mkdecl (GenerateDirective("neq"));
	     mkdecl (GenerateDirective("nfresh"))]
          else [] in
        let l3 =
          if (not(!ne_simpl) && !generate_negation)
          then [mkdecl (GenerateDirective("not"))]
          else [] in
	l1 @ l2 @ l3 @ decls
    | decl::decls ->
	decl:: insert_generation(decls)
  in
  sanity_check false decls0;
  insert_generation decls0
    ;;

let open_dump filename =
  open_out_gen [Open_wronly;Open_append;Open_creat;Open_text] 0o666 filename;;

let get_preds_to_negate test =
  let neg_preds = Dg.get_negative_preds test in
  if !Flags.debug
  then
    (print_endline ("term to test is : " ^ (t2s test) ^
                    "\nnegative preds in it are:");
     String_set.iter (fun neg_pred -> print_string (neg_pred ^ "\n")) neg_preds;
     print_endline "dependency graph";
     Dg.print_all_deps !depen_graph;
     print_newline ());
  let preds = String_set.fold
      (fun neg_pred prev ->
         let len = String.length neg_pred in
         let pos_pred = String.sub neg_pred 4 (len - 4) in
         String_set.add pos_pred prev) neg_preds String_set.empty in 
  let (dep_graph,preds_to_negate) =
    Dg.get_required_preds preds !depen_graph in
  if !Flags.debug
  then (print_endline "predicates to negate:";
        List.iter (fun pred -> print_string (pred ^ "\n")) preds_to_negate);
  depen_graph := dep_graph;
  preds_to_negate

    (* Some helper printing functions *)
let print_generated decls =
  print_string "GENERATED:\n";
  List.iter (fun decl -> print_to_channel pp_decl decl stdout;
    print_string "\n") decls;
  print_string "END\n"

let dump_generated decls =
  let oc = open_dump !dumpfile in
  List.iter
    (fun decl -> print_to_channel pp_decl decl oc; 
      output_string oc "\n")
    decls;
  close_out oc

let print_clause msg p =
  print_endline (msg);
  print_to_channel pp_term p stdout;
  print_string ".\n"

let print_term msg t =
  print_string msg;
  print_to_channel pp_term t stdout;
  print_string "\n";
  flush stdout

let print_internal pp t =
  print_to_channel (pp Isym.pp_term_sym) t stdout;
  print_string "\n"


(* TODO: factor this into:
   - a function that sets up evaluation and constructs a lazy stream of answer
   - a function that handles interactive query execution, printing 
     next answers and getting next stream element if requested
   - alternative stream handlers to handle functions 
 *)

type 'a stream = {next: unit -> ('a * 'a stream) option}

let handle_answer_stream_interactively sg tcenv fvs stream =
  let rec loop stream =
    match stream.next() with
      None -> print_string "No.\n"
    | Some (ans,stream) ->
	print_string "Yes.\n";
	Printer.print_to_channel (Unify.pp_answer sg tcenv fvs) ans stdout;
	flush stdout;
	let s = input_line stdin in
	if s = ";" then loop stream else ()
  in loop stream

let handle_query t sg idx =
  let init_sc tcenv fvs = 
    solve_constrs (fun ans -> 
      print_string "Yes.\n"; 
      Printer.print_to_channel (Unify.pp_answer sg tcenv fvs) ans stdout;
      flush stdout;
      do_save_to_file (Unify.pp_answer_term sg tcenv fvs ans);
      if !interactive 
      then (
        let s = input_line stdin in
        if s = ";" then () else succeed())
      else succeed()
    )
  in 
  let (tcenv,g) = Monad.run sg empty_env (Tc.check_goal t) in
  if not(!tc_only) && (!errors = 0 || !interactive)
  then (
    if !debug || not(!interactive) then print_term "--------\nQuery: " g;
    (try 
      let g' = Translate.translate_goal sg tcenv g in
      if !debug then print_internal Internal.pp_goal g';
      let fvs = Varset.elements (Internal.fvs_g g') in
      Solve.solve Isym.pp_term_sym idx g' (init_sc tcenv fvs);
      (* if we reach here, then no solution ws found *)
      print_string "No.\n"
    with Success -> ()
    |  Sys.Break -> print_string "\nInterrupted.\n"));
  sg,idx

let optionally b f x = if b then f(x) else x


let rec run1 pos decl sg idx =
  Var.reset_var();
  match decl with
    Query (t) -> handle_query t sg idx
  | SaveDirective(filename,"no_backtrack",decl) ->
      start_save_to_file ();
      let sg,idx = run1 pos decl sg idx in
      stop_save_to_file filename (fun docs ->
	text "as" <:> paren (
	quotes (text filename) <:> comma <:> newline <:>
	num (List.length docs) <:> comma <:> newline <:>
	bracket (sep (comma <:> newline) docs)) <:> dot
	) ;
      sg,idx
  | ClauseDecl(c) ->
      if !verbose then print_clause "" (Absyn.simplify c);
      let (tcenv,p) = Monad.run sg empty_env (Tc.check_prog c) in
      if !verbose && !debug then print_clause "Typechecked:" p;
      let (tcenv,p) = (* Linearization pass *)
	optionally (!Flags.linearize && pos <> None)
          (fun (tcenv,p) -> 
	    let c' = Absyn.linearize_prog p in
	    let (tcenv,p) = Monad.run sg empty_env (Tc.check_prog c')  in
	    if !verbose then print_clause "Linearized:" p;
	    (tcenv,p)) (tcenv,p) in
      let (tcenv,p) = (* Well-quantification pass *)
        optionally (!Flags.quantify && pos <> None)
          (fun (tcenv,p) -> 
            let c = Absyn.well_quantify_prog p in
            let (tcenv,p) = Monad.run sg empty_env (Tc.check_prog c) in
            if !verbose then print_clause "Well-quantified:" p;
            (tcenv,p)) (tcenv,p) in
      (* Simplification pass *)
      let p = optionally (!Flags.simplify_clauses) Absyn.simplify p in
      let sg = Tcenv.add_clause_decl sg p in

      if !ne_simpl then
        (let updated_dep_graph = Dg.add_clause_deps c !depen_graph in
        depen_graph := updated_dep_graph);

      if not(!tc_only) && (!errors = 0 || !interactive)
      then 
	(let p' = Translate.translate_prog sg tcenv p in
	let fas = Varset.elements(Internal.fas_p p') in
	let fvs = Varset.elements(Internal.fvs_p p') in
	let p' = List.fold_right (fun v p -> Internal.Dforall (v,p)) fvs p' in
	let p' = List.fold_right (fun a p -> Internal.Dnew(a,p)) fas p' in
	if !debug then print_internal Internal.pp_prog p';
	Index.add idx p');
      sg,idx
  | NamespaceDecl(sym,decls) -> 
      if !interactive || !verbose
      then (print_string ("namespace "^sym^" (\n"));
      Tcenv.enter_namespace sg sym;
      let sg' = run sg idx decls in
      Tcenv.exit_namespace sg;
      if !interactive || !verbose 
      then print_string ").\n";
      sg',idx
  | UseDirective(file) -> 
      let old_interactive = !interactive in
      interactive := false;
      let decls = get_decls find_lib file in
      let sg' = run sg idx decls in
      interactive := old_interactive;
      sg',idx
  | TraceDirective(i) -> 
      trace := i;
      sg,idx
  | KindDecl(s,k) -> 
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=decl} stdout;
	    print_string "\n");
      let sg,_ = Tcenv.add_kind_decl sg s k None in
      sg,idx
  | SymDecl (f,ty) -> 
      let (tcenv,ty) = Monad.run sg empty_env (Tc.check_ty ty false DataKd) in
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=SymDecl(f,ty)} stdout;
	    print_string "\n");
      let sg,_ = Tcenv.add_sym_decl sg f false false true ty in
      sg, idx
  | PredDecl(f,tys,is_user,is_abbrev) -> 
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=decl} stdout;
	    print_string "\n");
      let ty = List.fold_right (fun t u -> ArrowTy (t,u)) tys PropTy in
      let (tcenv,ty) = Monad.run sg empty_env (Tc.check_ty ty false TypeKd) in
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=SymDecl(f,ty)} stdout;
	    print_string "\n");
      let sg,_ = Tcenv.add_sym_decl sg f false is_abbrev is_user ty in
      sg, idx
  | TypeDefn (s,vs,ty) as decl -> 
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=decl} stdout;
	    print_string "\n");
      check_disjoint_vars vs;
      let ((_,tctx,_,_),ty) = Monad.run sg empty_env 
	  (Tc.check_ty ty true TypeKd) in
      let ks = 
	try List.map (fun v -> Varmap.find v tctx) vs 
	with Not_found -> 
	  raise (Tc.TcFail "Abbreviation has unconstrained type variables") in
      let ks = List.map (function NameKd -> NameK 
	                 |TypeKd|DataKd -> TypeK) ks in
      let k = List.fold_right (fun k k' -> ArrowK(k,k')) ks TypeK in
      (*let u = Unique.get() in
      Nstbl.add sg.ksg (Nstbl.Rel(Nstbl.Base(s))) 
	(k,u,Some (Tc.reflect_ty vs ty));
      let s' = Nstbl.resolve sg.ksg (Nstbl.Rel (Nstbl.Base s)) in
      Hashtbl.add sg.stbl u s'; *)
      let sg,_ = Tcenv.add_kind_decl sg s k (Some (Tc.reflect_ty vs ty)) in
      sg,idx
  | FuncDecl(f,tys,ty) as decl -> 
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=decl} stdout;
	    print_string "\n");
      let ty = List.fold_right (fun t u -> ArrowTy (t,u)) tys ty in
      let (_,ty) = Monad.run sg empty_env (Tc.check_ty ty false TypeKd) in
      let sg,_ = Tcenv.add_sym_decl sg f true false false ty in 
      sg,idx
  | BuiltinFuncDecl (sym,tys,ty,f) as decl -> 
      if !interactive || !verbose
      then (Printer.print_to_channel pp_decl {pos=pos;rdecl=decl} stdout;
	    print_string "\n");
      let ty = List.fold_right (fun t u -> ArrowTy (t,u)) tys ty in
      let (_,ty) = Monad.run sg empty_env (Tc.check_ty ty false TypeKd) in
      let sg,u = Tcenv.add_sym_decl sg sym false false false ty in 
      Runtime.bind u f;
      sg,idx
  | InfixDecl (_,_,_) -> sg,idx
  | TypeQuery (t) -> 
      let ((_,tctx,ctx,_),(t',ty)) = 
	Monad.run sg empty_env (Tc.infer_term t) in
      Printer.print_to_channel (Varmap.pp_map Tcenv.pp_symk) ctx stdout;
      print_string " |- ";
      Printer.print_to_channel pp_term t' stdout;
      print_string " : ";
      Printer.print_to_channel pp_ty ty stdout;
      nl();
      sg, idx
  | QuitDirective -> quit()
  | OpenDirective s -> 
      (try 
	Nstbl.open_ns sg.ksg s;
	Nstbl.open_ns sg.tsg s;
      with Not_found -> print_string ("Unknown namespace "^Nstbl.p2s s)
      );
      sg,idx
  | HelpDirective(_) -> (* ignore argument for now *)
      help();
      sg,idx
  | CheckDirective(name,bound,validity,test1) ->
    let do_ne_simpl test sg =
      let preds_to_negate = get_preds_to_negate test in
      let neg_decls = Negelim.generate_negative_decls sg preds_to_negate in
      if !Flags.debug then print_generated neg_decls;
      let sg = run sg idx neg_decls in
      let (neg_defns,stats_buffer) =
        Negelim.generate_negative_defns sg preds_to_negate in
      if !Flags.debug then print_generated neg_defns;
      let sg = run sg idx neg_defns in
      if !dump_ne then dump_generated (neg_decls@neg_defns);
      if !verbose then print_string stats_buffer;
      sg
    in
    let (tcenv,test2) = Monad.run sg empty_env (Tc.check_test test1) in
    let test3 = optionally (not (!custom_check)) 
                  (if !Flags.negelim then N.negate_test else N.add_generators sg tcenv) 
                  test2
    in
    let sg = optionally (!ne_simpl) (do_ne_simpl test3) sg in
        
    if !Flags.do_checks 
    then 
      if not(!tc_only) && (!errors = 0 || !interactive)
      then (if !debug || not(!interactive)
      then (
        print_string ("--------\nChecking for counterexamples to \n"^name^": ");
	Printer.print_to_channel Absyn.pp_term test1 stdout;
	print_string "\n";
	flush stdout);
      log_msg (name^"\n");
      let rec init_sc fvs depth = 
	solve_constrs (fun ans -> 
          if !verbose then time_msg("");
          print_string ("\nTotal: " ^ string_of_float (time2()) ^ " s:\n"); 
          Printer.print_to_channel (Unify.pp_answer sg tcenv fvs) ans stdout;
          flush stdout;
          do_save_to_file (Unify.pp_answer_term sg tcenv fvs ans);
          if !interactive 
          then (
	    let s = input_line stdin in
	    if s = ";" then () else succeed()
           ) else succeed()
		      )
      in
    (try
      let test4 = Translate.translate_test sg tcenv test3 in
      if !debug then print_internal Internal.pp_test test4;
      let fvs = Varset.elements (Internal.fvs_t test4) in
      flush(stdout);
      if not(!verbose) then log_msg("Checking depth");
      let do_check = if !Flags.negelim then Check.check_ne else Check.check in
      start_timer2();
      if bound < 0 then (
        if !verbose 
        then log_msg("unbounded")
        else log_msg(" unbounded");
        flush(stdout);
        start_timer();
        do_check Isym.pp_term_sym sg idx test4 (init_sc fvs) (-1);
        if !verbose then time_msg("")
        );
      for i = 1 to bound do
        if !verbose 
        then log_msg((string_of_int i))
        else log_msg(" "^(string_of_int i));
        flush(stdout);
        start_timer();
        do_check Isym.pp_term_sym sg idx test4 (init_sc fvs) i;
        if !verbose then time_msg("");
            done;
            print_string ("\nTotal: " ^ string_of_float (time2()) ^ " s:\n");
      if validity = Some false
            then (print_string "No counterexamples found!\n";
      raise (RuntimeError ("Specification "^name^" failed")))
    with Success ->
      if validity = Some true
      then (print_string "Specification fails!\n";
      raise (RuntimeError ("Specification "^name^" failed")))
      else print_string "\n"
	|  Sys.Break ->
	    time_msg("");
	    print_string("Interrupted\n");
	    print_string ("Total: " ^ string_of_float (time2()) ^ " s:\n")));
      sg,idx
  | GenerateDirective("gen") ->
      let decls = Negelim.generate_terms sg in
      if !debug then print_generated decls;
      run sg idx decls, idx
  | GenerateDirective("neq") ->
      let decls = Negelim.generate_neqs sg in
      if !debug then print_generated decls;
      if !dump_ne then dump_generated decls;
      run sg idx decls, idx
  | GenerateDirective("nfresh") ->
      let decls = Negelim.generate_nfreshs sg in
      if !debug then print_generated decls;
      if !dump_ne then dump_generated decls;
      run sg idx decls, idx
  | GenerateDirective("fresh") ->
     let decls = Negelim.generate_freshs sg in
     if !debug then print_generated decls;
     if !dump_ne then dump_generated decls;
     run sg idx decls, idx
  | GenerateDirective("eq") ->
     let decls = Negelim.generate_eqs sg in
     if !debug then print_generated decls;
     if !dump_ne then dump_generated decls;
     run sg idx decls, idx
  (* TODO: after negelim interface is adapted use commented code for generating not *)
  | GenerateDirective("not") -> 
     let decls = Negelim.generate_negation sg in
     if !debug then print_generated decls;
     run sg idx decls, idx
(* | GenerateDirective("not") -> *)
(*    let defns = Negelim.generate_negated_decls sg in *)
(*    let sg' = run sg idx defns in *)
(*    let decls = Negelim.generate_negated_defns sg' in *)
(*    if !debug then print_generated decls; *)
(*    run sg' idx decls, idx *)
  | GenerateDirective("forallstar") -> 
     let decls = Negelim.generate_forallstars sg in
     if !debug then print_generated decls;
     run sg idx decls, idx


and run sg idx rest = 
  match rest with 
    [] -> sg
  | decl::decls -> 
      let sg,idx = 
	try run1 decl.pos decl.rdecl sg idx 
	with Tc.TcFail msg -> (
	  handleTcFail decl.pos msg;
	  sg,idx
	 ) 
      in
      run sg idx decls
;;


let rec toploop sg idx = 
  print_string "?- ";
  flush stdout;
  try 
    start_timer();
    let decls0 = parse_input_line() in
    if !verbose then time_msg("Parsing");
    let decls = preprocess_decls decls0 in
    start_timer();
    let sg = run sg idx decls in
    if !verbose then time_msg("Running");
    toploop sg idx
  with 
    Parsing.Parse_error -> 
      print_string ("I don't understand.  (Try \"#help.\")\n");
      toploop sg idx
  | Lexer.LexFail msg -> 
      print_string ("I don't understand.  (Try \"#help.\")\n");
      toploop sg idx 
  | End_of_file -> 
      quit()
  | Util.Impos msg -> 
      print_string ("Internal error: "^msg^".\n"^
		    "(This is my fault, not yours.  "^
		    "Please submit a bug report so I can fix the problem).\n");
      toploop sg idx
  | Error msg -> 
      print_string ("I don't understand.\n"^msg^".\n");
      toploop sg idx
  | RuntimeError msg -> 
      print_string ("A runtime error occurred:\n"^msg^".\n");
      toploop sg idx
  | Sys.Break -> (* No effort at atomicity here. *)
      print_string "\nInterrupted.\n";
      toploop sg idx
;;

let rec set_dumpfile filename =
  if Sys.file_exists filename then Sys.remove filename;
  dumpfile := filename;
  dump_ne := true
  
let main args = 
  (* Banner hard to read because of escapes ... *)
  (* Looks like this
          ______                   
          ||   \\    /|           
          ||    )    ||           
    __  _ ||___/_ __ ||  __   __  _
   / \\/  || \\/ / \\|| / \\ / \\/
  (   )\  ||  ||(   )||(   )(   ) 
  \\_/ \\_||  ||\\_/ ||\\_/ \\_/  
          /   /      /      ((__ 
                            \\__))  
     *)
  let banner = 
    "          ______                  \n"^
    "          ||   \\\\    /|          \n"^
    "          ||    )    ||           \n"^
    "    __  _ ||___/_ __ ||  __   __  _\n"^
    "   / \\\\/  || \\\\/ / \\\\|| / \\\\ / \\\\/\n"^
    "  (   )\\  ||  ||(   )||(   )(   ) \n"^
    "  \\\\_/ \\\\_||  ||\\\\_/ ||\\\\_/ \\\\_/  \n"^
    "          /   /      /      ((__ \n"^
    "                            \\\\__))  \n"
  in print_string banner;
  
  Sys.catch_break true; (* ctrl-C will raise Break *)
  let rsg = ref (Tcenv.init_sg()) in
  let idx = Index.create 100 in
  (* Initialize by interpreting runtime library decls *)
  (* FIX hack *)
  Flags.forbid_prop := false;
  Flags.forbid_higher_order := false;
  rsg := run !rsg idx Runtime.decls;
  Flags.forbid_prop := true;
  Flags.forbid_higher_order := true;
  (* FIX end hack *)
  let arg_check_negelim () = 
    do_checks := true;
    negelim := true;
    extensional_forall := true;
    horn_clauses_only := false;
    consistency_check := true;
    generate_negation := true;
    quantify := true;
    simplify_clauses := true;
(*    strict_new_occurs := true *)
  in 
  let arg_check_negelim_minus () = 
    do_checks := true;
    negelim := true;
    extensional_forall := false;
    horn_clauses_only := false;
    consistency_check := true;
    generate_negation := true;
    quantify := true;
    simplify_clauses := true;
    (*    strict_new_occurs := true*)
  in 
  let arg_check_negfail () = 
    do_checks := true;
    generate_terms := true
(*    strict_new_occurs := false*)
  in
  let arg_check_ne_simpl () =
    do_checks := true;
    negelim := true;
    extensional_forall := true;
    horn_clauses_only := false;
    consistency_check := true;
    generate_negation := true;
    simplify_clauses := true;
    quantify := true;
    ne_simpl := true
  in
  let arg_check_ne_simpl_minus () =
    do_checks := true;
    negelim := true;
    extensional_forall := false;
    horn_clauses_only := false;
    consistency_check := true;
    generate_negation := true;
    simplify_clauses := true;
    quantify := true;
    ne_simpl := true
  in  let do_file file = 
    print_string ("Reading file "^file^"...\n");
    start_timer();
    let decls0 = 
      try 
	get_decls find_local file 
      with Error msg -> print_string msg; exit(1)
    in
    let decls = preprocess_decls decls0 in
    if !verbose then time_msg "Parsing";
    start_timer();
    let sg = run !rsg idx decls in
    rsg := sg;
    if !verbose then time_msg "Running"
  in 
  let spec = [ ("-b", Arg.Int(set_depth_first_bound), "Depth-first search bound");
	       (* ("-cc", Arg.Set(consistency_check), "Check consistency of answer constraints");
	       ("-check", Arg.Set(do_checks), "Search for counterexamples to #check specifications"); *)
	       ("-d", Arg.Set(debug), "Enable debugging messages");
               (* ("-ef", Arg.Set(extensional_forall), 
		"Extensional universal quantifier (experimental)");*)
	       ("-hh", Arg.Clear(horn_clauses_only), 
		"Permit hereditary Harrop programs (experimental)"); 
	       ("-ng", Arg.Set(new_goal_only), 
		"Restrict to new-goal Horn clauses");
	       ("-s", Arg.Set(simplify_clauses), 
		"Simplify generated clauses");
	       ("-l", Arg.Set(linearize), 
		"Linearize clauses");
	       ("-wq", Arg.Set(quantify), 
		"Normalize and well-quantify clauses");
	       ("-skip-occurs", Arg.Set(skip_occurs_check), 
		"Skip occurs check");
	       ("-q", Arg.Set(quit_early), 
		"Quit interpreting after reading all input");
	       ("-L", Arg.String(add_lib_dir), "Add directory to library search path");
	       ("-so", Arg.Set(strict_new_occurs),
		"Strict name occurs checks (experimental)");
	       ("-susp", Arg.Set(Flags.suspensions),
	        "Apply permutations as suspensions (experimental)");
	       ("-t", Arg.Int(fun i -> trace := i), "Set tracelevel (0,1,2)");
	       ("-to", Arg.Set(tc_only), "Typecheck only");
	       ("-v", Arg.Set(verbose), "Verbose mode");
	       ("-log", Arg.Set(log), "Log mode");
	       ("-ap", Arg.Clear(forbid_prop), "Allow prop as type");
	       ("-aho", Arg.Clear(forbid_higher_order), "Allow higher-order types");
	       ("-un", Arg.Clear(restrict_name_type), "Unrestrict name types");
               ("-check-ne", Arg.Unit(arg_check_negelim), "Check using negation elimination");
               ("-check-ne-minus", Arg.Unit(arg_check_negelim_minus), "Check using negation elimination (without extensional quantification)");
               ("-check-nf",Arg.Unit(arg_check_negfail), "Check using negation as failure");
               ("-check-ne-simpl", Arg.Unit(arg_check_ne_simpl), "Check using negation elimination with negative predicates simplification (experimental)");
               ("-check-ne-simpl-minus", Arg.Unit(arg_check_ne_simpl_minus), "Like -check-ne-simpl but without extensional quantification");
               ("-nd", Arg.String(set_dumpfile), "Dump negative predicates in the specified file");
               ("-cc",Arg.Set(custom_check), "Disables manipulation of the check directive, letting the user specify generators or negative predicates.");
               ("-a",Arg.Set(interactive), "Enables interactive mode also during specification checking") 
	     ]
  in
  print_string ("AlphaProlog "^version^"\n");
  print_string ("For help, type \"#help.\"\n");
  flush stdout;
  Arg.parse spec do_file "usage: aprolog [options] files";
  if !errors = 0 && not (!quit_early)
  then (interactive := true;
	toploop !rsg idx)
  else (if !errors != 0 
        then  (print_string (string_of_int !errors ^ " errors\n");
	       exit(1)))
;;


main Sys.argv;;
