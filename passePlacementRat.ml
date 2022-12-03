(* Module de la passe de placement de memoire *)
open Type
module PassePlacementRat : Passe.Passe with type t1 = Ast.AstType.programme and type t2 = Ast.AstPlacement.programme =
struct
  open Tds
  open Ast
  open AstType
  

  type t1 = Ast.AstType.programme
  type t2 = Ast.AstPlacement.programme

(* Créer une liste de déclaration de variables *)
  let rec createDeclarationList iaList = 
    match iaList with
      | [] -> []
      | ia::tl -> AstType.Declaration(ia,StructVars([]))::createDeclarationList tl

(* Renvoie la somme des tailles de chacune des variables *)
  let rec blocSize iaList = 
    match iaList with
     | [] -> 0
     | ia::tl -> 
        match ia with
          | InfoVar(_,t,_,_,_,_,_) -> getTaille t + blocSize tl
          | _ -> failwith "Error"
          
  (* analyse_placement_bloc : AstType.bloc -> AstPlacement.bloc *)
  (* Paramètre func_type : différencier entre la fonction main et une fonction auxiliaire *)
  (* Paramètre d : le déplacement intitial du bloc*)
  (* Paramètre bloc : le bloc à analyser*)
  (* Placement mémoire des variables déclarées dans le bloc *)
  
  let rec analyse_placement_bloc func_type d bloc = 
    (*Undefined -> le bloc est main*)
    if func_type = Undefined then
      let shiftInfoList = createShiftList d bloc in 
      let (shiftList,infoList) = List.split shiftInfoList in
      List.iter2 modifier_adresse_vars_sb shiftList infoList;
      bloc 
    else 
      let shiftInfoList = createShiftList d bloc in 
      let (shiftList,infoList) = List.split shiftInfoList in
      List.iter2 modifier_adresse_vars_lb shiftList infoList;
      bloc

    (* Créer une liste contenant les déplacements de toutes les variables déclarés *)
    and createShiftList d b = 

      match b with 

        | [] -> []
        | i::tl ->
          begin
          match i with 

          | AstType.Declaration(info_ast,_) ->
          begin
            match info_ast_to_info info_ast with 
              | InfoVar(_,t,_,_,_,_,ia) ->
                  begin
                  match t with
                    | Struct _ ->
                      let iaList = List.map(info_to_info_ast) ia in 
                      let dList = createDeclarationList iaList in
                      (d,info_ast)::createShiftList d dList@createShiftList (d + blocSize ia) tl          
                    | _ -> (d,info_ast)::createShiftList (d + getTaille t) tl    
                  end
                | _ -> failwith "Error"
             end
          (* Les variables déclarés dans les boucles for et blocs conditionnels sont locales et donc sont enlevés de la pile
             en sortie de ces blocs*)
          | AstType.Conditionnelle(_,b1,b2) -> (createShiftList d tl)@(createShiftList d b1)@(createShiftList d b2)   
          | AstType.TantQue(_,b) -> (createShiftList d tl)@createShiftList d b
          | _ -> createShiftList d tl
          end
    (*Modifier l'adresse des variables du main ou fonctions*)
    and modifier_adresse_vars_sb s i = 
        modifier_adresse_info s "SB" i  
    and modifier_adresse_vars_lb s i = 
        modifier_adresse_info s "LB" i

  (* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
  (* Paramètre AstType.Fonction : la fonction à analyser *)
  (* Placement mémoire des paramètres et des variables de locales de la fonction *)
  let rec analyse_placement_fonction (AstType.Fonction(info_func,info_typ_var,li)) = 

    let dList = createDeclarationList (info_typ_var) in
    let sList = createShiftListVars (-1) (List.rev dList) in
    let shiftList,infoList = List.split sList in
    
    List.iter2 modifier_adresse_vars_lb shiftList infoList;

    match info_ast_to_info info_func with
      | InfoFun(_,t,_) ->

          let nb = analyse_placement_bloc t 3 li in AstPlacement.Fonction(info_func,info_typ_var,nb)
      | _ -> failwith "Error"
  
  (* Créer une liste contenant les déplacements des paramètres d'une fonction*)
  and createShiftListVars d b = 
        match b with 
          | [] -> []
          | i::tl ->   
            match i with 
              | AstType.Declaration(info_ast,_) ->
              begin
                  match info_ast_to_info info_ast with
                  | InfoVar(_,t,_,_,_,_,ia) ->
                        begin
                        match t with
                          | Struct _ ->
                            (d,info_ast)::createShiftListVars (d - blocSize ia) tl          
                          | _ -> 
                              (d,info_ast)::createShiftListVars (d - getTaille t) tl    
                        end
                  | _ -> failwith "Error"
                  end
              | _ -> failwith "Error"
  
  (* analyser : AstType.ast -> AstPlacement.ast *)
  (* Paramètre AstType.Programme : le programme à analyser *)
  (* Placement mémoire du programme à compiler *)
  let analyser (AstType.Programme (_,fonctions,prog)) = 
    let nf = List.map (analyse_placement_fonction ) fonctions in 
    let nb = analyse_placement_bloc Undefined 0 prog in
    AstPlacement.Programme (nf,nb)

end
