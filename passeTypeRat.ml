(* Module de la passe de typage *)
open Type
module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstType
  open AstTds
  
  type t1 = Ast.AstTds.programme
  type t2 = Ast.AstType.programme

  (*** Liste de fonctions auxiliaires utiles pour la suite ***)

  (* Renvoie le type de tout les éléments d'un enregistrement *)
  let rec analyseStruct structList =
    match structList with
      | [ia] ->
          begin
            match info_ast_to_info ia with
            | InfoVar(_,t,_,_,_,_,_) -> t
            | _ -> failwith "Error"
          end
      | ia::tl -> 
          begin
            match info_ast_to_info ia with
              | InfoVar(n,t,_,_,_,_,_) ->
                begin           
                      match t with
                        | Struct _ -> 
                            analyseStruct tl        
                        | _ ->
                            raise(MauvaiseUtilisationIdentifiant ("Not a struct :"^n))
                end
              | _ -> failwith "Error"
           end
      | [] -> failwith "Error"

  (* Fonction auxilaire pour créer une liste des types associés à un enregistrement *)
  let rec createStructVars typeList = 
      match typeList with
        | [t] -> [(t,"")]
        | t::tl -> (t,"")::createStructVars tl
        | [] -> failwith "Error"
  
  (* Fonction pour analyser le types de tous les champs d'un enregistrement *)
  let rec structFieldsTypes t = 
    match t with
    | [] -> []
    | t::tl ->
          match t with
          | Struct _ -> (structAnalyser t)::structFieldsTypes tl
          | Pointer(t1) -> Pointer(structAnalyser t1)::structFieldsTypes tl
          | t -> t::structFieldsTypes tl

(* Renvoie le type t d'un élément pointé par un pointeur ou des éléments d'un enregistrement *)
and structAnalyser t = 
    match t with
        | Struct(typeIdList) -> let typeList,_ = List.split typeIdList in
            let ntypeList = structFieldsTypes typeList in
            Struct(createStructVars ntypeList)
        | Pointer t -> Pointer (structAnalyser t)
        | _ -> t
  
  (* Renvoie un booleén en testant si deux éléments sont de même type *)
  let rec typesEqual t1 t2 =
      match t1,t2 with
        | Struct(tidList1),Struct(tidList2) ->
            let typeList1,_ = List.split tidList1 in
            let typeList2,_ = List.split tidList2 in
            let tl1,tl2 = structFieldsTypes typeList1,structFieldsTypes typeList2 in 
            List.for_all2 (fun a b-> typesEqual a b) tl1 tl2             
        | Pointer(_), Pointer(Undefined) -> true
        | Pointer(Undefined), Pointer(_) -> true 
        | Pointer(t1),Pointer(t2) -> typesEqual t1 t2
        | t1,t2 -> t1 = t2

(* analyse_type_affectable : AstTds.affectable -> AstType.affectable       *)     
(* Paramètre affectable : l'affectable à analyser                          *)
(* Renvoie le type associée à l'affectable                                 *)
  let rec analyse_type_affectable affectable = 
    match affectable with
    | AstTds.Ident info_ast ->
     begin 
       match info_ast_to_info info_ast with
        | InfoVar(_,t,_,_,_,_,_) -> t
        | _ -> failwith "Error"     
     end
    | AstTds.Val affectable1 ->
      let _ = analyse_type_affectable affectable1 in 
      let ident = getIdVal affectable1 in
      let t = analyse_type_affectable ident in 
      let _, dType = derefType affectable t in
           dType
                  
    | AstTds.Field(affectable1,info_ast_field) -> 
            let structList = createStructList (AstTds.Field(affectable1,info_ast_field)) in 
            let t = analyseStruct (List.rev structList) in t
  
  (* Renvoie l'identifiant d'un affectable *)
   and getIdVal affectable =
        match affectable with
         | Ident info_ast -> Ident info_ast
         | Field(_,id) -> Ident id              
         | Val(affectable) -> getIdVal affectable

  (*Renvoie une liste d'affectables associés aux champs accédés *)
  (* Ex : Field(x,y),z) -> [z y x]  *) 
  and createStructList affectable = 
    match affectable with
        | Field(affectable1,id1) -> id1::createStructList affectable1
        | Val affectable1 -> 
          begin
            let derefAffectable,t = derefType affectable (analyse_type_affectable (getIdVal affectable1)) in      
            match derefAffectable with
              | Ident info_ast  ->
                begin
                  match info_ast_to_info info_ast with   
                  | InfoVar(n,_,_,_,_,_,_) -> createStructList (AstTds.Ident (info_to_info_ast (InfoVar(n,t,0,"","","",[]))))
                  | _ -> failwith "Error"
                end
              | _ -> failwith "Error"
            end    
        | Ident id -> [id]

  (* Fonction auxilairie pour renvoyer une liste d'affectables associés aux champs accédés *)
  and fieldType affectable = 
      let structList = createStructList affectable in 
       analyseStruct (List.rev structList) 
  
  (* Fonction auxilairie pour renvoyer une liste d'affectables associés aux champs accédés *)
  and derefType affectable t =    
      match affectable,t with
        | AstTds.Val affectable1, t1 -> 
            begin
              match t1 with
               | Pointer(t2) -> derefType affectable1 t2
               | _ -> raise(MauvaiseUtilisationIdentifiant ("NotAPointerDereference"))
            end
       | AstTds.Field(_,_),_ ->
        begin
            match getIdVal affectable with
            | Ident info_ast ->
          
              let t2 = fieldType affectable in
              begin 
                match info_ast_to_info info_ast with
                  | InfoVar _ -> derefType (AstTds.Val (Ident info_ast)) t2     
                  | _ -> failwith "Error"
              end
            | _ -> failwith "Error"
        end
       | affectable, t1 ->
          affectable,t1 


  (* analyse_type_expression : AstTds.expression -> AstType.expression *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre e : l'expression à analyser *)
  (* Renvoie le type associée à l'expression*)
  let rec analyse_type_expression e = 

    match e with
    
    | AstTds.AppelFonction (info_ast, e_list) -> 

    let ne_type_list = List.map (analyse_type_expression) e_list in 
        let (ne_list, t_list) = List.split ne_type_list in
        let (ne_list,t_list_flatten) = (ne_list,List.flatten t_list) in
        begin
        match info_ast_to_info info_ast with

         | InfoFun(_,t,tl) ->
           if List.length t_list = List.length tl then
           if checkVars t_list_flatten tl then 
            AstType.AppelFonction(info_ast,ne_list),[t]
            else raise(TypesParametresInattendus(t_list_flatten,tl))
        else raise(TypesParametresInattendus(t_list_flatten,tl))

        | _ -> failwith "Error"
        end
      | AstTds.Affectable affectable  -> 
        begin
          match affectable with
           | AstTds.Ident info_ast ->
            begin
              match info_ast_to_info info_ast with
               | InfoVar (_,t,_,_,_,_,_) -> AstType.Affectable(Ident info_ast),[t]
               | _ -> failwith "Error"
            end                                             
           | _ -> let t = analyse_type_affectable affectable in Affectable affectable,[t]         
                
        end                               
      | AstTds.Booleen b -> AstType.Booleen b,[Bool]
      | AstTds.Entier k -> AstType.Entier k,[Int]
      | AstTds.Unaire (u, expr) -> 
      begin
        match analyse_type_expression expr with
        | ne,[t] ->
          if (t = Rat) then 
            match u with 
             | Numerateur -> AstType.Unaire (Numerateur, ne), [Int]
             | Denominateur -> AstType.Unaire(Denominateur, ne), [Int]
          else raise (TypeInattendu(t,Rat))
        | _ -> failwith "Error"
      end
      | AstTds.Binaire (b,expr1,expr2) ->
      begin
      match (analyse_type_expression expr1, analyse_type_expression expr2) with
       | ((ne1,[t1]),(ne2,[t2])) -> 
          if est_compatible (t1) (t2) then 
              match (b,t1,t2) with
                | (Fraction,Int,Int) -> AstType.Binaire(Fraction,ne1,ne2), [Rat]
                | (Fraction,Rat,Rat) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (Fraction,Bool,Bool) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (Plus,Int,Int) -> AstType.Binaire(PlusInt,ne1,ne2), [Int]
                | (Plus,Rat,Rat) -> AstType.Binaire(PlusRat,ne1,ne2), [Rat]
                | (Plus,Bool,Bool) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (Equ,Int,Int) -> AstType.Binaire(EquInt,ne1,ne2), [Bool]
                | (Equ,Bool,Bool) -> AstType.Binaire(EquBool,ne1,ne2), [Bool]
                | (Equ,Rat,Rat) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (Mult,Int,Int) -> AstType.Binaire(MultInt,ne1,ne2), [Int]
                | (Mult,Rat,Rat) -> AstType.Binaire(MultRat,ne1,ne2), [Rat]
                | (Mult,Bool,Bool) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (Inf, Int, Int) -> AstType.Binaire(Inf,ne1,ne2), [Bool]
                | (Inf, Rat, Rat) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (Inf, Bool,Bool) -> raise (TypeBinaireInattendu(b,t1,t2))
                | (_,t1,t2) -> raise (TypeBinaireInattendu(b,t1,t2))
            else raise (TypeBinaireInattendu(b,t1,t2))
        | _ -> failwith "Error"
      end
      | AstTds.Malloc t -> AstType.Malloc t,[Pointer t] 
      | AstTds.NullPointer -> AstType.NullPointer,[Pointer Undefined]
      | AstTds.Adress info_ast ->
        begin
          match info_ast_to_info info_ast with 
           | InfoVar(_,t,_,_,_,_,_) -> AstType.Adress info_ast,[Pointer t]
           | _ -> failwith "Error"
        end
          
      | AstTds.StructVars le ->  let t = structTypes le in
                                 let t1 = createStructVars t in
                                 let nle,_ = List.split(List.map(analyse_type_expression) le) in
                                 AstType.StructVars(nle), [Struct t1]
    
    (* Créer une liste des types associés à un enregistrement *)   
    (* Ex :{int x int y} -> {int int} *)
    and structTypes le =
          match le with
            | e::tl ->
              begin
                match e with
                  | AstTds.StructVars le -> 
                        let _,typeList = List.split(List.map analyse_type_expression le) in
                        let structList = List.flatten typeList in
                            Struct(createStructVars structList)::structTypes tl
                    | _ -> 
                    
                      match analyse_type_expression e with
                      | (_,[t]) -> t::structTypes tl
                      | _ -> failwith "Error"                     
              end         
           | [] -> []
    (* Fonction auxilaire pour créer une liste des types associés à un enregistrement *)
    and createStructVars typeList = 
        match typeList with
          | [t] -> [(t,"")]
          | t::tl -> (t,"")::createStructVars tl
          | [] -> failwith "Error"
  
     (* Vérifie si les types sont les mêmes pour deux listes de variables *)
    and checkVars tl1 tl2 = 
    List.for_all2(fun t1 t2 -> typesEqual t1 t2) tl1 tl2
     

  (* analyse_type_instruction : AstTds.instruction -> AstType.instruction                 *)
  (* Paramètre func_type : différencier entre la fonction main et une fonction auxiliaire *)
  (* Paramètre i : l'instruction à analyser                                               *)
  (* Renvoie le type associée à l'instruction                                             *)
let rec analyse_type_instruction func_type i = 

  match i with 
    | AstTds.Declaration (t,info_ast,e) ->
      begin
          match analyse_type_expression e with
          | (ne,[te]) ->            
                if typesEqual t te then 
                  begin
                  modifier_type_info t info_ast;        
                  AstType.Declaration(info_ast,ne)
                  end
                else 
                raise(TypeInattendu(te,t))
         | _ -> failwith "Error"
      end
    | AstTds.Affectation (affectable,e) -> 
      begin
      let t = analyse_type_affectable affectable in
      
      match getIdVal affectable with
       | Ident _ ->
        begin
          match  analyse_type_expression e with
          |  (ne,[te]) -> if typesEqual t te then AstType.Affectation(affectable,ne) else raise(TypeInattendu(te,t))
          | _ -> failwith "Error"
        end
      | _ -> failwith "Error"
      end
    | AstTds.Affichage e -> 

      begin

        match analyse_type_expression e with
          
         | ne,[te] -> 
           begin
            match te with
              | Int -> AstType.AffichageInt ne
              | Rat -> AstType.AffichageRat ne
              | Bool -> AstType.AffichageBool ne
              | _ -> failwith "This functionnality is not implemented"
           end
        | _ -> failwith "Error"
      end
    
    | AstTds.Conditionnelle (e,b1,b2) -> 
      begin
        match analyse_type_expression e,analyse_type_bloc func_type b1,analyse_type_bloc func_type b2 with
           | (ne,[te]),nb1,nb2 -> if te = Bool then AstType.Conditionnelle(ne,nb1,nb2) else raise(TypeInattendu(te,Bool))
           | _ -> failwith "Error"   
      end
    | AstTds.TantQue (e,b) -> 
    begin
    match analyse_type_expression e with
      | (ne,[te]) -> 

        let nb = analyse_type_bloc func_type b in

        if te = Bool then AstType.TantQue(ne,nb) else raise(TypeInattendu(te,Bool))
      | _ -> failwith "Error"
    end
    | AstTds.PlusEgal (affectable,e) ->
       begin
        let t1 = analyse_type_affectable affectable in 
        match analyse_type_expression e with
         | ne,[t2] ->
          let t = addType t1 t2 in
          begin
            match t with 
              | Int -> AstType.PlusEgalInt(affectable,ne)
              | Rat -> AstType.PlusEgalRat(affectable,ne)
              | _ -> failwith "Error"
          end
         | _ -> failwith "Error"
        end
    | AstTds.Retour e ->
    begin
    match func_type with
        | Undefined -> raise(RetourDansMain)
        | _ -> 
             match analyse_type_expression e with
                | ne,[te] ->
                    if(typesEqual func_type te) then
                      AstType.Retour(ne)
                    else
                      raise(TypeInattendu(te,func_type))
                | _ -> failwith "Error" 
    end
    | AstTds.DeclarationType(info_ast,_) -> 
    
      AstType.DeclarationType(info_ast)
      
    | Empty -> Empty

(* Analyse le type d'une addition                       *)
(* Renvoie le type du resultat si celle-ci est possible *)  
and addType t1 t2 = 
  match t1,t2 with
    | Int,Int -> Int
    | Rat,Rat -> Rat
    | t1,t2 -> raise(TypeInattendu(t1,t2))

  (* analyse_type_bloc : AstTds.bloc -> AstType.bloc                                            *)
  (* Paramètre t : différencier entre la fonction main et une fonction auxiliaire               *)
  (* Paramètre li : la liste d'instructions                                                     *)
  (* Renvoie un nouveau bloc dont les instructions ont été analysées                            *)
and analyse_type_bloc t li = 
 
      let nli = List.map (analyse_type_instruction t) li in nli
        (*afficher_locale tdsbloc ; *)  (* décommenter pour afficher la table locale *)

  (* analyse_type_fonction : AstTds.fonction -> AstType.fonction                                *)
  (* Paramètre func_type : différencier entre la fonction main et une fonction auxiliaire       *)
  (* Paramètre AstTds.Fonction : la fonction à analyser                                         *)
  (* Renvoie la fonction dont les paramètres et les instructions ont été analysées              *)
let analyse_type_fonction (AstTds.Fonction(t,info_func,info_typ_var,li)) = 

    let nli = analyse_type_bloc t li in 
    let (_, info_ast_list) = List.split info_typ_var in 
    AstType.Fonction(info_func,info_ast_list,nli) 
  
  (* analyse : AstTds.ast -> AstType.ast                                                        *)
  (* Paramètre func_type : différencier entre la fonction main et une fonction auxiliaire       *)
  (* Paramètre AstTds.Programme : le programme à analyser                                       *)
  (* Renvoie un nouveau bloc dont les instructions ont été analysées                            *)                
let analyser (AstTds.Programme(types,fonctions,prog)) =

  let nf = List.map (analyse_type_fonction ) fonctions in
  let namedTypes = List.map(analyse_type_instruction Undefined) types in
  let nb = analyse_type_bloc Undefined prog in
  AstType.Programme (namedTypes,nf,nb)

end

