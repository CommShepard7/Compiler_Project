(* Module de la passe de gestion des identifiants *)
open Type
module PasseTdsRat : Passe.Passe with type t1 = Ast.AstSyntax.programme and type t2 = Ast.AstTds.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstTds
  

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme

(*** Liste de fonctions auxiliaires utiles pour la suite ***)

(* Vérifie si les paramètres d'une fonctions sont dupliqués ou non *)
let rec dupCheck id_list = 
         
  match id_list with
    | [] -> []
    | [t] -> [t]  
    | h::t -> if List.mem h t then raise(DoubleDeclaration h) else h::dupCheck t

(* Permet de récupérerle type qui définit un type nommé                 *)
(* Exemple : typedef Entier = int                                       *)
(*           Entier x = 1                                               *)
(* On stockera dans le TDS InfoVar(x,int) au lieu de InfoVar(x, Entier) *)                   
let rec initType tds t = 
  match t with
    | TypeNomme tid -> 
       begin
         match chercherGlobalement tds tid with
            | None -> raise(IdentifiantNonDeclare tid)
            | Some info -> 
              match info_ast_to_info info with
                | InfoType(_,tidType) -> initType tds tidType 
                | _ -> raise (MauvaiseUtilisationIdentifiant tid)
          end
    | Pointer t -> Pointer (initType tds t)
    | _ -> t

(* Créer l'info ast associé à une liste de variables pour les ajouter avec un itérateur *)
let rec create_info_ast tds t_l i_l f n iaList =
  match (t_l,i_l,iaList) with
    | ([],[],[]) -> []
    | (var_type::t_list,id::id_list,ia::tl) ->
    begin
      match namedPointer var_type with
        | TypeNomme _ -> 
          (info_to_info_ast (InfoVar(id,(initType tds var_type),0,"",f,"named",ia)))::create_info_ast tds t_list id_list f n tl
        | _ -> (info_to_info_ast (InfoVar(id,(initType tds var_type),0,"",f,n,ia)))::create_info_ast tds t_list id_list f n tl
    end
    | (var_type::t_list,id::id_list,[]) -> 
        begin
          match namedPointer var_type with
            | TypeNomme _ ->
              (info_to_info_ast (InfoVar(id,(initType tds var_type),0,"",f,"named",[])))::create_info_ast tds t_list id_list f n []
            | _ -> (info_to_info_ast (InfoVar(id,(initType tds var_type),0,"",f,n,[])))::create_info_ast tds t_list id_list f n []
        end
    | _ -> failwith "Val error"
    
    
    (* Renvoie le type du pointeur nommé *)
    and namedPointer t = 
      match t with
        | Pointer t -> namedPointer t
        | TypeNomme _ -> t
        | _ -> t

(* Ajouter les infos associés à une liste de variables *)    
let ajouter_vars tds_func info_ast_list id_list = 
        
      List.iter2 (ajouter tds_func) id_list info_ast_list

(* Recherche locale d'une liste de variables,utilisé pour détécter *)
(* les doubles déclarations des champs de struct                   *)
let rec rechercheLocaleList tds id_list = 
      match id_list with
       | [] -> []
       | hd::tl -> match chercherLocalement tds hd with
                     | None -> hd::rechercheLocaleList tds tl
                     | Some _ -> raise (DoubleDeclaration hd)

(* Association d'une liste d'identifiants avec le code respectif *)
let rec resolveListId idList n =
  if (n <> "") then 
    match idList with
      | [] -> []
      | id::tl -> 
      let n1 = List.hd(extractString n) in
            (n1^"_"^id)::resolveListId tl n
  else idList
  
  (* Permet d'extraire une chaîne de caractère à l'interieur  *)
  (* d'un string qui correspond à un identifiant              *)
  and extractString n = 
    if String.contains n '{' then String.split_on_char '{' (String.sub n 1 (String.length n - 2)) else [n]

(* Créer une liste des champs d'un enregistrement pour le *)
(* stocker dans l'InfoVar associé à l'enregistrement      *)
let rec linkFields tds t s = 
    match initType tds t with
      | Struct typeIdList -> let types,idList = List.split typeIdList in
                          if (s <> "") then     
                           let idList1 = resolveListId idList s in
                            let idList2 = List.map(fun var -> "{"^var^"}") idList1 in
                            link tds types idList2 else
                           link tds types idList 
      | Pointer t -> linkFields tds t s 
      | _ -> []         
     and link tds types ids = 
            match types,ids with
              | [],[] -> []
              | _::ttl,i::itl -> 
                  let ia = Option.get (chercherGlobalement tds i) in 
                  let info = info_ast_to_info ia in
                  begin
                     match info with 
                        | InfoVar(n,t,p,b,f,"",_) ->
                            let fields = linkFields tds t "" in
                            modifyLinks ia fields;
                            InfoVar(n,t,p,b,f,"",fields)::link tds ttl itl        
                        | InfoVar(n,t,p,b,f,"named",_) ->                          
                            let fields = linkFields tds t n in
                            modifyLinks ia fields;
                            InfoVar(n,t,p,b,f,"named",fields)::link tds ttl itl

                       | InfoVar(n,t,p,b,f,"Uninitialized",_) ->
                            let fields = linkFields tds t n  in
                            modifyLinks ia fields;
                            InfoVar(n,t,p,b,f,"Uninitialized",fields)::link tds ttl itl                           
                      | _ -> failwith "Error"
                  end
              | _ -> failwith "Error"

(* Ajouter les champs d'un struct lors de sa déclaration *)
let structInfo tds typeList idList n iaList =
  begin        
      let nidList = dupCheck idList in
      let nidList1 = rechercheLocaleList tds nidList in
      let info_ast_list = create_info_ast tds typeList nidList1 "field" n iaList in
      ajouter_vars tds info_ast_list nidList1;
      info_ast_list
  end

(* Permet de créer les string avec les accolades              *)
(* Ex:   typedef Droite (int x int y);                        *)
(*       Droite d1 = {1 2}                                    *)
(*       Droite d2 = {10 11}                                  *)
(*       tds = [d1, d2, {d1_x}, {d1_y}, {d2_x}, {d2_y}]       *)
let rec namedStructVars idList = 
  match idList with
    | [] -> []
    | (Struct t1,id)::tl ->
      id::(List.map(fun var -> id^"_"^var) (namedStructVars t1))@namedStructVars  tl
    | (Pointer t,id)::tl -> namedStructVars ((t,id)::tl)
    | (_,id)::tl -> id::namedStructVars  tl  
          
(* Permet de récupérer tous les types des champs d'un enregistrement sous forme de liste *)
let rec namedStructInfo tds t id =
  begin
    match t with
      | Struct typeIdList -> 
        let typeList = getAllFieldsTypes (Struct typeIdList) in
        let idList = namedStructVars  typeIdList in
        let namedIdList = List.map(fun var -> "{"^id^"_"^var^"}") idList in
        let info_ast_list = create_info_ast tds typeList namedIdList "field" "named" [] in
        ajouter_vars tds info_ast_list namedIdList;
        info_ast_list
      | _ -> failwith "Error"
  end

(* Permet de récupérer tous les types des champs d'un enregistrement sous forme de liste *)
(* Ex : typedef Droite = struct {int x int y};
        typedef Droite2 = struct {Droite d1 Droite d2} 
        Droite2 d3 = {{1 2} {4 5}}                   )
        getAllFieldsTypes d3 = [Droite,int,int,Droite,int,int] *)   
and getAllFieldsTypes t =
match t with
  | Struct (typeIdList) -> let typeList,_ = List.split typeIdList in
      extractType typeList 
  | Pointer t -> getAllFieldsTypes t
  | _ -> [] 

(* Fonction auxiliaire pour getAllFieldsTypes *)
(* Ex : typedef Droite = struct {int x int y};
        typedef Droite2 = struct {Droite d1 Droite d2} 
        Droite2 d3 = {{1 2} {4 5}}                   )
        getAllFieldsTypes d3 = [Droite,int,int,Droite,int,int] *)   
and extractType tl = 
  match tl with
    | t::ttl -> begin
                  match t with
                    | Struct _ -> t::(getAllFieldsTypes t)@extractType ttl
                    | t -> t::getAllFieldsTypes t@extractType ttl
                 end
    | [] -> []

(*Analyse du type,ajout des champs d'un struct dans la tds si nécessaire  *)
(*Renvoie le type analysé avec l'info associée                            *)
and checkType tds iaList1 id t = 
  match t with 
    | TypeNomme _ ->
          let nt = initType tds t in
          begin
          match nt with 
            | Struct _ -> 
                          let iaList = namedStructInfo tds nt id in
                          nt,iaList
            | _ -> nt,[]
          end
    | Struct(typeIdList) -> 
         let (typeList,idList) = List.split typeIdList in 
         let ntypeList = List.map2(checkType tds iaList1) idList typeList in
         let nt,_ = List.split ntypeList in
         let iaList1 = structInfo tds typeList idList "" iaList1 in
         let ntypeIdList = List.combine nt idList in
         Struct (ntypeIdList),iaList1
    | Pointer(t1) -> let nt,iaList = checkType tds iaList1 id t1 in Pointer(nt),iaList
    | _ -> t,[]

(* Analyse du type nommé   *)
(* Renvoie le type analysé *)
let rec checkNamedType tds id t =
  match t with 
    | TypeNomme _ ->
          initType tds t
    | Struct(typeIdList) -> 
         let (typeList,idList) = List.split typeIdList in 
         let ntypeList = List.map(checkNamedType tds id) typeList in
            let _ = structInfo tds ntypeList idList "Uninitialized" [] in
         let ntypeIdList = List.combine ntypeList idList in
         Struct ntypeIdList   
    | Pointer(t1) -> Pointer(checkNamedType tds id t1)
    | _ -> t

(* Créer une liste de déclarations de types nommés pour pouvoir les ajouter dans la tds *)
(* avec un itérateur                                                                    *)
let rec createTidList types = 
  match types with
   | [] -> []
   | AstSyntax.DeclarationType(tid,_)::tl -> 
      tid::createTidList tl
   | _ -> failwith "Not a type"

(* Résolution de nom de variable                                                       *)
(* Les InfoVars de champs de structs nommés sont "Uninitialized"                       *)
(* Il est possible de retrouver la variable à laquelle on accède grace à l'affectable  *)
(* Ex : Field(d,y), avec d = Droite {x y}                                              *)
(* (d.y) -> {d_y}                                                                      *)
(* Renvoie l'info_ast associée à cette variable                                        *)
let rec resolveInfoAst tds info_ast affectableList = 
    match info_ast_to_info info_ast with 
      | InfoVar(_,_,_,_,_,"Uninitialized",_) ->
          let ia = Option.get (chercherGlobalement tds (resolveAffectable affectableList)) in ia 
      | _ -> info_ast 
   and resolveAffectable affectableList = 
      match affectableList with 
        | [affectable] -> 
        begin
            match affectable with 
             | Ident info_ast ->
                begin
                  match info_ast_to_info info_ast with
                  | InfoVar(id,_,_,_,_,"Uninitialized",_) ->  id^"}"
                  | _ -> failwith "Error"
                 end
             | _ -> failwith "Error"
          end
        | affectable::tl -> 
          begin
            match affectable with
            | Ident info_ast ->
                  begin
                    match info_ast_to_info info_ast with
                      | InfoVar(id,_,_,_,_,"named",_) -> 
                          "{"^id^"_"^resolveAffectable tl
                      | InfoVar(id,_,_,_,_,"Uninitialized",_) ->
                        id^"_"^resolveAffectable tl 
                      | InfoVar _ -> resolveAffectable tl
                      | _ -> failwith "Error"
                  end
                
            | _ -> failwith "Error"
           end
        | [] -> "}"

(* analyse_tds_affectable : AstSyntax.affectable -> AstTds.affectable      *)
(* Paramètre tds : la table des symboles courante                          *)
(* Paramètre affectable : l'affectable à analyser                          *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'affectable *)
(* en un affectable de type AstTds.affectable                              *)
(* Erreur si mauvaise utilisation des identifiants                         *)
let rec analyse_tds_affectable tds affectable = 
  match affectable with
  | AstSyntax.Ident n -> let opt = chercherGlobalement tds n in
                begin
                match opt with
                  | None -> raise(IdentifiantNonDeclare n)
                  | Some info_ast -> 
                      match info_ast_to_info info_ast with
                        | InfoVar (_,_,_,_,"var",_,_) -> Ident info_ast 
                        | _ -> raise(MauvaiseUtilisationIdentifiant n)           
                end                   
  | AstSyntax.Val affectable1 ->
     let naffectable1 = Val (analyse_tds_affectable tds affectable1) in
          naffectable1
                    
  | AstSyntax.Field(affectable1,id) ->   let naffectable = analyse_tds_affectable tds affectable1 in
                                  let info_ast = fieldCheck tds id in
                                  let affectable2 = Ident info_ast in
                                  let aList = affectable2::(accessList naffectable) in
                                  let _ = accessCheck aList in
                                  let idList = List.rev (getField tds affectable) in
                                  let _ = resolveInfoAst tds (fieldCheck tds id) idList in
                                  Field(naffectable,info_ast)
                                 
  (*Création d'une liste de variables d'accès à un champ *)
  (*Ex : accessList Field(Field(x,y),z) = [z y x]       *)
   and accessList affectable = 
     match affectable with 
       | Ident n -> 
            begin
                  match info_ast_to_info n with    
                  | InfoVar _ -> [affectable]  
                  | _ -> failwith "Error"
            end
       | Val affectable -> accessList affectable
       | Field(affectable,n) -> 
          match info_ast_to_info n with
             | InfoVar _ ->
                   Ident n::accessList affectable
             | _ -> failwith "Error"
             
  (*Vérification d'accès à un champ de struct avec un accessList *)
  (*Ex : accessCheck [z y x] vérifie que z est un champ de y et que y est un champ de x*)
  (*Renvoie le champ accédé *)
  and accessCheck affectableList =
    match affectableList with
      | [affectable] -> affectable
      | affectable::tl -> 
        begin
          match affectable,List.hd tl with          
            | Ident ia1,Ident ia2 ->
                   begin
                   match  info_ast_to_info ia1,info_ast_to_info ia2 with
                    | InfoVar(n,_,_,_,_,_,_),  InfoVar(n1,t2,_,_,_,_,_) ->
                      let s = reverseNamedVar n in     
                        begin 
                            match pointerType t2 with 
                              | Struct tidList -> 
                                  let _,idl = List.split tidList in
                                    if (List.mem (List.hd(List.rev s)) idl) then                             
                                        accessCheck tl                              
                                    else raise(MauvaiseUtilisationIdentifiant ("Not a field : "^n))
                              | _ -> raise (MauvaiseUtilisationIdentifiant ("Not a struct : "^n1))
                        end
                    | _ -> failwith "Error"
                  end
            | _ -> failwith "Error"
        end
     | [] -> failwith "Error"
  
  (* Renvoie la variable associée au champ de struct nommé   *)
  (* Ex : {d_y} -> y                                        *)
  and reverseNamedVar id = 
      if String.contains id '{' then String.split_on_char '_' (String.sub id 1 (String.length id - 2)) else [id]
  
  (* Renvoie le type pointé *) 
  and pointerType t = 
      match t with 
        | Pointer t -> pointerType t
        | TypeNomme _ -> pointerType t
        | _ -> t

  
  (*Vérifie que la variable accédée est un champ, grace au paramètre dédié dans son InfoVar*)
  (*Permet d'éviter le masquage des champs par des variables de même nom*)
  (*Renvoie l'info ast associée*)
  and fieldCheck tds id = 
      let opt = chercherGlobalement tds id in
        match opt with
        | None -> raise (IdentifiantNonDeclare id)
        | Some info_ast ->
          match info_ast_to_info info_ast with
          | InfoVar (_,_,_,_,"field",_,_) ->    
                 info_ast  
          | _ -> raise(MauvaiseUtilisationIdentifiant id)
  (* Renvoie l'info ast associée au champ *)
  and getField tds affectable = 
      match affectable with 
        | AstSyntax.Field(idv1,id) -> Ident (fieldCheck tds id)::getField tds idv1
        | AstSyntax.Val(idv) -> getField tds idv
        | Ident _ -> let nidv = analyse_tds_affectable tds affectable in [nidv]
             

(** Toutes les fonctions analyses de la passe Tds Rat **)

(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e = 

    match e with
     
    | AstSyntax.AppelFonction (func_name, e_list) -> 
    begin
    let opt = chercherGlobalement tds func_name in

      match opt with 

        | None -> raise (IdentifiantNonDeclare func_name)
        | Some info_ast -> match info_ast_to_info info_ast with
          | InfoFun _ -> let ne_list = List.map (analyse_tds_expression tds) e_list in


              AstTds.AppelFonction (info_ast, ne_list)
          | _ -> raise(MauvaiseUtilisationIdentifiant func_name)
    end
      | AstSyntax.Affectable affectable  -> 
        begin
          match affectable with
           | AstSyntax.Ident n -> let opt = chercherGlobalement tds n in
                begin
                match opt with
                  | None -> raise(IdentifiantNonDeclare n)
                  | Some info_ast -> match info_ast_to_info info_ast with
                                      | InfoVar (_,_,_,_,"var",_,_) ->  Affectable (Ident info_ast)     
                                      | InfoConst(_,v) -> Entier v
                                      | _ -> raise(MauvaiseUtilisationIdentifiant n)
                end                    
          | _ ->
            let nidv = analyse_tds_affectable tds affectable in
            Affectable nidv
    
               
        end
                                     
      | AstSyntax.Booleen b -> (AstTds.Booleen b)
      | AstSyntax.Entier k -> (AstTds.Entier k)
      | AstSyntax.Unaire (u, expr) -> let ne = analyse_tds_expression tds expr in
          AstTds.Unaire (u,ne)
      | AstSyntax.Binaire(b,e1,e2) -> let (ne_1,ne_2) = (analyse_tds_expression tds e1,analyse_tds_expression tds e2) in 
          AstTds.Binaire(b,ne_1,ne_2)
      | AstSyntax.Malloc t -> Malloc (initType tds t)
      | AstSyntax.NullPointer -> NullPointer
      | AstSyntax.Adress n ->
       begin
        let opt = chercherGlobalement tds n in
          begin
          match opt with
              | None -> raise (IdentifiantNonDeclare n)
              | Some info_ast ->
                  match info_ast_to_info info_ast with
                  | InfoVar (_,_,_,_,"var",_,_)->  Adress info_ast
                  | _ -> raise(MauvaiseUtilisationIdentifiant n)
                   
          end
      end
    | AstSyntax.StructVars le -> let nle = List.map (analyse_tds_expression tds) le in
          StructVars nle
      
(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
          begin
            match chercherLocalement tds n with
            | None ->
                (* L'identifiant n'est pas trouvé dans la tds locale, 
                il n'a donc pas été déclaré dans le bloc courant *)
                (* Vérification de la bonne utilisation des identifiants dans l'expression *)
                (* et obtention de l'expression transformée *) 
                let typeInit,_ = checkType tds [] n t in
                let iaList = linkFields tds t (initId t n) in
                let id = checkId tds n in
                let ne = analyse_tds_expression tds e in
                (* Création du pointeur sur l'information *)
                let info = createInfoVar tds t id iaList in
                (* Création de l'information associée à l'identfiant *)
                let ia = info_to_info_ast info in      
                ajouter tds id ia;
                (*afficher_globale tds;
                print_string "\n\n\n\n";*)
                (* Ajout de l'information (pointeur) dans la tds *)
                Declaration (typeInit, ia, ne)
                (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
                et l'expression remplacée par l'expression issue de l'analyse *)
           
            | Some _ ->
                (* L'identifiant est trouvé dans la tds locale, 
                il a donc déjà été déclaré dans le bloc courant *) 
                raise (DoubleDeclaration n)
          end

  | AstSyntax.Affectation (idv,e) ->
      let nidv = analyse_tds_affectable tds idv in
      let ne = analyse_tds_expression tds e in Affectation(nidv,ne)
         
          
  | AstSyntax.PlusEgal(idv,e) ->
    let nidv = analyse_tds_affectable tds idv in
    let ne = analyse_tds_expression tds e in PlusEgal(nidv,ne)
        
        
  | AstSyntax.Constante (n,v) -> 
      begin
        match chercherLocalement tds n with
        | None -> 
        (* L'identifiant n'est pas trouvé dans la tds locale, 
        il n'a donc pas été déclaré dans le bloc courant *)
        (* Ajout dans la tds de la constante *)
        ajouter tds n (info_to_info_ast (InfoConst (n,v))); 
        (* Suppression du noeud de déclaration des constantes devenu inutile *)
        Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale, 
          il a donc déjà été déclaré dans le bloc courant *) 
          raise (DoubleDeclaration n)
      end
      
  | AstSyntax.Affichage e -> 
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) -> 
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) -> 
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds b in
      (* Renvoie la nouvelle structure de la boucle *)
      TantQue (nc, bast)
  | AstSyntax.Retour (e) -> 
      (* Analyse de l'expression *)
      let ne = analyse_tds_expression tds e in
      Retour (ne)
  | AstSyntax.DeclarationType (tid,t) -> 
      begin 
        match chercherLocalement tds tid with
          | None ->
              (* L'identifiant n'est pas trouvé dans la tds locale, 
              il n'a donc pas été déclaré dans le bloc courant *)
              (* Vérification de la bonne utilisation des identifiants dans l'expression *)
              (* et obtention de l'expression transformée *) 
              (* Création de l'information associée à l'identfiant *)
              let nt = checkNamedType tds tid t in
              let info = InfoType (tid,nt) in
              (* Création du pointeur sur l'information *)
              let ia = info_to_info_ast info in
              (* Ajout de l'information (pointeur) dans la tds *)
              ajouter tds tid ia;
              (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
              et l'expression remplacée par l'expression issue de l'analyse *)
              DeclarationType(ia,nt)
          | Some _ ->
              (* L'identifiant est trouvé dans la tds locale, 
              il a donc déjà été déclaré dans le bloc courant *) 
              raise (DoubleDeclaration tid)
        end

  (* Vérifie si l'identifiant n a déjà été déclaré dans le cas de déclaration des champs d'un struct *)
  (* Ex : struct {int x int y} y lève l'exception DoubleDeclaration y                                *)
  and checkId tds n = 
    match chercherLocalement tds n with
    | None -> n
    | Some _ ->
        raise (DoubleDeclaration n)
  
  (*Type à placer dans l'InfoVar, les structs doivent avoir le type struct dès la passe TDS         *)
  (*Cela rend possible de faire les vérifications des expressions d'accès à un champ d'un struct    *)
  (*Dans le cas contraire, ex : struct {int x int y} d = {1 2};                                     *)
  (*                            int r = 0;                                                          *)     
  (*                            int a = (d.r) //ne lève pas l'exception si type(d) = Undefined      *)     
  (*                                          //lève MauvaiseUtilisationIdentifiant("Not a field")  *)
  (*                                          //sinon                                               *)                   
  and typeSet tds t = 
    match t with
      | Struct _ -> t
      | TypeNomme _ -> typeSet tds (initType tds t)
      | Pointer t -> Pointer (typeSet tds t)
      | _ -> Undefined
  
  (*Créer l'info associée à une variable                                                             *)
  (*tds->typ->string->                                                                               *)

  and createInfoVar tds t id ia =
      (*let infoList = List.map(info_ast_to_info) ia in*)
      match t with
        | TypeNomme _ ->  InfoVar (id,typeSet tds t, 0, "","var","named",ia)
        | _ -> InfoVar (id,typeSet tds t, 0, "","var","",ia)
  
  (*Nom du  *)
  and initId t id = 
      match t with
        | TypeNomme _ -> id
        | _ -> ""


(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale 
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in 
  (* Analyse des instructions du bloc avec la tds du nouveau bloc 
  Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc) li in 
   nli
     (*afficher_locale tdsbloc ; *)  (* décommenter pour afficher la table locale *)
   

(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li))  =    
    let opt = chercherGlobalement maintds n in
       match opt with
        | None -> 
          begin    
            let (type_list,id_list) = List.split lp in
            let nid_list = dupCheck id_list in
            let nt = initType maintds t in
            let tds_func = creerTDSFille maintds in
            let ntypeList = List.map2(checkType tds_func [] ) id_list type_list in
            let nt1,_ = List.split ntypeList in
            let info_fun = info_to_info_ast (InfoFun(n,nt,nt1)) in
            ajouter maintds n (info_fun);
            let iaList = List.map2(linkFields tds_func) nt1 id_list in 
            let info_ast_list = create_info_ast tds_func type_list id_list "var" "" iaList in
            ajouter_vars tds_func info_ast_list id_list;
            let bloc = analyse_tds_bloc tds_func li in                      
            let info_id_list = List.map (chercherLocalement tds_func) nid_list in
            let type_id_list = List.combine type_list (List.map Option.get info_id_list) in
            AstTds.Fonction(nt,info_fun,type_id_list,bloc)
          end
        | Some _ -> raise (DoubleDeclaration n)


(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (types,fonctions,prog)) =
  let tds = creerTDSMere () in
  let tidList = createTidList types in
  let _ = dupCheck tidList in
  let namedTypes = List.map(analyse_tds_instruction tds) types in
  let nf = List.map (analyse_tds_fonction tds) fonctions in 
  let nb = analyse_tds_bloc tds prog in
  Programme (namedTypes,nf,nb)
end

