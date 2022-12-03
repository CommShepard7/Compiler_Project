(* Module de la passe de generation de code *)

open Type
open Code
module PasseCodeRatToTam : Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct

  open Tds
  open Ast
  open AstType
  open AstTds

  type t1 = Ast.AstPlacement.programme
  type t2 = string


(* Renvoie la position d'une variable dans un enregistrement   *)
(* Ainsi pour trouver l'adresse d'un champ de l'enregistrement *)
(* il suffit de charger l'adresse  de l'enregistrement et de   *) 
(* lui ajouter le déplacement, ex :                            *)
(* struct {rat x int y} d, @x = @d + 0,@y = @d + 2             *)
let rec getPos affectable ia = 
    match affectable,ia with 
      | Ident ia1,ia2 ->
          begin 
                match info_ast_to_info ia1,info_ast_to_info ia2 with
                  | InfoVar(_,t1,_,_,_,_,_), InfoVar(n2,_,_,_,_,_,_) ->  
                            begin
                              match getPointerType t1 with
                                    | Struct tidList -> let types,ids = List.split(tidList) in
                                          findPos types ids n2
                                    | _ -> failwith "Error"
                              end        
                  | _ -> failwith "Error"
              end
      | _ -> failwith "Error"

(* Fonction auxiliaire récursive pour la recherche de la  *)
(* position d'une variable dans un enregistrement         *)
 and findPos types ids n2 = 
    match types,ids with
      | [],[] -> 0
      | t::ttl,id::tl -> if id == n2 then 0 else getTaille t+findPos ttl tl n2
      | _ -> failwith "Error"
           
(* Renvoie le type pointé, utile pour trouver la position des champs*)
(* dans un *struct *)                           
 and getPointerType t = 
 match t with 
   | Pointer t -> getPointerType t
   | _ -> t

(* analyse_code_affectable : AstPlacement.affectable -> string                   *)
(* Paramètre func : Booléen pour savoir si on se trouve dans une fonction ou pas *)
(* Paramètre affectable : l'affectable à analyser                                *)
(* Gènère le code TAM pour charger l'adresse d'un affectable en sommet de pile   *)
let rec analyse_code_affectable func affectable = 
  match affectable with
      | Ident ia ->
       begin
        match info_ast_to_info ia with 
            | InfoVar(_,t,d,_,_,_,_) -> let s = getTaille t in            
              if func then 
                if (d<0) then "LOADA " ^string_of_int (d- getTaille t + 1)^" [LB]\n",d,s
                else "LOADA " ^string_of_int (d)^" [LB]\n",d,s
              else 
              "LOADA " ^string_of_int (d)^" [SB]\n",d,s
            | _ -> failwith "Error"
       end
      | Field(affectable1,id) ->
       begin
          let c,_,_ = analyse_code_affectable func affectable1 in
          match info_ast_to_info id with
           | InfoVar(_,t,_,_,_,_,_) ->
                let size = getTaille t in
                let s = getPos (getIa affectable1) id in
                    c^"LOADL "^string_of_int (s)^"\nSUBR Iadd\n",0,size
          | _ -> failwith "Error"
       end                                  
      | Val(affectable1) -> 
                let c,_,_ = analyse_code_affectable func affectable1 in
                match getIa affectable1 with
                 | Ident ia ->
                   begin
                    match info_ast_to_info ia with 
                    | InfoVar(_,t,_,_,_,_,_) ->
                        let size = getTaille(getPointerType t) in c^"LOADI (1)\n",0,size
                    | _ -> failwith "Error"
                   end
                | _ -> failwith "Error"
   
  (*Renvoie l'affectable soit le champ, soit l'affectable lui même *)
  (*Ex : getIa ((r.x).z) = z                                       *)
  (*Utilisé pour trouver la position d'un champ dans un struct     *)
  (* à l'interieur d'un autre struct                               *) 
  (* lors du traitement de ((r.x).z), on trouve la position de x   *)
  (* dans r, puis z dans x *)       
  and getIa affectable = 
    match affectable with
      | Ident _ -> affectable
      | Field(_,id) -> Ident id
      | Val(affectable1) -> getIa affectable1
  
(* analyse_code_expression : AstPlacement.expression -> string                   *)
(* Paramètre func : Booléen pour savoir si on se trouve dans une fonction ou pas *)
(* Paramètre e : expression à analyser                                           *)
(* Gènère le code TAM pour une expression                                        *)      
let rec analyse_code_expression func e  = 

   match e with 

   | AstType.AppelFonction (info_ast,e_list) -> 
       let cList = List.map (analyse_code_expression func) e_list in
       let c = List.fold_right(fun s c ->  s^c) cList "" in
       begin
       match info_ast_to_info info_ast with 
        | InfoFun(n,_,_) -> c^"CALL (ST) "^n^"\n"
        | _ -> failwith "Error"
       end
    | AstType.Affectable affectable ->
      
      let c,_,s = analyse_code_affectable func affectable in c^"LOADI ("^string_of_int s^")\n"
      

    | AstType.Booleen b -> if b then "LOADL 1\n" else "LOADL 0\n"
    | AstType.Entier k -> "LOADL "^string_of_int k^"\n"
    | AstType.Unaire(u,e) -> 
    
      let c = analyse_code_expression func e in 
      begin 
      match u with 
      
        | Numerateur -> c^"LOADA -2[ST]\n"^"LOADI (1)\nPOP (1) 2\n"
        | Denominateur -> c^"POP (1) 1\n"

      end
    
    | AstType.Binaire(b,e1,e2) -> 

      let c1 = analyse_code_expression func e1 in 
      let c2 = analyse_code_expression func e2 in

      begin
      match b with 
        
        | Fraction -> c1^c2
        | PlusInt -> c1^c2^"SUBR IAdd\n"
        | PlusRat -> c1^c2^"CALL (ST) RAdd\n"
        | MultInt -> c1^c2^"SUBR  IMul\n"
        | MultRat -> c1^c2^"CALL (ST)  RMul\n"
        | EquInt -> c1^c2^"SUBR IEq\n"
        | EquBool -> c1^c2^"SUBR IEq\n"
        | Inf -> c1^c2^"SUBR ILss\n"

      end
    | AstType.Malloc t -> "LOADL "^string_of_int (getTaille t)^"\n"^"SUBR MAlloc\n"
    | AstType.NullPointer -> "SUBR MVoid\n"
    | AstType.Adress ia -> 
        begin
          match info_ast_to_info ia with
             | InfoVar(_,_,d,b,_,_,_) ->
                               "LOADA "^string_of_int d^"["^b^"]\n"
             | _ -> failwith "Error"
        end
    | AstType.StructVars le -> 
        let cList = List.map(analyse_code_expression func) le in
        let c = List.fold_right(fun s c ->  s^c) cList "" in c

(* analyse_code_instruction : AstPlacement.instruction -> string                 *)
(* Paramètre r : taille des paramètres                                           *)
(* Paramètre s : taille du bloc                                                  *)
(* Paramètre func : Booléen pour savoir si on se trouve dans une fonction ou pas *)
(* Paramètre i : instruction à analyser                                          *)
(* Gènère le code TAM pour une instruction                                       *)           
let rec analyse_code_instruction r s func i = 
  match i with 
    | AstType.Declaration(info_ast,e) -> 
      begin
        match info_ast_to_info info_ast with
       | InfoVar(_,t,d,b,_,_,_) ->
          let s = getTaille t in 
          let c = analyse_code_expression func e in
          "PUSH "^string_of_int s^"\n"^c^"STORE ("^string_of_int s^") "^string_of_int d^"["^b^"]\n"
      | _ -> failwith "Error"
      end
    | AstType.Affectation(affectable,e) -> 
        let ci,_,s = analyse_code_affectable func affectable in
        let ce = analyse_code_expression func e in ce^ci^"STOREI ("^string_of_int s^")\n"    
    | AstType.AffichageInt e -> 
      let c = analyse_code_expression func e in c^"SUBR IOut\n"
    | AstType.AffichageRat e ->
      let c = analyse_code_expression func e in c^"CALL (SB) ROut\n"   
    | AstType.AffichageBool e ->
      let c = analyse_code_expression func e in c^"SUBR BOut\n"    
    | AstType.Conditionnelle(e,b1,b2) -> 
      let cList1,s1 = analyse_code_bloc r s func b1 in 
      let cList2,s2 = analyse_code_bloc r s func b2 in
      let c = analyse_code_expression func e in
      let startLabel = getEtiquette()^"\n" in
      let endLabel = getEtiquette()^"\n" in c^"JUMPIF (0) "^startLabel^cList1^"POP (0) "^string_of_int s1^"\n"^"JUMP "^endLabel^startLabel^cList2^"POP (0) "^string_of_int s2^"\n"^endLabel   
    | AstType.TantQue (e,b) -> 
      let cList,s = analyse_code_bloc r s func b in
      let c = analyse_code_expression func e in
      let startLabel = getEtiquette()^"\n" in
      let endLabel = getEtiquette()^"\n" in startLabel^c^"JUMPIF (0) "^endLabel^cList^"JUMP "^startLabel^endLabel^"POP (0) "^string_of_int s^"\n"  
    | AstType.PlusEgalInt (affectable,e) -> let c1,_,s = analyse_code_affectable func affectable in
                                     let ce = analyse_code_expression func e in 
                                     ce^c1^"LOADI ("^string_of_int s^")\n"^"SUBR IAdd\n"^c1^"STOREI ("^string_of_int s^")\n"
    | AstType.PlusEgalRat (affectable,e) -> let c1,_,s = analyse_code_affectable func affectable in
                                     let c2 = analyse_code_expression func e in                                                                         
                                     c2^c1^"LOADI ("^string_of_int s^")\n"^"CALL (ST) RAdd\n"^c1^"STOREI ("^string_of_int s^")\n"                
    | AstType.Retour e -> 
      let c = analyse_code_expression func e in c^"RETURN ("^string_of_int r^") "^string_of_int s^"\n" 
    | AstType.Empty -> ""
    | AstType.DeclarationType _ -> ""

    (* analyse_code_bloc : AstType.bloc -> AstPlacement.bloc                           *)
    (* Paramètre r : taille des paramètres                                                  *)
    (* Paramètre s : taille du bloc                                                         *)
    (* Paramètre func : Booléen pour savoir si on se trouve dans une fonction ou pas        *)
    (* Paramètre b : bloc à analyser                                                        *)
    (* Gènère le code TAM pour un bloc                                                      *)      
    and analyse_code_bloc r s func b = 
      let cList = List.map (analyse_code_instruction r s func) b in     
      let c = List.fold_right(fun s n -> s^n) cList "" in
      let s = getSizeBloc b in c,s
    
    (*  Renvoie la taille totale d'un bloc  *)
    and getSizeBloc b = 
      match b with 
      | [] -> 0
      | i::tl -> 
          begin
          match i with        
            | AstType.Declaration(info_ast,_) ->
              begin
                match info_ast_to_info info_ast with
                | InfoVar(_,t,_,_,_,_,_) -> let s = getTaille t in   s + getSizeBloc tl
                  
                | _ -> failwith "Error"
              end
            | _ -> getSizeBloc tl
          end
    
(* analyse_code_fonction : AstPlacement.fonction  -> string                      *)
(* Paramètre AstPlacement.Fonction : fonction à analyser                         *)
(* Gènère le code TAM pour une fonction                                          *)      
let rec analyse_code_fonction (AstPlacement.Fonction(info_func,info_typ_var,li)) = 
  let varSize = getSizeVars info_typ_var in
  match info_ast_to_info info_func with
   | InfoFun(n,t,_) -> let sizeReturn = getTaille t in
                       let c,_ = analyse_code_bloc sizeReturn (varSize) true li in n^"\n"^c^"HALT\n\n"
   | _ -> failwith "Error"
  
  (*Renvoie la taille totale des paramètres d'une fonction *)
  and getSizeVars iaList = 
    match iaList with
      | [] -> 0
      | ia::tl -> 
          match info_ast_to_info ia with
           | InfoVar(_,t,_,_,_,_,_) -> getTaille t + getSizeVars tl
           | _ -> failwith "Error"

  (* analyser : AstPlacement.ast -> string                      *)
  (* Paramètre AstPlacement.Programme : le programme à analyser *)
  (* Gènère le code TAM pour le programme                       *)    
let analyser (AstPlacement.Programme (fonctions,prog)) = 
  let hd = getEntete() in
  let cMain,s = analyse_code_bloc 0 0 false prog in
  let cListFunc = List.map (analyse_code_fonction) fonctions in
  let cFunc = List.fold_right(fun s n -> s^n) cListFunc "" in
  (*Generer le code TAM dans un fichier, remplacer path par le chemin du dossier source*)
  ecrireFichier "PATH_SOURCE_ETU" (hd^cFunc^"main\n"^cMain^"POP (0) "^string_of_int s^"\nHALT");
  hd^cFunc^"main\n"^cMain^"POP (0) "^string_of_int s^"\nHALT"
end


