/* Imports. */

%{

open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token <string> TID
%token RETURN
%token PV
%token AO
%token AF
%token PF
%token PO
%token POINT
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token STRUCT
%token TYPEDEF
%token NEW
%token NULL 
%token RAT
%token CALL 
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token PLUS_EQUAL
%token ET
%token MULT
%token INF
%token EOF

(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction list> is
%type <instruction> i
%type <typ> typ
%type <(typ*string) list> dp
%type <expression> e
%type <affectable> affectable
%type <expression list> cp
%type <instruction list> td

(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%

main : lfi = prog EOF     {lfi}

prog :
| lt = td lf = fonc lfi = prog   {let (Programme (lt1,lf1,li))=lfi in (Programme (lt@lt1,lf::lf1,li))}
| ID li = bloc                   {Programme ([],[],li)}

fonc : t=typ n=ID PO p=dp PF AO li=is AF {Fonction(t,n,p,li)}

bloc : AO li = is AF      {li}

is :
|                         {[]}
| i1=i li=is              {i1::li}

i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)}
| TYPEDEF n=TID EQUAL t=typ PV      {DeclarationType (n,t)}
| idv=affectable EQUAL e1=e PV      {Affectation (idv,e1)}
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)}
| PRINT e1=e PV                     {Affichage (e1)}
| IF exp=e li1=bloc ELSE li2=bloc   {Conditionnelle (exp,li1,li2)}
| WHILE exp=e li=bloc               {TantQue (exp,li)}
| idv=affectable PLUS_EQUAL e1=e PV      {PlusEgal (idv,e1)}
| RETURN exp=e PV                   {Retour (exp)}

dp :
|                         {[]}
| t=typ n=ID lp=dp        {(t,n)::lp}

typ :
| BOOL    {Bool}
| INT     {Int}
| RAT     {Rat}
| STRUCT AO tl = dp AF {Struct tl}
| n = TID {TypeNomme n}
| t = typ MULT {Pointer t}

affectable :
| n=ID                     {Ident n}
| PO MULT idv = affectable PF   { Val idv }
| PO idv = affectable POINT n=ID PF  {Field (idv,n)}


e : 
| CALL n=ID PO lp=cp PF   {AppelFonction (n,lp)}
| CO e1=e SLASH e2=e CF   {Binaire(Fraction,e1,e2)}
| id = affectable         {Affectable id}
| TRUE                    {Booleen true}
| FALSE                   {Booleen false}
| e=ENTIER                {Entier e}
| NULL                    {NullPointer}
| PO NEW t=typ PF         {Malloc t}
| ET n=ID                 {Adress n}
| NUM e1=e                {Unaire(Numerateur,e1)}
| DENOM e1=e              {Unaire(Denominateur,e1)}
| PO e1=e PLUS e2=e PF    {Binaire (Plus,e1,e2)}
| PO e1=e MULT e2=e PF    {Binaire (Mult,e1,e2)}
| PO e1=e EQUAL e2=e PF   {Binaire (Equ,e1,e2)}
| PO e1=e INF e2=e PF     {Binaire (Inf,e1,e2)}
| PO exp=e PF             {exp}
| AO le=cp AF             {StructVars (le)}


cp :
|               {[]}
| e1=e le=cp    {e1::le}

td :

|                                      {[]}
| TYPEDEF n=TID EQUAL t=typ PV lt = td {DeclarationType(n,t)::lt}