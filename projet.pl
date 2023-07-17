/*A Box et T Box*/
equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).
cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).



/**************************************************************************/
/**************************Partie 1****************************************/
/**************************************************************************/



/*Prédicat concept : vérifie la correction syntaxique et sémantique de la ABox et de la TBox.*/
concept(A) :- setof(X,cnamea(X),L), member(A,L),!. /*On vérifie que A est bien un concept atomique (cnamea) de la TBox*/
concept(A) :- setof(X,cnamena(X),L), member(A,L), equiv(A,B), concept(B),!. /*On vérifie que A est un concept non atomique de la TBox*/
concept(not(A)) :- concept(A),!.
concept(or(A,B)) :- concept(A), concept(B),!.
concept(and(A,B)) :- concept(A), concept(B),!.
concept(some(A,B)) :- setof(X,rname(X),L), member(A,L), concept(B),!. /*On vérifie que A est un rôle de la TBox*/
concept(all(A,B)) :-  setof(X,rname(X),L), member(A,L), concept(B),!. /*On vérifie que A est un rôle de la TBox*/
concept(inst(A,B)) :- setof(X1,iname(X1),L1), member(A,L1), /*On vérifie que A est un iname*/
		     		  				setof(X2,cname(X2),L2), member(B,L2),!. /*On vérifie que B est un cname*/
concept(instR(A,B,C)) :- setof(X1,iname(X1),L1), member(A,L1), /*On vérifie que A est un iname*/
						 						 setof(X2,iname(X2),L2), member(B,L2), /*On vérifie que B est un iname*/
						 					 	 setof(X3,rname(X3),L3), member(C,L3),!. /*On vérifie que C est un rname*/





/*Prédicat autoref : teste si un concept est autoréférent, ce qui pourrait faire tourner en boucle le programme*/
autoref(A,A,L):-!. /*Cas de base*/
autoref(A,B,L) :- member(B,L),!. /*Si B est déjà dans la liste alors le concept est autoréférent*/
autoref(A,B,L) :- equiv(B,X), autoref(B,X,[A|L]),!. /*Si B n'est pas un concept atomique, il faut explorer son expression conceptuelle équivalente*/
autoref(A,and(B,C),L) :- autoref(A,B,L),!.
autoref(A,and(B,C),L) :- autoref(A,C,L),!.
autoref(A,or(B,C),L) :- autoref(A,B,L),!.
autoref(A,or(B,C),L) :- autoref(A,C,L),!.
autoref(A,not(B),L) :- autoref(A,B,L),!.
autoref(A,some(R,C),L) :- autoref(A,C,L),!.
autoref(A,all(R,C),L) :- autoref(A,C,L),!.


/*Prédicat nnf : mettre sous forme normale négative*/
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

/*Prédicat remplace_cnamena : remplace dans une expression complexe les concepts non atomiques
par leur expression conceptuelle composée uniquement de concepts atomiques*/
remplace_cnamena(A,A) :- cnamea(A),!. /*cas de base*/
remplace_cnamena(A,X) :- cnamena(A), equiv(A,B), remplace_cnamena(B,X),!.
remplace_cnamena(and(A,B),X) :- remplace_cnamena(A,R1), remplace_cnamena(B,R2), X=and(R1,R2),!.
remplace_cnamena(or(A,B),X) :- remplace_cnamena(A,R1), remplace_cnamena(B,R2), X=or(R1,R2),!.
remplace_cnamena(not(A),X) :- remplace_cnamena(A,R), X=not(R),!.
remplace_cnamena(some(R,C),some(R,R2)) :- rname(R), remplace_cnamena(C,R2), X=some(R,R2),!.
remplace_cnamena(all(R,C),all(R,R2)) :- rname(R), remplace_cnamena(C,R2), X=all(R,R2),!.

/*Prédicat traitement_Tbox : vérification de la correction syntaxique et sémantique d'un concept complexe de la TBox et mise sous forme nnf*/
traitement_Tbox(A,Res) :- equiv(A,B), /*On récupère un concept non atomique et son expression conceptuelle*/
						 						  concept(A), concept(B), /*on vérifie la correction synthaxique et sémantique*/
												  not(autoref(A,B,[])), /*on vérifie que le concept n'est pas autoréférent*/
												  remplace_cnamena(B,X), /*l'expression conceptuelle n'est composée que de concepts atomiques*/
												  nnf(X,Res). /*on met l'expression conceptuelle sous forme nnf*/


/*Prédicat traitement_Abox : vérification de la correction syntaxique et sémantique d'un concept complexe de la ABox
et remplace les concepts non atomiques par leur expression conceptuelle ne contenant que des concepts atomiques*/
traitement_AboxConcept(I,Res) :- inst(I,C), concept(C), remplace_cnamena(C,R), nnf(R,Res).
traitement_AboxRole(I,C,R) :- instR(I,C,R), concept(instR(I,C,R)) .

traitement_Abox(I,R) :- traitement_AboxConcept(I,R).
traitement_Abox(I,(C,R)) :- traitement_AboxRole(I,C,R).





/**************************************************************************/
/**************************Partie 2****************************************/
/**************************************************************************/

/*Prédicat programme : correspond au point d'entrée du programme*/
programme :- premiere_etape(Tbox,Abi,Abr),
			 			 deuxieme_etape(Abi,Abi1,Tbox),
			 		 	 troisieme_etape(Abi1,Abr).

/*Prédicat premiere_etape : liste représentant la TBox, les assertions de concepts de la ABox et les assertions de rôles de la ABox*/
premiere_etape(TBox, ABoxConcept, ABoxRole) :- setof((A,B), traitement_Tbox(A,B), TBox),
                                               setof((I,C), traitement_AboxConcept(I,C), ABoxConcept),
											   									 		 setof((I,C,R), traitement_AboxRole(I,C,R), ABoxRole).

/*Prédicat deuxieme_etape : permet de récupérer Abi1 la ABox complétée par la propriété à démontrer*/
deuxieme_etape(Abi,Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :- nl, write("Entrez le numero du type de proposition que vous voulez demontrer :"),
																												nl, write("1 Une instance donnee appartient a un concept donne."),
																												nl, write("2 Deux concepts n'ont pas d'elements en commun (ils ont une intersection vide)"),
																												nl, read(R),
																												suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(R,Abi,Abi1,Tbox) :- nl,write("Cette reponse est incorrecte."),
				          				nl, saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

/*Prédicat acquisition_prop_type1*/
acquisition_prop_type1(Abi, Abi1, Tbox) :- nl, write("Saisir instance : "),
										   										 nl, read(I), /*On récupère l'instance*/
										   								 		 nl, write("Saisir concept : "),
										   								 		 nl,read(C), /*On récupère le concept*/
										   								 		 remplace_cnamena(C,R), /*On remplace de manière récursive les identificateurs de concepts complexes par leur définition*/
										   								 		 nnf(not(R),Res), /*On met la négation du concept sous forme nnf*/
										   								 		 Abi1 = [(I,Res) | Abi]. /*On ajoute la négation de l'assertion à la ABox*/

/*Prédicat acquisition_prop_type2*/
acquisition_prop_type2(Abi, Abi1, Tbox) :- nl, write("Saisir concept C1 : "),
										   										 nl,read(C1), /*On récupère le concept*/
										   								 		 nl, write("Saisir concept C2 : "),
										   								 		 nl,read(C2), /*On récupère le concept*/
										   								 		 remplace_cnamena(and(C1,C2),R), /*On remplace de manière récursive les identificateurs de concepts complexes par leur définition*/
										   								 		 nnf(R,Res), /*On met le concept sous forme nnf*/
										   								 		 genere(Inst), /*On génère un nom pour l'instance*/
										   								 		 Abi1 = [(Inst,Res)| Abi]. /*On ajoute l'assertion*/



/**************************************************************************/
/**************************Partie 3****************************************/
/**************************************************************************/


troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
														resolution(Lie,Lpt,Li,Lu,Ls,Abr),
														nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

/*Prédicat tri_Abox permettant de trier la ABox*/
tri_Abox([],[],[],[],[],[]). /*Cas de base*/
tri_Abox([X|L],[X|Lie],Lpt,Li,Lu,Ls) :- X=(I,some(R,C)), tri_Abox(L,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([X|L],Lie,[X|Lpt],Li,Lu,Ls) :- X=(I,all(R,C)), tri_Abox(L,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([X|L],Lie,Lpt,[X|Li],Lu,Ls) :- X=(I,and(C1,C2)), tri_Abox(L,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([X|L],Lie,Lpt,Li,[X|Lu],Ls) :- X=(I,or(C1,C2)), tri_Abox(L,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([X|L],Lie,Lpt,Li,Lu,[X|Ls]) :- X\=(I,some(R,C)), X\=(I,all(R,C)),
																				X\=(I,and(C1,C2)), X\=(I,or(C1,C2)),
																				tri_Abox(L,Lie,Lpt,Li,Lu,Ls).


/*Prédicat resolution permettant de savoir s'il y un clash dans la ABox ou de continuer l'exploration*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- test_clash(Ls). /*Si on a un clash qui renvoie true : il faut désormais savoir si les autres feuilles ont aussi un clash ou non*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- complete_some(Lie,Lpt,Li,Lu,Ls,Abr). /*Si on n'a pas de clash il faut savoir si on peut appliquer l'une des règles de résolution*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- transformation_and(Lie,Lpt,Li,Lu,Ls,Abr).
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-	deduction_all(Lie,Lpt,Li,Lu,Ls,Abr).
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- !,nl, write("================= NOEUD OUVERT =================="),/*Si aucune règle de résolution ne peut s'appliquer alors que l'on n'a pas eu de clash, alors la feuille est ouverte, on n'a donc pas démontré l'assertion de base*/
																			nl, write("Un noeud est ouvert. La proposition est donc fausse."),
																			nl, notation_infixe(Ls),
																			nl, write("================================================="),nl,
																			test_clash(Ls),!. /*renvoie false*/

/*Prédicat complete_some cherchant une assertion de concept de la forme (I,some(R,C)) dans Lie*/
complete_some([(A,some(R,C))|Lie],Lpt,Li,Lu,Ls,Abr) :- genere(B), /*On génère une instance B*/
																										   evolue((B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*On ajoute l'assertion de concept*/
																										   nl, write("======= Application de la regle some ======="),
																										   nl, affiche_evolution_Abox(Ls, [(A,some(R,C))|Lie], Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, [(A,B,R)|Abr]),
																										   nl,write("============================================"),nl,
													 													   !,resolution(Lie1, Lpt1, Li1, Lu1, Ls1, [(A,B,R)|Abr]). /*On ajoute l'assertion de rôle*/

/*Prédicat transformation_and cherchant une assertion de concept de la forme (I,and(C1,C2)) dans Li*/
transformation_and(Lie,Lpt,[(A,and(C,D))|Li],Lu,Ls,Abr) :- evolue((A,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
																												   evolue((A,D),Lie1,Lpt1,Li1,Lu1,Ls1,Lie2,Lpt2,Li2,Lu2,Ls2),
																												   nl, write("======= Application de la regle intersection ======="),
																												   nl, affiche_evolution_Abox(Ls, Lie, Lpt, [(A,and(C,D))|Li], Lu, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
																												   nl, write("===================================================="),nl,
																												   !,resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr). /*On ajoute à Ls les deux assertions et l'on résoud*/

/*Prédicat deduction_all cherchant une assertion de concept de la forme (I,all(R,C)) dans Lpt*/

deduction_all(Lie,[(A,all(R,C))|Lpt],Li,Lu,Ls,Abr) :- not(member((A,B,R), Abr)), /*S'il n'y a pas d'assertion de la forme <a,b>:R on résoud */
													  													!,resolution(Lie, Lpt, Li, Lu, Ls, Abr).

deduction_all(Lie,[(A,all(R,C))|Lpt],Li,Lu,Ls,Abr) :- member((A,B,R), Abr), /*Tant qu'il y a une assertion de la forme <a,b>:R ...*/
																										  evolue((B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*... on ajoute à Abe b:C */
																										  enleve((A,B,R), Abr, Abr1),
																										  nl,write("======= Application de la regle pour tout ======="),
																								      nl,affiche_evolution_Abox(Ls, Lie, [(A,all(R,C))|Lpt], Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
																								      nl,write("================================================="),nl,
																								      !,deduction_all(Lie1,[(A,all(R,C))|Lpt1],Li1,Lu1,Ls1,Abr1). /*On garde bien l'assertion (I,all(R,C)) en tête de liste*/


/*Prédicat transformation_or cherchant une assertion de concept de la forme (I,or(C1,C2)) dans Lu*/
transformation_or(Lie,Lpt,Li,[(A,or(C,D))|Lu],Ls,Abr) :- evolue((A,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*On ajoute l'assertion (A,C) dans la ABox*/
																												 nl,write("======= Application de la regle OU (1) ======="),
																												 nl,affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(A,or(C,D))|Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
																												 nl,write("=============================================="),nl,
																											   !,resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr), /*On résoud une branche*/
																 												 evolue((A,D),Lie,Lpt,Li,Lu,Ls,Lie2,Lpt2,Li2,Lu2,Ls2), /*On ajoute l'assertion (A,D) dans la ABox*/
																												 nl,write("======= Application de la regle OU (2) ======="),
																												 nl,affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(A,or(C,D))|Lu], Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
																												 nl,write("=============================================="),nl,
																												 !,resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr). /*On résoud une branche*/

/*Prédicat evolue intégrant dans l'une des listes l'assertion A*/
evolue((I,some(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt,Li,Lu,Ls) :- Lie1=[(I,some(R,C))|Lie],!.
evolue((I,all(R,C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt1,Li,Lu,Ls) :- Lpt1=[(I,all(R,C))|Lpt],!.
evolue((I,and(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li1,Lu,Ls) :- Li1=[(I,and(C1,C2))|Li],!.
evolue((I,or(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu1,Ls) :- Lu1=[(I,or(C1,C2))|Lu],!.
evolue(X,Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1) :- X\=(I,some(R,C)), X\=(I,all(R,C)),
																								X\=(I,and(C1,C2)), X\=(I,or(C1,C2)),
																								Ls1=[X|Ls].

/*Prédicat affiche_evolution_Abox*/
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
	nl, write("====== Avant ======"),
	nl, write("== ABox concept : "),
	notation_infixe(Ls1),
	notation_infixe(Lie1),
	notation_infixe(Lpt1),
	notation_infixe(Li1),
	notation_infixe(Lu1),
	nl, write("== ABox role : "),
	afficheAbr(Abr1),
	nl,nl, write("====== Apres ======"),
	nl, write("== ABox concept : "),
	notation_infixe(Ls2),
	notation_infixe(Lie2),
	notation_infixe(Lpt2),
	notation_infixe(Li2),
	notation_infixe(Lu2),
	nl, write("== ABox role : "),
	afficheAbr(Abr2),nl.


/*Prédicat test_clash permettant de savoir s'il y a un clash*/
test_clash(Ls) :- member((I,X),Ls), member((I,not(X)),Ls),
	              	nl,write("================= CLASH ======================="),
								  notation_infixe(Ls),
								  nl,write("==============================================="),!.

/*Le prédicat notation_infixe permet de transformer une notation préfixe en notation infixe*/
notation_infixe([]).
notation_infixe([(I,A)|L]) :- nl, write(I), write(" : "), notation_infixe(A), notation_infixe(L).
notation_infixe(C) :- cnamea(C), write(C).
notation_infixe(some(R,C)) :- write("∃"), write(R), write(".("), notation_infixe(C), write(")").
notation_infixe(or(C1,C2)) :- write("("), notation_infixe(C1), write(" ⊔ "), notation_infixe(C2), write(")").
notation_infixe(not(A)) :- write("¬("), notation_infixe(A), write(")").
notation_infixe(all(R,C)) :- write("∀"), write(R), write(".("), notation_infixe(C), write(")").
notation_infixe(and(C1,C2)) :- write("("), notation_infixe(C1), write(" ⊓ "), notation_infixe(C2), write(")").

afficheAbr([]).
afficheAbr([(A,B,R)|L]) :- nl, write("<"), write(A), write(","), write(B), write("> : "), write(R), afficheAbr(L).

/**************************************************************************/
/**************************Fonctions utiles********************************/
/**************************************************************************/

compteur(1).


/*Fonction permettant de concatr deux listes*/
concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

/*Fonction permettant de supprimer X de la liste L1 et renvoie la liste résultante dans L2*/
enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

/*Fonction qui génère un nouvel identificateur qui est fourni en sortie dans Nom*/
genere(Nom) :- compteur(V), nombre(V,L1),
						   concat([105,110,115,116],L1,L2),
						   V1 is V+1,
						   dynamic(compteur/1),
						   retract(compteur(V)),
						   dynamic(compteur/1),
						   assert(compteur(V1)),nl,nl,nl,
						   name(Nom,L2).

nombre(0,[]).

nombre(X,L1) :- R is (X mod 10),
		      			Q is ((X-R)//10),
								chiffre_car(R,R1),
								char_code(R1,R2),
								nombre(Q,L),
								concat(L,[R2],L1).


chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').
