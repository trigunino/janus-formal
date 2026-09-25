# T12 — correction de la cible terminale

Statut : direction de travail retenue sous la délégation explicite de l'utilisateur
du 2026-09-24 ; T12 reste ouvert. Aucune validation personnelle supplémentaire
n'est attendue. La fermeture dépend des preuves ci-dessous.

Audit du 2026-09-24 : `regularGeneralLorentzMetric_isEmpty` prouve que le
repère tangent global lisse demandé par le type historique est impossible
sur D8 réfléchi. `globalCandidateAActionData_isEmpty` en déduit que les
données globales historiques sont vides. Les théorèmes qui prennent ces
données en paramètre ne constituent donc pas une réalisation concrète.
`smoothGeneralLorentzMetric_nonempty` confirme que la géométrie intrinsèque
sans cette exigence existe. La fermeture requiert désormais le raccord de
l'action complète à des données habitables ; aucune élimination du type
vide ne sera utilisée pour remplir le certificat T12.

La reprise construit désormais `intrinsicBulkAction` sur un domaine ouvert
contenant zéro, avec les couplages conservés, et sa vraie Hessienne symétrique
`intrinsicBulkHessian`. Bulk et bord utilisent `finiteSmoothTangentFrame` ;
le cœur C3 est fidèle sur sa projection C2. La base GHY à deux feuilles et
les évaluations conjointement C2 de la métrique et de Dg sur le graphe mobile
sont construites. Les tangentes sont reconstruites dans la famille redondante ;
leur contraction métrique C2 coïncide avec le pullback lisse. Le lift fidèle,
son domaine non nul, la densité induite positive et l'inverse ambiant mobile
sont construits avec leurs accords géométriques. La normale unitaire C2
est désormais construite sur un ouvert contenant le fond au paramètre 1,
avec accord géométrique exact. Les jets spatiaux de latitude, la dérivée
des tangentes mobiles et la connexion de Koszul sont C2 et raccordés aux
champs lisses réels. La contraction en seconde forme, l'action GHY C2
complète et le raccord H11 global restent à obtenir.

Le cœur commun impose la compatibilité des deux métriques C3 avec les
métriques du bulk et partage un seul déplacement normal. Il est complet,
son oubli vers bulk × déplacement est injectif et la Hessienne du bulk
s'y transporte exactement. La base des domaines du bord est admissible
pour tout paramètre fixé, notamment 1. Aucun terme GHY n'est encore ajouté
à cette action sur le cœur commun.

La restriction réelle du bulk aux champs B donne exactement
`H(jB B,jB C) = -P(B,C)`, avec P défini par l'intégrale des champs.
Le Lorenz projeté continu coïncide avec le codifférentiel géométrique sur
les potentiels lisses. Pour les quatre composantes des ghosts temporels
périodiques, le FP intrinsèque vaut exactement -f'' sur tout le quotient,
par calcul du courant et de la densité dans les mêmes cartes réelles.
Ces identités n'impliquent pas la propriété Fredholm globale.

La colonne mixte est également calculée : H(jB B,jA A) vaut l'intégrale
B·δA. La projection qui efface uniquement les champs non minimaux conserve
exactement EH, interaction, Maxwell, SpinC et LL. Sa Hessienne physique
est le pullback prouvé de la Hessienne du bulk ; ses colonnes B et ghosts
sont nulles pour tous les couplages. Les contributions GHY ne sont pas
incluses dans cette conclusion.

Les secteurs BRST difféomorphe et abélien pairé lisses s'insèrent fidèlement
dans le bulk. Leurs lectures physiques sont celles des différentiels
natifs, avec le signe abélien sA = -dc. L'action bulk et sa vraie Hessienne
se décomposent exactement en parties physique et BRST. Les colonnes non
minimales de cette Hessienne BRST coïncident avec celles du bulk ; les
pairings B/B et B/A sont donc aussi calculés pour l'action BRST native.
Cela ne constitue pas encore une réalisation Fredholm du complexe réduit.

Pour le secteur abélien, Lorenz et FP sont réalisés en familles C∞ de CLM
sur le domaine métrique. L'action BRST native est identifiée à K(h)(u,u),
avec K une vraie forme bilinéaire continue C2 en h. Sa Hessienne en zéro
vaut exactement K(0)(u,v) + K(0)(v,u), même avec directions métriques.
Le gel des coefficients au second ordre est prouvé par calcul différentiel,
sans hypothèse de pairing ni de réalisation. Le transport au graphe pairé
et le raccord analogue du secteur difféomorphe restent à composer.

Aux poids Einstein opposés et aux deux métriques intrinsèques égales,
la colonne complète de chaque ghost difféomorphisme partagé est nulle.
Pour une période positive, leur insertion fidèle donne un noyau infini
du bulk non réduit. Une réalisation fidèle sur ces ghosts, préservant
ce pairing sur des tests denses, ne peut donc avoir un noyau fini.
La forme bilinéaire descend par la fermeture de leur image lisse réelle.
Cela ne prouve ni la descente de l'action ou du BRST, ni la propriété
Fredholm du quotient, ni l'impossibilité de toutes les réductions autorisées.

L'injectivité H1 vers L2 et les domaines minimaux H1 du FP et de son adjoint
formel sont maintenant établis sans données vides. L'adjonction s'étend aux
deux graphes minimaux L2 ; le FP intrinsèque y est symétrique et son défaut
de pairing des ghosts est nul. Aucune égalité avec le domaine maximal ni
propriété Fredholm n'est déduite de ces résultats.

Le raccord sectoriel à la fibre D9/Friedrichs positive est exclu par
`no_actual_to_fullFriedrichs_sector_pairing` : un champ Nakanishi–Lautrup
pur non nul a un auto-pairing strictement négatif, H11 compris, alors que
sa cible sectorielle a un pairing non négatif. La densité L2 ne change pas
cette incompatibilité.

## Direction retenue

Conserver le critère `hessianMatchesNaturalFredholmFamily`, la même action,
la géométrie réelle, les ghosts et antighosts, H11 et les quotients justifiés.
Remplacer uniquement la cible D9 positive imposée par une famille signée
construite depuis les opérateurs réels. Ne pas imposer les poids d'un modèle
modal avant d'avoir prouvé leur accord avec l'opérateur géométrique.

La fermeture exige toujours une preuve concrète du transport du Hessien,
des domaines et de la propriété Fredholm globale ; puis le raccord à la
ligne de Quillen existante, le certificat terminal, la façade et l'audit.
Aucune de ces conclusions ne devient une hypothèse. La densité L2 acquise
ne sera pas utilisée comme une densité en norme de graphe.

Cette correction retire une cible contradictoire ; elle ne prouve pas
que la famille signée réelle est Fredholm. Si cette propriété échoue dans
le cadre autorisé, T12 devra rester ouvert avec l'obstruction précise.

Vérification du 2026-09-24 : audit Lean gardé des deux théorèmes ci-dessus
vert (pic 3880 Mo), dépendances limitées à propext, Classical.choice et
Quot.sound. Aucun changement du statut terminal T12.
