# T12 : pairing matière–LL et obstruction BRST → D9

## Résultat positif

`strong_actualMatterLL_pairing_eq_physicalZero` établit le pairing exact entre
le Riesz augmenté réel et la fibre physique de Friedrichs à paramètre zéro,
sur le cœur réduit matière–LL de la carte forte centrée. Il utilise les données
géométriques, la réalisation matière et l'extension physique existantes, sans
hypothèse supplémentaire d'égalité des formes transportées et sans
`ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D`.

Source : `P0EFTJanusProgramPT12StrongMatterLLUnconditionalPairing4D.lean`.

## Obstruction démontrée

- `d9Real_pairing_nonneg` : le D9 installé, de poids `normSquared (covector i)`,
  a un pairing réel non négatif pour tous les modes, covecteurs et éléments
  de son domaine maximal.
- `exists_abelianBRST_negative_direction` : un champ Nakanishi–Lautrup abélien
  pairé constant non nul donne un pairing BRST strictement négatif.
- `no_abelianBRST_actual_to_D9_pairing` : aucune application du cœur BRST
  abélien vers ce domaine D9 ne préserve tous les auto-pairings. Le théorème
  n'exige même pas que l'application soit linéaire ou injective.
- `pureAbelianNakanishiLautrupCore_physicalHessian_left_zero` et
  `pureAbelianNakanishiLautrupCore_augmented_pairing_self` : sur ce témoin,
  la colonne physique H11 est nulle et le pairing réel augmenté vaut
  exactement `-‖globalPairedGaugeLieL2LinearMap ... field‖²`.

Sources : `P0EFTJanusProgramPT12D9NonnegativePairing4D.lean`,
`P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D.lean`,
`P0EFTJanusProgramPT12AbelianBRSTActualD9NoGo4D.lean` et
`P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D.lean`, dans
`JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates/`.

## Conséquence pour la fermeture

L'obstruction est maintenant prouvée pour la fibre complète de Friedrichs,
augmentation H11 incluse : `no_actual_to_fullFriedrichs_sector_pairing`
exclut toute application du cœur réel complet qui préserve les auto-pairings
et envoie les champs Nakanishi–Lautrup purs dans le noyau du readout
matière–LL cible. Aucune linéarité ou injectivité n'est nécessaire.
Cette conservation du contenu sectoriel suffit à rendre la fermeture
demandée incompatible avec la cible BRST positive actuellement installée.

La réalisation sectorielle actual→D9 demandée est impossible avec le D9
positif actuel. L'obstruction abélienne suffit à bloquer cette identification
globale. Les constructions signées ci-dessous préparent une autre cible ;
elles n'établissent pas encore son accord modal avec le cœur réel.

Le quotient LL auxiliaire/mesure existe déjà dans
`P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D.lean` et demeure la voie LL.
Les gates Quillen existantes sont conservées. Aucun certificat terminal
global n'est ajouté et T12 n'est pas coché.

## Avancée signée du 22 septembre 2026

- `P0EFTJanusProgramPT12SignedBRSTGram4D.lean` construit les opérateurs de
  Gram et les termes croisés signés par adjoints, avec leurs pairings exacts.
- `P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D.lean` identifie
  `pairedAbelianSignedRiesz` au Riesz abélien pairé réel sur le graphe
  complété et retrouve la polarisation BRST sur le cœur lisse. La complétion
  du carré conserve le terme négatif Nakanishi–Lautrup et les deux ghosts.
- `P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D.lean`
  identifie `diagonalDiffeomorphismSignedRiesz` au Riesz difféomorphisme
  diagonal réel, avec les poids sectoriels et l'unique triplet nonminimal
  partagé. Son pairing lisse retrouve également l'action BRST réelle.
- `P0EFTJanusProgramPT12SignedBRSTAugmentedPairing4D.lean` assemble ces deux
  opérateurs avec les formes matière–LL et la forme physique complète.
  `signedBRST_retains_all_physical_columns` expose l'accord H11 déjà fourni
  par l'extension physique existante ; il ne construit pas une nouvelle
  extension ni une estimation spectrale des colonnes.
- `P0EFTJanusProgramPT12SignedD9Reference4D.lean` double le multiplicateur
  D9 avec les poids opposés. La référence est densément définie,
  autoadjointe et fermée ; elle est Fredholm sous les données existantes
  d'ellipticité à modes caractéristiques finis. Le module prouve aussi la
  décomposition signée exacte du symbole abélien nonminimal.

Ces égalités de Gram concernent les Riesz bornés des graphes réels. Une
complétion de carrés est une congruence, pas une identification isométrique
avec la référence modale. Elle ne fournit donc pas à elle seule un domaine
L² non borné, la propriété Fredholm ou la compacité des perturbations H11
pour l'opérateur géométrique réel. Le double D9 est une référence analytique,
pas une preuve d'identification de ses composantes avec les champs réels.

Restent à construire le transport géométrique actual→modes signé, son
accord de domaine et de cœur, les estimations nécessaires pour H11, puis
l'intertwining global avec le secteur LL quotienté et le certificat terminal.
Aucune hypothèse `ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D`
n'est ajoutée. L'obstruction vers le D9 positif reste valable.

## Symbole abélien complet et norme de graphe

`P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D.lean` construit un
changement de coordonnées inversible pour le symbole Maxwell + BRST
nonminimal :

```text
(A, c, cbar, B) → (A.x, A.y, A.z, B − ξ·A, cbar + c, cbar − c).
```

L'inverse restitue explicitement tous les champs. Le changement respecte
l'addition et la multiplication scalaire. Le pairing complet est exactement
diagonal, de poids `(q, q, q, −1, q/2, −q/2)`, où `q = ‖ξ‖²`.
Le terme physique utilisé est le symbole Maxwell `−ξ×(ξ×A)` ; l'identification
avec le Hessien H11 géométrique global n'est pas démontrée par ce calcul.

`P0EFTJanusProgramPT12AbelianMixedOrderReference4D.lean` réalise ces poids sur
le domaine diagonal maximal, puis les duplique pour les deux secteurs
abéliens. Les douze coordonnées complexes par mode sont conservées. La
référence est dense, autoadjointe et fermée ; les données d'ellipticité D9
existantes donnent un gap `min(1, gap/2)` et la propriété Fredholm. Le poids
auxiliaire `−1` n'a jamais de zéro ; les cinq autres coordonnées s'annulent
exactement aux modes caractéristiques. Ce résultat précise la cible
abélienne : le double uniforme `±q` précédent ne décrit pas ce carré
auxiliaire d'ordre zéro.

`P0EFTJanusProgramPT12AbelianSignedCoordinateGraphBounds4D.lean` compare les
tailles quadratiques avant et après ce changement, en ajoutant `|ξ·A|²` de
chaque côté. Chacune est majorée par trois fois l'autre, uniformément en ξ.
En revanche, aucune constante uniforme ne contrôle le changement sur la
norme brute des coefficients : l'état `A=(1,0,0), c=cbar=B=0`, de taille
quadratique 1, a une image de taille `1+n²` pour `ξ=(n,0,0)`.

La congruence est donc contrôlée au niveau du graphe longitudinal, sans
être une isométrie L². Le transfert de domaine géométrique, les coefficients
variables et les autres colonnes H11 restent à traiter avant d'appliquer
ces références à l'opérateur réel. Le bloc difféomorphisme reste lui aussi
à identifier modalement. Aucun certificat global ni fermeture T12 n'est
déduit de ces trois gates.

## Annulation des ghosts diagonaux sur le cœur réel

`P0EFTJanusProgramPT12DiagonalGhostCancellation4D.lean` traite directement
le graphe difféomorphisme réel avec son unique triplet partagé. Sous les
deux conditions explicites

```text
metric.plus = metric.minus
candidateAPlusEinsteinKineticWeight + candidateAMinusEinsteinKineticWeight = 0,
```

les deux pairings sectoriels coïncident sur toute colonne ghost pur. Leur
somme pondérée s'annule. La densité du cœur lisse étend cette annulation
à tous les tests du graphe complété : `diagonalPureGhost_riesz_zero` est
une égalité du Riesz réel, sans référence modale.

`P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D.lean` montre que la
projection physique du même ghost est nulle, donc que H11 laisse la colonne
nulle. Il étend le résultat au Riesz augmenté sur l'espace de Hilbert complet.
`diagonalGhost_injects_into_augmented_kernel` construit une injection linéaire
de tout l'espace des ghosts lisses dans ce noyau. En conséquence, prouver
que ce noyau est de dimension finie dans ce régime imposerait aussi la
dimension finie de l'espace des ghosts. La preuve de dimension infinie,
ajoutée ensuite, est décrite ci-dessous.

Ce résultat est conditionnel : il n'affirme pas que le fond retenu satisfait
ces deux égalités. Les couplages Einstein actuels imposent séparément leur
non-nullité, pas leur positivité ; cette seule non-nullité ne suffit donc
pas à exclure des poids opposés. Une réalisation globale doit traiter le
couplage du triplet partagé et vérifier ses hypothèses sur le fond choisi.
Dupliquer deux réalisations mono-métriques indépendantes ne traite pas ce
couplage. T12 reste ouvert ; Quillen et le quotient LL sont inchangés.

## Dimension infinie et obstruction au transport du noyau

`P0EFTJanusProgramPT12ScalarFrameGhostInjection4D.lean` construit l'application
linéaire injective `f ↦ (f X_i)_i`, où les `X_i` sont la famille finie de
champs tangents engendrant chaque fibre déjà construite sur le quotient.
Il n'est pas nécessaire de supposer une base globale du fibré tangent.
Une dimension finie des ghosts impliquerait celle des champs scalaires lisses.

Pour une période strictement positive,
`P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D.lean` réfute cette
dernière propriété. Les parties réelle et imaginaire plongent les champs
complexes dans deux copies des champs réels ; l'injection de Fourier
temporelle existante y réalise `Int →₀ Complex`, qui est de dimension réelle
infinie. Les ghosts difféomorphismes lisses sont donc eux-mêmes de dimension
réelle infinie.

`P0EFTJanusProgramPT12DiagonalGhostInfiniteKernel4D.lean` compose ce résultat
avec l'injection dans le noyau augmenté. Sous période positive, métriques
égales et somme nulle des poids cinétiques :

- `diagonalGhost_augmented_kernel_not_finiteDimensional` établit la dimension
  infinie du noyau du Riesz réel complet, avec H11 ;
- `diagonalGhost_no_finite_kernel_transport` exclut tout transport linéaire
  injectif de ce noyau vers un espace de dimension finie, donc vers un noyau
  de référence fini.

Il s'agit d'une obstruction sur l'opérateur réel, indépendante du choix de
signes de la référence D9. Une fermeture couvrant ce régime ne peut donc
conserver simultanément le noyau réel complet, un transport injectif de
ce noyau et un noyau cible fini. Les hypothèses d'égalité des métriques et
d'annulation des poids restent explicites ; elles ne sont pas affirmées
pour le fond choisi. Aucun quotient de ghosts ni certificat terminal n'est
introduit par ces modules.

## Quotient de Hilbert des ghosts et antighosts nuls

`P0EFTJanusProgramPT12ClosedNullQuotient4D.lean` établit la descente d'un
opérateur borné autoadjoint `A` par un sous-espace fermé `N ⊆ ker A`.
L'opérateur quotient satisfait `Aq(q x) = q(A x)` et préserve exactement
le pairing `⟨Aq(q x), q y⟩ = ⟨A x, y⟩`. Son autoadjonction est prouvée,
et son noyau vaut l'image de `ker A` par la projection quotient.

`P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D.lean` applique cette
construction à l'espace de Hilbert réel augmenté. Le sous-espace quotienté
est l'adhérence de l'image des couples lisses `(ghost, antighost)`, avec
métriques perturbées et champ B nuls. L'annulation des deux colonnes dans
le Riesz augmenté est démontrée sous les mêmes conditions de métriques
égales et de somme nulle des poids. La période doit seulement être non nulle
pour cette construction, contrairement à la preuve de dimension infinie
qui utilise sa positivité.

Le cœur réel projeté est dense dans le quotient. Les deux colonnes nulles
y deviennent zéro ; le pairing du Riesz quotient sur ce cœur est exactement
le Hessien local gauge-fixé existant, avec toutes les contributions H11.
L'intertwining utilise la projection quotient concrète, qui n'est pas
injective sur l'espace initial. Il ne suppose pas le paquet terminal
`ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D`.

Cette réduction concerne le Hessien linéaire dans le régime d'annulation.
Elle ne démontre ni une équivalence BRST non linéaire, ni la réalisation
géométrique L² actual→D9. Le noyau résiduel est conservé explicitement :
sa dimension finie et un gap sur son complément restent à établir. Le
raccord au quotient LL et au certificat global reste ouvert ; T12 n'est
pas coché.

## Quotient du Jacobi LL non borné et raccord Friedrichs

`P0EFTJanusProgramPT12ClosedNullPMapQuotient4D.lean` construit la descente
d'un opérateur symétrique non borné par un sous-espace fermé de son noyau.
Le graphe quotient est défini par les représentants orthogonaux. Il reste
fermé ; son domaine est exactement l'image du domaine initial et reste
dense. La symétrie et le pairing sont préservés, sans perdre de sortie
non nulle de l'opérateur.

`P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D.lean` applique cette
construction au Jacobi LL littéral à trois composantes, à flux de fond nul.
Le sous-espace quotienté est le noyau de la projection sur le champ LL :
il contient exactement les composantes L² auxiliaire et mesure. La preuve
utilise leur annulation déjà établie pour le Jacobi fermé.

`P0EFTJanusProgramPT12LLFullReducedQuotientCore4D.lean` identifie ce quotient
isométriquement au L² LL canonique. Le quotient lisse auxiliaire–mesure
existant s'y plonge injectivement avec image dense, et les deux projections
commutent sur toute direction lisse complète. Cette identification des
espaces ne nécessite pas l'hypothèse de flux nul.

`P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D.lean` compose ensuite
la décomposition du graphe LL déjà prouvée avec cette isométrie. À flux nul,
le graphe quotient est exactement conjugué au Jacobi fermé du champ LL,
et se transporte dans le graphe du Friedrichs canonique existant. Son noyau
est nul. Le noyau du Jacobi LL complet est donc exactement constitué des
directions auxiliaire–mesure.

Le transport vers Friedrichs est une inclusion de graphes : l'égalité des
domaines avec cette extension n'est pas démontrée ici. Aucun certificat
Fredholm global, ni raccord des quotients LL et ghosts avec les colonnes H11
globales, n'en est déduit. L'obstruction BRST vers le D9 positif reste
présente ; T12 reste ouvert.

## Réalisation de Friedrichs sur le quotient LL

`P0EFTJanusProgramPT12IsometricPMapTransport4D.lean` transporte un opérateur
non borné par une isométrie linéaire surjective, avec son domaine explicite
et son graphe. Il préserve fermeture, densité, symétrie et bijectivité ;
l'autoadjonction est établie pour une réalisation symétrique surjective à
domaine dense.

`P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D.lean` applique ce
transport au Friedrichs LL déjà construit, via l'isométrie concrète du
quotient auxiliaire–mesure. Le domaine est la préimage exacte du domaine
canonique. Cette réalisation est autoadjointe, fermée, à domaine dense,
bijective et Fredholm. Son inverse borné compact est le transport de
`canonicalLLWeakL2Inverse`, avec identités d'inversion des deux côtés et
borne en norme. Aucun solveur ni intertwiner terminal n'est postulé.

À flux de fond nul, le Jacobi LL quotient fermé est une restriction de
cette réalisation. `P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D.lean`
place chaque direction lisse complète dans son domaine et prouve le pairing
exact avec le Hessien LL de la même action, y compris lorsque les représentants
contiennent des composantes auxiliaire et mesure arbitraires.

Ce certificat concerne le secteur LL quotient. Il ne prouve pas l'égalité
du Jacobi minimal fermé avec son extension de Friedrichs : la densité du
cœur pour la norme de graphe reste à établir. Les raccords BRST et H11 du
certificat global restent ouverts ; T12 n'est pas coché.

## Colonne LL augmentée et quotient commun ghosts–LL

`P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D.lean` identifie la
colonne LL complète du Riesz augmenté au Hessien LL de même action, contre
tout test du cœur global. Sur la carte forte centrée, l'annulation des
sept blocs physiques déjà prouvée couvre aussi les directions auxiliaire
et mesure. À flux nul, ce pairing est exactement celui de la réalisation
de Friedrichs du quotient LL, avec la composante LL du test global.

`P0EFTJanusProgramPT12StrongGhostLLNullSpace4D.lean` en déduit que l'adhérence
des directions LL auxiliaire–mesure appartient au noyau du Riesz augmenté,
à flux nul. Elle est réunie au sous-espace fermé des ghosts–antighosts par
l'adhérence de leur somme. L'inclusion de cette somme fermée dans le noyau
est prouvée avec les conditions explicites d'égalité des métriques et de
somme nulle des poids d'Einstein, ainsi que les données de la carte forte.

`P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D.lean` construit le
quotient commun dans l'espace de Hilbert réel augmenté. Le cœur projeté
est dense ; les deux familles de directions nulles y disparaissent.
Le Riesz descend concrètement, reste autoadjoint et conserve exactement
le pairing augmenté, donc toutes les contributions H11. Sa colonne LL
reste identifiée au pairing de Friedrichs LL après cette réduction commune.
Le noyau quotient est exactement l'image du noyau initial.

Il s'agit d'une descente du Riesz borné augmenté ; aucun opérateur global
non borné actual→D9 ni certificat Fredholm global n'est déduit. Les
hypothèses de cancellation ne sont pas affirmées pour le fond choisi.
Le noyau résiduel des autres secteurs, leur réalisation BRST et la fermeture
terminale restent ouverts ; T12 n'est pas coché.

## Facteur abélien et colonne H11 sur le quotient commun

`P0EFTJanusProgramPT12JointQuotientAbelianFactor4D.lean` construit la
projection abélienne continue sur le quotient ghosts–LL et son inclusion
linéaire isométrique. La projection est surjective et rétracte l'inclusion.
Ces constructions ne requièrent pas les hypothèses d'annulation : elles
utilisent seulement les coordonnées nulles des deux sous-espaces éliminés,
puis leur fermeture. Le secteur abélien complété reste donc intact.

`P0EFTJanusProgramPT12JointQuotientAbelianColumn4D.lean` établit une égalité
de vecteurs : l'opérateur augmenté réduit appliqué à l'inclusion abélienne
est la somme de l'inclusion du Riesz BRST signé et de la colonne physique
H11 projetée sur le quotient. Cette colonne conserve ses composantes dans
tous les secteurs. Son pairing contre tout représentant complété reste
exactement `physical.form` sur les représentants initiaux.

`P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D.lean` raccorde
l'inclusion au cœur lisse réel. Le pairing réduit est exactement l'action
BRST abélienne polarisée plus la Hessienne physique H11, contre tout test
lisse global. Le champ B non nul conserve l'auto-pairing strictement négatif
`-‖globalPairedGaugeLieL2LinearMap ... field‖²` après quotient.

La descente de l'opérateur et ces pairings réduits gardent explicitement
les hypothèses du quotient commun : flux LL nul, métriques sectorielles
égales et somme des poids cinétiques Einstein nulle, ainsi que la carte
forte centrée et l'extension physique déjà utilisée. L'isométrie du facteur
abélien ne signifie pas qu'il est invariant sous H11. Aucun accord modal
avec une cible D9 signée ni certificat Fredholm global n'est établi ici ;
l'obstruction vers le D9 positif persiste et T12 reste ouvert.

## Facteur difféomorphisme réduit et opérateur H11 commun

`P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D.lean` définit le
quotient du graphe diagonal par la fermeture de l'image des ghosts et
antighosts partagés. Son inclusion dans le quotient ghosts–LL est
isométrique ; une projection continue la rétracte. Leur relation
d'adjonction est prouvée.
Cette construction géométrique ne requiert aucune annulation des poids.

`P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D.lean` descend le
Riesz signé réel sur ce quotient sectoriel, sous égalité des métriques et
annulation de la somme des poids Einstein. L'opérateur est auto-adjoint,
son pairing est inchangé et son noyau est l'image du noyau initial. Aucune
dimension finie du noyau résiduel n'est déduite.

`P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D.lean` descend séparément
l'opérateur physique H11 complet sur le quotient commun. Sur la carte
forte centrée, cette descente ne demande ni flux LL nul, ni égalité des
métriques, ni annulation des poids Einstein. Elle conserve l'auto-adjonction
et retrouve exactement la Hessienne physique sur le cœur lisse.

`P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D.lean` établit
l'égalité de vecteurs entre la colonne augmentée réduite et la somme du
Riesz signé sectoriel inclus et de H11 appliqué à la même inclusion. H11
reste un opérateur global, avec ses composantes hors du secteur source.
La colonne abélienne précédemment construite utilise ce même H11 réduit.

`P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D.lean`
construit le cœur lisse sectoriel dense, annule ses ghosts et raccorde son
inclusion au cœur réel global. Contre tout test lisse global, le pairing
augmenté réduit est exactement l'action BRST difféomorphisme polarisée
plus H11. Il garde les hypothèses d'annulation du quotient augmenté.

Ces résultats réalisent les colonnes BRST sur les quotients réels ; ils ne
construisent pas leur identification modale avec D9 signé. L'obstruction
abélienne vers D9 positif demeure. L'identification modale signée et la
fermeture Fredholm globale restent à établir. T12 n'est pas coché.

## Décomposition globale du quotient de graphe et de son Riesz

`P0EFTJanusProgramPT12ClosedNullFactorIsometry4D.lean` isole le transport
isométrique d'un facteur entre quotients fermés compatibles. Ce petit
lemme évite un timeout de dépliage des types géométriques, sans augmenter
les limites de heartbeats.

`P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D.lean` construit le
facteur matière–LL complété, quotienté par la fermeture des directions
LL auxiliaires/mesure, avec inclusion isométrique et projection adjointe.
`P0EFTJanusProgramPT12JointQuotientSectorDecomposition4D.lean` prouve la
reconstruction unique de tout vecteur du quotient global par les facteurs
difféomorphisme, abélien et matière–LL. Le produit scalaire et le carré de
la norme sont exactement les sommes sectorielles.

`P0EFTJanusProgramPT12ReducedMatterLLGraphRiesz4D.lean` extrait le bloc
matière–LL du Riesz de graphe existant, indépendamment de l'extension
physique. Son pairing est explicitement la somme des formes matière et
LL réelles. Sous les données fortes centrées et le flux LL nul, il descend
en un opérateur auto-adjoint sur le quotient sectoriel et sa colonne
coïncide avec celle du Riesz augmenté. H11 annule ce facteur entier.

`P0EFTJanusProgramPT12ThreeBlockHilbertAssembly4D.lean` isole l'assemblage
abstrait des trois colonnes et de l'opérateur physique commun, avec le
pairing et l'auto-adjonction de la différence de deux opérateurs.
`P0EFTJanusProgramPT12JointQuotientGlobalRiesz4D.lean` établit l'égalité
d'opérateurs sur tout le quotient global : Riesz augmenté = somme des trois
blocs sectoriels inclus et projetés + H11 réduit. La somme diagonale est
auto-adjointe ; son pairing global est explicite. H11 dépend seulement des
deux coordonnées BRST, en conservant leurs éventuels termes croisés.
L'assemblage garde les hypothèses d'annulation du Riesz augmenté.

Le quotient matière–LL construit ici porte la norme du graphe global.
Il n'est pas identifié au quotient LL en norme L² portant l'opérateur
non borné de Friedrichs. Cette égalité globale bornée ne fournit ni
l'identification modale signée ni le certificat Fredholm géométrique
terminal. T12 reste ouvert.

## Cisaillement géométrique abélien sur le quotient global

Le changement `B -> B + delta_g A` est désormais une équivalence linéaire
continue du graphe abélien réel complété. Son inverse est `B -> B - delta_g A`.
L'incrément est construit à partir des projections L2 existantes ; son carré
est nul et il préserve le sous-espace fermé engendré par les champs lisses.
L'accord avec le changement géométrique sur le cœur lisse est exact.

Le pairing BRST transformé sépare le carré positif de Lorenz et le carré
négatif de B. Le pairing ghost–antighost conserve le véritable opérateur
Faddeev–Popov géométrique. Il s'agit d'une congruence d'opérateurs, sans
prétendre à une conjugaison isométrique dans la norme L2 brute.

L'incrément auxiliaire est annulé par le Riesz physique H11 sur tout le
graphe, par annulation du tangent physique puis densité. Le cisaillement
s'étend en une équivalence continue du quotient global ghosts–LL et
préserve tous ses pairings H11, y compris les termes entre secteurs.
Le pairing augmenté abélien réduit conserve exactement ce même H11 après
séparation du carré auxiliaire, sous les hypothèses de descente déjà
explicites (flux LL nul, métriques égales, somme des poids d'Einstein nulle).

Ces résultats ne fournissent pas encore la transformation spectrale des
opérateurs différentiels réels ni leur domaine maximal L2. L'identification
à la référence signée et la fermeture Fredholm globale restent ouvertes.
T12 reste non coché.

## Rotation réelle des ghosts et cœur abélien signé dense

La rotation `(cbar, c) -> (cbar + c, cbar - c)` est construite comme une
équivalence linéaire du cœur BRST abélien lisse, avec inverse explicite.
Le potentiel et le champ B restent inchangés. Le pairing réel transformé
conserve le défaut d'adjonction de Faddeev–Popov : pour les coordonnées
signées `(u, v)` et `(x, y)`, il vaut
`(SymFP(u,x) - SymFP(v,y))/2 + (DefFP(u,y) + DefFP(x,v))/4`.

Pour la métrique intrinsèque, `DefFP` est exactement la somme des quatre
intégrales scalaires de densité antisymétrique déjà construites. Un test
mixte plus/moins du véritable Hessien mesure un quart de cette somme.
Son annulation n'est pas supposée. La réalisation L2 de FP disponible
ailleurs reste conditionnée par des données analytiques non construites.

La colonne H11 est identique pour tous les états lisses abéliens ayant le
même potentiel, contre tous les tests globaux complétés. Cette égalité
s'applique à la rotation ghost et descend au quotient commun ghosts–LL.
La composition de l'inverse de cette rotation avec le cisaillement de
Lorenz définit un cœur concret dense dans le graphe abélien réel ; chaque
vecteur reste l'image d'un état lisse authentique. Son pairing et sa colonne
augmentée réduite sont établis avec le même H11.

La rotation ghost n'est pas déclarée continue sur l'ancien graphe complété,
qui contrôle FP(c) mais pas FP(cbar). Le domaine maximal L2, la symétrie FP
sur le domaine retenu, le raccord spectral et la fermeture globale restent
à construire. T12 reste non coché.

## Rotation continue sur le graphe avec contrôle des deux images FP

Le graphe abélien est renforcé par une seule coordonnée : FP(antighost).
Il est défini comme la fermeture de l'image des véritables états lisses
dans l'ancien espace de caractéristiques, augmenté de cette coordonnée L2.
Son cœur lisse est dense et injectif ; l'espace complété est complet.

La rotation ghost somme/différence agit simultanément sur les deux champs
et sur leurs images FP. Elle préserve ce sous-espace fermé et définit une
équivalence linéaire continue, avec inverse continu. Les deux applications
coïncident exactement avec la rotation lisse et sa reconstruction.

L'oubli de FP(antighost) est une application linéaire continue d'image dense
vers le graphe abélien existant. Son injectivité est désormais établie pour
les métriques régulières, via l'adjoint canonique et la closabilité ci-dessous.
La reconstruction signée suivie de cet oubli est elle aussi continue et dense.

Par densité, la colonne physique H11 est préservée sur tout le graphe renforcé,
contre tous les tests globaux complétés. La colonne augmentée sur le quotient
ghosts–LL est établie avec le H11 d'origine et les hypothèses de descente déjà
explicites. Ce résultat prolonge l'égalité auparavant disponible sur le seul
cœur lisse, sans prétendre à une rotation bornée sur l'ancien graphe.

Le Stokes global du FP est établi ci-dessous dans la mesure d'un métrique
régulier. La closabilité et le domaine de l'adjoint Hilbert dans le L2
canonique sont établis ci-dessous. Le raccord spectral reste à construire.
Le défaut FP canonique n'est pas annulé et T12 reste non coché.

## Pairing signé sur le graphe renforcé complété

`abelianTwoSidedSignedRealization` compose la reconstruction ghost continue,
l'oubli et le cisaillement de Lorenz. Cette application continue a une image
dense dans le graphe abélien réel ; sur les états lisses elle redonne exactement
la reconstruction signée suivie du véritable incrément de Lorenz.

Son pairing hessien est établi sur tous les vecteurs complétés : carré de
Lorenz positif, carré B négatif, deux blocs ghosts signés et les deux termes
mixtes du défaut FP. `twoSidedSignedGhostPairing` conserve ces derniers
explicitement, sans supposer leur annulation.

`abelianTwoSidedSignedRiesz` est la congruence `T* R T` dans la norme du
graphe renforcé. Son pairing exact et sa symétrie sont prouvés. La colonne
physique H11 reste celle du vecteur initial après oubli, et la colonne
augmentée est établie dans tout le quotient commun, avec les hypothèses de
descente existantes. Ce résultat ne donne ni une isométrie L2 ni un domaine
maximal auto-adjoint.

Le raccord du Stokes canonique avec la divergence utilisée par le FP est
établi ci-dessous dans la mesure du métrique fourni. La closabilité dans
le L2 canonique et l'injectivité de l'oubli sont également établies ci-dessous.
La fermeture spectrale globale reste ouverte. T12 demeure non coché.

Sources : `P0EFTJanusProgramPT12TwoSidedGhostPairing4D.lean`,
`P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D.lean` et
`P0EFTJanusProgramPT12AbelianTwoSidedSignedPhysical4D.lean`.

## Stokes global du Lorenz réel et symétrie FP dans la mesure métrique

Les six nouvelles gates raccordent la divergence des dix flots à l'opérateur
différentiel réel, sans hypothèse de jauge de volume ni donnée de Green
supplémentaire :

- `canonicalCurrentDivergence_eq_local` identifie la divergence canonique à
  la divergence pondérée locale de tout courant lisse. La décomposition
  exacte en dix générateurs et leurs résidus déjà annulés font la preuve.
- `metricCurrentDivergence_eq_local` transfère cette identité à la densité
  du métrique fourni, avec son véritable rapport de volumes.
- `localLorenz_eq_densityDivergence` utilise la dérivée du déterminant et
  la trace de Christoffel pour identifier le Lorenz local installé.
- `lorenzRaisedCurrent` construit le champ lisse `A♯` par reconstruction
  dans le dual fini. Son pullback est exactement le potentiel relevé local.
- `globalLorenz_weak_stokes` prouve l'intégration par parties globale du
  Lorenz réel ; son intégrale sans test est également nulle.
- `globalFP_component_green` spécialise le résultat à `δ_g d`. Le pairing
  est l'opposé de la contraction métrique des gradients, d'où
  `globalFP_component_metric_symmetry` pour chaque composante réelle.

La mesure est explicitement `generalLorentzVolumeMeasure ... metric.metric`,
pour un `RegularGeneralLorentzMetric` fourni. Il ne s'agit pas encore de la
symétrie dans le L2 canonique du graphe abélien pour un métrique quelconque.
Le transport de l'adjoint, la closabilité FP et l'injectivité de l'oubli
sont établis dans la section suivante. Le raccord spectral global reste
ouvert. Aucun certificat terminal T12 n'est déclaré.

Sources : `P0EFTJanusProgramPT12CanonicalCurrentPullback4D.lean`,
`P0EFTJanusProgramPT12CanonicalCurrentLocalDivergence4D.lean`,
`P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D.lean`,
`P0EFTJanusProgramPT12LorenzLocalDensity4D.lean`,
`P0EFTJanusProgramPT12LorenzRaisedCurrent4D.lean` et
`P0EFTJanusProgramPT12LorenzGlobalStokes4D.lean`.

## Adjoint canonique, closabilité FP et réalisation abélienne fidèle

Avec `r` le rapport entre la mesure métrique et la mesure canonique,
`canonicalFPFormalAdjoint` construit l'adjoint formel réel `r FP(r⁻¹ ·)`.
Son pairing exact, composante par composante puis pour les deux secteurs,
découle du Stokes métrique et du changement de densité déjà prouvés.

`linearFeatureGraphClosure_fst_injective` établit abstraitement la closabilité
à partir d'une famille dense de tests d'adjoint. Son application au véritable
FP pairé montre que la fermeture du graphe dans le L2 canonique ne contient
aucun vecteur vertical non nul.

Les coordonnées antighost et FP(antighost) de tout vecteur du graphe renforcé
appartiennent à cette fermeture. L'oubli de FP(antighost) est donc injectif,
ainsi que `abelianTwoSidedSignedRealization`, déjà continue et d'image dense.
`candidateAAbelianSignedRealization_injective` spécialise ce résultat aux
données réelles de Candidate A : leurs deux métriques de gravité fournissent
directement la régularité nécessaire, sans nouvelle hypothèse analytique.

Ces résultats ne prouvent ni la surjectivité de la réalisation signée, ni
un inverse borné, ni l'identification d'un domaine maximal auto-adjoint L2.
Le défaut FP canonique et les domaines minimal/adjoint sont précisés
ci-dessous. Le raccord spectral et le certificat global restent à traiter ;
T12 demeure non coché.

Sources : `P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D.lean`,
`P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D.lean`,
`P0EFTJanusProgramPT12DenseAdjointGraphClosable4D.lean`,
`P0EFTJanusProgramPT12PairedFPClosable4D.lean`,
`P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D.lean` et
`P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D.lean`.

## FP fermé sur L2, domaine adjoint maximal et défaut ghost exact

`pairedFPDefect_eq_canonicalCorrection` identifie le défaut de symétrie au
pairing avec `FP*formel - FP`, où `FP*formel = r FP(r⁻¹ ·)`. L'annulation
contre tous les tests lisses équivaut à l'annulation de cette correction L2.
Le Hessien ghost mixte réel vaut exactement un quart de ce pairing.
La relation d'adjonction s'étend également à tout le graphe FP fermé.

`candidateAFPCanonicalMinimal` réalise le véritable FP pairé de Candidate A
comme `LinearPMap` dans le L2 canonique. Son graphe est exactement la
fermeture de l'image lisse `(champ, FP(champ))`. Il est fermé, son domaine
est dense, son action sur le cœur lisse est exacte et toute extension
fermée de cette action le contient. La construction utilise l'injectivité
du graphe déjà prouvée pour les métriques effectives de l'action.

Son adjoint Hilbert est fermé et à domaine dense. Le domaine maximal de
cet adjoint est caractérisé sans hypothèse supplémentaire : `u` y appartient
si et seulement s'il existe `v` dans L2 tel que, pour tout test lisse `φ`,
`⟨FP φ, u⟩ = ⟨φ, v⟩`. La valeur de l'adjoint est alors `v` ; sur les tests
lisses, elle est exactement l'adjoint canonique pondéré construit auparavant.

Ces deux domaines ne sont pas identifiés entre eux. L'auto-adjonction du
bloc ghost abélien est désormais établie ci-dessous, sans affirmer celle
du FP canonique. Le raccord spectral signé, les autres secteurs et la
propriété Fredholm globale restent à traiter ; T12 demeure non coché.

Sources : `P0EFTJanusProgramPT12FPCanonicalDefect4D.lean`,
`P0EFTJanusProgramPT12ClosedFeatureOperator4D.lean`,
`P0EFTJanusProgramPT12ClosedFeatureAdjoint4D.lean`,
`P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D.lean` et
`P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D.lean`.

## Réalisation auto-adjointe du bloc ghost abélien réel sur L2

`closedOperator_adjoint_adjoint` prouve `F†† = F` pour un opérateur fermé
dont le domaine et celui de l'adjoint sont denses. La preuve passe par
le double orthogonal de son graphe dans le produit de Hilbert.

`offDiagonalOperator` construit le véritable opérateur non borné
`(a, c) ↦ (F c, G a)`, avec domaine `D(G) × D(F)` et graphe explicites.
Son adjoint est le bloc construit à partir de `G†` et `F†`. Pour `G = F†`
et `F` fermé, le double adjoint donne l'auto-adjonction du bloc.

`candidateAAbelianGhostOperator` applique cette construction au FP minimal
réel de Candidate A. Il est auto-adjoint, fermé et à domaine dense dans
le L2 canonique des deux champs ghosts. Le domaine de l'antighost est
celui de l'adjoint Hilbert maximal ; le domaine du ghost est celui du FP
minimal fermé. Sur les champs lisses, la seconde sortie est exactement
`r FP(r⁻¹ antighost)`, sans supposer la symétrie du FP canonique.

`candidateAAbelianGhostOperator_smooth_hessian` identifie son pairing L2
au Hessien off-shell réel sur les états ghosts purs. Les paires de champs
lisses constituent une famille dense dans le L2 produit. Cette densité
ne prouve pas qu'elles soient un cœur pour la norme de graphe du bloc :
l'approximation dans le domaine de l'adjoint reste à établir.

Aucune propriété Fredholm, identification spectrale à D9 ou fermeture
globale des secteurs BRST et H11 n'en est déduite. T12 demeure non coché.

Sources : `P0EFTJanusProgramPT12ClosedDoubleAdjoint4D.lean`,
`P0EFTJanusProgramPT12OffDiagonalClosedOperator4D.lean`,
`P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D.lean`,
`P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D.lean` et
`P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D.lean`.

## Opérateur ghost signé auto-adjoint et raccord exact du pairing

`unboundedCongruence` construit `T A T` avec domaine exact `T⁻¹(D(A))`
pour une équivalence linéaire continue `T`. Lorsque `T` est symétrique,
son adjoint est `T A† T` ; la congruence préserve donc l'auto-adjonction,
la fermeture et la densité du domaine. Le pairing transporté est prouvé
sur tout le domaine, contre tout test L2.

`ghostL2Reconstruction` réalise sur L2 la reconstruction déjà utilisée sur
le cœur lisse : `(u, v) ↦ ((u+v)/2, (u-v)/2)`. Son inverse est la rotation
somme/différence. Elle est symétrique, bornée et inversible ; le facteur
`1/2` est conservé, sans la présenter comme une isométrie.

`candidateAAbelianSignedGhostOperator` est la congruence concrète du bloc
ghost auto-adjoint de Candidate A. Son domaine impose `(u+v)/2 ∈ D(FP†)`
et `(u-v)/2 ∈ D(FP)`. Il est auto-adjoint, fermé et à domaine dense.
Son pairing lisse est exactement le Hessien réel après reconstruction,
puis la formule signée existante : différence des pairings symétrisés
divisée par deux, plus les deux défauts FP divisés par quatre.

Il s'agit d'une congruence de formes, sans identification du spectre à D9.
La densité du cœur lisse en norme de graphe, la propriété Fredholm et le
raccord global des secteurs BRST et H11 restent ouverts. T12 n'est pas coché.

Sources : `P0EFTJanusProgramPT12UnboundedCongruence4D.lean`,
`P0EFTJanusProgramPT12SymmetricCongruenceAdjoint4D.lean`,
`P0EFTJanusProgramPT12GhostL2Reconstruction4D.lean`,
`P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Operator4D.lean` et
`P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Pairing4D.lean`.

## Fermeture minimale réelle du bloc ghost et critère exact de cœur

`closedFeatureOperator_hasCore` prouve au sens de `LinearPMap.HasCore` que
l'image lisse est un cœur de la fermeture minimale de son graphe. Pour
toute extension fermée compatible avec l'action lisse, cette propriété
équivaut à l'égalité avec la fermeture minimale, via le calcul explicite
du graphe de la restriction et de sa fermeture.

`candidateAFPFormalAdjointMinimal` construit la fermeture minimale réelle
de `r FP(r⁻¹ ·)`. Elle est fermée, à domaine dense et contenue dans
l'adjoint Hilbert maximal `FP†`. Son action lisse et son cœur lisse sont
établis, ainsi que le cœur lisse du FP minimal d'origine.

`offDiagonalOperator_closure` calcule la fermeture du bloc en fermant ses
deux graphes séparément. Une permutation continue des quatre coordonnées
réduit la preuve à la fermeture d'un produit. Le critère de cœur du bloc
se réduit alors exactement à celui de la seconde composante dès que la
première possède déjà son cœur.

`candidateAAbelianGhostMinimal` est le bloc formé du FP minimal et de
l'adjoint formel minimal. Il est fermé, symétrique, à domaine dense et
possède le cœur des paires de champs lisses. Il est inclus dans le bloc
auto-adjoint construit auparavant. Le théorème
`candidateAAbelianGhost_smoothClosure_eq_minimal` l'identifie exactement
à la fermeture de la restriction lisse de ce bloc auto-adjoint.

Le théorème `candidateAAbelianGhostOperator_hasCore_iff` isole la question
analytique restante : le cœur lisse est un cœur du bloc auto-adjoint si
et seulement si `candidateAFPFormalAdjointMinimal = FP†`. Cette égalité
n'est ni prouvée ni supposée. Le cœur minimal est acquis ; son identification
avec le domaine maximal, la propriété Fredholm et la fermeture globale
restent ouvertes. T12 n'est pas coché.

Sources : `P0EFTJanusProgramPT12ClosedFeatureCore4D.lean`,
`P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D.lean`,
`P0EFTJanusProgramPT12OffDiagonalClosure4D.lean`,
`P0EFTJanusProgramPT12OffDiagonalCore4D.lean` et
`P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D.lean`.

## Validation

### Pairing et obstruction vers le D9 positif

Les cinq nouveaux modules sont compilés séquentiellement avec
`scripts/run_lean_guarded.ps1`, priorité haute, un seul processus Lean,
`MemoryMB=4096` et `ReserveMB=4096`. Pics échantillonnés : pairing 4170 Mo,
D9 3630 Mo, témoin BRST 3733 Mo, impossibilité 3718 Mo, colonne H11 4010 Mo.
Le hub T12 importe les cinq modules via trois imports directs ; sa compilation
gardée est verte (4090 Mo). L'audit `#print axioms` des six théorèmes listés
ci-dessus ne retourne que `propext`, `Classical.choice` et `Quot.sound`
(3917 Mo). Aucun `sorry`, `admit` ou nouvel axiome ; `git diff --check` vert.

### Réalisations signées

Les cinq modules signés ont été compilés séparément avec le même protocole
gardé, séquentiel, priorité haute et réserve de 4096 Mo. Pics échantillonnés :
Gram 1929 Mo, abélien 3746 Mo, difféomorphisme 3995 Mo, assemblage H11
3872 Mo et référence D9 3612 Mo. Le hub T12 les importe par deux imports
directs supplémentaires ; sa compilation est verte (3957 Mo).
L'audit `#print axioms` porte sur treize résultats : les deux pairings de
Gram, les deux identifications au Riesz réel et leurs deux accords lisses,
les deux théorèmes d'assemblage/H11, les quatre propriétés du D9 signé et
son identité de symbole. Il ne retourne que `propext`, `Classical.choice`
et `Quot.sound` (3906 Mo). Aucun `sorry`, `admit` ou nouvel axiome dans les
cinq modules ; `git diff --check` vert.

### Symbole complet et référence abélienne d'ordre mixte

Les trois modules supplémentaires sont verts sous `run_lean_guarded`, un
seul Lean à priorité haute et réserve de 4096 Mo. Pics échantillonnés :
symbole 3706 Mo, référence pairée 3637 Mo, bornes de graphe 3691 Mo.
Le hub les importe via deux imports directs ; il compile à 3988 Mo.
L'audit `#print axioms` de quatorze déclarations (équivalence, linéarité,
pairing, zéros, gap pairé, quatre propriétés de l'opérateur, deux bornes de
graphe, croissance du témoin et absence de borne brute) ne retourne que
`propext`, `Classical.choice` et `Quot.sound` (3907 Mo). Aucun `sorry`,
`admit` ou nouvel axiome ; `git diff --check` vert.

### Noyau diagonal réel et augmentation H11

Les deux modules de cancellation sont compilés séquentiellement avec
`run_lean_guarded`, priorité haute et réserve de 4096 Mo. Pics échantillonnés :
graphe diagonal 3765 Mo, noyau augmenté et injection 4160 Mo. Le hub importe
les deux modules par un import direct supplémentaire et compile à 3993 Mo.
L'audit `#print axioms` des neuf théorèmes publics ne retourne que `propext`,
`Classical.choice` et `Quot.sound` (3889 Mo). Aucun `sorry`, `admit` ou nouvel
axiome ; `git diff --check` vert.

### Dimension infinie des ghosts et du noyau réel

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : injection par les
générateurs 3695 Mo, dimension infinie des ghosts 3814 Mo, noyau augmenté et
impossibilité de transport 3844 Mo. Le hub importe ces résultats par un
import direct supplémentaire et compile à 4082 Mo.
L'audit `#print axioms` des sept théorèmes publics ne retourne que `propext`,
`Classical.choice` et `Quot.sound` (3889 Mo). Aucun `sorry`, `admit` ou nouvel
axiome ; `git diff --check` vert.

### Quotient fermé des ghosts et antighosts

Les deux nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : quotient abstrait
1929 Mo, quotient réel augmenté 4185 Mo. Le hub importe ces résultats par
un import direct supplémentaire et compile à 4226 Mo.
L'audit `#print axioms` des dix-sept théorèmes publics ne retourne que
`propext`, `Classical.choice` et `Quot.sound` (3897 Mo). Aucun `sorry`,
`admit` ou nouvel axiome ; `git diff --check` vert.

### Quotient du Jacobi LL non borné

Les quatre nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : descente
abstraite 1923 Mo, quotient du Jacobi LL 3892 Mo, isométrie et cœur lisse
3899 Mo, raccord Friedrichs et noyau 3896 Mo. Le hub compile à 3970 Mo.
L'audit `#print axioms` des trente-deux théorèmes publics ne retourne que
`propext`, `Classical.choice` et `Quot.sound` (3920 Mo). Aucun `sorry`,
`admit` ou nouvel axiome ; `git diff --check` vert.

### Réalisation de Friedrichs sur le quotient LL

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : transport
isométrique 1928 Mo, réalisation quotient 3978 Mo, pairing de même action
3895 Mo. Le hub compile à 3971 Mo. L'audit `#print axioms` des vingt-huit
théorèmes publics ne retourne que `propext`, `Classical.choice` et
`Quot.sound` (3893 Mo). Aucun `sorry`, `admit` ou nouvel axiome ;
`git diff --check` vert.

### Colonne LL augmentée et quotient commun ghosts–LL

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : colonne LL
4184 Mo, sous-espace nul commun 4432 Mo, quotient augmenté 4476 Mo.
Le hub compile à 4107 Mo. L'audit `#print axioms` des quinze théorèmes
publics ne retourne que `propext`, `Classical.choice` et `Quot.sound`
(3893 Mo). Aucun `sorry`, `admit` ou nouvel axiome ; `git diff --check` vert.

### Facteur abélien et H11 sur le quotient commun

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : facteur
isométrique 4075 Mo, colonne opérateur 4239 Mo, raccord lisse 4480 Mo.
Le hub compile à 3962 Mo. L'audit `#print axioms` des dix-neuf théorèmes
publics et des deux inclusions isométriques ne retourne que `propext`,
`Classical.choice` et `Quot.sound` (3801 Mo). Aucun `sorry`, `admit` ou
nouvel axiome ; `git diff --check` vert.

### Facteur difféomorphisme réduit et H11 commun

Les cinq nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : facteur
isométrique 4306 Mo, Riesz signé réduit 4232 Mo, H11 réduit 3951 Mo,
colonne opérateur 4277 Mo, raccord lisse 3995 Mo. Le hub compile à 3969 Mo.
L'audit `#print axioms` des trente-trois théorèmes publics et des deux
inclusions isométriques ne retourne que `propext`, `Classical.choice` et
`Quot.sound` (3923 Mo). Aucun `sorry`, `admit` ou nouvel axiome ;
`git diff --check` vert.

### Décomposition et Riesz globaux sur le quotient de graphe

Les six nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : isométrie
abstraite 1921 Mo, facteur matière–LL 4334 Mo, décomposition 4328 Mo,
Riesz matière–LL 4311 Mo, assemblage abstrait 1987 Mo, Riesz global
4519 Mo. Le hub compile à 3981 Mo. Les timeouts de dépliage ont été
résolus par des lemmes abstraits et des compositions explicites, sans
augmenter les heartbeats.
L'audit `#print axioms` des trente-six théorèmes publics et des trois
inclusions isométriques ne retourne que `propext`, `Classical.choice` et
`Quot.sound` (3902 Mo). Aucun `sorry`, `admit` ou nouvel axiome ;
`git diff --check` vert.
### Cisaillement abélien réel et préservation globale de H11

Les cinq nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : cisaillement
abstrait 1905 Mo, réalisation géométrique 3755 Mo, pairing 3764 Mo,
colonne H11 3975 Mo, quotient global et pairing augmenté 3981 Mo.
La première tentative H11 a atteint la limite mémoire ; la preuve finale
passe explicitement par l'annulation du tangent physique, sans augmenter
le budget mémoire ni les heartbeats. Le hub compile à 4055 Mo.
L'audit `#print axioms` des trente-deux déclarations publiques ne retourne
que `propext`, `Classical.choice` et `Quot.sound` (3934 Mo). Aucun `sorry`,
`admit`, nouvel axiome ou hypothèse terminale d'intertwiner ;
`git diff --check` vert.
### Rotation ghost réelle, défaut FP et cœur signé dense

Les cinq nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : algèbre du défaut
2143 Mo, rotation lisse 3746 Mo, défaut intrinsèque 3727 Mo, colonne H11
3963 Mo, assemblage du cœur dense 3946 Mo. Le hub compile à 4187 Mo.
L'audit `#print axioms` des trente-trois déclarations publiques ne retourne
que `propext`, `Classical.choice` et `Quot.sound` (3934 Mo). Aucun `sorry`,
`admit`, nouvel axiome ou hypothèse terminale d'intertwiner ;
`git diff --check` vert.
### Graphe ghost renforcé et rotation continue

Les quatre nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : rotation ambiante
2195 Mo, graphe réel 3742 Mo, équivalence et oubli dense 3760 Mo, H11 et
colonne augmentée 4229 Mo. Le dépliage géométrique initial a dépassé les
heartbeats ; le calcul des caractéristiques a été isolé dans un lemme
abstrait, sans augmenter les budgets. Le hub compile à 3977 Mo.
L'audit `#print axioms` des trente-et-une déclarations publiques ne retourne
que `propext`, `Classical.choice` et `Quot.sound` (3930 Mo). Aucun `sorry`,
`admit`, nouvel axiome ou hypothèse terminale d'intertwiner ;
`git diff --check` vert.

### Pairing signé et colonnes globales sur le graphe renforcé

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : pairing abstrait
2180 Mo, réalisation et Riesz complétés 3908 Mo, colonnes H11 et augmentée
3939 Mo. Le hub compile à 4178 Mo. L'élaboration de l'adjoint a été résolue
en explicitant ses espaces source et cible, sans augmenter les budgets.
L'audit `#print axioms` des quatorze déclarations publiques ne retourne
que `propext`, `Classical.choice` et `Quot.sound` (3907 Mo). Aucun `sorry`,
`admit`, nouvel axiome ou hypothèse terminale d'intertwiner ;
`git diff --check` vert.

### Stokes global réel du Lorenz et FP

Les six nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : pullback 3853 Mo,
divergence canonique locale 3846 Mo, transfert de mesure 3858 Mo, densité
Lorenz 3852 Mo, courant relevé 3901 Mo, Stokes global 3856 Mo. Le hub compile
à 4194 Mo et l'audit des seize déclarations à 3918 Mo. Les difficultés de
dépliage ont été résolues par des congruences explicites, sans augmenter
les heartbeats ni le budget mémoire.

L'audit retourne `propext`, `Classical.choice`, `Quot.sound` et, pour les
résultats utilisant les dix flots, la dépendance existante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Elle provient du `native_decide` préexistant à la ligne 114 du module IPP,
prouvant `Fintype.card CanonicalFlowIndex = 10`. Cet audit ne se limite donc
pas aux trois axiomes usuels. Aucun axiome, `sorry`, `admit` ou hypothèse
terminale d'intertwiner n'a été ajouté par les six gates ;
`git diff --check` vert. Les fichiers externes et T08 sont préservés.

### Bloc ghost abélien auto-adjoint sur L2

Les cinq nouvelles gates sont vertes sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : double adjoint
2153 Mo, bloc fermé 2192 Mo, auto-adjonction abstraite 2145 Mo, réalisation
Candidate A 3911 Mo, pairing hessien 3917 Mo. Le hub compile à 4004 Mo et
l'audit des vingt-deux déclarations publiques à 3926 Mo. Les corrections
d'élaboration utilisent des projections et congruences explicites ; aucun
budget n'a été augmenté.

L'audit retourne `propext`, `Classical.choice`, `Quot.sound` et, pour les
résultats dépendant du Stokes réel, le `native_decide` préexistant
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner ;
`git diff --check` vert. Les fichiers externes et T08 sont préservés.

### Adjoint canonique et fidélité de la réalisation abélienne

Les six nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : adjoint composante
4110 Mo, adjoint pairé 3854 Mo, closabilité abstraite 2154 Mo, FP réel 3889 Mo,
oubli injectif 3968 Mo, spécialisation Candidate A 3890 Mo. Le hub compile
à 4166 Mo et l'audit des vingt-trois déclarations publiques à 3926 Mo.
Le timeout de simplification de la spécialisation a été résolu par transport
explicite de l'égalité des métriques, sans augmenter les budgets.

L'audit retourne `propext`, `Classical.choice`, `Quot.sound` et, pour les
preuves issues du Stokes, la dépendance native préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner
n'a été ajouté. `git diff --check` vert ; fichiers externes et T08 préservés.

### Opérateur FP minimal fermé et adjoint Hilbert canonique

Les cinq nouvelles gates sont vertes sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : défaut canonique
3914 Mo, opérateur fermé abstrait 2162 Mo, domaine adjoint abstrait 2145 Mo,
FP minimal Candidate A 3912 Mo, adjoint Candidate A 4136 Mo. Le hub compile
à 4136 Mo et l'audit des trente-et-une déclarations publiques à 3927 Mo.

Les dépendances de l'audit sont `propext`, `Classical.choice`, `Quot.sound`
et, pour les résultats issus du Stokes, le `native_decide` préexistant
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner ;
`git diff --check` vert. Les fichiers externes et T08 sont préservés.

### Congruence signée auto-adjointe sur L2

Les cinq nouvelles gates sont vertes sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : congruence 2196 Mo,
transport de l'adjoint 2180 Mo, reconstruction L2 2184 Mo, opérateur signé
Candidate A 3917 Mo, pairing signé 3917 Mo. Le hub compile à 4092 Mo et
l'audit des vingt-sept déclarations publiques à 3926 Mo. Aucun budget
mémoire ou heartbeat n'a été augmenté.

L'audit retourne `propext`, `Classical.choice`, `Quot.sound` et, pour les
résultats issus du Stokes réel, le `native_decide` préexistant
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner ;
`git diff --check` vert. Les fichiers externes et T08 sont préservés.

### Cœur de la fermeture minimale ghost et comparaison minimale/maximale

Les cinq nouvelles gates sont vertes sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : critère abstrait
2145 Mo, adjoint formel minimal 3915 Mo, fermeture du bloc 2185 Mo,
critère de cœur du bloc 2228 Mo, fermeture ghost réelle 3930 Mo. Le hub
compile à 4220 Mo et l'audit des trente-quatre déclarations publiques à
3946 Mo. Aucun budget mémoire ou heartbeat n'a été augmenté.

L'audit retourne `propext`, `Classical.choice`, `Quot.sound` et, pour les
résultats utilisant le Stokes réel, le `native_decide` préexistant
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner ;
`git diff --check` vert. Les fichiers externes et T08 sont préservés.

### Conjugaison des graphes minimaux par le volume réel

`P0EFTJanusProgramPT12L2VolumeMultiplier4D.lean` construit la multiplication
bornée réelle sur L2 et son inverse. `P0EFTJanusProgramPT12PairedVolumeEquiv4D.lean`
l'applique au rapport positif de volume des métriques réelles des deux secteurs :
la compacité borne le rapport et son inverse. L'équivalence est symétrique pour
le pairing canonique et transporte exactement les inclusions lisses.

`P0EFTJanusProgramPT12ClosedFeatureVolumeTransport4D.lean` transporte la fermeture
du graphe par cette équivalence. La spécialisation réelle dans
`P0EFTJanusProgramPT12CandidateAFPVolumeGraph4D.lean` établit
`A_min = r FP_min r⁻¹`, avec égalité des graphes et
`D(A_min) = r D(FP_min)`, puis égalité des actions sur tout le domaine minimal.
Ce résultat n'identifie pas `A_min` à l'adjoint maximal `FP_min†` ; cette égalité
reste à démontrer pour le cœur ghost. T12 reste ouvert.

Les quatre gates, le hub et l'audit des vingt-et-une déclarations publiques
sont verts sous `run_lean_guarded`, priorité haute, un seul Lean, réserve
4096 Mo. Pics échantillonnés : 2066, 3876, 2145, 4153 Mo ; hub 4033 Mo,
audit 3893 Mo. Aucun budget n'a été augmenté.

L'audit retourne les trois axiomes usuels et, pour les quatre théorèmes de
graphe/domaine minimal réel, la dépendance Stokes native préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; fichiers externes et T08 préservés.

### Deux extensions ghost et critère d'unicité

`P0EFTJanusProgramPT12OffDiagonalExtensionPair4D.lean` compare les blocs
`B₁ = B(F_min, F_min†)` et `B₂ = B(A_min†, A_min)`. La spécialisation
`P0EFTJanusProgramPT12CandidateAAbelianGhostExtensions4D.lean` construit `B₂`
pour les métriques réelles de Candidate A, avec son domaine exact. Les deux
blocs sont fermés, auto-adjoints et à domaine dense ; ils étendent le même
bloc minimal `B_min = B(F_min, A_min)`. Leur intersection de graphes est
exactement le graphe de `B_min`.

Les équivalences suivantes sont prouvées : `B₁ = B₂`, `A_min = F_min†`,
autoadjonction de `B_min`, propriété de cœur lisse pour `B₁`, et unicité
parmi toutes les extensions auto-adjointes de `B_min`.
`P0EFTJanusProgramPT12CandidateAAbelianGhostExtensionPairing4D.lean` prouve
l'accord des deux actions sur tout le domaine minimal et le pairing exact
avec le même Hessien ghost lisse. Si la propriété de cœur échoue, `B₂` est
un témoin explicite distinct de `B₁`. Son échec n'est pas affirmé pour les
données actuelles : ni l'égalité ni l'inégalité des extensions n'est établie.

La compacité seule ne justifie pas de remplacer ce critère par une preuve
d'autoadjonction essentielle : le théorème 5.1 de
[Colin de Verdière–Le Bihan](https://afst.centre-mersenne.org/articles/10.5802/afst.1719/)
donne des laplaciens lorentziens non essentiellement auto-adjoints sur des
tores compacts de dimension deux. Il s'agit d'un repère analytique externe,
pas d'un contre-exemple formalisé sur le quotient Janus. La condition de
centrage de la carte forte identifie sa géométrie au centre ; elle ne fournit
pas à elle seule l'approximation en norme de graphe manquante. T12 reste ouvert.

Les trois gates, le hub et l'audit des vingt-sept déclarations publiques sont
verts sous `run_lean_guarded`, priorité haute, un seul Lean, réserve 4096 Mo.
Pics : 2251, 3917, 3916 Mo ; hub 3994 Mo ; audit 3897 Mo.
L'audit retourne `propext`, `Classical.choice`, `Quot.sound` et, pour les
résultats issus du Stokes réel, la dépendance native préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner ;
`git diff --check` vert. Fichiers externes et T08 préservés.

### Obstruction globale dans la fibre complète, H11 inclus

`P0EFTJanusProgramPT12SpectralBRSTNonnegative4D.lean` prouve la positivité
du pairing spectral sur les états dont les coordonnées matière sont nulles.
`P0EFTJanusProgramPT12FullFriedrichsBRSTNonnegative4D.lean` identifie le noyau
du readout matière–LL et établit la positivité du pairing de l'opérateur
complet sur ce noyau, pour chaque paramètre de la famille. Le transport
physique et son terme H11 s'annulent sur ces états ; le slot LL est nul.

`P0EFTJanusProgramPT12ActualFullFriedrichsSectorNoGo4D.lean` fournit un champ
pairé lisse non nul et conserve le carré strictement négatif du témoin B dans
le Riesz augmenté réel. La contradiction avec la positivité cible prouve
`no_actual_to_fullFriedrichs_sector_pairing` à paramètre zéro. Le théorème
porte sur tout le cœur réel et la fibre complète, avec leurs termes physiques.
Il ne dépend ni de l'égalité minimale–maximale des ghosts, ni d'une hypothèse
terminale d'intertwiner, ni du centrage fort.

La portée est précise : la conservation exigée ici est l'annulation du
readout matière–LL cible sur les B purs. Le théorème ne tranche pas les
applications arbitraires qui mélangeraient ces champs aux secteurs matière
signés. La correction de la cible BRST reste nécessaire pour le raccord
sectoriel demandé ; T12 n'est pas coché.

Les trois gates, le hub et l'audit des sept déclarations publiques sont verts
sous `run_lean_guarded`, priorité haute, un seul Lean, réserve 4096 Mo.
Pics des compilations vertes : 3653, 3915, 3915 Mo ; hub 4169 Mo ; audit
3714 Mo. L'audit retourne uniquement `propext`, `Classical.choice`, `Quot.sound`.
Aucun nouvel axiome, `sorry`, `admit` ou budget augmenté dans les fichiers
retenus. Le corollaire isométrique séparé a été écarté après dépassement de
la limite `whnf` ; la gate générale de non-existence du pairing est conservée.
`git diff --check` vert ; fichiers externes et T08 préservés.

### Réalisation constructive du BRST abélien complet

Les gates `ProductClosedOperator4D`, `ProductSelfAdjoint4D` et
`BRSTSaddleProduct4D` (préfixe `P0EFTJanusProgramPT12`) construisent le
produit auto-adjoint du bloc potentiel–B signé et du bloc fantôme non borné.
Pour la projection Lorenz L sur son espace de graphe, le premier bloc est
`(A,B) ↦ (L†B, LA − B)`. Le second est
`(cbar,c) ↦ (Fmin c, Fmin† cbar)`, sur les vrais domaines L² déjà construits.

`CandidateAAbelianMixedOperator4D` spécialise cette construction aux métriques
réelles de Candidate A. L'opérateur est auto-adjoint, fermé et de domaine
dense. Son domaine est exactement : potentiel dans le graphe Lorenz,
B arbitraire dans L², antighost dans dom(Fmin†), ghost dans dom(Fmin).
`CandidateAAbelianMixedPairing4D` prouve le pairing avec la Hessienne complète
et avec la polarisation de l'action BRST intégrée, pour tous les états lisses.
`CandidateAAbelianMixedSmooth4D` fournit leur réalisation linéaire injective
à image dense ; les quatre champs sont conservés, sans supprimer le carré B négatif.

La norme du potentiel reste celle du graphe Lorenz. La densité démontrée
est une densité hilbertienne, pas une propriété de cœur pour l'opérateur.
Le raccord au D9 corrigé, les colonnes H11, le secteur difféomorphisme et le
certificat global restent à établir ; T12 n'est pas coché. Quillen et T08
ne sont pas modifiés.

Validation : six gates, hub T12 et audit des 31 déclarations publiques verts
sous `run_lean_guarded`, priorité haute, Lean séquentiel, réserve 4096 Mo.
Pics des runs verts : 2181, 2188, 2183, 3926, 3984, 3947 Mo ; hub 4106 Mo ;
audit 3894 Mo. Axiomes : `propext`, `Classical.choice`, `Quot.sound`, avec
la dépendance native de Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`
pour l'auto-adjonction et les pairings réels. Aucun nouvel axiome, `sorry`,
`admit` ou hypothèse terminale d'intertwiner ; `git diff --check` vert.

### Raccord H11 à la réalisation abélienne mixte

`AbelianPotentialGraphInclusion4D` et `CandidateAAbelianMixedPotential4D`
(préfixe `P0EFTJanusProgramPT12`) construisent l'inclusion continue du graphe
Lorenz et le readout physique de l'espace mixte. Les slots nonminimaux y sont
nuls, tandis que le potentiel complété est conservé.

`CandidateAAbelianMixedPhysical4D` compose ce readout avec le véritable Riesz
physique. Sa colonne prend ses valeurs dans tout le Hilbert commun : elle
conserve les sorties H11 vers les autres secteurs. Sur chaque état abélien
lisse, elle égale la colonne réelle, contre tout test commun complété.
La même égalité est prouvée après projection au quotient ghosts–LL.

`CandidateAAbelianMixedH114D` construit le bloc interne par transport adjoint
et prouve son auto-adjonction bornée ainsi que son pairing physique exact.
`BoundedSelfAdjointPerturbation4D` prouve directement la formule de l'adjoint
pour une perturbation bornée d'un opérateur densément défini.
`CandidateAAbelianMixedAugmented4D` ajoute H11 au BRST abélien non borné :
auto-adjonction, domaine inchangé, pairing lisse égal au Riesz augmenté réel.

Ces résultats utilisent l'extension physique commune et le centrage fort
existants. Ils ne construisent pas une nouvelle extension physique globale.
Le potentiel reste en norme de graphe Lorenz ; l'identification à une cible
D9 corrigée, la propriété de cœur des ghosts et la réalisation du secteur
difféomorphisme restent ouvertes. T12 n'est pas coché.

Validation : six gates, hub et audit des 29 déclarations publiques verts,
Lean séquentiel gardé, priorité haute, réserve 4096 Mo. Pics des runs verts :
3750, 3914, 3966, 2190, 4181, 4007 Mo ; hub 4006 Mo ; audit 3922 Mo.
L'audit retourne `propext`, `Classical.choice`, `Quot.sound` ; seuls
l'auto-adjonction et les deux pairings de l'opérateur augmenté héritent de
la dépendance native Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; Quillen et T08 préservés.

### Opérateur BRST couplé : difféomorphisme et abélien

`CoupledBRSTOperator4D` (préfixe `P0EFTJanusProgramPT12`) assemble un bloc
borné auto-adjoint, un bloc non borné auto-adjoint et le transport adjoint
d'une Hessienne physique commune. Le transport est la somme des deux
inclusions : les deux termes H11 croisés sont donc conservés.

`CandidateACoupledBRST4D` spécialise cet opérateur au véritable Riesz signé
difféomorphisme et au BRST abélien mixte. Il est auto-adjoint ; son domaine
est exactement le domaine fantôme abélien dans le deuxième facteur, sans
restriction supplémentaire dans le graphe difféomorphisme. Sa colonne
physique prend ses valeurs dans tout le Hilbert commun et égale la colonne
réelle sur les états considérés.

`CandidateACoupledBRSTDomainPairing4D` prouve le pairing sur tout le domaine.
`CandidateACoupledBRSTPairing4D` et `CandidateACoupledBRSTActual4D` établissent
l'égalité exacte avec le Riesz augmenté réel pour des entrées difféomorphisme
complétées et des champs abéliens lisses. `CandidateACoupledBRSTSmooth4D`
construit la réalisation linéaire injective dense des deux familles lisses,
dont l'image est incluse dans le domaine de l'opérateur.

Le secteur difféomorphisme conserve ici sa norme de graphe existante ; les
fantômes abéliens restent en L² canonique. La densité prouvée est hilbertienne,
pas une propriété de cœur d'opérateur. Le centrage et l'extension physique
commune sont ceux du cadre existant. Aucun raccord D9, certificat terminal
global ou fermeture T12 n'est revendiqué à ce stade.

Validation : six gates, hub et audit des 26 déclarations publiques verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo. Pics des
runs verts : 2178, 4047, 4302, 4010, 4175, 3984 Mo ; hub 4050 Mo ; audit
3925 Mo. Les limites de récursion rencontrées ont été résolues par une gate
séparée de pairing sur le domaine, sans augmentation des budgets.
Axiomes : `propext`, `Classical.choice`, `Quot.sound`, et la seule dépendance
native Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`
pour les résultats utilisant le domaine fantôme réel et son auto-adjonction.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Réduction du BRST couplé et entrelacement concret

`CandidateAReducedBRST4D` (préfixe `P0EFTJanusProgramPT12`) remplace le
facteur difféomorphisme par son quotient fermé des ghosts partagés. Le
facteur abélien mixte est conservé. La projection est continue et surjective,
et conserve exactement la condition de domaine abélienne. Sous les
hypothèses existantes de métriques égales et de poids cinétiques opposés,
l'opérateur réduit est auto-adjoint. La colonne H11 complète est transportée
vers le quotient global ghosts–LL déjà construit.

`CandidateAReducedBRSTPairing4D` conserve le pairing pour chaque entrée du
domaine non borné et chaque test complété. `QuotientPairingIntertwiner4D`
établit que la projection composée avec son adjoint est l'identité et en
déduit l'entrelacement d'opérateurs à partir du pairing.
`CandidateAReducedBRSTIntertwining4D` applique ce résultat : l'opérateur réduit
composé avec la projection égale la projection de l'opérateur couplé réel.
L'annulation de la sortie réduite équivaut à celle de la sortie originale.

`CandidateAReducedBRSTSmooth4D` fournit une réalisation lisse linéaire dense,
contenue dans le domaine réduit, et annule les générateurs ghosts partagés.
Le noyau de la projection est exactement le sous-espace ghost difféomorphisme
avec composante abélienne nulle.

La norme difféomorphisme reste une norme de graphe. Le raccord à la fibre
D9/Friedrichs, les propriétés de cœur et le certificat terminal global
restent ouverts. La présente réduction utilise le quotient ghosts–LL
existant pour les sorties physiques ; T12 n'est pas coché.

Validation : cinq gates, hub et audit des 25 déclarations publiques verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo. Pics des
runs verts : 4309, 1905, 4318, 4302, 3995 Mo ; hub 4162 Mo ; audit 3907 Mo.
Les réécritures de pairing ont été séparées par composante, sans augmentation
des budgets. L'audit utilise `#print axioms` sur chaque déclaration publique
des cinq gates. Axiomes : `propext`, `Classical.choice`, `Quot.sound`, et la
seule dépendance native Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`
pour l'auto-adjonction et l'appartenance des champs lisses au domaine.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Assemblage BRST réduit et LL quotienté

`CandidateABRSTLLRealization4D` (préfixe `P0EFTJanusProgramPT12`) construit
le produit de l'opérateur BRST réduit, avec son bloc physique H11, et de la
réalisation de Friedrichs sur le quotient LL auxiliaire/mesure. Sous les
hypothèses existantes de métriques égales et de poids cinétiques opposés,
ce produit est auto-adjoint. Son domaine impose exactement la condition
fantôme abélienne et celle du Friedrichs LL. `ProductOperatorPairing4D`
isole le pairing générique du produit pour éviter les longues réécritures.

`CandidateABRSTLLSmooth4D` réalise ensemble les champs difféomorphisme,
abéliens et LL lisses. L'image est dense dans le Hilbert produit et incluse
dans le domaine de l'opérateur ; les représentants LL auxiliaires et mesure
restent arbitraires avant projection. `CandidateABRSTLLPairing4D` identifie,
à flux LL nul, le pairing lisse avec la somme du pairing augmenté réel des
deux secteurs BRST et de la Hessienne LL complète de la même action.

Cette somme garde les termes H11 entre les deux secteurs BRST. Elle ne
constitue pas encore un transport de tout le Hilbert physique commun vers
D9, ni une preuve de cœur d'opérateur. La matière, le raccord D9/Friedrichs
global et le certificat terminal restent à intégrer ; T12 n'est pas coché.

Validation : quatre gates, hub et audit des 11 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des runs verts : 2146, 4323, 4055, 4276 Mo ; hub 4097 Mo ; audit 3906 Mo.
Le timeout de réécriture a été résolu par le lemme générique de pairing,
sans augmentation des budgets. `#print axioms` confirme seulement `propext`,
`Classical.choice`, `Quot.sound` et la dépendance native Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`
pour l'auto-adjonction et les résultats utilisant le domaine lisse.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Réalisation simultanée des quatre secteurs et pairing original

`MatterGraphRealization4D` (préfixe `P0EFTJanusProgramPT12`) donne
l'auto-adjonction du Riesz signé matière sur tout son Hilbert de graphe,
ainsi que l'inclusion dense des coefficients finis et leur pairing exact.
La matière n'est pas remplacée par zéro : seule sa colonne physique H11
s'annule dans le cadre fort existant.

`CandidateAFourSectorRealization4D` assemble ce facteur avec le BRST réduit
et le LL quotienté. L'opérateur est auto-adjoint sous les hypothèses
existantes de métriques égales et de poids cinétiques opposés. Son domaine
garde exactement les conditions fantômes abéliennes et de Friedrichs LL ;
le facteur matière n'ajoute aucune restriction dans sa norme de graphe.
`CandidateAFourSectorSmooth4D` construit l'inclusion des quatre familles
lisses, dense dans le Hilbert produit et contenue dans ce domaine.

`CandidateAFourSectorPairing4D` prouve le pairing de la somme des secteurs.
`OrthogonalColumnPairing4D` isole la décomposition d'un opérateur symétrique
le long d'une colonne orthogonale invariante.
`CandidateAFourSectorOriginalPairing4D` utilise la colonne matière–LL déjà
établie ; `CandidateAFourSectorActual4D` compose les résultats pour identifier ce pairing,
à flux LL nul, avec le Riesz augmenté original évalué sur les quatre
secteurs simultanément. Les termes H11 BRST sont conservés et les termes
croisés matière–LL/BRST sont annulés par des preuves, sans nouvelle hypothèse.

La norme de graphe reste utilisée pour la matière et le difféomorphisme.
La densité est hilbertienne, sans affirmation de cœur d'opérateur.
Cette égalité de pairing globale sur les représentants lisses n'est pas
encore l'identification à la fibre D9/Friedrichs ; le certificat terminal
reste ouvert et T12 n'est pas coché.

Validation : sept gates, hub et audit des 21 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des runs verts : 3796, 4355, 4172, 4037, 1906, 4139, 4041 Mo ; hub
4084 Mo ; audit 3925 Mo. Les limites de réécriture et de récursion ont été
résolues par séparation du pairing original et du raccord final, sans
augmentation des budgets. Un avertissement stylistique de tactique reste
dans `CandidateAFourSectorOriginalPairing4D` ; la compilation réussit.
`#print axioms` confirme `propext`, `Classical.choice`, `Quot.sound` et la
seule dépendance native Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`
pour les résultats utilisant l'auto-adjonction BRST ou le domaine lisse.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Matière en L² canonique et cœur d'opérateur

`MatterCanonicalOperator4D` (préfixe `P0EFTJanusProgramPT12`) réalise le
multiplicateur signé exact `2D + m²` des deux secteurs matière sur le Hilbert
canonique des coefficients L². Son domaine est le domaine maximal diagonal,
et son auto-adjonction découle du résultat diagonal réel existant. Le pairing
des coefficients finis est exactement celui de la Hessienne matière.

`MatterCanonicalCore4D` prouve `HasCore` pour l'image des coefficients finis :
la fermeture de la restriction est l'opérateur maximal lui-même. La preuve
utilise la densité déjà démontrée des modes finis dans le graphe complexe,
puis identifie les graphes réel et complexe comme ensembles. Il s'agit ici
d'une propriété de cœur d'opérateur, au-delà de la densité hilbertienne.

`CandidateACanonicalMatterFourSector4D` insère cette matière L² dans le
produit avec le BRST réduit et le LL quotienté. L'auto-adjonction conserve
les hypothèses existantes de métriques égales et de poids opposés ; le
domaine inclut maintenant explicitement le domaine maximal matière.
`CandidateACanonicalMatterSmooth4D` construit une réalisation dense des mêmes
représentants, contenue dans le domaine. `CandidateACanonicalMatterActual4D`
conserve, à flux LL nul, l'égalité de pairing avec le Riesz augmenté original
pour les quatre secteurs simultanément.

La matière de cette nouvelle réalisation est en L² canonique. Le facteur
difféomorphisme garde sa norme de graphe ; les propriétés de cœur globales
BRST/LL et le raccord complet à la fibre D9/Friedrichs restent ouverts.
Le certificat terminal n'est pas construit et T12 n'est pas coché.

Validation : cinq gates, hub et audit des 21 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des runs verts : 3748, 3814, 4200, 4060, 4045 Mo ; hub 4160 Mo ; audit
3911 Mo. Aucun budget augmenté. `#print axioms` donne seulement `propext`,
`Classical.choice`, `Quot.sound` pour l'opérateur matière et son cœur.
Les résultats globaux utilisant le BRST gardent la seule dépendance native
Stokes préexistante
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Fermeture minimale du BRST abélien complet et H11

`ProductClosure4D`, `ProductCore4D` et `BoundedPerturbationCore4D` (préfixe
`P0EFTJanusProgramPT12`) transportent les fermetures de graphes et les cœurs
d'opérateurs par produit et par perturbation bornée.

`CandidateAAbelianMixedMinimal4D` construit le BRST abélien minimal fermé,
avec potentiel, multiplicateur B, fantôme et antifantôme. L'image des champs
lisses réels est un cœur de cet opérateur. La fermeture de la restriction
lisse de l'extension auto-adjointe existante est exactement cet opérateur
minimal, sans hypothèse d'égalité entre adjoints minimal et maximal.

`CandidateAAbelianMixedMinimalH114D` conserve ces résultats après ajout de
la correction physique H11 complète : fermeture, cœur lisse et calcul de
la fermeture de la restriction de l'opérateur augmenté existant.

Cela ne prouve pas encore que le minimal est auto-adjoint. L'égalité de
l'adjoint formel minimal avec l'adjoint maximal FP reste ouverte, ainsi que
le difféomorphisme en L² canonique, le cœur LL et le raccord global D9.
Le certificat terminal n'est pas construit et T12 reste ouvert.

Validation : cinq gates, hub et audit des 28 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 2186, 2185, 2190, 4038, 4045 Mo ; hub 4250 Mo ; audit
3933 Mo. Aucun budget augmenté. `#print axioms` donne `propext`,
`Classical.choice`, `Quot.sound`, avec la seule dépendance native Stokes
préexistante pour les preuves analytiques BRST :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Cœur minimal du BRST couplé et pairing original

`CoupledBRSTCore4D` (préfixe `P0EFTJanusProgramPT12`) transporte les cœurs
et calcule la fermeture d'une restriction du BRST couplé, en conservant
tout le bloc physique borné, y compris les termes croisés H11.

`CandidateACoupledBRSTMinimal4D` construit concrètement l'opérateur couplé
minimal fermé. L'image simultanée des champs lisses difféomorphisme et
abéliens est un cœur de cet opérateur. La fermeture de la restriction
lisse de l'extension auto-adjointe existante est exactement ce minimal.

`CandidateACoupledBRSTMinimalActual4D` identifie son action sur les champs
lisses à celle de l'extension existante, puis prouve le pairing exact avec
le Riesz augmenté original. Aucun terme physique croisé n'est supprimé.

Le facteur difféomorphisme reste dans le Hilbert de graphe existant. Ces
résultats ne prouvent pas l'auto-adjonction du minimal : l'égalité des
adjoints FP minimal/maximal reste ouverte. Le passage difféomorphisme en
L² canonique, le cœur LL et l'identification globale D9 restent également
à établir. T12 n'est pas coché.

Validation : trois gates, hub et audit des 12 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 2182, 4320, 4030 Mo ; hub 4003 Mo ; audit 3906 Mo.
La limite de récursion du raccord d'action a été résolue en explicitant
les domaines et en utilisant `LinearPMap.domRestrict_apply`, sans augmenter
les budgets. `#print axioms` confirme `propext`, `Classical.choice`,
`Quot.sound` et la seule dépendance native Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Cœur minimal BRST après quotient des fantômes partagés

`CandidateAReducedBRSTMinimal4D` (préfixe `P0EFTJanusProgramPT12`) construit
le minimal fermé sur le quotient hilbertien des directions fantômes
partagées. L'image des champs lisses quotientés est un cœur d'opérateur,
et la fermeture de la restriction lisse de l'extension réduite existante
est exactement ce minimal. Le quotient préserve le domaine abélien.

`CandidateAReducedBRSTMinimalPairing4D` prouve la conservation du pairing
sur tout le domaine minimal, contre tout test complété. Tous les blocs
physiques H11, y compris les termes croisés, sont conservés.

`CandidateAReducedBRSTMinimalIntertwining4D` en déduit l'égalité exacte des
sorties après projection et l'équivalence de leur annulation. Sur le cœur
des champs réels, le pairing est celui du Riesz augmenté original.

Ces résultats gardent les hypothèses existantes de métriques égales et de
poids cinétiques opposés. Ils n'identifient pas le minimal à l'extension
auto-adjointe : l'égalité des adjoints FP reste ouverte. Le difféomorphisme
reste dans son Hilbert de graphe ; le passage L², le cœur LL et le raccord
global D9 restent à établir. T12 n'est pas coché.

Validation : trois gates, hub et audit des 19 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 4366, 4468, 4351 Mo ; hub 4000 Mo ; audit 3936 Mo.
Les timeouts `whnf` ont été résolus par des lemmes de domaine et un raccord
de pairing séparé, sans augmenter les budgets. L'audit des pairings sur
le domaine complet et de l'entrelacement utilise seulement `propext`,
`Classical.choice`, `Quot.sound`. Les preuves de cœur et leur spécialisation
lisse gardent la seule dépendance native Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Cœur LL quotienté et cœur minimal commun aux quatre secteurs

`ClosedNullPMapCore4D` (préfixe `P0EFTJanusProgramPT12`) prouve que le cœur
d'un opérateur fermé symétrique descend par quotient d'un sous-espace
fermé de directions nulles. Il identifie aussi la fermeture de la
restriction d'une extension au cœur de l'opérateur minimal.

`LLReducedMinimalCore4D` applique ces résultats au LL réel à flux nul :
les champs lisses forment un cœur du Jacobi minimal quotienté. La fermeture
de la restriction lisse du Friedrichs quotienté est exactement ce Jacobi
minimal. Cela ne prouve pas encore l'égalité du minimal avec Friedrichs.

`ProductRestrictionClosure4D` isole la formule de fermeture d'une restriction
produit. `CandidateABRSTLLMinimal4D` construit le produit minimal BRST–LL
fermé et son cœur lisse commun, puis calcule la fermeture de la restriction
de la réalisation existante.

`CandidateAFourSectorMinimalCore4D` y ajoute la matière en L² canonique.
L'image commune des champs des quatre secteurs est un cœur de ce minimal
global fermé ; celui-ci est la fermeture calculée de la restriction de la
réalisation globale existante. Les directions LL auxiliaires/mesure sont
quotientées et le bloc H11 BRST complet est conservé.

Les hypothèses restent métriques égales, poids opposés et flux LL nul.
L'identification du minimal à l'extension auto-adjointe exige encore les
égalités d'extensions BRST et LL. Le difféomorphisme reste en norme de
graphe ; son passage L² et le raccord global D9 ne sont pas établis.
T12 n'est pas coché.

Validation : cinq gates, hub et audit des 16 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates (quotient, LL, produit, BRST–LL, quatre secteurs) : 2184,
3921, 2145, 4328, 4314 Mo ; hub 4071 Mo ; audit 3929 Mo.
Les timeouts du produit global ont été résolus en isolant la formule de
fermeture, en nommant les étapes et en explicitant localement les instances
hilbertiennes/topologiques, avec respect de la transparence rétabli pour
les deux derniers théorèmes. Aucun budget augmenté.
L'audit LL et des lemmes généraux donne seulement `propext`,
`Classical.choice`, `Quot.sound`. Les résultats composés avec le BRST gardent
la seule dépendance native Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Domaine minimal global, symétrie et raccord au Riesz original

`CoreRestrictionExtension4D` (préfixe `P0EFTJanusProgramPT12`) établit
l'inclusion de la fermeture d'une restriction dans une extension fermée,
et la symétrie d'une restriction d'un opérateur auto-adjoint.

`CandidateAFourSectorMinimalExtension4D` prouve concrètement que le minimal
global des quatre secteurs est inclus dans la réalisation auto-adjointe
existante. Son domaine est dense et il est symétrique. Sa fermeture et
son cœur commun étaient déjà établis dans la gate précédente.

`CandidateAFourSectorMinimalActual4D` construit les éléments du domaine
minimal associés aux champs réels, identifie exactement leur action à
celle de l'extension existante, puis obtient le pairing avec le Riesz
augmenté original sur les quatre secteurs simultanément.

L'auto-adjonction du minimal n'est pas déduite de sa seule symétrie.
Les égalités d'extensions BRST et LL restent ouvertes. Pour LL, les gates
de solution faible fournissent encore un critère d'appartenance au domaine
minimal, pas une preuve de cette appartenance. Le difféomorphisme en L²
canonique et le raccord global D9 restent à établir. T12 reste ouvert.

Validation : trois gates, hub et audit des 9 déclarations publiques verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 1907, 4062, 4291 Mo ; hub 4009 Mo ; audit 3920 Mo.
Les instances locales explicites du cœur global sont réutilisées ; le
raccord d'inclusion emploie une composition d'égalité et d'ordre pour
éviter une réécriture à travers les instances. Aucun budget augmenté.
`#print axioms` confirme `propext`, `Classical.choice`, `Quot.sound`, avec
la seule dépendance native Stokes préexistante pour les résultats globaux :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou hypothèse terminale d'intertwiner.
`git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Cœur L² et différentiel BRST difféomorphisme

`DiffeomorphismL2Core4D` (préfixe `P0EFTJanusProgramPT12`) construit une
complétion des seules coordonnées d'ordre zéro : les deux perturbations
métriques et un unique triplet fantôme/antifantôme/multiplicateur. La mesure
est le volume canonique ; la normalisation des trois champs vectoriels est
celle de la métrique plus. Les coordonnées de repère étant redondantes,
on prend la fermeture de leur image réelle, sans supposer qu'elle remplit
l'espace ambiant. L'inclusion lisse est injective et dense.

`DiffeomorphismGraphToL24D` construit une application linéaire continue de
l'ancien graphe différentiel vers ce L². Elle restitue exactement les
coordonnées d'ordre zéro sur les champs lisses et son image est dense.
Son injectivité sur le graphe complété n'est pas encore établie.

`DiffeomorphismL2BRST4D` réalise le différentiel BRST diagonal original
comme opérateur partiel en L², sur le domaine lisse dense. Ce domaine est
invariant et le carré de l'opérateur est nul sur tout son domaine.
La linéarité et la nilpotence sont prouvées à partir des champs originaux.

Cette construction porte sur le différentiel BRST. La fermeture et la
réalisation L² de son Hessien gauge-fixé, ainsi que le transport des colonnes
H11 dans ce L², restent à prouver. Les égalités d'extensions abélienne/LL
et le raccord D9 restent ouverts ; T12 n'est pas coché.

Validation : trois gates, hub et audit des 25 déclarations nommées verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3745, 3763, 3966 Mo ; hub 4010 Mo ; audit 3689 Mo.
`#print axioms` donne uniquement `propext`, `Classical.choice`, `Quot.sound`
pour ces 25 déclarations, sans dépendance native Stokes supplémentaire.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; Quillen, T08 et les fichiers
externes préservés.

### Contraction du doublet BRST difféomorphisme en L²

`DiffeomorphismL2Triplet4D` (préfixe `P0EFTJanusProgramPT12`) construit les
transferts entre les trois champs du triplet comme applications linéaires
continues sur le L² réel. Leur préservation de l'image lisse complétée et
leurs lois de composition sont prouvées, avec la normalisation commune
fixée précédemment.

`DiffeomorphismL2Doublet4D` construit le différentiel nonminimal borné N,
l'homotopie bornée h et le projecteur P sur antifantôme/multiplicateur.
On a N² = h² = 0, Nh + hN = P et P² = P. L'homotopie préserve le domaine
du différentiel BRST original Q, et Qh + hQ = P y est démontré. La composante
doublet de chaque cycle est donc un bord explicite, de primitive hx.

`DiffeomorphismDoubletGraphClosure4D` prolonge cette identité à la fermeture
du graphe réel : (x,y) dans cette fermeture implique (hx,Px-hy) dans la même
fermeture. Ainsi, chaque cycle du graphe complété conserve une primitive
explicite pour sa composante doublet.

La fermeture est ici une relation linéaire fermée ; son caractère univoque
n'est pas supposé. La fermabilité du générateur métrique, le Hessien L²/H11,
les égalités d'extensions abélienne/LL et le raccord D9 restent ouverts.
Cette contraction du doublet ne ferme pas T12.

Validation : trois gates, hub et audit des 21 déclarations nommées verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3794, 3762, 3754 Mo ; hub 4132 Mo ; audit 3689 Mo.
`#print axioms` donne uniquement `propext`, `Classical.choice`, `Quot.sound`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; Quillen, T08 et les fichiers
externes préservés.

### Adjoint de Stokes, dérivées fermées et injection H¹ scalaire en L²

`CanonicalFrameDerivativeAdjoint4D` (préfixe `P0EFTJanusProgramPT12`)
construit, pour tout repère générateur lisse fini, l'adjoint concret
Dᵢ*φ = −div(φXᵢ) contre le volume canonique. L'identité intégrale découle
de Stokes pour les champs de vecteurs lisses ; son pairing L² est prouvé.
Une métrique régulière sert à la construction existante de la divergence.

`CanonicalFrameDerivativeClosed4D` exclut les vecteurs verticaux dans la
fermeture du graphe de chaque dérivée, puis construit son opérateur minimal
fermé en L², de domaine dense et de cœur lisse, avec l'action réelle exacte.
L'identité d'adjoint et la fermabilité ne sont pas des hypothèses ajoutées.

`CanonicalScalarH1Injective4D` raccorde chaque coordonnée dérivée du graphe
H¹ existant à cet opérateur fermé. Il en déduit l'injectivité de H¹ vers L²
pour tout repère générateur lisse, puis pour le H¹ scalaire physique canonique.
La complétion ne crée donc aucun vecteur H¹ scalaire non nul de valeur L² nulle.

Il reste à exprimer le générateur métrique BRST dans ces coordonnées et à
prouver son raccord d'adjoint. L'injectivité scalaire ne prouve pas seule
la fermabilité de toute combinaison différentielle ni celle du Hessien
BRST. Les réalisations L²/H11, les égalités d'extensions abélienne/LL et le
raccord D9 restent ouverts ; T12 n'est pas coché.

Validation : trois gates, hub et audit des 19 déclarations nommées verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3687, 3821, 3696 Mo ; hub 4010 Mo ; audit 3671 Mo.
L'audit donne `propext`, `Classical.choice`, `Quot.sound` et, pour les preuves
utilisant Stokes, la dépendance native préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; Quillen, T08 et les fichiers
externes préservés.

### Adjoint réel de Cartan et réalisation métrique appariée en coefficients L²

`CanonicalFirstOrderColumn4D` (préfixe `P0EFTJanusProgramPT12`) construit
les colonnes à coefficients lisses comportant deux dérivées de repère et
un terme d'ordre zéro. Leurs adjoints concrets sont obtenus par Stokes,
y compris les dérivées des coefficients pondérant le champ test.

`RegularFrameCartanAdjoint4D` décompose exactement le Cartan intrinsèque
L_c g en ces colonnes. Les coefficients de structure du repère non holonome
sont conservés. Le pairing d'adjoint est prouvé pour tout fantôme lisse réel,
via sa reconstruction dans un repère régulier fixé.

`RegularFrameCartanClosed4D` travaille dans les Hilbert L² des quatre
coefficients du fantôme et des seize coefficients du tenseur. Le pairing
passe à la fermeture du graphe et exclut ses vecteurs verticaux non nuls.
Il fournit donc un opérateur de Cartan fermé à domaine dense, avec l'action
intrinsèque exacte sur les coefficients lisses, pour tout tenseur symétrique
lisse fixé, notamment chaque métrique physique.

`PairedRegularFrameCartan4D` impose simultanément les deux conditions de
graphe fermé avec un unique fantôme en entrée. Le domaine commun est dense
et l'opérateur apparié fermé. Sa sortie lisse est exactement celle de
`globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap`, secteur
par secteur. Aucun second triplet ni poids cinétique de remplacement.

Cette réalisation utilise les coefficients du repère régulier : le transport
borné vers les anciennes coordonnées L² normalisées reste à prouver.
Le domaine apparié est l'intersection des deux domaines minimaux ; aucun
cœur d'opérateur commun ni égalité avec la fermeture du graphe lisse apparié
n'est revendiqué ici. Le Hessien BRST/H11, les égalités d'extensions
abélienne/LL et le raccord D9 restent ouverts ; T12 n'est pas coché.

Validation : quatre gates, hub et audit des 40 déclarations nommées verts
sous `run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3909, 3855, 3864, 4101 Mo ; hub 4004 Mo ; audit 3806 Mo.
L'audit donne `propext`, `Classical.choice`, `Quot.sound` et la seule dépendance
native Stokes préexistante pour les résultats qui l'utilisent :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; Quillen, T08 et les fichiers
externes préservés.
