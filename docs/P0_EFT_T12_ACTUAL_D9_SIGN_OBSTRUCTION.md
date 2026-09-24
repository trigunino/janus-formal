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

### Cœur Cartan apparié et équivalence des complétions L² du fantôme

`PairedRegularFrameCartanCore4D` (préfixe `P0EFTJanusProgramPT12`)
ferme la restriction du Cartan apparié aux coefficients lisses communs.
La réalisation minimale est fermée, de domaine dense, possède ce véritable
cœur d'opérateur et conserve l'action exacte des deux métriques avec un
fantôme partagé. Elle est incluse dans l'intersection précédente des domaines
minimaux ; l'égalité avec cette intersection n'est pas supposée.

`SmoothMatrixL24D` réalise les matrices de coefficients lisses comme
opérateurs bornés sur le L² canonique, avec accord exact sur les champs lisses.
`RegularGhostL2Transport4D` l'applique au changement des quatre coefficients
du repère régulier vers les anciennes coordonnées normalisées redondantes.
`RegularGhostL2Recovery4D` construit la récupération inverse, à partir du
pairing de repère et du vrai ratio de volume, puis prouve l'identité sur
tout le L² des quatre coefficients par densité.
`RegularGhostL2Equiv4D` identifie l'image fermée du transport à la fermeture
des anciens fantômes lisses et construit l'équivalence linéaire continue
avec inverse borné. Il ne s'agit pas d'une affirmation d'isométrie.

Le transport du fantôme est donc acquis. Restent notamment le transport des
tenseurs métriques (avec leur symétrie), le raccord du domaine Cartan apparié
aux anciennes coordonnées complètes, le Hessien BRST/H11, les égalités
d'extensions abélienne/LL et D9. T12 reste ouvert ; aucun intertwiner terminal
n'est pris en hypothèse.

Validation : cinq gates et audit des 34 déclarations nommées verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3856, 3765, 3853, 4002, 3880 Mo ; audit 3819 Mo.
L'audit donne `propext`, `Classical.choice`, `Quot.sound` ; seul le cœur Cartan
hérite en outre de l'axiome natif Stokes déjà présent :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit` ou budget augmenté.
Hub T12 compilé : pic 4004 Mo. `git diff --check` vert ; Quillen, T08 et les fichiers externes préservés.

### Tenseurs symétriques L² et Cartan apparié dans les coordonnées originales

`FrameTensorL2Transport4D` (préfixe `P0EFTJanusProgramPT12`) construit
le changement borné entre les coefficients de deux familles génératrices
finies. Les deux indices tensoriels sont reconstruits avec les coefficients
duaux réels ; l'accord sur tout tenseur symétrique lisse est exact.
`FrameTensorL2Equiv4D` construit les inverses sur les fermetures des images
lisses, puis leur équivalence linéaire continue. La symétrie des coefficients
passe à ces fermetures. Aucune densité dans l'ambient tensoriel entier ni
isométrie des coordonnées n'est supposée.

`RegularTensorL2Bridge4D` spécialise ce transport au repère régulier et à
`globalGeneralMetricTensorFrameL2LinearMap`. Le Cartan lisse commute avec
ce transport ; les deux sorties du domaine minimal apparié appartiennent
aux complétions tensorielles symétriques, par fermeture du graphe commun.

`PairedActualCartanClosed4D` reconstruit le graphe à partir du Cartan minimal
régulier, via l'inverse borné du fantôme normalisé et les inverses tensoriels.
Il fournit un opérateur fermé à domaine dense dans les anciennes coordonnées
L² : un fantôme commun normalisé par la métrique plus et les deux complétions
tensorielles réelles. Son action sur le domaine lisse est exactement le
Cartan des deux métriques. Le résultat ne remplace pas le Hessien BRST par
le différentiel de jauge.

Restent le raccord au domaine du BRST complet, le certificat de cœur commun
dans ces nouvelles présentations, le Hessien/H11, les égalités d'extensions
abélienne/LL et D9. T12 reste ouvert. Quillen et T08 sont préservés.

Validation : quatre gates et audit des 45 déclarations nommées verts sous
`run_lean_guarded`, un Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3857, 3863, 3956, 3881 Mo ; audit 3821 Mo.
Les transports tensoriels utilisent seulement `propext`, `Classical.choice`,
`Quot.sound`. Les preuves dépendant de la fermeture du Cartan héritent de
l'axiome natif Stokes préexistant :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté.
Hub T12 compilé : pic 4004 Mo. `git diff --check` vert ; fichiers externes préservés.

### Différentiel BRST diagonal complet : fermeture, cœur et contraction

`DiffeomorphismL2Readouts4D` (préfixe `P0EFTJanusProgramPT12`) fournit
les projections bornées des deux perturbations métriques et du triplet
partagé depuis le L² original. Les sorties tensorielles restent dans leurs
images lisses complétées ; leur récupération dans le repère régulier est
fidèle sur ces images.

`DiffeomorphismBRSTGraphRecovery4D` prouve que la fermeture du graphe du
BRST réel conserve le graphe de Cartan apparié récupéré et les trois équations
non minimales : sortie fantôme nulle, sortie antighost égale au multiplicateur
d'entrée, sortie multiplicateur nulle.
`DiffeomorphismBRSTClosed4D` en déduit l'absence de vecteurs verticaux non
nuls, donc la fermabilité du différentiel complet dans le L² original, à
partir du repère régulier fourni. Sa fermeture minimale est fermée, de domaine
dense, possède le véritable cœur des états lisses et prolonge exactement
le BRST diagonal initial. Aucun poids de graphe supplémentaire n'est ajouté
au Hilbert de base.

`DiffeomorphismBRSTClosedComplex4D` prouve l'invariance de ce domaine par Q
et Q² = 0. L'homotopie bornée antighost/multiplicateur préserve aussi le domaine
fermé et satisfait Qh + hQ = P_doublet. Un cycle possède donc explicitement
la primitive h pour sa composante doublet, jusque dans le domaine fermé.

Cette étape ferme le différentiel BRST de difféomorphisme et son cœur lisse.
Elle ne démontre pas encore la réalisation du Hessien de jauge fixé ni ses
colonnes H11. Le raccord actual→D9, les égalités d'extensions abélienne/LL,
l'intertwining global et le certificat terminal restent ouverts. T12 n'est
pas coché ; Quillen et T08 restent inchangés.

Validation : quatre gates et audit des 30 déclarations nommées verts sous
`run_lean_guarded`, un Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3866, 4222, 3898, 4132 Mo ; audit 3821 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound`, avec la dépendance
native Stokes préexistante pour les résultats qui utilisent Cartan fermé :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté.
Hub T12 compilé : pic 4004 Mo. `git diff --check` vert ; fichiers externes préservés.

### De Donder réel : fermeture L² et tests de l'adjoint

Quatre gates `P0EFTJanusProgramPT12DeDonder{SmoothCoefficients,RowAdjoint,L2Closed,L2Adjoint}4D`
réalisent le véritable opérateur de de Donder dans la complétion L² des
tenseurs symétriques. La formule en repère fini est identifiée à l'opérateur
existant, avec les termes de connexion et les dérivées des coefficients.
L'intégration par parties construit explicitement l'adjoint des lignes.
Elle exclut les vecteurs verticaux non nuls du graphe fermé : la fermeture
minimale a un domaine dense, un cœur lisse et l'action lisse initiale exacte.

Les tests scalaires par coordonnée appartiennent au domaine du véritable
adjoint hilbertien. Son action est la projection orthogonale de l'adjoint
explicite sur la complétion tensorielle réelle ; aucune conservation de la
régularité lisse par cette projection n'est supposée.

Restent notamment Faddeev–Popov, l'assemblage du Hessien BRST/H11, les
égalités d'extensions abélienne/LL et le raccord global à D9. La fermeture
du différentiel BRST et celle de De Donder ne constituent pas à elles seules
la fermeture terminale du Hessien. T12 reste ouvert ; Quillen et T08 préservés.

Validation des quatre gates sous `run_lean_guarded`, un Lean séquentiel,
priorité haute, réserve 4096 Mo : pics 3858, 3855, 3878, 3863 Mo.
Audit des 37 déclarations nommées vert, pic 3801 Mo ; hub T12 vert, pic 4007 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance native
Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; fichiers externes préservés.

### Faddeev–Popov réel : fermeture et cœur lisse commun

`P0EFTJanusProgramPT12FaddeevPopovAdjoint4D` compose les adjoints explicites
de De Donder et de Cartan. La formule conserve les dérivées des coefficients
et les termes de connexion ; son action est identifiée au véritable
`globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap` évalué dans le repère
régulier. Les tests satisfont l'identité de pairing sans hypothèse terminale.

`FaddeevPopovL2Core4D` et `FaddeevPopovL2Closed4D` (même préfixe) construisent
la fermeture minimale dans le L² d'ordre zéro des quatre coefficients du
repère régulier. L'entrée lisse est injective et dense. L'identité de pairing
exclut les vecteurs verticaux non nuls, prouve la fermabilité, puis fournit
un véritable cœur lisse, l'action lisse exacte et le graphe de l'adjoint
hilbertien sur les tests scalaires par coordonnée.

`PairedFaddeevPopovClosed4D` ferme simultanément les deux sorties métriques
avec un seul fantôme. Son cœur impose une approximation lisse commune aux
deux sorties. Il n'est pas identifié sans preuve à l'intersection des deux
domaines minimaux séparés. La fermeture de la composition différentielle
est démontrée directement ; aucune règle générale de fermeture des
compositions d'opérateurs fermés n'est utilisée.

Restent le transport des sorties covectorielles et de ces graphes vers les
espaces originaux du Hessien, l'assemblage avec les poids et le triplet
non minimal partagé, H11, les égalités d'extensions abélienne/LL et le raccord
global à D9. Ces réalisations Faddeev–Popov ne ferment pas encore le Hessien
BRST global. T12 reste ouvert ; Quillen et T08 sont préservés.

Validation : quatre gates vertes sous `run_lean_guarded`, un Lean séquentiel,
priorité haute, réserve 4096 Mo. Pics : 3863, 3883, 3929, 3887 Mo.
Audit des 43 déclarations nommées vert, pic 3822 Mo ; hub T12 vert, pic 4007 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance native
Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; fichiers externes préservés.

### Faddeev–Popov apparié dans les complétions L² originales

`P0EFTJanusProgramPT12FrameCovectorL2Transport4D` construit les matrices
bornées de changement de repère des covecteurs et leur accord exact sur les
champs lisses. `FrameCovectorL2Equiv4D` (même préfixe) les prolonge en
équivalences continues inverses entre les complétions des images réelles.
Les coordonnées redondantes ne sont pas assimilées à des champs indépendants.

`ActualFaddeevPopovCore4D` identifie exactement l'entrée au fantôme normalisé
original et chaque sortie à De Donder appliqué au générateur de jauge réel.
Les deux métriques partagent la même entrée. La récupération dans le repère
régulier est bornée et injective sur la complétion covectorielle réelle.
`ActualFaddeevPopovClosed4D` en déduit la fermabilité, une fermeture minimale
fermée de domaine dense, un véritable cœur lisse commun et l'action lisse
initiale exacte dans les espaces originaux. La récupération de son graphe
appartient au graphe minimal apparié régulier ; la surjectivité entre ces
deux graphes n'est pas affirmée ici.

Restent l'assemblage du Hessien BRST avec ses poids et son triplet partagé,
les colonnes H11, les égalités d'extensions abélienne/LL et le raccord global
à D9. T12 reste ouvert ; Quillen et T08 sont préservés.

Validation : quatre gates, audit des 46 déclarations nommées et hub T12 verts
sous `run_lean_guarded`, un Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3865, 3873, 3893, 3922 Mo ; audit 3821 Mo ; hub 4257 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance native
Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; fichiers externes préservés.

### Assemblage du Hessien BRST sur un domaine différentiel commun

`P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D` réalise par matrices
bornées l'abaissement métrique et les normalisations sectorielles du triplet
partagé dans le L² original. L'accord lisse est exact, notamment pour B♭.

`DiffeomorphismHessianFeatureCore4D` et `DiffeomorphismHessianFeatureClosed4D`
(même préfixe) ferment simultanément les deux sorties De Donder et les deux
sorties Faddeev–Popov depuis l'état BRST complet. Le domaine est dense et
possède un véritable cœur lisse commun : les quatre sorties sont approchées
par une même suite d'états, avec un seul triplet non minimal.

`DiffeomorphismHessianL2Form4D` assemble sur ce domaine la forme symétrique
réelle, conserve B♭, les signes des fantômes et les deux poids cinétiques
d'Einstein. Sur les états lisses, elle égale exactement la polarisation BRST
du fermion de jauge existant. Le terme auxiliaire symétrisé possède un
représentant de Riesz borné sur le L² original.

La fermeture prouvée concerne l'opérateur des quatre sorties différentielles.
Elle ne démontre pas encore que la forme indéfinie représente un opérateur
fermé/auto-adjoint sur tout le domaine requis. Restent cette réalisation et
ses domaines d'adjoints, H11, les égalités d'extensions abélienne/LL et le
raccord global D9. T12 reste ouvert ; Quillen et T08 sont préservés.

Validation : quatre gates, audit des 38 déclarations nommées et hub T12 verts
sous `run_lean_guarded`, un Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 3887, 3892, 4191, 4159 Mo ; audit 3822 Mo ; hub 4279 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance native
Stokes préexistante :
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`, `admit`, hypothèse terminale d'intertwiner ou
budget augmenté. `git diff --check` vert ; fichiers externes préservés.

### Hessien BRST : opérateur L² minimal fermé et symétrique

`P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D` explicite le transport
transposé des tests lisses. `HessianSmoothTestAdjoint4D` (même préfixe)
construit les représentants L² des pairings De Donder et Faddeev–Popov sur
tout le domaine différentiel commun, dans les coordonnées originales.

`HessianSmoothRiesz4D` assemble pour chaque état lisse un vecteur L² concret,
avec B, B♭, les adjoints différentiels, les deux poids d'Einstein et le
triplet partagé. Son pairing égale la forme assemblée sur tout le domaine
différentiel commun, et la polarisation BRST initiale sur les états lisses.
Il ne s'agit pas d'une existence de Riesz ajoutée comme hypothèse.

`HessianL2OperatorCore4D` prouve la linéarité de cette action et définit
l'opérateur sur l'image lisse dense du L² original. Les pairings contre
les tests lisses excluent une composante verticale dans la fermeture du
graphe, ce qui prouve directement sa fermabilité.
`HessianL2OperatorClosed4D` construit sa fermeture minimale : opérateur
fermé, densément défini, symétrique, avec véritable cœur lisse et action
lisse exacte. L'inclusion dans son adjoint est également établie pour la
fermeture, via le petit lemme abstrait `SymmetricL2Closure4D`.
Aucune préservation de la régularité lisse par les projections
hilbertiennes n'est supposée.

La réalisation minimale du Hessien de jauge fixé est donc construite.
L'égalité avec son adjoint n'est pas prouvée. Son domaine fermé n'est pas
identifié au domaine des quatre sorties différentielles : des compensations
entre termes pourraient les distinguer. Restent l'extension terminale et
ses domaines, les colonnes physiques H11, les égalités d'extensions
abélienne/LL et le raccord global D9. T12 reste ouvert ; Quillen et T08
sont préservés.

Validation : les six modules ci-dessus passent `run_lean_guarded`
(séquentiel, priorité haute, réserve 4096 Mo). Pics respectifs : 3694,
3908, 3905, 3915, 1805 Mo pour le lemme abstrait et 4040 Mo pour la
fermeture. Le hub T12 passe à 4009 Mo. L'audit des 39 déclarations publiques
passe à 3824 Mo : seulement `propext`, `Classical.choice`, `Quot.sound` et
l'axiome natif hérité de Stokes
`JanusFormal.P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit`, hypothèse terminale d'intertwiner,
ni hausse des budgets Lean. `git diff --check` passe.

### Hessien BRST : domaine maximal et opérateur de la forme

`P0EFTJanusProgramPT12DenseL2AdjointGraph4D` isole le critère de graphe
faible d'un adjoint réel densément défini. `HessianL2Adjoint4D` définit
le Hessien maximal comme adjoint du Hessien minimal déjà construit.
Son graphe est exactement décrit par les pairings avec les états lisses
et leur Hessien concret. Il est fermé, densément défini et contient
le minimal ; aucune égalité minimal/maximal n'est supposée.

`HessianFormGraphTests4D` prolonge les identités contre les tests lisses
à tous les tests du domaine différentiel commun, par continuité sur le
graphe des quatre sorties. `HessianFormAdjoint4D` en déduit, pour tout
état de ce domaine, l'équivalence entre appartenance au domaine maximal
et représentation L² de la forme BRST contre tous les tests différentiels.
Le représentant est exactement la valeur du Hessien maximal.

`HessianFormOperator4D` construit l'opérateur de représentation de la
forme : restriction du maximal à l'intersection de son domaine avec
le domaine différentiel commun. Cet opérateur est densément défini,
symétrique et fermable, conserve l'action lisse concrète, et son pairing
représente la forme complète, avec les deux poids et les signes BRST.
Sa fermeture et son éventuelle égalité avec le minimal ne sont pas
identifiées ici. L'auto-adjonction, les colonnes physiques H11,
les extensions abélienne/LL et le raccord global D9 restent ouverts.
T12 n'est pas coché ; Quillen et T08 sont préservés.

Validation : les cinq modules passent `run_lean_guarded`, séquentiellement,
priorité haute, réserve 4096 Mo. Pics : 1817 Mo (lemme d'adjoint),
4146 Mo (maximal), 4156 Mo (tests du graphe), 4102 Mo (forme/adjoint),
3942 Mo (opérateur de la forme). Audit des 26 déclarations : 3842 Mo ;
hub T12 : 4009 Mo. Axiomes : `propext`, `Classical.choice`, `Quot.sound`
et la dépendance native Stokes déjà documentée ci-dessus. Aucun nouvel
axiome, `sorry`/`admit`, hypothèse terminale d'intertwiner ou budget
augmenté. `git diff --check` passe.

### Fermeture de l'opérateur de la forme BRST

`P0EFTJanusProgramPT12HessianFormSmoothCore4D` identifie exactement la
restriction lisse de l'opérateur de la forme au cœur du Hessien déjà
construit. Sa fermeture redonne donc le Hessien minimal.

`HessianFormClosed4D` définit la fermeture de l'opérateur de la forme et
prouve qu'elle est fermée, densément définie et symétrique. Elle contient
le Hessien minimal et reste contenue dans le maximal. Son action lisse
et son pairing avec l'action BRST originale sont exacts. Le domaine de
l'opérateur de la forme est un cœur de cette nouvelle fermeture.
`SymmetricL2GraphClosure4D` fournit les lemmes généraux de fermeture ;
la preuve de symétrie reprend le lemme privé déjà utilisé pour LL.

`HessianFormClosedDomain4D` prouve que la restriction de cette fermeture
au domaine différentiel commun est exactement l'opérateur de la forme.
La fermeture n'ajoute donc aucun état dans ce domaine. Le critère de
représentation de la forme caractérise aussi ce domaine fermé restreint.
La restriction lisse demeure exactement le cœur initial ; avoir ce cœur
lisse comme cœur de la nouvelle fermeture équivaut à l'égalité avec le
Hessien minimal. Cette égalité et l'auto-adjonction ne sont pas affirmées.
Les colonnes H11, extensions abélienne/LL et raccord global D9 restent
à construire. T12 reste ouvert ; Quillen et T08 sont préservés.

Validation : quatre modules verts sous `run_lean_guarded`, un Lean à la
fois, priorité haute, réserve 4096 Mo. Pics : 1929 Mo (lemmes généraux),
3886 Mo (restriction lisse), 3926 Mo (fermeture), 4136 Mo (domaines).
Audit des 23 déclarations : 3824 Mo ; hub T12 : 4008 Mo. Dépendances
axiomatiques : `propext`, `Classical.choice`, `Quot.sound` et l'axiome
natif Stokes préexistant documenté ci-dessus. Aucun nouvel axiome,
`sorry`/`admit`, hypothèse terminale d'intertwiner ni budget augmenté.
`git diff --check` passe.

### Décomposition orthogonale du triplet BRST dans le L² original

`P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D` prouve les
pairings adjoints des transferts du triplet, l'idempotence des projections
et l'orthogonalité des trois composantes. `DiffeomorphismGhostProjection4D`
construit la projection orthogonale fantôme–antifantôme et son complément
métrique–multiplicateur. Son image est fermée et complète ; sa restriction
aux états lisses est explicitement identifiée aux transferts existants.

`DiffeomorphismGhostL2Core4D` construit l'image lisse dense dans ce vrai
sous-espace L² et prouve la décomposition exacte du produit scalaire et
de la norme au carré. Aucun changement du produit scalaire ni doublement
artificiel de l'espace total n'est utilisé.

Cette décomposition porte sur l'espace de Hilbert. La commutation du
Hessien avec ces projections et la réalisation du bloc FP pondéré avec
son domaine d'adjoint restent à établir avant d'appliquer les théorèmes
de blocs auto-adjoints existants. H11, les extensions abélienne/LL et le
raccord D9 restent ouverts. T12 reste non coché ; Quillen et T08 préservés.

Validation : trois gates, audit des 19 déclarations et hub T12 verts,
`run_lean_guarded`, séquentiel, priorité haute, réserve 4096 Mo. Pics :
3810 Mo (triplet), 3779 Mo (projection), 3765 Mo (cœur lisse), 3727 Mo
(audit), 4008 Mo (hub). Les 19 déclarations ne dépendent que de `propext`,
`Classical.choice` et `Quot.sound`. Aucun nouvel axiome, `sorry`/`admit`,
hypothèse terminale d'intertwiner ou budget augmenté. `git diff --check` OK.

### Réduction effective du Hessien par les projections fantômes

`P0EFTJanusProgramPT12HessianGhostSmooth4D` identifie la projection lisse :
les deux métriques et B disparaissent, tandis que FP et l'antifantôme sont
conservés. `HessianGhostCommutation4D` prouve la commutation de la forme
et du Hessien lisse concret avec la projection fantôme–antifantôme, pour
les deux poids cinétiques initiaux.

`HessianGhostMinimal4D` prolonge cette commutation au graphe fermé minimal,
avec appartenance au domaine projeté et valeur exacte de l'opérateur.
`HessianGhostMaximal4D` établit les mêmes propriétés pour l'adjoint maximal
par les tests lisses. Les projections complémentaires conservent aussi
ces graphes et le pairing Hessien fantôme–boson s'annule.

`HessianGhostReduced4D` construit un opérateur sur le véritable sous-espace
Hilbert fantôme–antifantôme : son graphe est exactement la restriction du
graphe minimal aux deux composantes dans ce sous-espace. Il est fermé,
densément défini et symétrique. L'image lisse projetée appartient à son
domaine ; sa sortie a exactement le pairing de l'action BRST initiale
restreinte aux fantômes. La structure hilbertienne est celle induite par
le L² original. Aucun espace auxiliaire doublé n'est identifié à l'espace
réel.

Restent la réalisation auto-adjointe du bloc FP pondéré et ses domaines,
le bloc métrique–B, les colonnes H11, les extensions abélienne/LL et le
raccord global D9. La commutation n'est pas encore établie ici pour la
fermeture intermédiaire de l'opérateur de la forme. T12 reste ouvert ;
Quillen et T08 sont préservés.

Validation : cinq gates, audit des 31 déclarations et hub T12 verts sous
`run_lean_guarded`, séquentiel, priorité haute, réserve 4096 Mo. Pics :
4130 Mo (projection lisse), 3894 Mo (commutation lisse), 3913 Mo (minimal),
3885 Mo (maximal), 4143 Mo (opérateur réduit), 3823 Mo (audit), 4007 Mo
(hub). Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance
native Stokes préexistante documentée ci-dessus. Aucun nouvel axiome,
`sorry`/`admit`, hypothèse terminale d'intertwiner ni budget augmenté.
`git diff --check` OK.

### Cœur opératoriel et adjoint du Hessien fantôme réduit

`P0EFTJanusProgramPT12HessianGhostReducedCore4D` prouve que le graphe
réduit est exactement la fermeture du graphe lisse projeté. L'image de
`diffeomorphismGhostPairSmooth` est donc un véritable cœur d'opérateur
(`HasCore`), au-delà de sa densité dans le Hilbert. La réalisation réduite
coïncide avec `closedFeatureOperator` pour cette inclusion et la sortie
Riesz projetée concrète.

`HessianGhostReducedAdjoint4D` caractérise son adjoint hilbertien par les
tests lisses initiaux. Son graphe est exactement la restriction du graphe
maximal complet aux deux composantes fantôme–antifantôme. Son domaine est
exactement l'intersection du domaine maximal avec ce sous-espace : aucune
condition supplémentaire sur la sortie n'est supposée, grâce à la
commutation déjà prouvée de la projection avec le graphe maximal.

Cela ne prouve pas l'égalité minimal = maximal ni l'auto-adjonction du
bloc FP pondéré. Restent cette réalisation, le bloc métrique–B, les
colonnes H11, les extensions abélienne/LL et le raccord global D9.
T12 reste ouvert ; Quillen et T08 sont préservés.

Validation : deux gates, audit des neuf déclarations et hub T12 verts
sous `run_lean_guarded`, séquentiel, priorité haute, réserve 4096 Mo.
Pics : 4170 Mo (cœur), 4027 Mo (adjoint), 3824 Mo (audit), 4009 Mo (hub).
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance
native Stokes préexistante documentée ci-dessus. Aucun nouvel axiome,
`sorry`/`admit`, hypothèse terminale d'intertwiner ni budget augmenté.
Les conversions coûteuses sont évitées par deux attributs locaux
`irreducible` et un petit lemme de prolongement des pairings à la fermeture.

### Colonne FP pondérée fermée et bloc auto-adjoint sur la paire réelle

`DiffeomorphismTripletComponent4D` construit les trois sous-espaces fermés
images des projections Eii dans le L² original, avec transferts isométriques
inverses Eij/Eji. `DiffeomorphismGhostPairIsometry4D` prouve l'isométrie
surjective (x,y) ↦ x + E10 y entre deux copies de la composante fantôme E00
et le véritable sous-espace fantôme–antifantôme. Il ne s'agit plus d'une
identification supposée avec un espace doublé.

`DiffeomorphismComponentSmooth4D` fournit les transferts lisses linéaires
et les inclusions denses dans chaque composante. `WeightedFPSmooth4D`
extrait du Riesz concret les colonnes A₀ = E01 R E00 et B₀ = E00 R E10,
avec la normalisation L² initiale. Leur pairing adjoint et le pairing
croisé de l'action BRST originale sont prouvés ; les poids cinétiques
plus/minus et les signes sont ceux du Riesz initial.

`WeightedFPClosed4D` construit A, fermeture minimale de A₀. Il est fermé,
densément défini, avec un vrai cœur lisse. Son adjoint hilbertien A*
est dense et vaut B₀ sur les champs lisses. `WeightedFPComponentBlock4D`
construit le bloc (x,y) ↦ (A*y,Ax), auto-adjoint de domaine exactement
D(A) × D(A*), avec son graphe lisse explicite.

`IsometricPMapAdjoint4D` prouve que le transport isométrique commute à
l'adjoint et préserve l'auto-adjonction, sans hypothèse de surjectivité
de l'opérateur. `WeightedFPBlock4D` transporte ainsi ce bloc sur la paire
fantôme réelle ; son auto-adjonction, son graphe transporté exact et son
graphe lisse sont validés.

Le raccord de ce bloc au Hessien fantôme réduit est établi ci-dessous.
L'égalité minimal = maximal n'est pas affirmée.
Restent aussi le bloc métrique–B, les colonnes H11, les extensions
abélienne/LL et le raccord global D9. T12 reste ouvert ; Quillen et T08
sont préservés.

Validation : huit gates, audit des 51 déclarations et hub T12 verts,
`run_lean_guarded`, séquentiel, priorité haute, réserve 4096 Mo.
Pics des validations réussies : 3781 Mo (composantes), 3774 Mo (isométrie),
3970 Mo (cœurs lisses), 3896 Mo (colonne pondérée), 4151 Mo (fermeture),
1885 Mo (transport adjoint abstrait), 4138 Mo (bloc en coordonnées),
4140 Mo (bloc réel), 3823 Mo (audit), 4009 Mo (hub).
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et dépendance
native Stokes préexistante. Aucun nouvel axiome, `sorry`/`admit`,
hypothèse terminale d'intertwiner ni budget augmenté.
Le bloc a été scindé après arrêt du garde mémoire ; les instances
hilbertiennes explicites et les attributs locaux `irreducible` évitent
les dépliages coûteux. `git diff --check` OK.

### Raccord du bloc FP au Hessien fantôme réel

`HessianGhostDiagonal4D` annule les deux colonnes diagonales du Hessien :
les pairings fantôme–fantôme et antifantôme–antifantôme sont nuls,
puis la densité lisse annule les projections E00 R E0j et E11 R E1j.

`WeightedFPActualCore4D` combine ces annulations avec la commutation
au projecteur fantôme. Les sorties R E0j et R E1j sont respectivement
antifantômes et fantômes. L'isométrie d'assemblage reconstitue alors
exactement l'entrée et le Riesz initiaux, pour tout champ du cœur
projeté. Le graphe lisse réel appartient au bloc FP auto-adjoint.

`WeightedFPExtension4D` passe à la fermeture de ce graphe et prouve :
Hessien fantôme minimal ≤ bloc FP réel auto-adjoint ≤ Hessien fantôme
maximal. Il s'agit d'inclusions d'opérateurs avec leurs domaines,
pas seulement d'une égalité de pairings. Aucun intertwiner supposé.

L'égalité minimal = maximal et le caractère de cœur lisse pour tout le
bloc auto-adjoint ne sont pas affirmés. Restent notamment le secteur
métrique–B, les colonnes H11, les extensions abélienne/LL, le quotient
LL auxiliaire/mesure et le certificat global D9. T12 reste ouvert.

Validation : trois gates, audit des 15 déclarations et hub T12 verts, sous
`run_lean_guarded`, un seul Lean, priorité haute, réserve 4096 Mo.
Pics : 3910 Mo (diagonales), 3912 Mo (raccord lisse), 3909 Mo
(extension), 3824 Mo (audit), 4011 Mo (hub). Axiomes : `propext`, `Classical.choice`,
`Quot.sound` et l'axiome natif Stokes préexistant
`canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté. Quillen et T08
préservés. Import du hub remplacé par la nouvelle gate terminale locale.

### Cœur réel métrique–B, adjoint et décomposition globale des graphes

`DiffeomorphismBosonL2Core4D` construit le sous-espace fermé image de
Q = id − P_fantôme dans le L² original, sa complétude et son inclusion
lisse dense. `HessianBosonReduced4D` restreint le Hessien minimal à cet
espace : opérateur fermé, symétrique et densément défini, avec graphe
lisse et pairing de l'action BRST originale. La commutation R Q = Q R
est prouvée sur les champs lisses.

`HessianBosonReducedCore4D` identifie son graphe à la fermeture du
graphe lisse projeté et établit un véritable cœur au sens opérateur.
`HessianBosonReducedAdjoint4D` caractérise l'adjoint par les tests lisses
et identifie exactement son graphe et son domaine à la restriction du
Hessien maximal original.

`HessianReducedGraphSplit4D` établit les deux équivalences de graphes :
le graphe complet minimal, respectivement maximal, se décompose en ses
restrictions fantôme et métrique–B. La reconstruction inverse est
prouvée par addition des deux graphes projetés.

`HessianBosonForm4D` donne la formule sectorielle exacte sur le cœur :
⟨D h, B k⟩ + ⟨B h, D k⟩ + ⟨M h, k⟩, où D est le de Donder original
et M l'opérateur continu `auxiliarySectorL2Riesz` déjà construit.
Les composantes FP et antifantôme projetées s'annulent ; de Donder,
B et B abaissé sont conservés. Les signes de la masse sont inchangés.

L'extension auto-adjointe du bloc métrique–B reste à construire à partir
de cette formule et de ses domaines réels. Ni auto-adjonction du minimal,
ni égalité minimal = maximal ne sont affirmées. Les colonnes H11,
les extensions abélienne/LL, le quotient LL auxiliaire/mesure et le
certificat global D9 restent ouverts. T12 n'est pas coché.

Validation : six gates vertes, `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo. Pics : 3971 Mo (sous-espace),
4148 Mo (restriction), 4171 Mo (cœur), 3920 Mo (adjoint),
4125 Mo (décomposition), 3906 Mo (formule). Le timeout initial de la
décomposition a été résolu par des projections localement `irreducible`
et des conversions explicites, sans augmenter les budgets.
Audit des 38 déclarations et hub T12 verts, pics respectifs 3825 et
4010 Mo. Axiomes : `propext`, `Classical.choice`, `Quot.sound` et
l'axiome Stokes natif préexistant
`canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou hypothèse terminale d'intertwiner.
`git diff --check` OK. Quillen, T08 et les fichiers externes préservés.

### Bloc rectangulaire et retrait exact de la masse métrique–B

`RectangularOffDiagonal4D` construit les graphes, domaines et fermetures
du bloc entre deux Hilbert distincts. `RectangularDoubleAdjoint4D`
étend la double adjonction aux opérateurs E → F fermés, avec domaines
denses de l'opérateur et de l'adjoint. `RectangularSelfAdjoint4D`
prouve l'auto-adjonction de (x,y) ↦ (A*y,Ax) sur D(A) × D(A*).
Les anciennes gates carrées sont conservées.

`BosonBoundedMass4D` construit M sur le véritable sous-espace métrique–B
par compression de la somme pondérée des `auxiliarySectorL2Riesz`.
M est continu et auto-adjoint. Son pairing sur le cœur projeté égale
le pairing de masse original, avec les poids cinétiques plus/minus
et les signes initiaux.

`BosonDeDonderCore4D` construit K = Hessien métrique–B minimal − M.
K est fermé, symétrique et densément défini ; son domaine et son cœur
lisse sont ceux du Hessien réduit. L'identité K + M = Hessien réduit
est prouvée comme égalité d'opérateurs partiels, domaines compris.
`BosonDeDonderPairing4D` identifie exactement son pairing lisse à la
somme pondérée des termes ⟨D h, B k⟩ + ⟨B h, D k⟩.

Prochaine construction concrète : extraire la colonne de Donder fermée
entre les composantes métrique et B réelles, identifier son adjoint lisse,
assembler et transporter le bloc rectangulaire, puis réintroduire M.
Le bloc abstrait ne constitue pas encore une extension auto-adjointe
du Hessien métrique–B réel. T12, H11 et le raccord global D9 restent ouverts.

Validation : six gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo. Pics : 2178 Mo (bloc rectangulaire),
2188 Mo (double adjonction), 2185 Mo (auto-adjonction), 4164 Mo (masse),
4168 Mo (retrait et restauration), 3895 Mo (pairing).
Les conversions d'instances et les lemmes de pairing ont été explicités
et scindés sans augmenter les budgets.
Audit des 33 déclarations et hub T12 verts, pics 3823 et 4010 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou hypothèse terminale d'intertwiner.
`git diff --check` OK. Quillen, T08 et les fichiers externes préservés.

### Extension auto-adjointe concrète du Hessien métrique–B

`DiffeomorphismMetricProjection4D` sépare la projection métrique C = Q − E₂₂
et la projection auxiliaire B = E₂₂ dans le sous-espace réel Q.
`MetricBAuxiliaryIsometry4D` reconstruit Q isométriquement par addition
des composantes métrique et B. `DiffeomorphismMetricSmooth4D` fournit
le cœur métrique dense et vérifie ses composantes physiques originales.

`WeightedDeDonderSmooth4D` extrait D₀ = B R C et sa transposée T₀ = C R B
du Riesz lisse réel, avec les poids et signes du BRST original.
`RectangularFeatureClosed4D` et `RectangularFeatureAdjoint4D` traitent
la fermeture et l'adjoint entre deux Hilbert distincts.
`WeightedDeDonderClosed4D` construit ainsi D fermé à domaine dense,
avec un véritable cœur lisse ; D* possède un domaine dense et agit
sur les tests B lisses par T₀.

`WeightedDeDonderComponentBlock4D` prouve l'auto-adjonction de
(x,y) ↦ (D*y,Dx) sur D(D) × D(D*). `WeightedDeDonderBlock4D` transporte
ce bloc dans le sous-espace métrique–B réel.
`WeightedDeDonderPairing4D` identifie son terme croisé au de Donder
original. `WeightedDeDonderActualCore4D` prouve que son action sur
le cœur projeté est exactement `bosonDeDonderSmoothOutput`.

`WeightedDeDonderExtension4D` rétablit la masse bornée originale M.
L'opérateur obtenu `weightedDeDonderBosonHessian` est auto-adjoint,
fermé et prolonge le Hessien métrique–B minimal ; il est contenu dans
son adjoint maximal. Son domaine est celui du bloc sans masse.
Ces inclusions ne supposent ni minimal = maximal, ni auto-adjonction
du minimal, ni intertwiner terminal.

La construction métrique–B annoncée dans la section précédente est
ainsi réalisée. Restent l'assemblage diffeomorphisme complet avec le
bloc fantôme, les colonnes physiques H11, les secteurs abélien/LL,
le quotient LL auxiliaire/mesure et le raccord/certificat global D9.
T12 reste ouvert ; Quillen, T08 et les modifications externes sont préservés.

Validation : douze gates vertes sous `run_lean_guarded`, un seul processus
Lean, priorité haute, réserve 4096 Mo ; pic maximal des passes vertes :
4153 Mo. Audit des 94 déclarations et hub T12 verts, pics 3832 et 4011 Mo.
La vérification du domaine, initialement trop coûteuse par dépliage,
utilise le lemme de perturbation et des instances explicites ; budgets inchangés.
Axiomes audités : `propext`, `Classical.choice`, `Quot.sound` et l'axiome
Stokes natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou intertwiner terminal supposé.
`git diff --check` OK.

### Assemblage du Hessien BRST difféomorphisme complet

`DiagonalProductPMap4D` construit la somme directe d'opérateurs partiels
sur deux Hilbert distincts, avec graphe et domaine produits exacts.
`DiagonalProductAdjoint4D` calcule son adjoint et prouve son auto-adjonction
lorsque les deux blocs sont auto-adjoints.

`GhostBosonIsometry4D` reconstruit le champ L2 complet à partir des
composantes fantôme et métrique–B. L'inverse est explicitement donné
par les projections orthogonales P et Q, sans choix de nouvelles coordonnées.
`DiffeomorphismHessianSum4D` assemble le bloc FP réel et le Hessien
métrique–B avec masse. `DiffeomorphismHessianRealization4D` transporte
leur somme auto-adjointe dans le Hilbert L2 complet ; son domaine est
caractérisé par l'appartenance des deux projections aux domaines des blocs.

`DiffeomorphismHessianExtension4D` établit les inclusions concrètes
Hessien minimal ≤ réalisation auto-adjointe ≤ Hessien maximal.
Sur le cœur lisse original, la réalisation agit exactement par
`hessianSmoothRiesz` et son pairing est l'action polarisée BRST originale.
Aucune égalité minimal = maximal ni hypothèse terminale d'intertwiner
n'est introduite.

L'assemblage fantôme/métrique–B annoncé précédemment est donc réalisé.
Le raccord des colonnes physiques H11 à cette réalisation L2, le raccord
abélien/LL, le quotient LL auxiliaire/mesure et le certificat global D9
restent à terminer. T12 reste ouvert ; Quillen et T08 sont préservés.

Validation : six gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo. Pics : 2178 Mo (somme directe),
2187 Mo (adjoint), 3771 Mo (isométrie), 4052 Mo (somme réelle),
3966 Mo (transport), 4136 Mo (raccord au cœur original).
Audit des 34 déclarations et hub T12 verts, pics 3826 et 4010 Mo.
Les conversions des isométries ont été rendues explicites sans augmenter
les budgets. Axiomes : `propext`, `Classical.choice`, `Quot.sound` et
l'axiome Stokes natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou intertwiner terminal supposé.
`git diff --check` OK ; fichiers externes préservés.

### Colonne complète BRST + H11 sur le cœur L2 difféomorphisme

`DiffeomorphismH11MetricDependence4D` établit que la colonne physique
complète dépend seulement de la perturbation métrique. Les transferts
purement métriques conservent donc toutes ses composantes de sortie.
`DiffeomorphismH11Smooth4D` expose cette colonne dans le Hilbert commun,
avec pairing physique, symétrie sur les relevés lisses et annulation
lorsque la perturbation métrique est nulle.

`InjectiveSmoothColumn4D` transporte une application linéaire par une
injection lisse, avec domaine, graphe et tests d'adjoint exacts.
`DiffeomorphismH11Core4D` réalise ainsi H11 comme opérateur partiel
densément défini du L2 réel vers le Hilbert commun complet.
`DiffeomorphismH11Adjoint4D` caractérise son adjoint fermé et son domaine
par les tests lisses originaux. La densité du domaine de cet adjoint,
et donc la fermabilité de la colonne H11 L2, restent à établir.
Aucune bornitude de H11 pour la norme L2 n'est supposée.

`DiffeomorphismGraphRieszBridge4D` étend le pairing du Hessien L2 à tous
les tests du graphe complété original. `DiffeomorphismCommonL2Column4D`
utilise l'adjoint de la lecture commune vers L2 pour reconstruire
exactement la colonne BRST originale dans le Hilbert commun.
`DiffeomorphismAugmentedL2Core4D` ajoute la colonne H11 entière : sur
chaque champ lisse original, cette somme égale, comme vecteur commun,
`strongAugmentedRiesz` appliqué au relevé original. Le terme BRST est
celui de la réalisation auto-adjointe L2 déjà construite.

Le raccord sur le cœur est donc concret et conserve les sorties H11
vers les autres secteurs. Il ne fournit pas encore une réalisation
fermée de la colonne physique complète ni l'intertwining global D9.
Le raccord abélien/LL, le quotient LL auxiliaire/mesure et le certificat
terminal restent ouverts ; T12 n'est pas coché. Quillen et T08 sont préservés.

Validation : huit gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pic maximal des passes vertes : 4263 Mo.
Audit des 44 déclarations et hub T12 verts, pics 3949 et 4011 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou intertwiner terminal supposé.
Budgets inchangés ; `git diff --check` OK.

### Adjoint H11 métrique et descente de la colonne L2 au quotient

`DiffeomorphismH11AdjointMetric4D` prouve que toute sortie de l'adjoint
H11 appartient au sous-espace métrique. Son graphe se caractérise
exactement par cette condition et les tests transférés métriques ;
les directions non métriques sont orthogonales à toutes ses sorties.

`DiffeomorphismAugmentedL2Quotient4D` construit la colonne partielle
à source L2 dense et à cible quotient commun fantômes/LL. Elle conserve
la réalisation BRST auto-adjointe et toute la colonne physique H11.
Sous les hypothèses déjà présentes de descente (`hZero`, `hMetric`,
`hWeights`), sa valeur égale celle de `jointGhostLLRiesz` sur la source
réduite originale. Deux représentants lisses de la même source réduite
donnent donc exactement le même vecteur cible.

`DiffeomorphismH11MetricBound4D` construit un représentant de Riesz
métrique par prolongement des tests scalaires H11. L'appartenance au
domaine de l'adjoint équivaut à l'existence, pour le test fixé, d'une
borne de ces tests scalaires par la seule norme L2 du champ métrique.
Lorsque cette borne est satisfaite, le représentant construit appartient
au graphe de l'adjoint complet. Toutes les composantes physiques de
sortie sont conservées dans le test scalaire.

Cette estimation n'est pas encore prouvée sur un ensemble dense de
tests communs : la fermabilité H11 reste ouverte. La descente construite
ne confond pas le LL littéral avec la fibre de Friedrichs et ne ferme
pas encore l'intertwining global D9. T12 reste ouvert ; Quillen, T08
et les fichiers externes sont préservés.

Validation : trois gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo. Pics des gates : 3985, 4004 et 4004 Mo.
Audit des 16 déclarations et hub T12 verts, pics 3949 et 4011 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou intertwiner terminal supposé.
Budgets inchangés ; `git diff --check` OK.

### Équation de graphe et adjoint H11 sur le quotient commun

`DiffeomorphismH11GraphBridge4D` identifie la colonne physique transposée
comme la lecture difféomorphisme du Riesz physique complet. Le graphe de
l'adjoint H11 se caractérise par l'équation exacte : l'adjoint de l'oubli
graphe→L2 appliqué à la sortie égale cette colonne transposée du test.
Son domaine, et la borne métrique précédente, correspondent exactement
à l'appartenance de cette colonne à l'image de l'adjoint de l'oubli.

`DiffeomorphismH11MatterLLTests4D` utilise l'annulation physique déjà
compilée pour inclure tout le secteur matière–LL complété dans le
domaine de l'adjoint, avec sortie nulle. Ajouter un tel test ne change
ni le graphe de l'adjoint ni la validité de la borne métrique.
Aucune nouvelle estimation ni hypothèse de flux nul n'est nécessaire.

`ClosedRangeEquation4D` construit un opérateur partiel fermé à partir
d'une équation entre deux applications continues, lorsque celle de
sortie est injective. Aucune fermeture de son image n'est supposée.
`DiffeomorphismH11QuotientAdjoint4D` applique cette construction à la
colonne transposée, descendue par le sous-espace nul commun fantômes/LL.
L'injectivité requise vient de la densité de l'oubli graphe→L2.
Le graphe et le domaine de cet opérateur quotient fermé se relèvent
exactement au graphe et au domaine de l'adjoint H11 original.
Cette descente physique ne requiert pas `hZero`, `hMetric` ou `hWeights`.

Il reste à prouver la densité du domaine de l'adjoint pour conclure à
la fermabilité H11 sur L2 : les tests métriques et Maxwell ne sont pas
couverts par l'annulation matière–LL. Le raccord global D9 et le
certificat terminal restent ouverts ; T12 n'est pas coché.
Quillen, T08 et les fichiers externes sont préservés.

Validation : quatre gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo. Pics : 4302 Mo (équation de graphe),
4281 Mo (tests matière–LL), 1928 Mo (construction générique),
4402 Mo (adjoint quotient). Audit des 29 déclarations et hub T12 verts,
pics 3944 et 4012 Mo. Axiomes des nouvelles déclarations : seulement
`propext`, `Classical.choice`, `Quot.sound`.
Les lemmes de translation évitent les timeouts par un calcul séparé,
sans augmenter les budgets. Aucun nouvel axiome, `sorry`/`admit` ou
intertwiner terminal supposé. `git diff --check` OK.

### Cœur H11 quotienté et identification de son véritable adjoint

`DiffeomorphismH11QuotientCore4D` construit le cœur physique de source
L2 réelle dense et de cible quotient commun. Son pairing avec toute
classe de test est exactement celui de H11 avant quotient. Les sorties
H11 sont orthogonales au sous-espace nul commun ; leur norme est donc
conservée exactement, sans supprimer de composante physique.

`DiffeomorphismH11QuotientDuality4D` prouve que l'adjoint de ce cœur est
précisément l'opérateur fermé `diffeomorphismH11QuotientAdjoint` construit
précédemment. L'égalité porte sur les opérateurs partiels complets et
leurs domaines ; elle fournit aussi le pairing contre tout élément du
domaine de l'adjoint quotienté. Aucune densité de ce dernier domaine
n'est supposée.

Le raccord cœur réel–adjoint quotienté est établi. Les estimations sur
les tests métriques et Maxwell, nécessaires à la densité du domaine de
l'adjoint et à la fermabilité H11, restent à prouver. Le certificat
global D9 n'est pas encore construit ; T12 reste ouvert.
Quillen, T08 et les fichiers externes sont préservés.

Validation : deux gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3984 et 3997 Mo.
Audit des 13 déclarations et hub T12 verts, pics 3942 et 4013 Mo.
Axiomes : seulement `propext`, `Classical.choice`, `Quot.sound`.
La réécriture de l'adjoint porte sur son graphe pour préserver les
arguments de domaine dépendants. Aucun budget augmenté, nouvel axiome,
`sorry`/`admit` ou intertwiner terminal supposé. `git diff --check` OK.

### Covecteurs métriques L2 et première variation Maxwell induite

`RegularTensorCovectorL24D` réalise les covecteurs lisses exprimés dans
le repère métrique comme vecteurs du L2 tensoriel réel. Le transport
adjoint conserve exactement le pairing intégral et fournit une borne
par la norme L2, sans dérivée de la variation test.

`InducedMaxwellMetricL24D` applique cette construction au résidu Maxwell
induit par la mobilité du repère métrique. Son pairing est exactement
le terme `fderiv` natif déjà calculé. Il définit donc un covecteur continu
sur le L2 tensoriel réel, sans hypothèse de stationnarité Maxwell.

`PairedInducedMaxwellL24D` lit les deux composantes métriques du L2 réel
difféomorphisme, compose ces covecteurs et incorpore leurs poids. La
somme des deux variations induites possède ainsi une borne dans cette
norme L2 réelle. La métrique de normalisation du L2 peut être distincte
des deux métriques physiques de base.

Cette étape concerne uniquement la première variation Maxwell induite.
Elle ne borne pas encore les termes complets stress/volume, ni les
secondes variations métriques et Maxwell de H11. La densité du domaine
de l'adjoint, la fermabilité H11 et le certificat global D9 restent
ouverts ; T12 n'est pas coché. Quillen, T08 et les fichiers externes
sont préservés.

Validation : trois gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3873, 3865 et 3873 Mo.
Audit des 17 déclarations et hub T12 verts, pics 3843 et 4014 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit`, hypothèse d'intertwiner terminal
ou budget augmenté. `git diff --check` OK.

### Première variation Maxwell métrique complète dans le L2 réel

`MaxwellStressCoefficients4D` relève les deux indices du stress Maxwell
par l'inverse de la métrique et prouve son pairing exact avec les
composantes du tenseur test. La contraction inverse du terme de trace
fournit aussi la correction positive de volume. Leur combinaison est
exactement le résidu à volume fixé ; aucun terme physique n'est omis.

`FullMaxwellMetricL24D` construit son représentant dans le L2 tensoriel
réel, puis l'ajoute au représentant du terme induit. Le pairing obtenu
égale le `fderiv` natif complet de l'action Maxwell à repère mobile et
volume fixé. La borne L2 est inconditionnelle, sans stationnarité.

`PairedFullMaxwellL24D` transporte ce covecteur complet vers le L2 réel
difféomorphisme, pour les deux feuillets et leurs poids. Il réutilise
les lectures métriques déjà établies et conserve l'égalité avec la
somme pondérée des dérivées natives.

La première variation Maxwell métrique complète est donc couverte.
Les estimations de seconde variation nécessaires à la densité du
domaine de l'adjoint et à la fermabilité H11 restent à établir, ainsi
que le raccord global D9. T12 reste ouvert. Quillen, T08 et les fichiers
externes sont préservés.

Validation : trois gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3889, 3896 et 3879 Mo.
Audit des 18 déclarations et hub T12 verts, pics 3839 et 4015 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit`, hypothèse d'intertwiner terminal
ou budget augmenté. `git diff --check` OK.

### Variation mixte Maxwell potentiel–métrique et borne L2

`MaxwellCoefficientQuadratic4D` réalise le pairing puis l'action Maxwell
comme applications quadratiques sur le cœur C2 des coefficients de jauge.
Le transport du repère mobile est linéaire en ce paquet : l'action native
transportée reste donc exactement quadratique, pour chaque variation
métrique. L'égalité conserve les coefficients de Cartan et l'anholonomie.

`QuadraticParameterDerivative4D` prouve qu'une dérivée de paramètre de
cette famille possède une dérivée le long de toute droite du potentiel.
Sa valeur est la polarisation : valeur en A+B moins valeur en A moins
valeur en B. Les différentiabilités requises concernent ces trois points.

`MaxwellMixedMetricL24D` les établit pour l'action native au centre de la
carte métrique, à partir de sa régularité C2 déjà démontrée. La dérivée
en potentiel de la première variation métrique complète est exactement
le pairing avec la polarisation de trois représentants L2 existants.
C'est une véritable dérivée itérée, sans hypothèse de stationnarité ni
hypothèse de borne. Son test métrique ne requiert que la norme L2 réelle.

`PairedMaxwellMixedL24D` construit le covecteur pondéré des deux feuillets
et la même borne sur le L2 réel difféomorphisme.

Cette estimation couvre le terme mixte Maxwell potentiel–métrique.
Le raccord au test scalaire H11 complet et les estimations du bloc
métrique–métrique restent à établir, avant la densité du domaine de
l'adjoint, la fermabilité et le certificat global D9. T12 reste ouvert.
Quillen, T08 et les fichiers externes sont préservés.

Validation : quatre gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3880, 1848, 4110 et 3884 Mo.
Audit des 21 déclarations et hub T12 verts, pics 3838 et 4098 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
La forme quadratique reste localement opaque dans la preuve de dérivation
pour éviter les timeouts de réduction. Aucun budget augmenté, nouvel
axiome, `sorry`/`admit` ou intertwiner terminal supposé.
`git diff --check` OK.

### Hessien natif Maxwell et norme métrique du critère H11

`MixedPartialHessian4D` identifie la dérivée en jauge de la dérivée
partielle métrique à l'entrée correspondante du Hessien joint véritable.
La preuve applique les règles de chaîne et d'évaluation des applications
linéaires continues, sans permuter formellement deux dérivations.

`MaxwellNativeMixedHessian4D` définit le second `fderiv` de l'action
Maxwell native à repère mobile sur le cœur joint métrique–jauge. Sa
régularité C2 au centre est établie pour tout paquet de coefficients.
La symétrie du Hessien identifie alors les deux ordres métrique–jauge
et jauge–métrique au représentant L2 précédemment construit. Aucune
stationnarité ni hypothèse de borne n'est introduite.

`PairedMaxwellNativeHessian4D` réalise les sommes natives pondérées des
deux feuillets par le covecteur L2 existant, dans les deux ordres. La
borne vaut aussi dans la seule norme `diffeomorphismMetricSmooth`, en
utilisant le transfert métrique qui conserve exactement les tenseurs
et supprime les composantes non métriques. C'est la norme du critère
analytique de domaine de l'adjoint H11.

Le bloc mixte Maxwell est ainsi raccordé au Hessien natif, mais pas
encore au test scalaire H11 de l'action physique totale. Ce raccord,
les estimations métrique–métrique, la densité du domaine de l'adjoint,
la fermabilité et le certificat global D9 restent ouverts. T12 n'est
pas coché ; Quillen, T08 et les fichiers externes sont préservés.

Validation : trois gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1797, 4153 et 4149 Mo.
Audit des 15 déclarations et hub T12 verts, pics 3820 et 4271 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit`, hypothèse d'intertwiner terminal
ou budget augmenté. `git diff --check` OK.
### Transport exact des Hessiennes Maxwell sur le cœur apparié

`AffineHessianPullback4D` prouve la règle de chaîne du second `fderiv`
pour une action C2 composée avec une projection linéaire continue,
une translation de fond et un facteur réel.

`PairedMaxwellHessianPullback4D` construit les projections métrique–jauge
plus et moins du cœur apparié. Les actions Maxwell effectivement utilisées
sont exactement les actions natives translatées par leurs coefficients
de fond. La reconstruction du potentiel restitue ces mêmes coefficients.
Les deux Hessiennes pondérées au centre sont donc les Hessiennes natives
appliquées aux deux directions projetées, pour des directions arbitraires.
Aucune hypothèse de stationnarité, de borne ou d'intertwiner n'est ajoutée.

Ce raccord atteint les blocs Maxwell sur le cœur métrique–jauge apparié.
Le passage à la dérivée forte et au test scalaire H11 de l'action physique
totale reste à établir, ainsi que les estimations métrique–métrique,
la densité du domaine de l'adjoint, la fermabilité et le certificat global
D9. T12 reste ouvert ; Quillen, T08 et les fichiers externes sont préservés.

Validation : deux gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1797 et 4170 Mo. Audit des dix
déclarations et hub T12 verts, pics 3851 et 4243 Mo. Ces dix déclarations
ne dépendent que de `propext`, `Classical.choice`, `Quot.sound`.
Les égalités d'actions sont transportées par congruence explicite pour
éviter le timeout de réécriture du Hessien ; aucun budget augmenté.
Aucun nouvel axiome, `sorry`/`admit` ou hypothèse terminale.
`git diff --check` OK.
### Hessiennes des blocs Maxwell dans la véritable topologie forte

`ProjectedGradientDerivative4D` différentie le gradient tiré en arrière
par une projection linéaire continue. `PairedMaxwellCenterC24D` établit
la régularité C2 au centre des deux actions Maxwell appariées pondérées,
à partir de leur identification affine avec l'action native.

`StrongMaxwellHessianPullback4D` applique cette dérivation aux deux
gradients Maxwell forts effectivement utilisés : leur second jet est
le Hessien natif pondéré, évalué sur les deux directions projetées par
`globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM`, puis par
la projection métrique–jauge propre au feuillet.

`StrongMaxwellActionHessian4D` raccorde ces expressions aux Hessiennes
des blocs `maxwellPlus` et `maxwellMinus` de l'action physique admissible.
L'ouverture du domaine fort et son appartenance au centre donnent
l'égalité des gradients sur un voisinage, donc l'égalité de leurs
secondes dérivées. Seule la compatibilité géométrique de base déjà
requise pour ces blocs est utilisée ; aucune hypothèse d'intertwiner,
de stationnarité ou de borne n'est ajoutée.

Il reste à identifier les projections des directions H11 concrètes,
à réunir les contributions de l'action physique totale et les bornes
métrique–métrique, puis à établir la densité du domaine de l'adjoint,
la fermabilité et le certificat global D9. T12 reste ouvert.
Quillen, T08 et les fichiers externes sont préservés.

Validation : quatre gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1762, 4110, 4164 et 4149 Mo.
Audit des neuf théorèmes et hub T12 verts, pics 3823 et 4117 Mo.
Les neuf théorèmes ne dépendent que de `propext`, `Classical.choice`,
`Quot.sound`. Aucun nouvel axiome, `sorry`/`admit`, hypothèse terminale
ou budget augmenté. `git diff --check` OK.
### Couplage Maxwell des directions BRST concrètes et borne métrique L2

`MaxwellPhysicalCoreProjection4D` calcule les projections Maxwell des
directions physiques minimales, du cœur diagonal global et de ses
inclusions difféomorphisme et abélienne. La première fournit exactement
le tenseur métrique et une jauge nulle ; la seconde fournit une métrique
nulle et les coefficients du potentiel dans le repère physique de `data`.

`StrongMaxwellBRSTMixedHessian4D` conserve ce repère sans l'identifier
implicitement à la base Maxwell : `maxwellGaugeRebase` reconstruit le
potentiel dans la base choisie en préservant exactement ses coefficients
C2. Les deux Hessiennes mixtes des blocs d'action forts, évaluées sur
ces inclusions BRST concrètes, sont les entrées natives métrique–jauge
avec ce transport de repère.

`StrongMaxwellBRSTMixedL24D` représente leur somme par un covecteur du
L2 réel difféomorphisme. Sa norme borne cette contribution Maxwell dans
la seule norme `diffeomorphismMetricSmooth`, celle du critère de domaine
de l'adjoint H11. La compatibilité de base est conservée ; aucune
hypothèse de borne, de stationnarité ou d'intertwiner n'est ajoutée.

Cette borne porte sur la contribution Maxwell mixte concrète. Le H11
de l'action physique totale, les estimations métrique–métrique, la densité
du domaine de l'adjoint, la fermabilité et le certificat global D9 restent
à établir. T12 reste ouvert ; Quillen, T08 et les fichiers externes sont
préservés.

Validation : trois gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 4243, 4235 et 3997 Mo.
Audit des 17 déclarations et hub T12 verts, pics 3919 et 4021 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound`, et uniquement pour
les trois déclarations L2 l'axiome Stokes natif préexistant
`canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit`, hypothèse terminale ou budget augmenté.
`git diff --check` OK.
### Tests abéliens dans le domaine de l'adjoint H11 difféomorphisme

`PhysicalGaugeHessianReduction4D` transporte une égalité locale de gradients
évalués sur un test fixe vers leurs Hessiennes. L'évaluation d'une dérivée
à valeurs dans les applications linéaires continues est différentiée
explicitement ; aucune permutation formelle de dérivations n'est utilisée.

`StrongPhysicalGaugeGradient4D` identifie le tangent physique du cœur
abélien à la direction de jauge pure déjà construite. Les annulations
existantes de Candidate-A, Robin, Einstein–Hilbert plus et moins, et BV
réduisent le gradient physique total testé aux deux gradients Maxwell,
sur tout le domaine admissible fort.

`StrongPhysicalBRSTMixedHessian4D` différentie cette identité autour du
centre, en utilisant la régularité C2 des neuf blocs et l'ouverture du
domaine. Le Hessien physique total sur une direction difféomorphisme et
un test abélien coïncide exactement avec la somme Maxwell déjà bornée.
Il possède donc le même covecteur L2 et la même borne métrique.

`DiffeomorphismH11AbelianTests4D` raccorde ce calcul au H11 complet de
l'extension physique commune déjà fixée, par son accord sur le cœur
lisse et le pont fort concret. Pour tout état BRST abélien lisse,
son plongement physique dans le Hilbert commun satisfait le critère
`diffeomorphismH11MetricTestBound` et appartient au domaine de
`diffeomorphismH11Adjoint`. La borne est construite, non postulée.

Le traitement des tests métriques et la densité du domaine de l'adjoint
restent nécessaires avant la fermabilité et le certificat global D9.
T12 reste ouvert. Aucun intertwiner terminal n'est supposé ; Quillen,
T08 et les fichiers externes sont préservés.

Validation : quatre gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3753, 3976, 3974 et 3995 Mo.
Audit des 14 déclarations et hub T12 verts, pics 3858 et 4022 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et l'axiome Stokes
natif préexistant `canonicalFlowIndex_card._native.native_decide.ax_1_1`
pour les résultats utilisant la borne L2. Aucun nouvel axiome,
`sorry`/`admit` ou budget augmenté. `git diff --check` OK.
## Préparation des tests métriques : gravité native dans L2 (23 septembre 2026)

`RaisedTensorCovectorL24D` relève les deux indices de coefficients lisses
arbitraires, puis représente leur pairing invariant dans les coordonnées
L2 tensorielles physiques. L'égalité et la borne sont démontrées.

`StoredVolumeEinsteinHilbertL24D` construit séparément les représentants
L2 du Ricci pondéré par le volume stocké et du terme de Palatini complet.
La somme représente exactement la première variation native d'Einstein–Hilbert
à volume fixé. Aucune hypothèse de jauge de volume ni de stationnarité
n'est ajoutée ; le terme de Palatini n'est pas éliminé.

`PairedEinsteinHilbertL24D` assemble les deux secteurs en un covecteur
continu sur le L2 BRST difféomorphisme et prouve une borne utilisant
uniquement la norme métrique. `StrongEinsteinHilbertL24D` raccorde ce
covecteur à la somme des deux dérivées gravitationnelles fortes au centre,
évaluées sur la direction métrique physique.

Cette étape concerne la première variation. Elle ne prouve pas encore
la borne du Hessien métrique complet ni l'appartenance des tests métriques
au domaine de l'adjoint H11. Leur traitement, la densité du domaine de
l'adjoint et le certificat global actual→D9 restent nécessaires. T12 reste
ouvert ; aucun intertwiner terminal n'est supposé.
Validation : quatre gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3892, 3941, 4062 et 3901 Mo.
Audit des 24 déclarations et hub T12 verts, pics 3848 et 4025 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et, pour Palatini
et ses consommateurs, l'axiome Stokes natif préexistant
`canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ou budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## Hessien gravitationnel fort sur le cœur BRST (23 septembre 2026)

`NativeEinsteinHilbertHessian4D` définit la seconde dérivée de l'action
native à volume fixé, prouve sa symétrie par la régularité C2 existante,
et identifie les deux Hessiens appariés par leurs projections métriques
continues. Aucune hypothèse de représentation du Hessien n'est ajoutée.

`StrongEinsteinHessianPullback4D` différentie les gradients gravitationnels
forts effectivement définis. `StrongEinsteinActionHessian4D` utilise leur
accord avec les gradients des blocs admissibles sur un voisinage ouvert
du centre pour identifier les Hessiens des véritables blocs d'action.

`StrongEinsteinBRSTHessian4D` spécialise ces égalités à deux états BRST
difféomorphisme lisses plongés dans le tangent physique. Pour chaque
secteur, le résultat est exactement le Hessien natif sur les deux
perturbations métriques correspondantes, avec le couplage physique.

Il reste à représenter ces entrées de seconde variation par des covecteurs
L2 pour les tests métriques fixés, puis à traiter les autres blocs du
Hessien métrique complet. La borne de première variation du gate précédent
n'est pas utilisée comme borne de seconde variation. La densité du domaine
adjoint H11 et le certificat global actual→D9 restent ouverts ; T12 n'est
pas coché.
Validation : quatre gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 4170, 4154, 4163 et 4239 Mo.
Audit des 21 déclarations et hub T12 verts, pics 3752 et 4022 Mo.
Les 21 déclarations ne dépendent que de `propext`, `Classical.choice`
et `Quot.sound`. Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## Covecteurs L2 des jets métriques d'ordre deux (24 septembre 2026)

`RegularFrameSecondJetAdjoint4D` prouve l'intégration par parties ordonnée
contre la mesure canonique. Le terme `c X_outer(X_inner h)` devient
`(X_inner* (X_outer* c)) h` ; les champs du repère ne sont pas supposés
commuter. Les termes d'ordre zéro, un et deux sont assemblés en un
coefficient adjoint lisse explicite, sans jauge de volume.

`TensorSecondJetL24D` applique cette formule aux seize coefficients du
tenseur dans le repère régulier. Il construit le vecteur de Riesz dans
le L2 tensoriel physique, prouve son pairing exact avec l'expression de
jets et la borne en norme L2 du tenseur variable.

`PairedTensorSecondJetL24D` assemble les deux secteurs et transporte leur
covecteur dans le L2 BRST difféomorphisme. La borne finale ne dépend que
de la norme métrique, donc a la forme requise pour les tests H11.

Les coefficients d'ordre zéro, un et deux sont des données lisses
arbitraires dans ces résultats. Aucun accord avec le Hessien natif n'est
supposé ni annoncé : la prochaine étape est d'extraire ses coefficients
pour un test métrique lisse fixé et de prouver l'égalité avec
`tensorSecondJetFunctional`. La borne du Hessien complet, la densité du
domaine adjoint H11 et le certificat global actual→D9 restent ouverts.
T12 n'est pas coché ; aucun intertwiner terminal n'est supposé.
Validation : trois gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3868, 4113 et 3875 Mo.
Audit des 15 déclarations et hub T12 verts, pics 3845 et 4022 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et, pour les résultats
utilisant les adjoints de Stokes, l'axiome natif préexistant
`canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## Factorisation exacte du Hessien natif par les jets (24 septembre 2026)

`CurvatureJetSymbol4D` expose les formules finies de Koszul, de dérivée
de connexion, de Riemann, de Ricci et de courbure scalaire. Elles sont
C∞ dans les quatre blocs : valeur métrique, inverse métrique, premier
jet, second jet ordonné. L'inverse est un argument indépendant de cette
formule polynomiale ; il n'est pas supposé indépendant dans l'action.

`NativeCurvatureJetBridge4D` identifie chaque formule à l'implémentation
C0 native, point par point, avec les véritables coefficients d'anholonomie
et leurs dérivées. L'accord scalaire ne requiert pas d'hypothèse ajoutée.

`NonlinearHessianPullback4D` conserve les deux termes de la règle de
chaîne d'ordre deux : Hessien extérieur sur les deux vitesses du jet,
et gradient extérieur appliqué à l'accélération du jet.
`NativeCurvatureJetHessian4D` prouve la régularité du jet natif au centre
et applique cette règle à la vraie courbure scalaire.

`EinsteinJetHessianIntegral4D` ajoute le volume stocké et les couplages,
puis identifie exactement `nativeEinsteinHilbertHessian` à l'intégrale
de cette expression finie. Le passage de la dérivée seconde sous
l'intégration utilise l'application linéaire continue C0 déjà construite.
Ni jauge de volume, ni stationnarité, ni suppression de l'accélération
du jet ne sont postulées.

Il reste à expliciter les vitesses et accélérations de ces blocs,
notamment la variation seconde de l'inverse métrique, et à convertir
l'expression intégrée en coefficients lisses de `tensorSecondJetFunctional`
pour un test fixé. Les bornes L2 génériques précédentes pourront alors
s'appliquer. Le Hessien métrique complet, la densité du domaine adjoint
H11 et le certificat global actual→D9 restent ouverts. T12 reste non coché.
Validation : cinq gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1790, 3880, 1789, 4144 et 4147 Mo.
Audit des 43 déclarations et hub T12 verts, pics 3660 et 4020 Mo.
Les déclarations ne dépendent que de `propext`, `Classical.choice`
et `Quot.sound`. Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## 2026-09-24 — Accélération native de l'inverse et des jets métriques

`C2InverseHessian4D` calcule la dérivée seconde de l'inversion dans
l'algèbre C², sur son ouvert d'inversibilité. Au centre identité elle
vaut `K H + H K` : les deux ordres non commutatifs sont conservés.
`VectorHessianPullback4D` transporte les Hessiennes vectorielles par
entrée affine et sortie linéaire continue.

`NativeInverseMetricHessian4D` applique ces résultats à l'inverse
relatif puis à l'inverse métrique effectivement utilisés par l'action.
`InverseMetricHessianPointwise4D` donne l'évaluation ponctuelle, sa
spécialisation aux directions covariantes lisses et chaque coefficient
scalaire. On obtient exactement
`g⁻¹ k g⁻¹ h g⁻¹ + g⁻¹ h g⁻¹ k g⁻¹`, sans hypothèse d'accord ajoutée.

`MetricJetAcceleration4D` prouve que les Hessiennes paramétriques C0
du coefficient métrique, de son premier jet et de son second jet ordonné
sont nulles. Les opérateurs de dérivée spatiale sont réalisés comme
applications linéaires continues avant d'utiliser l'affinité du cœur C².
Ces annulations ne s'appliquent pas au bloc inverse, dont l'accélération
est celle calculée ci-dessus.

Prochaine étape : assembler ces résultats avec les vitesses lisses déjà
présentes dans le jet de courbure natif, puis extraire les coefficients
lisses de `tensorSecondJetFunctional` pour un test fixé. La borne L2 du
Hessien Einstein, le secteur métrique du domaine adjoint H11, sa densité
et le certificat global actual→D9 restent ouverts. T12 reste non coché.

Validation : cinq gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3902, 1796, 4125, 4135 et 4135 Mo.
Audit des 12 théorèmes et hub T12 verts, pics 3634 et 4020 Mo.
Axiomes : uniquement `propext`, `Classical.choice`, `Quot.sound`.
Aucun `sorry`/`admit`, nouvel axiome ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## 2026-09-24 — Coefficients concrets du Hessien Einstein natif

`CurvatureJetDifferentials4D` assemble les dérivées première et seconde
du jet fini à partir de ses coordonnées, par lectures linéaires continues.
`NativeCurvatureJetAcceleration4D` identifie l'accélération complète du
jet natif : seuls les coefficients inverses contribuent, avec les deux
ordres matriciels déjà prouvés. `NativeCurvatureJetVelocity4D` identifie
sa vitesse sur toute direction covariante lisse : valeur, inverse,
première dérivée et seconde dérivée spatiale ordonnée.

`MetricJetCovector4D` décompose un jet de variation en bases finies et
extrait exactement les trois familles de coefficients d'une forme
linéaire. `MetricJetLinearization4D` réalise comme applications linéaires
continues la vitesse du jet et son accélération mixte, pour un premier
test fixé. La forme obtenue conserve le gradient extérieur appliqué à
l'accélération de l'inverse ; ce terme n'est pas supprimé.

`NativeEinsteinJetCoefficients4D` construit alors les coefficients réels
`nativeEinsteinJetValueCoefficient`, `nativeEinsteinJetFirstCoefficient`
et `nativeEinsteinJetSecondCoefficient`. Leur combinaison avec la valeur,
le premier jet et le second jet du test est exactement la densité du
Hessien natif. `nativeEinsteinHilbertHessian_eq_coefficientsIntegral`
identifie le vrai Hessien Einstein à l'intégrale de cette combinaison,
sans hypothèse d'accord, de stationnarité ou de jauge de volume ajoutée.

Les coefficients sont maintenant construits et leur accord avec le
Hessien est prouvé. Leur régularité spatiale reste à formaliser : les
fonctions nommées `smooth...` ci-dessus désignent les formules sur des
directions lisses, sans ajouter par leur nom un théorème de régularité.
Il faut encore réaliser ces coefficients comme champs scalaires lisses,
les raccorder à `tensorSecondJetFunctional`, puis appliquer la borne L2.
Le secteur métrique du domaine adjoint H11, sa densité et le certificat
global actual→D9 restent ouverts. T12 reste non coché.

Validation : six gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1789, 4159, 3895, 1791, 1894 et
4133 Mo. Audit des 33 déclarations et hub T12 verts, pics 3857 et 4020 Mo.
Axiomes : uniquement `propext`, `Classical.choice`, `Quot.sound`.
Aucun `sorry`/`admit`, nouvel axiome ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## 2026-09-24 — Régularité et borne L2 du Hessien Einstein BRST concret

`CurvatureJetJointSmooth4D` établit la régularité conjointe du symbole de
courbure dans le jet métrique, les coefficients du repère et leurs dérivées.
`EinsteinSymbolJointSmooth4D` donne celle du symbole Einstein, de son
gradient partiel et de son Hessien partiel en conservant les paramètres.
`NativeJetSpatialSmooth4D` prouve la régularité spatiale du vrai jet au
centre, de l'inverse, du repère et des jets covariants de variation.
`MetricJetLinearizationSmooth4D` traite la vitesse et l'accélération mixte.

`NativeEinsteinCoefficientFields4D` compose ces résultats et réalise les
trois familles de coefficients déjà identifiées comme de véritables
champs scalaires lisses. Aucune régularité de coefficient n'est postulée.

`NativeEinsteinHessianL24D` raccorde exactement le Hessien natif à
`tensorSecondJetFunctional`. L'intégration par parties existante produit
`nativeEinsteinHessianL2` et son identité de pairing, puis la borne par
la norme L2 du tenseur test. Il s'agit bien de la dérivée seconde de
l'action, avec le terme d'accélération de l'inverse et le volume stocké.

`PairedEinsteinHessianL24D` rassemble les deux secteurs dans un covecteur
sur l'espace L2 BRST réel. Sa borne ne dépend que de la norme métrique
du test. `StrongEinsteinBRSTL24D` identifie ce covecteur à la somme des
Hessiennes des deux blocs Einstein réels sur les inclusions BRST lisses.
`strongEinsteinBRSTHessian_metric_bound` donne la borne métrique de cette
somme pour chaque premier champ BRST lisse fixé.

Le contrôle L2 gravitationnel est donc établi. Restent l'assemblage des
blocs physiques pour la borne métrique totale, le domaine adjoint H11
métrique et sa densité, puis le certificat global actual→D9. Ces résultats
ne ferment pas à eux seuls T12, qui reste non coché. Quillen n'est pas refait.

Validation : huit gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1788, 1795, 3876, 1889, 3895,
4142, 4140 et 3965 Mo. Audit des 44 déclarations et hub T12 verts, pics
3899 et 4019 Mo. Axiomes standards `propext`, `Classical.choice`, `Quot.sound` ;
les réalisations L2 et leurs conséquences réutilisent seulement l'axiome
natif de Stokes déjà présent
`P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; T08 et les fichiers externes préservés.
## 2026-09-24 — Accélération du transport Maxwell et Hessien BRST métrique

`BilinearHessian4D` prouve les quatre termes de la dérivée seconde
bilinéaire. `C2RootHessian4D` différentie l'identité réelle de la branche
racine C² : au centre, son Hessien vaut `-(1/8) • (HK + KH)`.
Les deux ordres matriciels sont conservés, sans commutation supposée.

`MobileGaugeTransportHessian4D` transporte cette accélération au paquet
de jauge fixe, puis au cœur métrique complété natif. `GraphHessian4D`
isole le calcul des dérivées d'une carte graphe ; `MobileMetricChartHessian4D`
l'applique à la vraie carte `(variation, transport variation coefficients)`.
Sa vitesse est `(h, (1/2) Hᵀa)` et son accélération n'a qu'une composante
jauge, donnée par la racine précédente.

`MaxwellMetricHessianTransport4D` identifie exactement l'entrée
métrique–métrique du Hessien mobile natif avec le Hessien à repère fixe
sur les deux vitesses transportées, plus le gradient à repère fixe
appliqué à l'accélération. Ce dernier terme n'est pas supprimé ; aucune
stationnarité du fond n'est postulée.

`StrongMaxwellBRSTMetricHessian4D` raccorde cette formule aux deux blocs
Maxwell réels sur les inclusions BRST difféomorphes, avec leurs facteurs
de couplage respectifs. Il ne s'agit pas d'une hypothèse d'accord ajoutée.

Il reste à réaliser cette formule Maxwell comme covecteur L2 métrique,
puis à assembler les blocs physiques restants pour H11 métrique,
établir la densité du domaine adjoint et le certificat global actual→D9.
La présente étape établit le Hessien et son transport, pas encore sa
borne L2 métrique. T12 reste non coché ; Quillen n'est pas refait.
Validation : sept gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1790, 3896, 4135, 1790, 4130,
4152 et 4231 Mo. Audit des 21 déclarations et hub T12 verts, pics
3914 et 4023 Mo. Axiomes : uniquement `propext`, `Classical.choice`,
`Quot.sound`. Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.
## 2026-09-24 — Jet Maxwell natif explicite et identité intégrale du Hessien

`MaxwellJetSymbol4D` construit le symbole fini Maxwell, son gradient
et son Hessien partiels dans l'inverse métrique et la courbure de jauge.
Leur régularité conjointe avec le volume stocké est prouvée.
`NativeMaxwellJetBridge4D` fournit les deux slots depuis la vraie carte
complétée, prouve l'égalité exacte de densité et leur régularité C².

`MaxwellJetHessianIntegral4D` identifie l'entrée métrique–métrique du
Hessien mobile réel à l'intégrale de la formule de chaîne du jet fini.
Le terme gradient appliqué à l'accélération complète du jet est conservé.

`GaugeCurvatureReadout4D` réalise la courbure comme application linéaire
continue du cœur de coefficients C² vers les valeurs finies, avec le
terme de crochet du repère et l'accord sur les champs lisses.
`MobileCurvatureDifferentials4D` calcule sa vitesse et son accélération
sur le paquet transporté en utilisant les dérivées de la racine validées.
Le domaine de cette lecture bornée est le cœur C².

`MaxwellJetDifferentials4D` assemble les dérivées du jet par coordonnées.
`NativeMaxwellJetDifferentials4D` identifie la vitesse et l'accélération
du jet natif complet sur toute direction du cœur métrique complété :
la vitesse inverse vaut `-H g⁻¹`, son accélération `(KH + HK) g⁻¹`,
et la courbure reçoit les lectures des transports `(1/2) Hᵀa` et
`-(1/8) (HK + KH)ᵀa`. Les deux ordres matriciels sont conservés.

`NativeMaxwellExplicitHessian4D` remplace les dérivées de la carte dans
la densité par ces expressions calculées et prouve
`nativeMobileMaxwellHessian_eq_explicitIntegral`. Les dérivées restantes
sont celles du symbole polynomial fini. Aucune stationnarité ni hypothèse
d'accord avec le Hessien n'est ajoutée.

Prochaine étape : extraire les coefficients en valeur et premier jet du
tenseur test dans la courbure transportée, établir leur régularité spatiale,
puis appliquer l'intégration par parties pour la borne L2 métrique Maxwell.
Restent ensuite l'assemblage physique H11, la densité du domaine adjoint
et le certificat global actual→D9. T12 reste non coché.
Validation : huit gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 1790, 3892, 4148, 4058, 4146,
1796, 4151 et 4131 Mo. Audit des 38 déclarations et hub T12 verts,
pics 3851 et 4024 Mo. Axiomes : uniquement `propext`, `Classical.choice`,
`Quot.sound`. Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.

## 2026-09-24 — Borne L2 Maxwell métrique complète

Le bloc Maxwell métrique est désormais représenté dans le véritable L2
BRST, avec la variation de la racine et les deux ordres matriciels.
`NativeMaxwellHessianL24D.nativeMobileMaxwellHessian_metric_bound`
borne la Hessienne native métrique–métrique, pour toute première
variation lisse fixée, par la norme L2 du tenseur test.
`StrongMaxwellBRSTL24D.strongMaxwellBRSTHessian_metric_bound`
porte cette borne sur la somme des blocs Maxwell plus/minus de l'action
forte, dans la norme `diffeomorphismMetricSmooth`.

La chaîne de preuve extrait le covecteur du premier jet relatif,
identifie son intégrale à la Hessienne réelle, prouve la régularité
spatiale de ses coefficients et leur applique l'adjoint du repère.
Le retour de `g⁻¹h` au tenseur covariant est explicite dans
`RelativeTensorFirstJetL24D`. Aucune borne en norme C2 n'est substituée
à la borne L2, aucune stationnarité ni hypothèse d'intertwining n'est ajoutée.

Cette étape ferme la borne L2 Maxwell annoncée dans l'entrée précédente.
T12 reste ouvert : l'assemblage physique H11 et le certificat global
actual→D9 ne sont pas établis par ces seuls résultats. Quillen inchangé.
Validation : onze gates, audit des 65 déclarations et hub T12 verts sous
`run_lean_guarded`, un seul Lean, priorité haute, réserve 4096 Mo.
Pic maximal des gates : 4153 Mo ; audit : 3901 Mo ; hub : 4023 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound`, et, pour l'IPP/L2,
la dépendance existante
`JanusFormal.P0EFTJanusMappingTorusCanonicalTenFlowIPP4D.canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; T08 et les fichiers externes préservés.

## 2026-09-24 — Assemblage du pairing H11 métrique

`PhysicalMetricHessianReduction4D` retire exactement les Hessiennes Robin
et BV finie par leur gradient localement nul. `StrongPhysicalBRSTMetricHessian4D`
spécialise la réduction aux deux directions BRST réelles : interaction,
Einstein plus/minus et Maxwell plus/minus, sans hypothèse de stationnarité.

`StrongEinsteinMaxwellBRSTL24D` assemble les quatre blocs Einstein–Maxwell
en un unique covecteur L2. `DiffeomorphismH11MetricPairing4D` raccorde ce
résultat au véritable pairing H11 sur les tests métriques lisses :
interaction native plus ce covecteur. La différence entre le pairing H11
et l'interaction est bornée dans la norme métrique BRST.

`StrongInteractionHessianPullback4D.strongInteractionActionHessian_eq_native`
identifie ensuite la Hessienne d'interaction forte à celle de l'action C2
paire, via la projection métrique réelle. L'admissibilité au centre et
la régularité C2 sont dérivées des données existantes.

Pour terminer cette colonne métrique, la borne L2 à établir est celle de
cette interaction native. Le présent assemblage ne prouve donc pas encore
l'appartenance des tests métriques au domaine adjoint complet. T12 reste
non coché ; aucune hypothèse terminale d'intertwining n'est introduite.

Validation : cinq gates vertes sous `run_lean_guarded`, Lean séquentiel,
priorité haute, réserve 4096 Mo ; pics 3762, 4030, 3959, 4002 et 4297 Mo.
Audit des 15 déclarations et hub T12 verts, pics 3914 et 4023 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et, pour les bornes L2,
la seule dépendance IPP existante `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et les fichiers externes préservés.

## 2026-09-24 — Borne L2 interaction BRST et tests métriques H11

La borne d'interaction laissée ouverte dans l'entrée précédente est prouvée.
`StrongInteractionBRSTL24D.strongInteractionBRSTHessian_eq_covector` représente
la Hessienne réelle par un covecteur continu sur le L2 BRST ;
`strongInteractionBRSTHessian_metric_bound` donne la borne dans la norme
métrique réelle, sans remplacer celle-ci par une norme de graphe C2.

La preuve utilise la localité ponctuelle de la racine sélectionnée : la
surjectivité du Sylvester C2, appliquée aux matrices constantes, donne
l'injectivité du Sylvester fini en chaque point. La localité passe ensuite
au gradient puis à la Hessienne réelle de la densité d'interaction.
`InteractionHessianCoefficients4D` construit ses 32 coefficients C2 et
prouve la formule exacte de reconstruction. `NativeInteractionHessianL24D`
intègre cette identité et fournit le représentant L2. Les gates
`RelativeMatrixL2Readout4D` et `InteractionBRSTMatrixReadout4D` raccordent
ces coordonnées au véritable espace L2 des tenseurs/BRST.

`DiffeomorphismH11MetricTests4D` assemble les bornes interaction,
Einstein et Maxwell. Son théorème `diffeomorphismH11_metric_test_mem_adjoint`
place les tests métriques physiques lisses dans le domaine adjoint H11
complet. Cette étape ferme la borne et l'appartenance annoncées ; elle
ne constitue pas encore le certificat terminal global actual→D9.
T12 reste non coché ; Quillen et T08 inchangés.

Validation : dix gates, audit des 39 déclarations et hub T12 verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pic maximal des gates : 4259 Mo ; audit : 3946 Mo ; hub : 4024 Mo.
L'interaction BRST n'utilise que `propext`, `Classical.choice`, `Quot.sound`.
L'assemblage H11 reprend uniquement la dépendance IPP déjà présente dans
Einstein–Maxwell : `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; aucun fichier externe/T08 modifié.

## 2026-09-24 — Fermeture minimale H11 et transport exact au quotient

`DiffeomorphismH11AdjointDensity4D` place tout le cœur lisse commun dans
le domaine adjoint H11 : tests métriques, abéliens et matière–LL complétée.
La densité en résulte. `DenseAdjointMinimalClosure4D` prouve le passage
abstrait de cette densité à la fermeture minimale, avec le même adjoint.

`DiffeomorphismH11Minimal4D` construit ainsi la réalisation fermée de la
colonne physique réelle H11, avec domaine dense et cœur lisse explicite.
`DiffeomorphismH11QuotientMinimal4D` construit la réalisation correspondante
sur le quotient par le noyau joint fantômes–LL et identifie son adjoint.

`DiffeomorphismH11ClosedQuotientTransport4D` transporte exactement les graphes
fermés par projection et relèvement orthogonal. Les domaines sources sont
égaux ; les sorties restent orthogonales au noyau joint. Norme, pairing et
noyau de la colonne fermée sont conservés par le quotient.

Ces résultats ne supposent aucun intertwiner terminal. Le certificat global
actual→D9 reste à construire ; T12 reste non coché. Quillen et T08 inchangés.

Validation : cinq gates, audit des 31 déclarations et hub T12 verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des gates : 4274, 2235, 4002, 4066 et 4138 Mo ; audit : 3918 Mo ;
hub : 4025 Mo. Axiomes : `propext`, `Classical.choice`, `Quot.sound` et
la seule dépendance IPP existante
`canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; aucun fichier externe/T08 modifié.

## 2026-09-24 — Fermeture de la colonne BRST complète avec H11

`DiffeomorphismAugmentedAdjointDensity4D` traite la colonne réelle entière,
somme du BRST diffeomorphisme et de H11, avec la mesure canonique. Le readout
d'un test commun lisse est son véritable représentant L2 diffeomorphisme.
La symétrie du BRST et les tests H11 déjà prouvés placent tout le cœur commun
dans le domaine adjoint. Sa densité prouve la fermabilité de la somme.

`DiffeomorphismAugmentedMinimal4D` construit sa fermeture minimale : graphe
fermé, domaine dense, cœur lisse original et adjoint inchangé. Le graphe
contient exactement les couples lisses source L2 / sortie de
`strongAugmentedRiesz`, sans hypothèse terminale d'intertwining.

`ClosedColumnTargetQuotient4D` donne le transport général d'une colonne
fermée dont les sorties sont orthogonales au sous-espace quotienté.
`DiffeomorphismAugmentedClosedQuotient4D` l'applique à la colonne complète.
Sous les conditions existantes `hZero`, `hMetric`, `hWeights` (fond LL nul,
métriques plus/minus égales, somme des poids cinétiques nulle), toutes les
sorties fermées sont orthogonales au noyau joint fantômes–LL. La réalisation
quotientée conserve le domaine dense et réalise la colonne actual projetée.
Son graphe se relève exactement dans le graphe réel ; son noyau est inchangé.

Cette étape construit une colonne BRST réelle fermée avec H11 et sa réduction.
Le certificat global actual→D9 reste ouvert ; T12 reste non coché.

Validation : quatre modules, audit des 31 déclarations et hub T12 verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des modules : 4058, 4007, 1930 et 4220 Mo ; audit : 3924 Mo ; hub : 4026 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et la seule dépendance IPP
existante `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et fichiers externes préservés.

## 2026-09-24 — Cœur minimal et adjoint du BRST complet quotienté

`ClosedColumnTargetCore4D` prouve que le quotient orthogonal de la cible
commute avec la fermeture minimale du graphe lisse. Il conserve le cœur
lisse original. `ClosedColumnTargetAdjoint4D` transporte exactement le
graphe et le domaine de l'adjoint Hilbert : une classe quotientée appartient
au domaine adjoint si et seulement si son représentant original y appartient.
La densité du domaine adjoint passe ainsi au quotient.

`DiffeomorphismAugmentedQuotientMinimal4D` applique ces résultats à BRST + H11.
La réalisation fermée quotientée construite précédemment est exactement la
fermeture du `diffeomorphismAugmentedL2QuotientCore` existant. Le cœur lisse
L2 est conservé et l'adjoint reste celui de ce cœur. Son graphe et son domaine
se transportent exactement depuis l'adjoint de la colonne actual complète ;
ce domaine est dense. Les hypothèses sont les conditions déjà présentes
`hZero`, `hMetric`, `hWeights`, avec la mesure canonique.

Aucune extension supplémentaire ni hypothèse terminale d'intertwining n'est
introduite. L'accord géométrique avec les modes signés et le certificat global
restent ouverts ; T12 reste non coché.

Validation : trois modules, audit des 16 déclarations et hub T12 verts sous
`run_lean_guarded`, Lean séquentiel, priorité haute, réserve 4096 Mo.
Pics des modules : 1938, 1907 et 4363 Mo ; audit : 3923 Mo ; hub : 4025 Mo.
Axiomes : `propext`, `Classical.choice`, `Quot.sound` et la seule dépendance IPP
existante `canonicalFlowIndex_card._native.native_decide.ax_1_1`.
Aucun nouvel axiome, `sorry`/`admit` ni budget augmenté.
`git diff --check` OK ; Quillen, T08 et fichiers externes préservés.
