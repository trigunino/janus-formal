# Programme P — TODO exhaustive de fermeture

Date de référence : 2026-07-16.

Ce document couvre Programme P et toutes ses dépendances directes nécessaires
à une fermeture physique : géométrie globale, opérateurs spectraux, BRST,
Quillen/anomalies, action covariante, contraintes, renormalisation, stabilité
et échelle absolue. Il ne transforme pas un modèle fini, pointwise ou
conditionnel en résultat global.

Légende :

- `[x]` : résultat formalisé dans l'arbre de travail actuel ;
- `[ ]` : obligation restante ;
- **acceptation** : résultat minimal permettant de fermer le bloc ;
- **rejet** : résultat qui invaliderait Candidate A ou imposerait sa révision.

Documents de référence :

- `docs/program_master_roadmap.md` ;
- `docs/research_dashboard.md` ;
- `docs/program_p_explicit_covariant_candidate.md` ;
- `docs/program_pd_global_pairing_modules.md` ;
- `docs/current_status.md`.

## 0. Frontière D7 à ne pas rouvrir

- [x] Construire la trace thermique monopolaire comme un `tsum` convergent à
  tout temps strictement positif.
- [x] Calculer les jets de bord Euler--Maclaurin donnant les coefficients
  spectraux `2`, `-1/3` et `(5*q^2-1)/30`.
- [x] Prouver algébriquement que les coefficients spectraux du produit sont
  exactement les coefficients universels `a0`, `a2`, `a4`.
- [x] Construire le déterminant renormalisé des deux racines physiques `Z4`,
  avec le même contre-terme local et l'égalité PT.
- [x] Décharger `EulerMaclaurinRemainderControlled data`.
  - [x] Fixer l'énoncé Euler--Maclaurin infini utilisé pour
    `(2*x+q) * exp (-u*x*(x+q))`.
  - [x] Formaliser les dérivées nécessaires et les identités de jets.
  - [x] Prouver l'annulation des termes de bord à l'infini, uniformément pour
    `u` dans un voisinage positif de zéro.
  - [x] Borner le noyau périodique de Bernoulli intervenant dans le reste.
  - [x] Obtenir une majoration intégrable uniforme des dérivées du terme
    spectral après la remise à l'échelle adaptée.
  - [x] Prouver que le reste, divisé par `u`, tend vers zéro lorsque
    `u -> 0+`.
  - [x] En déduire `EulerMaclaurinRemainderControlled data` sans hypothèse.
  - [x] Promouvoir
    `small_time_coefficients_match_of_euler_maclaurin_control` en corollaire
    inconditionnel.
  - [x] Ajouter à la façade D7 un statut distinct pour la limite petit temps ;
    ne pas confondre ce statut avec la correspondance algébrique déjà fermée.

**Acceptation D7** : la limite petit temps est prouvée sans hypothèse
analytique externe et la façade distingue explicitement : trace convergente,
correspondance algébrique des coefficients, puis asymptotique effective.

## 1. Stabilisation et intégration immédiates

- [x] Vérifier que les gates D7 récents sont tous importés par
  `FundamentalGeometryD7SpectralTheory.lean`.
- [x] Vérifier que le pont P--D7 est importé par la façade Programme P.
- [x] Ajouter les déclarations D7 récentes aux audits d'intégrité pertinents.
- [x] Remplacer, pour les deux racines physiques `Z4`, le certificat P--D7
  conditionnel à `HeatRemainderQuadraticBound` par un théorème combinant
  directement compacité des blocs et `z4RenormalizedDeterminant`.
- [x] Conserver la borne quadratique uniquement pour une famille générale en
  holonomie, pas pour les secteurs `1/4` et `3/4` déjà fermés.
- [x] Compiler les façades D7 et P.
- [x] Exécuter l'audit Programme P et les contrôles de placeholders.
- [x] Aligner roadmap, dashboard, registre et statut canonique.
- [x] Committer ce lot séparément des futurs travaux analytiques lourds.

## 2. Dépendances géométriques globales D0/D8

- [ ] Construire la variété globale Janus et le mapping torus décoré effectif.
  - [x] Construire le quotient topologique effectif de `S³ × ℝ` par
    l'action libre et proprement discontinue, sa projection de covering et son
    espace charté topologique.
  - [x] Construire sur ce même quotient l'involution continue de renversement
    du temps, prouver son involutivité et l'instancier sur le throat fixe.
  - [ ] Promouvoir cet objet en variété lisse (`IsManifold` et atlas lisse)
    et ajouter toutes les décorations physiques globales.
    - [x] Donner aux covers concrets `S³ × ℝ` et `S² × ℝ` leurs atlas
      analytiques, puis prouver que les deux quotients sont des variétés
      topologiques `C⁰` et que la projection de covering est `C⁰`.
    - [ ] Promouvoir l'atlas quotient et la projection de `C⁰` à `C∞`.
- [ ] Construire l'immersion du throat et sa stratification non-nulle/null/joint.
  - [x] Construire l'inclusion continue injective du `S²` équatorial au
    niveau du cover et l'inclusion injective induite de son mapping torus dans
    le quotient effectif.
  - [x] Prouver que cette même inclusion de quotient entrelace exactement les
    involutions PT du throat et de l'espace-temps.
  - [x] Décomposer le complément du `S²` équatorial dans le `S³` concret en
    deux côtés ouverts, disjoints et non vides, échangés par la réflexion.
  - [x] Prouver qu'un tour de deck échange ces côtés, que l'image de chacun
    est exactement le complément du throat effectif, et que PT préserve ce
    complément : c'est le sens topologique prouvé de « une-face ».
  - [x] Identifier les deux côtés par leur connexité par arcs dans la
    décomposition disjointe avant quotient et prouver que le complément après
    quotient est lui-même connexe par arcs, donc connexe.
  - [ ] Prouver l'immersion/embedding lisse et la stratification
    non-nulle/null/joint.
    - [x] Prouver que l'inclusion du throat au niveau cover est un embedding
      topologique `C⁰` et que l'inclusion quotient est `C⁰`.
    - [ ] Promouvoir cette inclusion en embedding lisse et construire les
      strates non-nulles/nulles/joints.
- [ ] Construire la ligne normale, son orientation locale et son recollement
  global sur le domaine non orientable pertinent.
  - [x] Construire la ligne normale associée comme quotient d'orbites
    topologique, avec projection, section nulle et monodromies à un/deux tours.
  - [x] Construire sur le throat le quotient par les enroulements pairs, sa
    projection couvrante à deux feuillets, l'involution de deck libre et la
    trivialisation topologique explicite du pullback de la ligne normale.
  - [ ] Identifier ces quotients aux objets normaux différentiels d'un
    embedding lisse et les promouvoir en `VectorBundle` lisses.
- [ ] Construire le relèvement Pin/SpinC et la racine normale `Z4` comme objets
  globaux, pas seulement comme phases ou cocycles fournis.
- [ ] Identifier les classes caractéristiques et prouver les compatibilités
  entre racine déterminante, Spin et twist monopolaire.
- [ ] Fixer les domaines géométriques sur lesquels métriques, racines,
  opérateurs et conditions au bord sont simultanément définis.

**Acceptation** : un objet géométrique global unique alimente sans conversion
ad hoc les espaces de champs, les opérateurs D7/D9/D10 et les termes de bord.

## 3. Verrou 1 — racine lorentzienne et densités croisées

- [ ] Définir le domaine admissible des paires indépendantes
  `(g_plus, g_minus)` en dimension quatre.
  - [ ] Non-dégénérescence et signature lorentzienne.
  - [ ] Compatibilité causale requise.
  - [ ] Condition spectrale garantissant une racine réelle choisie.
  - [ ] Description des composantes connexes et de leur frontière.
- [ ] Construire la racine principale réelle de `g_plus⁻¹ g_minus` sur ce
  domaine.
  - [x] Construire sans hypothèse une branche locale réelle autour de la paire
    diagonale de Minkowski, par composition avec le vrai produit
    `g_plus⁻¹ g_minus`, et prouver qu'elle vaut l'identité au point de base et
    que son carré redonne le produit dans un voisinage.
  - [x] Remplacer le simple voisinage éventuel par un domaine ouvert explicite
    tiré de la cible/source de `localSquareChart`, avec continuité, carré exact
    sur tout le domaine et unicité parmi les racines restant dans la source IFT.
  - [ ] Étendre cette branche locale en une sélection principale, causale et
    globale sur le domaine admissible.
- [ ] Prouver existence, unicité et régularité de la branche.
  - [x] Sur le domaine ouvert IFT explicite, extraire la borne quantitative de
    l'inverse locale, prouver l'inversibilité de Sylvester par série de Neumann
    et obtenir la différentiabilité de la racine en chaque point du domaine.
- [ ] Inclure les points diagonalisables et les blocs de Jordan admissibles.
- [ ] Prouver l'inversibilité globale de l'opérateur de Sylvester pertinent.
- [ ] Recoller les branches IFT locales sur tout le domaine admissible.
  - [x] Le recollement local et la dérivabilité inverse-Sylvester sont prouvés
    le long de tout relèvement continu fourni qui reste ponctuellement
    Sylvester-régulier.
  - [ ] Construire ce relèvement continu et prouver sa régularité Sylvester
    sur le domaine physique, sans les conserver comme hypothèses.
- [ ] Contrôler l'approche de la frontière spectrale et les changements de
  branche éventuels.
- [ ] Dériver la variation de la racine par rapport aux deux métriques
  indépendantes, inverse métrique comprise.
  - [x] Cette dérivée complète est prouvée au point diagonal de Minkowski pour
    la branche locale, y compris la dérivée de l'inverse dans
    `g_plus⁻¹ g_minus` et l'inverse de Sylvester égal à la demi-identité.
  - [ ] Étendre la formule à toute la branche physique globale.
- [ ] Dériver la variation fonctionnelle complète du potentiel spectral
  `sum beta_n e_n(X)`.
  - [x] La dériver réellement après composition avec la branche de racine pour
    deux variations métriques indépendantes au point diagonal de Minkowski.
  - [x] Étendre cette dérivée à chaque point du domaine ouvert IFT explicite.
- [ ] Dériver la variation de `sqrt(|det g_plus|)` et la densité croisée
  complète dans les deux secteurs.
  - [x] Dériver la mesure plus, la racine et le potentiel dans une même chaîne
    de Fréchet, puis la variation directionnelle Candidate A complète au point
    diagonal de Minkowski.
  - [x] Étendre la chaîne complète à tout le domaine ouvert, construire le
    domaine PT où les deux ordres sont admissibles, dériver les deux secteurs
    et prouver l'invariance de leur somme par échange.
  - [ ] Étendre cette chaîne au domaine lorentzien global et au second secteur.
- [ ] Prouver covariance, réalité, échange PT et régularité spatiale de la
  densité obtenue.

**Acceptation** : une densité Candidate A globale, réelle et différentiable,
avec dérivées métriques complètes sur un domaine invariant non vide.

**Rejet** : absence de domaine global non vide, perte inévitable de réalité,
non-unicité incompatible avec l'action ou singularité de Sylvester rencontrée
par toute évolution admissible.

## 4. Verrou 2 — espace de champs, champs induits et jauge

- [ ] Définir l'espace de configuration global :
  - [x] Fournir le paquet paramétré des champs indépendants/induits, des
    contrats PT, des espaces fonctionnels et des conditions au bord.
  - [x] Instancier ses bases abstraites par les quotients D8 effectifs, leurs
    involutions PT et la même inclusion de throat équivariante.
  - [x] Construire sur ces mêmes bases une branche algébrique non vide : deux
    métriques de Minkowski égales, matières nulles, racine relative identité
    et point fixe de l'échange PT.
  - [ ] deux métriques lorentziennes indépendantes ;
  - [ ] deux multiplets matière et leur identification PT ;
  - [ ] champs de jauge, ghosts et auxiliaires ;
  - [ ] données d'immersion/throat et champs LL ;
  - [ ] espaces fonctionnels, régularité et conditions au bord.
    - [x] Définir sur les quotients D8 effectifs les prédicats concrets de
      continuité de tous les champs indépendants, induits et LL, puis construire
      sur ces mêmes objets une configuration continue non vide, PT-matched,
      avec inclusion du throat et équation de carré exactes.
    - [x] Construire sur le cover analytique D8 des champs de coefficients
      réellement lisses et invariants sous tous les iterés de deck, prouver
      leur descente continue et injective au quotient, et exhiber une
      configuration lisse non vide à deux métriques/deux scalaires/racine.
    - [ ] Construire les espaces Sobolev/lisses, leurs traces et les conditions
      au bord directement sur le quotient `C∞`; le gate lisse actuel est
      intrinsèque au cover et sa descente n'est encore que `C⁰`.
- [ ] Distinguer les variables indépendantes des champs induits.
- [ ] Formaliser la chaîne de variation des champs induits sans double
  comptage des équations.
- [ ] Définir l'action des difféomorphismes diagonaux et son générateur
  infinitésimal sur tous les secteurs.
- [ ] Définir exactement la symétrie PT/échange et ses conditions au bord.
- [ ] Construire l'action matière holonomique covariante en dimension quatre.
- [x] Construire sur la carte plate continue `R^4` le jet holonomique d'un
  champ scalaire différentiable, sa ligne affine dans l'espace des fonctions
  et sa variation pointwise puis intégrée sous un contrat explicite de
  mesurabilité, domination intégrable et Lipschitz local.
- [ ] Relier globalement valeur, gradient, mesure et inverse métrique à un même
  champ et à une même métrique.
  - [x] Au niveau pointwise 4D, relier une valeur et un covecteur-gradient fixés
    à l'inverse exact et à `sqrt(|det g|)` issus d'une seule métrique symétrique
    sur un domaine ouvert à signe de déterminant fixé.
  - [x] Sur la carte plate continue `R^4`, imposer `p = d phi` par la dérivée
    de Fréchet réelle du même champ et varier simultanément `phi` et `d phi`.
  - [x] Sur cette même carte plate, varier pointwise la métrique et le champ
    holonomique le long d'un même paramètre : mesure, inverse, valeur et
    `p = d phi` proviennent des mêmes objets, et la variation se scinde
    exactement en contributions de stress et de champ.
  - [ ] Imposer globalement `p = d phi`, les espaces fonctionnels, la régularité
    sur la variété courbe et les conditions au bord.
- [ ] Dériver les équations matière covariantes.
  - [x] Sur la carte plate à métrique fixe, décomposer pointwise la variation
    holonomique en opérateur d'Euler scalaire et divergence du flux de bord.
  - [x] Après hypothèses explicites d'intégrabilité et
    `IntegratedScalarFluxVanishes`, identifier la variation intégrée et la
    dérivée déjà justifiée de l'action au pairing faible avec l'opérateur
    d'Euler plat.
  - [ ] Déduire l'annulation du flux intégré des conditions au bord retenues et
    promouvoir l'identité en équation covariante courbe.
- [ ] Dériver les deux tenseurs de stress par variation métrique fonctionnelle.
  - [x] Dériver pointwise le tenseur de stress symétrique d'un secteur scalaire
    et prouver `delta rho = -sqrt(|det g|)/2 <T,delta g>` le long de la courbe
    métrique exacte.
  - [x] Intégrer l'action scalaire et la variation de stress sur une base
    mesurée arbitraire, pour les deux secteurs, sous le contrat explicite de
    mesurabilité, domination intégrable et Lipschitz local, ou sous une borne
    uniforme de la dérivée pointwise à tout paramètre admissible.
  - [x] Imposer `p = d phi` pour la variation scalaire sur la carte plate
    continue, avec dérivée intégrée sous le contrat de domination explicite.
  - [x] Combiner pointwise, sur la carte plate `R^4`, la variation holonomique
    avec la variation métrique exacte et prouver le split stress + `p = d phi`.
  - [x] Intégrer cette variation simultanée sur la carte plate et une mesure
    arbitraire sous le contrat explicite de mesurabilité, domination intégrable
    et Lipschitz local.
  - [ ] Décharger ce contrat à partir des espaces fonctionnels et dériver les
    PDE covariantes sur la variété courbe.
- [ ] Prouver leurs lois de covariance et d'échange.
  - [x] Prouver l'invariance par échange des deux secteurs pour l'action
    intégrée et sa variation de stress.
  - [ ] Prouver la covariance difféomorphe et les identités de conservation.
- [ ] Définir le contenu de champs exact qui sera utilisé par D9/D10 et par le
  régulateur quantique.

**Acceptation** : un espace de champs unique sert à l'action, au Hessien, au
complexe BRST, aux anomalies et aux conditions au bord.

## 5. Verrou 3 — bulk, frontières, joints et worldvolume LL

- [ ] Construire l'action EH des deux métriques sur la géométrie globale.
- [ ] Dériver sa première variation en coordonnées arbitraires.
- [ ] Construire et varier les termes GHY sur chaque face non nulle.
- [ ] Prouver l'annulation intégrée du flux EH+GHY pour les conditions au bord
  retenues.
- [ ] Construire les termes de frontière nulle : inaffinité, expansion et
  contre-terme de reparamétrisation.
- [ ] Définir un domaine variationnel admissible près de `Theta = 0`, en tenant
  compte de la non-différentiabilité déjà prouvée.
- [ ] Construire les termes de joints/corners et leurs orientations globales.
- [ ] Prouver la cancellation globale des transformations de
  reparamétrisation nulle.
- [ ] Construire les champs LL globaux : métrique auxiliaire, mesure composite,
  champs de mesure et flux.
- [ ] Intégrer l'action LL sur le worldvolume.
- [ ] Dériver ses PDE, contraintes et branche de noyau nul.
- [ ] Prouver l'existence d'une branche throat non vide compatible avec les
  deux secteurs gravitationnels.
- [ ] Dériver les conditions de jonction et l'équilibre des flux.
- [ ] Étendre le Stokes fini à une formule de Stokes géométrique pour données
  variables et toutes les strates.
- [ ] Classifier les termes de bord/null/joint admissibles à divergence près.

**Acceptation** : la variation complète bulk+frontières+LL ne laisse aucun flux
non contrôlé et produit les conditions de jonction annoncées.

## 6. Verrou 4 — complexe concret `K/J`, cohomologie et quotient

- [ ] Définir le vrai opérateur de compatibilité géométrique `K` sur les
  bundles Janus.
- [ ] Calculer sa dérivée de Fréchet `J` sur les espaces fonctionnels choisis.
- [ ] Définir le générateur de jauge `R` et l'opérateur d'identités `B`.
- [ ] Prouver `J ∘ R = 0` et `B ∘ K = 0` globalement.
- [ ] Promouvoir l'exactitude symbolique non nulle vers un complexe
  différentiel lorentzien global.
- [x] Étendre la reconstruction Fourier axiale à la maille dénombrable
  `ℤ^4`, avec pivot dominant, résidu du zéro-mode et contrôle `ℓ²` uniforme
  pour tout poids non négatif commun aux coefficients métriques et potentiels.
- [x] Réaliser ces coefficients dans les espaces de Hilbert `ℓ²` pondérés :
  reconstruction bornée, symbole de Lorentz--Gram sur son domaine maximal,
  image fermée égale au sous-espace symétrique compatible sans zéro-mode,
  et obstruction du zéro-mode isolée à la même échelle.
- [ ] Identifier ces espaces de coefficients pondérés aux espaces de Sobolev
  globaux requis sur les bundles Janus.
  - [x] Construire sur `ℤ⁴` l'échelle de Sobolev de graphe décalée d'un ordre,
    où le symbole Lorentz--Gram est un opérateur borné de norme au plus un, et
    prouver son égalité exacte avec le symbole physique après encodage pondéré.
  - [ ] Identifier cette échelle périodique aux sections Sobolev des vrais
    bundles du mapping torus et à leurs cartes de recollement.
- [ ] Contrôler convergence des séries, modes zéro et cohomologie globale.
- [ ] Imposer et analyser les conditions au bord du mapping torus/throat.
- [ ] Prouver fermeture de l'image, propriétés de Fredholm ou identifier
  précisément leur échec.
- [ ] Construire le pairing/Hessien cible `H`, continu et auto-adjoint.
  - [x] Sur l'échelle de coefficients Sobolev décalée, prendre le Hessien cible
    identité, continu, auto-adjoint et positif.
- [ ] Instancier le pullback `Jᵀ H J` et la seconde variation complète.
  - [x] Construire réellement `J† H J` comme opérateur continu, prouver la
    formule de pairing, symétrie, positivité, noyau égal à celui de `J` et
    positivité définie après retrait du zéro-mode.
  - [ ] Identifier ce pullback au Hessien de la même action Janus globale.
- [ ] Construire le quotient physique topologique/lisse par `ker J` ou
  `im R`, pas seulement le quotient algébrique.
  - [x] Dans le modèle périodique de coefficients Sobolev décalés, construire
    une projection bornée du mode zéro, la scission topologique et le quotient
    normé par `ker J`, continûment linéairement équivalent aux représentants
    sans mode zéro.
- [ ] Prouver continuité et non-dégénérescence de la forme descendue sur le
  quotient physique pertinent.
  - [x] Prouver la non-dégénérescence du pullback continu `J†J` sur ces
    représentants canoniques; l'identification au quotient global Janus reste
    ouverte.

**Acceptation** : un complexe global avec bord, cohomologie contrôlée et
Hessien physique réellement descendu.

## 7. P-D/P-E — classification naturelle globale

- [ ] Définir la catégorie Janus et les bundles source/cible naturels.
- [ ] Vérifier localité, régularité et réalisations holonomiques requises.
- [ ] Construire le groupoïde différentiable des jets structurés.
- [ ] Déterminer sa stratification d'isotropie.
- [ ] Construire les revêtements Spin de dimension pertinente.
- [ ] Dériver les données Cech/SpinC depuis l'atlas réel, et non depuis des
  transitions fournies.
- [ ] Construire les bundles vectoriels et principaux Janus globaux.
- [ ] Prouver l'accord des classes caractéristiques Spin/déterminant.
- [ ] Construire la descente effective et le théorème d'intégrabilité des jets
  d'ordre supérieur.
- [ ] Calculer l'algèbre des scalaires invariants au jet requis.
- [ ] Calculer les modules globaux de pairings équivariants sur cette algèbre.
- [ ] Prouver l'extension à travers les strates d'isotropie singulières.
- [ ] Imposer ordre différentiel, degré, poids, parité, ghost number, symétrie
  d'échange et conditions de Helmholtz.
- [ ] Obtenir une base finie de termes locaux admissibles ou prouver qu'aucune
  telle base finie n'existe sous les hypothèses choisies.
- [ ] Identifier la connexion de ligne déterminante globale et l'action de
  chaque secteur naturel.

**Acceptation** : `invariantLocalFunctionalBasisClassified` est fermé comme
énoncé global, pas seulement fibre par fibre.

## 8. Verrou 5 — Euler, Helmholtz, Noether, Bianchi et contraintes

- [ ] Assembler une action covariante Candidate A unique à partir des verrous
  1 à 3.
- [ ] Calculer l'opérateur d'Euler--Lagrange complet pour toutes les variables
  indépendantes.
- [ ] Vérifier que les variations induites utilisent bien la règle de chaîne
  et ne créent pas d'équations supplémentaires.
- [ ] Calculer la dérivée de l'opérateur d'Euler sur le domaine global.
- [ ] Prouver les conditions de Helmholtz non linéaires bloc par bloc.
- [ ] Reconstruire ou identifier l'action globale normalisée à partir de ces
  données.
- [ ] Prouver l'identité de Noether pour les difféomorphismes diagonaux.
- [ ] Dériver les deux identités de Bianchi avec échange matière/interaction et
  flux de frontière.
- [ ] Déterminer quand les conservations sectorielles se séparent réellement.
- [ ] Calculer la cohomologie variationnelle.
- [ ] Classifier lagrangiens nuls, divergences et ambiguïtés de bord.
- [ ] Dériver la limite faible covariante et la loi de charge signée, au lieu de
  l'importer comme donnée réduite.
- [ ] Calculer les paramètres PPN pour les couplages matière exacts.
- [ ] Dériver la réduction ADM depuis l'action EH/GHY/matière covariante.
- [ ] Construire lapses, shifts, moments et contraintes primaires exactes.
- [ ] Calculer les contraintes secondaires et leur rang générique.
- [ ] Prouver la fermeture du crochet fonctionnel avec dérivées spatiales.
- [ ] Prouver l'algèbre de déformation des hypersurfaces ou documenter son
  obstruction.
- [ ] Exclure le mode de Boulware--Deser sur le domaine physique, ou rejeter
  Candidate A.
- [ ] Descendre la seconde variation sur l'espace tangent contraint/quotient.
- [ ] Classifier la stabilité physique des branches admissibles.

**Acceptation** : `fullEulerLagrangeOperatorDerived`,
`nonlinearHelmholtzConditionsProved`,
`variationalBicomplexObstructionVanishing` et
`nullLagrangiansAndBoundaryTermsClassified` sont fermés sur le même espace de
champs et avec les mêmes conditions au bord.

## 9. Verrou 6 — opérateurs, BRST, anomalies et schéma

- [ ] Étendre l'opérateur de Dirac du cercle au vrai opérateur Janus global.
- [ ] Fixer son domaine commun, ses conditions au bord et sa réalisation
  auto-adjointe.
- [ ] Identifier le domaine du générateur du semi-groupe avec celui de `D²`.
- [ ] Prouver l'égalité avec le calcul fonctionnel abstrait `exp(-t D²)`.
- [ ] Prouver les propriétés trace-class requises.
- [ ] Construire la famille de Fredholm lisse en holonomie et sur le vrai
  espace de paramètres.
  - [x] Construire une famille holomorphe finite-mode symétrique, Fredholm au
    sens algébrique d'indice zéro, avec covariance PT et inversibilité aux deux
    quarts d'holonomie.
  - [x] Sur le cercle infini normalisé à fold fixé, prouver que toutes les
    holonomies ont le même domaine maximal, que leur différence est une
    perturbation scalaire bornée exacte, que la famille complexifiée est
    entière sur ce domaine commun et construire explicitement la résolvante
    compacte `(D-i)⁻¹`.
  - [x] Munir ce domaine de sa norme de graphe complète, obtenir l'opérateur
    borné Fredholm, identifier noyau et conoyau finis, prouver l'indice zéro et
    construire la fibre déterminante de rang un avec une section non nulle.
  - [x] Construire sur le cercle la transformée bornée canonique auto-adjointe,
    prouver sa dépendance 1-Lipschitz en holonomie, son caractère Fredholm
    d'indice zéro, ses crossings exacts et l'orientation opposée sous PT.
  - [ ] Passer à l'opérateur Janus global non borné, avec domaine commun et
    dépendance lisse sur le vrai espace de paramètres.
- [ ] Relier cette famille au Hessien naturel de l'action Programme P.
- [ ] Instancier le complexe D9/BRST avec les vrais champs, ghosts, symboles,
  domaines et cohomologie de modes zéro.
- [ ] Fixer un régulateur commun à tous les secteurs physiques et ghosts.
- [ ] Insérer les multiplicités, statistiques et signes de tous les champs dans
  les coefficients de chaleur et le déterminant.
- [x] Construire le pont spectral P--D7--D10 pour les deux secteurs `Z4`.
  Ce pont ferme la compacité à niveau fixé, le déterminant spectral convergent,
  l'égalité PT et l'inflow mode par mode ; il ne construit ni famille Fredholm,
  ni holonomie eta, ni ligne ou section Quillen.
- [ ] Construire l'objet d'indice familial et la ligne/gerbe d'anomalie de la
  bonne dimension.
  - [x] Construire, au cutoff fini, la section induite sur la puissance
    extérieure maximale et prouver que sa fibre de ligne déterminante est de
    rang un.
  - [x] Construire aussi la fibre déterminante de l'opérateur infini du cercle
    sur norme de graphe, avec noyau/conoyau explicites et section non nulle.
  - [ ] Construire la ligne/gerbe globale et sa géométrie de
    Quillen/Bismut--Freed.
- [ ] Calculer l'anomalie locale dans le régulateur commun.
- [ ] Calculer l'holonomie eta et l'anomalie globale.
- [ ] Comparer le représentant eta à la classe d'inflow.
- [ ] Prouver l'annulation PT/inflow pour le contenu de champs complet.
- [ ] Construire et trivialiser la section de partition lorsque permis.
- [ ] Distinguer explicitement le déterminant spectral positif D7 de la ligne
  déterminante Quillen.
  - [x] Séparer formellement la magnitude spectrale positive finite-mode de la
    section à valeurs dans la vraie ligne extérieure finite-mode.
  - [ ] Établir cette distinction pour la famille globale régularisée et sa
    ligne de Quillen.
- [ ] Déterminer les contre-termes locaux covariants autorisés.
- [ ] Dériver leurs parties finies depuis une loi microscopique ; ne pas les
  ajuster à un rayon observé.
- [ ] Prouver l'indépendance de schéma des prédictions retenues.

**Acceptation** : `anomalyConstraintsApplied`,
`hessianMatchesNaturalFredholmFamily` et
`finiteCountertermsFixedMicroscopically` utilisent exactement la même action,
le même contenu de champs, les mêmes domaines et le même régulateur.

## 10. Sélection, normalisation, vide et échelle absolue

- [ ] Dériver un parent bulk/junction ou un principe microscopique qui
  sélectionne Candidate A parmi les extensions compatibles.
- [ ] Fixer l'ambiguïté affine de l'action par une normalisation dérivée.
- [ ] Fixer l'échelle globale sans entrée de rayon observé.
- [ ] Construire l'action effective renormalisée complète.
- [ ] Déterminer toutes ses branches stationnaires admissibles.
- [ ] Prouver existence et unicité du vide physique retenu.
- [ ] Prouver sa stabilité sur le quotient contraint, pas dans l'espace
  ambiant non réduit.
- [ ] Vérifier la compatibilité avec les charges bulk/throat/LL/bimétriques.
- [ ] Fermer les unités communes et l'échelle absolue.
- [ ] Produire ensuite seulement les prédictions observationnelles natives.

**Acceptation** : `parentBulkOrMicroscopicSelectionPrincipleDerived`,
`actionNormalizationDerived`, `globalActionClassReconstructed`,
`uniqueStableVacuumDerived` et `absoluteScaleDerivedNoFit` sont tous prouvés.

## 11. Checklist exacte de `fullProgramPClosure`

Fondation déjà représentée par `programPFoundationClosed` :

- [ ] Revalider chaque statut après intégration des objets globaux, sans
  réutiliser un témoin fini comme témoin global.

Classification globale :

- [ ] `invariantLocalFunctionalBasisClassified`.

Reconstruction non linéaire :

- [ ] `fullEulerLagrangeOperatorDerived`.
- [ ] `nonlinearHelmholtzConditionsProved`.
- [ ] `variationalBicomplexObstructionVanishing`.
- [ ] `nullLagrangiansAndBoundaryTermsClassified`.
- [ ] `anomalyConstraintsApplied`.
- [ ] `parentBulkOrMicroscopicSelectionPrincipleDerived`.
- [ ] `actionNormalizationDerived`.
- [ ] `finiteCountertermsFixedMicroscopically`.
- [ ] `globalActionClassReconstructed`.
- [ ] `hessianMatchesNaturalFredholmFamily`.

Fermeture prédictive :

- [ ] `uniqueStableVacuumDerived`.
- [ ] `absoluteScaleDerivedNoFit`.

Programme P ne doit être annoncé à 100 % que lorsque cette liste est fermée
par des théorèmes portant sur les mêmes objets globaux.

## 12. Ordre d'exécution recommandé

### Vague 0 — stabiliser la frontière actuelle

1. Intégration/audit des nouveaux gates D7 et P--D7.
2. Contrôle uniforme Euler--Maclaurin.
3. Certificat `Z4` P--D7 inconditionnel.

### Vague 1 — fondations globales indépendantes

1. Géométrie globale D0/D8.
2. Domaine global de racine 4D.
3. Espace de champs/matière covariant.
4. Complexe Sobolev `K/J` avec bord.
5. Groupoïde de jets et bundles SpinC/BRST.

### Vague 2 — action covariante

1. Variation métrique complète de l'interaction.
2. EH+GHY en coordonnées arbitraires.
3. Strates nulles, joints et action LL globale.
4. Action matière et tenseurs de stress.
5. Assemblage de l'action Candidate A.

### Vague 3 — équations et contraintes

1. Euler/Helmholtz/Noether/Bianchi non linéaires.
2. Cohomologie variationnelle et termes de bord.
3. Réduction ADM dérivée.
4. Fermeture secondaire et stabilité contrainte.
5. Limite faible et PPN.

### Vague 4 — quantification cohérente

1. Opérateur Janus global et famille Fredholm.
2. BRST/ghosts et régulateur commun.
3. Eta, Quillen, anomalies locale/globale et inflow.
4. Parties finies microscopiques.

### Vague 5 — prédictivité

1. Sélection microscopique/parent.
2. Action effective complète.
3. Vide unique et stable.
4. Normalisation, charges et échelle absolue.

## 13. Règle de validation pour chaque case

Une case n'est fermée que si :

- [ ] l'énoncé exact et sa portée sont documentés ;
- [ ] le théorème compile sans `sorry`, `admit` ni axiome métier ajouté ;
- [ ] les hypothèses restantes sont visibles dans le type du théorème ;
- [ ] le gate est importé par la façade appropriée ;
- [ ] le statut de façade correspond à la portée réelle du théorème ;
- [ ] le build focalisé est vert ;
- [ ] l'audit d'intégrité est vert ;
- [ ] roadmap, dashboard et document canonique sont alignés ;
- [ ] aucune conclusion globale n'est tirée d'un modèle fini, axial,
  pointwise, réduit ou conditionnel.

## 14. Risques et tests de rejet permanents

- La racine lorentzienne globale peut ne pas exister sur le domaine physique.
- La branche peut atteindre une frontière où Sylvester cesse d'être inversible.
- L'extension nulle à `Theta = 0` n'est pas différentiable dans le modèle
  actuellement prouvé.
- Le vide PT-flat réduit est déjà exclu sans matière/courbure appropriée.
- Une anomalie annulée ne fixe ni les contre-termes pairs ni la normalisation.
- Un déterminant spectral positif n'est pas une trivialisation Quillen.
- La correspondance `a0/a2/a4` ne stabilise pas à elle seule le module.
- Une multiplicité pointwise égale à un ne fixe pas un coefficient global.
- Une exactitude Fourier axiale ne prouve pas la solvabilité PDE globale avec
  bord.
- Une stabilité ambiante ne remplace pas la stabilité sur le quotient
  contraint.
- Si l'un de ces tests échoue sur tout domaine admissible, Candidate A doit être
  rejetée ou révisée au lieu de contourner l'obstruction.
