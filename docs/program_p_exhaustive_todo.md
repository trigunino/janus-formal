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
  - [x] Promouvoir cet objet en variété lisse (`IsManifold` et atlas lisse).
  - [ ] Ajouter toutes les décorations physiques globales sur ce même objet.
    - [x] Donner aux covers concrets `S³ × ℝ` et `S² × ℝ` leurs atlas
      analytiques, puis prouver que les deux quotients sont des variétés
      topologiques `C⁰` et que la projection de covering est `C⁰`.
    - [x] Promouvoir l'atlas quotient et la projection de `C⁰` à `C∞`.
      - [x] Prouver la lissité des actions de deck sur les deux covers
        analytiques, la lissité de l'inclusion du throat cover, la loi locale
        de transition entre sections et sa compatibilité au groupoïde lisse.
      - [x] Installer effectivement les instances `ChartedSpace` et
        `IsManifold` sur les deux quotients et prouver la projection `C∞`.
      - [x] Promouvoir le renversement du temps en difféomorphisme analytique
        involutif sur les quotients effectifs 4D et du throat 3D.
      - [x] Prouver la compacité des quotients effectifs 4D et 3D par projection
        continue surjective de leurs bandes fondamentales compactes.
- [ ] Compléter la géométrie du throat par sa stratification non-nulle/null/joint.
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
  - [ ] Construire la stratification non-nulle/null/joint de l'embedding lisse.
    - [x] Sur le bundle normal différentiel réel effectivement construit,
      séparer les strates intrinsèques zéro/non-zéro : elles sont disjointes
      et couvrantes, la section zéro est analytique et plongée, son image est
      fermée, le complément est ouvert, et le `Diffeomorph` normal transporte
      exactement les deux strates. La classification null/non-null requiert
      encore une forme quadratique lorentzienne absente de cette fibre réelle.
    - [x] Prouver que l'inclusion du throat au niveau cover est un embedding
      topologique `C⁰` et que l'inclusion quotient est `C⁰`.
    - [x] Prouver que l'inclusion injective du throat quotient est `C∞` pour
      les atlas quotient effectivement installés.
    - [x] Prouver que cette inclusion est un embedding topologique fermé et que
      sa différentielle de variété est injective en tout point.
    - [x] Construire le quotient tangent normal ponctuel et prouver qu'il est
      de rang réel un en tout point.
    - [x] Construire sur le throat effectif un vrai `VectorBundle` normal de
      rang un, analytique, à cocycle de signe exact et transition d'un tour
      égale à `-id`.
    - [x] Identifier non canoniquement chaque fibre de ce bundle au quotient
      différentiel normal correspondant par une équivalence linéaire.
    - [x] Promouvoir l'inclusion en `IsSmoothEmbedding` : construire une forme
      normale locale de `S² ↪ S³`, son complément normal réel de dimension un,
      la descendre au cover puis au quotient, et empaqueter globalement
      `IsImmersion` et `IsSmoothEmbedding` avec l'embedding fermé déjà prouvé.
    - [x] Choisir simultanément les équivalences normales ponctuelles et les
      empaqueter en une équivalence globale des espaces totaux dépendants,
      préservant la base, l'addition, l'action scalaire et la monodromie `-id`.
    - [ ] Construire l'atlas du bundle normal quotient, promouvoir cette
      équivalence algébrique en équivalence lisse globale et construire les
      strates non-nulles/nulles/joints.
      - [x] Transporter la topologie du vrai normal analytique sur le total
        dépendant différentiel, construire l'homéomorphisme total
        base-préservant et les trivializations, puis installer les instances
        `FiberBundle`, `VectorBundle` et `ContMDiffVectorBundle ω` avec le même
        cocycle de signe. Les strates restent ouvertes.
- [x] Construire la ligne normale, son orientation locale et son recollement
  global sur le domaine non orientable pertinent.
  - [x] Construire la ligne normale associée comme quotient d'orbites
    topologique, avec projection, section nulle et monodromies à un/deux tours.
  - [x] Construire sur le throat le quotient par les enroulements pairs, sa
    projection couvrante à deux feuillets, l'involution de deck libre et la
    trivialisation topologique explicite du pullback de la ligne normale.
  - [x] Identifier globalement et lissement ce bundle au bundle normal
    différentiel de l'`IsSmoothEmbedding` par un `Diffeomorph` total
    base-préservant, fibre-linéaire, compatible aux trivializations et au
    cocycle de monodromie `-id`.
- [x] Construire les deux racines normales `Z4` comme vraies lignes complexes
  globales sur le throat, avec sous-jacent réel lisse et carré de chaque
  transition égal au cocycle normal pour tout enroulement.
  - [x] Prouver que la conjugaison complexe, vue comme isométrie réelle
    involutive, échange les deux racines et entrelace leurs transitions pour
    tout enroulement. Le relèvement principal ambiant reste séparé.
- [x] Construire le relèvement principal normal `Pin⁻(1) ≃ Z4` comme vrai
  `FiberBundleCore` global : transitions données par le cocycle entier,
  action droite libre/transitive, carré central et projection d'orientation.
- [ ] Étendre ce relèvement normal au fibré de repères tangent ambiant et
  construire le relèvement `SpinC` compatible ; le gate normal ne l'affirme pas.
- [ ] Identifier les classes caractéristiques et prouver les compatibilités
  entre racine déterminante, Spin et twist monopolaire.
  - [x] Prouver au niveau du relèvement normal que les deux caractères quart
    associés au fibré principal `Pin⁻(1)` construisent de vrais
    `FiberBundleCore`, reproduisent les deux cocycles racines, se carrent en
    demi-tour d'orientation pour tout enroulement et sont échangés par PT.
    Les classes du fibré tangent ambiant et le twist monopolaire restent ouverts.
- [ ] Fixer les domaines géométriques sur lesquels métriques, racines,
  opérateurs et conditions au bord sont simultanément définis.

**Acceptation** : un objet géométrique global unique alimente sans conversion
ad hoc les espaces de champs, les opérateurs D7/D9/D10 et les termes de bord.

## 3. Verrou 1 — racine lorentzienne et densités croisées

- [x] Définir le domaine admissible diagonal global des paires indépendantes
  `(g_plus, g_minus)` en dimension quatre.
  - [x] Non-dégénérescence et signature lorentzienne sur ce domaine diagonal.
  - [x] Compatibilité causale requise sur le domaine diagonal retenu : les deux
    métriques partagent explicitement la même direction temporelle stricte.
  - [x] Condition spectrale positive garantissant la racine réelle choisie sur ce domaine.
  - [x] Description de la composante connexe positive retenue, de sa clôture
    non négative et de sa frontière spectrale exacte, pour une ou deux métriques.
  - [x] Sur le sous-domaine global à repère fixé des deux métriques diagonales
    lorentziennes `diag(-a₀,a₁,a₂,a₃)` et `diag(-b₀,b₁,b₂,b₃)`, imposer les
    huit magnitudes strictement positives et prouver ouverture, convexité,
    connexité, non-vacuité et inverses métriques exacts. Ce résultat ne couvre
    pas les paires non simultanément diagonalisables.
- [x] Construire la racine principale réelle de `g_plus⁻¹ g_minus` sur ce domaine diagonal global.
  - [x] Construire sans hypothèse une branche locale réelle autour de la paire
    diagonale de Minkowski, par composition avec le vrai produit
    `g_plus⁻¹ g_minus`, et prouver qu'elle vaut l'identité au point de base et
    que son carré redonne le produit dans un voisinage.
  - [x] Remplacer le simple voisinage éventuel par un domaine ouvert explicite
    tiré de la cible/source de `localSquareChart`, avec continuité, carré exact
    sur tout le domaine et unicité parmi les racines restant dans la source IFT.
  - [x] Identifier formellement la branche IFT locale à la sélection principale
    globale sur leur recouvrement explicite : ce recouvrement est ouvert, non
    vide au point de Minkowski, inclus dans le domaine IFT, et les deux racines
    y sont exactement égales. Ce résultat reste diagonal.
  - [x] Construire sans recollement la racine principale positive sur tout le
    sous-domaine diagonal global et prouver que son carré est exactement
    `g_plus⁻¹ g_minus`.
- [x] Prouver existence, unicité et régularité de la branche diagonale positive.
  - [x] Sur le domaine ouvert IFT explicite, extraire la borne quantitative de
    l'inverse locale, prouver l'inversibilité de Sylvester par série de Neumann
    et obtenir la différentiabilité de la racine en chaque point du domaine.
  - [x] Sur le sous-domaine diagonal global, prouver existence, unicité dans la
    branche diagonale positive et régularité `C∞` de la racine.
- [ ] Inclure les points diagonalisables et les blocs de Jordan admissibles.
- [x] Prouver l'inversibilité de Sylvester sur tout le domaine diagonal retenu.
  - [x] Construire un inverse continu bilatère de Sylvester en chaque point du
    sous-domaine diagonal global, par division par les sommes de racines
    propres strictement positives.
- [ ] Recoller les branches IFT locales sur tout le domaine admissible.
  - [x] Le recollement local et la dérivabilité inverse-Sylvester sont prouvés
    le long de tout relèvement continu fourni qui reste ponctuellement
    Sylvester-régulier.
  - [ ] Construire ce relèvement continu et prouver sa régularité Sylvester
    sur le domaine physique, sans les conserver comme hypothèses.
- [ ] Contrôler l'approche de la frontière spectrale et les changements de
  branche éventuels.
  - [x] Sur le sous-domaine diagonal global, construire les chemins vers les
    deux faces : numérateur vers zéro donne une extension continue de la
    racine vers zéro et une dégénérescence explicite de Sylvester ; dénominateur
    vers zéro avec numérateur positif fait diverger ratio et racine vers
    `+∞`. L'unicité positive exclut tout changement de branche dans la
    composante. Les cas `0/0` et les matrices générales restent ouverts.
- [x] Dériver la variation de la racine sur ce domaine par rapport aux deux métriques indépendantes, inverse métrique comprise.
  - [x] Cette dérivée complète est prouvée au point diagonal de Minkowski pour
    la branche locale, y compris la dérivée de l'inverse dans
    `g_plus⁻¹ g_minus` et l'inverse de Sylvester égal à la demi-identité.
  - [x] Étendre la formule à toute la branche diagonale globale retenue.
  - [x] Étendre la dérivée complète aux deux métriques sur tout le sous-domaine
    diagonal global et l'identifier exactement à l'inverse de Sylvester
    appliqué à la variation de `g_plus⁻¹ g_minus`.
- [x] Dériver la variation fonctionnelle complète du potentiel spectral sur le domaine diagonal global.
  `sum beta_n e_n(X)`.
  - [x] La dériver réellement après composition avec la branche de racine pour
    deux variations métriques indépendantes au point diagonal de Minkowski.
  - [x] Étendre cette dérivée à chaque point du domaine ouvert IFT explicite.
  - [x] Dériver le potentiel spectral complet aux cinq coefficients en chaque
    point du sous-domaine diagonal lorentzien global, sans hypothèse de
    petitesse autour de Minkowski.
- [x] Dériver sur ce domaine la variation de `sqrt(|det g_plus|)` et la densité croisée complète dans les deux secteurs.
  - [x] Dériver la mesure plus, la racine et le potentiel dans une même chaîne
    de Fréchet, puis la variation directionnelle Candidate A complète au point
    diagonal de Minkowski.
  - [x] Étendre la chaîne complète à tout le domaine ouvert, construire le
    domaine PT où les deux ordres sont admissibles, dériver les deux secteurs
    et prouver l'invariance de leur somme par échange.
  - [x] Intégrer cette somme sur une base mesurée, différencier le vrai
    fonctionnel sous un contrat explicite de domination uniforme, transporter
    l'admissibilité et la variation sous échange/PT, et l'instancier sur la
    même base effective D8 avec toute mesure Borel PT-invariante fournie.
  - [x] Étendre cette chaîne aux deux ordres sur le domaine lorentzien diagonal global.
  - [x] Étendre la chaîne mesure/racine/potentiel aux deux ordres métriques sur
    tout le sous-domaine diagonal global, avec une dérivée de Fréchet portant
    sur les deux métriques indépendantes.
  - [x] Sur les mêmes champs métriques lisses du quotient D8, construire leurs
    courbes exponentielles positives, dériver exactement la densité Candidate A
    à tout paramètre et dériver le fonctionnel intégré sous un contrat explicite
    de domination uniforme.
- [x] Prouver réalité, échange PT et régularité spatiale de la densité diagonale globale.
  - [x] Sur le sous-domaine diagonal global, prouver la réalité, la
    différentiabilité en chaque point, l'invariance exacte par échange et
    l'invariance du domaine ; covariance et régularité spatiale restent
    ouvertes hors de ce secteur.
  - [x] Sur le même quotient D8 lisse, construire deux champs indépendants de
    métriques lorentziennes diagonales positives, leur ratio et leur racine
    principale `C∞`, avec carré exact et unicité ponctuelle positive.
  - [x] Identifier exactement la métrique et la racine consommées par Candidate
    A à ces mêmes champs globaux, sans conversion ni nouvelle racine ad hoc.
  - [x] Prouver la régularité spatiale `C∞` de cette densité Candidate A et sa
    règle de chaîne exacte via la différentielle de variété.
  - [x] Prouver sa covariance PT/échange exacte sur ce secteur diagonal, puis
    l'invariance de son action intégrée pour toute mesure Borel PT-invariante.

**Acceptation** : une densité Candidate A globale, réelle et différentiable,
avec dérivées métriques complètes sur un domaine invariant non vide.

**Rejet** : absence de domaine global non vide, perte inévitable de réalité,
non-unicité incompatible avec l'action ou singularité de Sylvester rencontrée
par toute évolution admissible.

## 4. Verrou 2 — espace de champs, champs induits et jauge

- [x] Définir l'espace de configuration global lisse du secteur de coefficients retenu :
  - [x] Fournir le paquet paramétré des champs indépendants/induits, des
    contrats PT, des espaces fonctionnels et des conditions au bord.
  - [x] Instancier ses bases abstraites par les quotients D8 effectifs, leurs
    involutions PT et la même inclusion de throat équivariante.
  - [x] Construire sur ces mêmes bases une branche algébrique non vide : deux
    métriques de Minkowski égales, matières nulles, racine relative identité
    et point fixe de l'échange PT.
  - [x] deux métriques lorentziennes diagonales positives indépendantes sur le
    quotient lisse effectif ; le secteur tensoriel général reste ouvert ;
    - [x] Construire intrinsèquement les champs lisses de deux-tenseurs
      covariants symétriques, leurs domaines fibre non dégénéré et lorentzien
      `(3,1)`, puis prouver leur préservation par le pullback fibre. La lissité
      globale de ce pullback et l'injection de la branche diagonale restent
      ouvertes.
  - [x] deux multiplets matière lisses et leur identification PT exacte ;
  - [x] champs de coordonnées de jauge, ghosts et auxiliaires lisses ;
    - [x] pour le secteur abélien `U(1)^2`, construire les vraies 1-formes de
      connexion lisses, l'action `A ↦ A + dλ`, sa covariance difféomorphe, le
      BRST `s(A,c) = (dc,0)`, sa nilpotence et le pont aux ghosts indépendants ;
    - [x] construire le vrai ghost difféomorphe tangent lisse, ses lois de
      pullback, la dérivée de Lie scalaire et le complexe BRST linéarisé
      nilpotent, avec un slot séparé dans les champs indépendants ;
    - [ ] construire le ghost difféomorphe, le BRST non abélien/BV et leur
      accord avec l'action, le Hessien et les conditions au bord ;
      - [x] Prouver le no-go du ghost tangent réel ordinaire : son crochet de
        Lie avec lui-même est identiquement nul, donc la formule non graduée
        `s c = -1/2 [c,c]` ne produit aucun terme quadratique non trivial. Une
        extension à coefficients impairs/gradués est une obligation réelle.
  - [x] inclusion effective du throat et champs de coefficients LL lisses ; les
    strates et les PDE LL restent ouvertes ;
  - [x] espaces fonctionnels lisses/L², régularité et condition de Dirichlet ; Sobolev reste séparé.
    - [x] Définir sur les quotients D8 effectifs les prédicats concrets de
      continuité de tous les champs indépendants, induits et LL, puis construire
      sur ces mêmes objets une configuration continue non vide, PT-matched,
      avec inclusion du throat et équation de carré exactes.
    - [x] Construire sur le cover analytique D8 des champs de coefficients
      réellement lisses et invariants sous tous les iterés de deck, prouver
      leur descente continue et injective au quotient, et exhiber une
      configuration lisse non vide à deux métriques/deux scalaires/racine.
    - [x] Promouvoir cette descente de `C⁰` à `C∞` sur le vrai quotient lisse,
      construire le pullback inverse et obtenir une équivalence exacte entre
      champs lisses quotient et champs lisses deck-invariants du cover.
    - [x] Construire le pullback PT involutif sur les vrais champs de
      coefficients `C∞` du quotient, puis l'équivalence d'échange des deux
      secteurs et une famille non vide de paires PT-matched.
    - [x] Instancier sur ce même espace deux champs métriques diagonaux
      lorentziens indépendants et leur champ racine principal, tous `C∞`.
    - [x] Installer les espaces vectoriels réels de champs `C∞` sur le quotient
      et le throat effectifs.
    - [x] Construire l'inclusion canonique des champs lisses dans le vrai
      complété `L²` pour toute mesure Borel finie sur le quotient compact.
    - [x] Prouver complétude et structure hilbertienne du `L²` sous les
      hypothèses explicites de complétude/Hilbert sur la fibre.
    - [x] Construire le pullback PT comme isométrie linéaire involutive et
      équivalence `L²` pour toute mesure PT-préservée.
    - [x] Construire la trace lisse vers le throat réel, sa linéarité et son
      équivariance PT exacte.
    - [x] Construire un espace de Dirichlet exact, PT-stable et non vide.
    - [ ] Construire les échelles Sobolev intrinsèques sur le quotient et le
      vrai théorème de trace Sobolev inconditionnel.
      - [x] À partir d'une famille tangentielle lisse finie couvrante fournie,
        construire le graphe global du premier jet dans `L²`, sa fermeture
        complète `H1GraphSpace`, l'inclusion continue vers `L²` et la densité
        des champs lisses.
      - [x] Sous l'inégalité quantitative explicite `HasH1TraceBound`, étendre
        canoniquement la trace lisse au graphe `H¹`, avec accord sur les lisses,
        borne de norme et unicité.
      - [x] Construire sans hypothèse une famille tangentielle globale finie
        `C∞`, couvrante et fibre-par-fibre génératrice, par trivialisation
        locale finie et partition de l'unité sur le quotient compact, puis la
        raccorder directement au graphe `H¹`.
      - [x] Pour la mesure d'espace-temps poussée depuis une mesure finie du
        throat, construire `HasH1TraceBound` avec constante exacte `1` et la
        trace continue correspondante. L'identification à l'espace Sobolev
        intrinsèque et le théorème de trace pour la mesure volumique physique
        restent ouverts.
      - [x] Plonger le vrai cœur scalaire statique dans le graphe `H¹`
        existant, prendre sa clôture complète et prouver que le pont continu
        depuis le Hilbert d'énergie existe si et seulement si la borne de
        comparaison des deux normes est satisfaite. L'égalité avec tout le
        graphe est exactement équivalente à une densité statique séparée ;
        aucune identification Sobolev n'est postulée.
- [x] Distinguer les variables indépendantes des champs induits : métriques,
  matières, jauge, ghosts, auxiliaires et LL sont indépendants ; matrices
  métriques, racine principale et traces matière sont uniquement induites.
- [x] Formaliser la chaîne abstraite de variation des champs induits sans double comptage des équations.
  - [x] Prouver existence et unicité du paquet induit à partir du seul paquet
    indépendant, sans stocker une seconde copie variationnelle.
  - [x] Dériver la chaîne fonctionnelle complète du paquet diagonal global :
    une courbe simultanée varie chaque champ indépendant, les deux métriques,
    chaque entrée de la racine principale et les deux traces matière ont leurs
    dérivées exactes, et jauge/ghosts/auxiliaires/LL ont une réponse induite
    nulle lorsque les directions métrique et matière s'annulent.
- [x] Définir l'action des difféomorphismes diagonaux et son générateur
  infinitésimal sur tous les secteurs.
- [x] Définir exactement la symétrie PT/échange sur tous les champs de
  coefficients construits et une condition de Dirichlet lisse PT-compatible.
  - [x] Définir cette symétrie comme une équivalence involutive exacte sur les
    paires de champs de coefficients lisses du quotient 4D.
  - [x] Identifier les paires PT-matched aux points fixes de cette équivalence
    et prouver leur non-vacuité.
  - [ ] Étendre l'action aux métriques générales, matière, jauge, ghosts,
    auxiliaires et conditions au bord retenues.
- [ ] Construire l'action matière holonomique covariante en dimension quatre.
  - [x] Pour une métrique lorentzienne tensorielle générale munie de son
    isomorphisme musical exact, construire pointwise l'inverse, le Gram,
    `sqrt(|det|)`, `p = dφ`, la densité scalaire du même champ et son expansion
    variationnelle quadratique exacte.
    - [x] Prouver la naturalité exacte de la contraction, du Gram, du
      déterminant-volume et de la densité sous changement de frame, puis la
      spécialiser au vrai `mfderiv` d'un difféomorphisme D8 et à la règle de
      chaîne de `dφ`.
    - [x] Définir l'espace fonctionnel régulier où sharp, frame, volume et
      différentielle scalaire varient lissement, prouver la lissité et
      l'intégrabilité de la densité sur toute mesure finie, construire l'action
      globale et dériver sa variation intégrée exacte. Le témoin métrique
      global provenant de la branche diagonale reste à construire.
    - [x] Isoler l'obstruction déterminantielle à une frame globale
      deck-compatible sur D8, puis la remplacer par les frames tangentes
      locales canoniques, une partition de l'unité lisse subordonnée et une
      régularisation locale non vide avec musical, sharp, tenseur et volume.
      Le recollement en un unique tenseur lorentzien global reste ouvert.
      - [x] Construire sur le cover le cocycle lorentzien produit non vide :
        tangent de `S³` orthogonal, musical non dégénéré, frame d'inertie
        `(3,1)` et isométrie exacte sous la réflexion génératrice. Les deux
        ponts vers la section tensorielle intrinsèque puis sa descente lisse
        quotient sont typés explicitement mais restent à décharger.
  - [x] Construire sur le vrai quotient D8 compact une action scalaire globale
    à repère diagonal fixé : valeur, différentielle de variété, contraction par
    l'inverse de la même métrique et volume métrique proviennent des mêmes
    objets ; la covariance tensorielle générale reste ouverte.
  - [x] À métrique et mesure globales fixes, varier le même champ scalaire par
    une courbe affine, prouver l'affinité exacte de sa différentielle, puis la
    dérivée pointwise et intégrée de l'action sous un contrat d'intégrabilité
    explicite. La forme Euler--flux covariante reste ouverte.
  - [x] Décharger automatiquement ce contrat pour toute mesure Borel finie et
    tout `FixedFrameRegularScalar`, classe stable par courbes affines où les
    quatre composantes du covecteur holonomique sont continues ; construire en
    particulier des secteurs constants arbitraires non nuls sans mesure nulle.
    La continuité intrinsèque pour un repère tensoriel général reste ouverte.
- [x] Construire sur la carte plate continue `R^4` le jet holonomique d'un
  champ scalaire différentiable, sa ligne affine dans l'espace des fonctions
  et sa variation pointwise puis intégrée sous un contrat explicite de
  mesurabilité, domination intégrable et Lipschitz local.
- [x] Relier globalement valeur, gradient, mesure et inverse métrique à un même
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
  - [x] Imposer globalement `p = d phi`, les espaces fonctionnels, la régularité
    sur la variété courbe et les conditions au bord.
    - [x] Définir `p` comme la vraie différentielle de variété du même champ
      scalaire global `C∞` sur le quotient D8 et prouver son unicité.
    - [x] Prouver les règles de chaîne exactes de cette différentielle sous
      restriction au throat et pullback PT.
    - [x] Sur le secteur diagonal global, contracter cette différentielle par
      l'inverse exact de la même métrique, multiplier par son volume
      `sqrt(|det g|)`, intégrer la densité et construire deux secteurs échangés.
    - [ ] Achever la complétion Sobolev intrinsèque et l'équation d'Euler
      covariante avec les conditions au bord retenues.
- [ ] Dériver les équations matière covariantes.
  - [x] Sur le vrai quotient D8 et la même action scalaire globale, construire
    `K` faible et son Jacobi `J` symétrique pour tous les champs lisses sous le
    contrat commun d'intégrabilité, puis les identifier exactement à la
    première et seconde variation. Isoler le coefficient temporel lorentzien
    strictement négatif ; sur le seul secteur statique positif, construire le
    Hilbert d'énergie, le Riesz fort, son domaine dense, son noyau nul et
    l'équivalence stationnaire/faible/forte. La dynamique lorentzienne complète
    n'est pas déclarée positive.
    - [x] Prolonger ce Riesz au complété statique comme opérateur identité
      borné auto-adjoint, prouver noyau nul, image totale fermée, critère
      Fredholm et indice zéro, puis identifier son pairing au Jacobi/Hessien de
      la même action. Ce gate exclut explicitement le secteur dynamique de sa
      portée et n'affirme aucune résolvante compacte.
  - [x] Sur la carte plate à métrique fixe, décomposer pointwise la variation
    holonomique en opérateur d'Euler scalaire et divergence du flux de bord.
  - [x] Après hypothèses explicites d'intégrabilité et
    `IntegratedScalarFluxVanishes`, identifier la variation intégrée et la
    dérivée déjà justifiée de l'action au pairing faible avec l'opérateur
    d'Euler plat.
  - [ ] Déduire l'annulation du flux intégré des conditions au bord retenues et
    promouvoir l'identité en équation covariante courbe.
- [x] Dériver les deux tenseurs de stress dans le modèle scalaire mesuré sous le contrat fonctionnel explicite.
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
  - [x] Projeter de façon typée la même variation indépendante globale vers
    les slots D9 effectivement fournis (métrique diagonale induite, jauge
    tangentielle, ghost `U(1)`, matière), et prouver que cette projection
    métrique n'est pas surjective vers les tenseurs symétriques D9 généraux.
  - [x] Construire les modes D10 tronqués comme de vraies troncatures des
    `ProductDiracMode`, avec multiplicité sphérique, période `|period|`, action
    PT exacte, spectre envoyé au régulateur et annulation chirale régulée finie.
  - [x] Alimenter localement le mode normal D9 par une vraie section lisse du
    fibré normal D8 ; prouver que la transition après un tour vaut `-1` et que
    le carré de chaque multiplicateur `Z4` reproduit ce signe. Aucune
    coordonnée scalaire globale canonique n'est revendiquée.
  - [ ] Fournir le ghost difféomorphe, l'identification SpinC, les métriques
    hors diagonale, puis prouver l'accord entre action, Hessien, développement
    modal et domaines au bord dans les contrats résiduels.

**Acceptation** : un espace de champs unique sert à l'action, au Hessien, au
complexe BRST, aux anomalies et aux conditions au bord.

## 5. Verrou 3 — bulk, frontières, joints et worldvolume LL

- [ ] Construire l'action EH des deux métriques sur la géométrie globale.
- [ ] Dériver sa première variation en coordonnées arbitraires.
- [x] Construire et varier les termes GHY sur toute famille finie de faces non nulles en jauge normale de Gauss.
  - [x] Pour toute famille finie pondérée de faces en jauge normale de Gauss,
    construire les courbes GHY exact-inverse et sommer leurs vraies dérivées.
- [x] Prouver l'annulation intégrée du flux EH+GHY pour ces faces et conditions au bord retenues.
  - [x] Prouver face par face puis après toute somme finie que la dérivée GHY
    annule exactement le flux de Palatini--Einstein en jauge normale de Gauss.
- [ ] Construire les termes de frontière nulle : inaffinité, expansion et
  contre-terme de reparamétrisation.
  - [x] Intégrer réellement le shift de reparamétrisation le long de chaque
    générateur nul orienté et l'identifier à sa transgression d'extrémités par
    le théorème fondamental du calcul intégral.
- [x] Définir un domaine variationnel admissible près de `Theta = 0`, en tenant
  compte de la non-différentiabilité déjà prouvée.
- [x] Construire les termes et orientations de joints sur toute stratification finie retenue.
  - [x] Sur une stratification finie, orienter les deux shifts de joint de
    chaque générateur nul et prouver leur annulation exacte avec le terme de
    face intégré.
- [x] Prouver la cancellation globale finie des transformations de reparamétrisation nulle.
- [x] Construire les champs LL globaux : métrique auxiliaire, mesure composite,
  champs de mesure et flux.
- [x] Intégrer l'action LL sur le worldvolume.
- [ ] Dériver ses PDE, contraintes et branche de noyau nul.
  - [x] Pour l'action LL globale effectivement sélectionnée, varier
    simultanément mesure et flux, prouver l'expansion cubique pointwise et
    intégrée pour toute mesure finie, dériver les deux coefficients d'Euler et
    montrer que leur annulation équivaut exactement au flux nul.
  - [x] Construire l'équivalence mesurable PT du throat et prouver la covariance
    exacte des champs, tangentes, densité, action, première variation,
    coefficients d'Euler et stationnarité LL pour toute mesure PT-invariante.
  - [ ] Introduire la dépendance différentielle et la métrique auxiliaire dans
    l'action LL physique, puis dériver la vraie PDE forte.
    - [x] Sur le vrai throat compact, construire sans hypothèse une famille
      tangentielle lisse finie génératrice, l'énergie différentielle LL et une
      dépendance non triviale à la métrique auxiliaire ; dériver les variations
      intégrées et l'équation faible stationnaire exacte. L'opérateur fort,
      la contraction lorentzienne intrinsèque et les flux restent ouverts.
    - [x] Symétriser cette même action différentielle par moyenne PT et prouver
      exactement l'invariance de l'action, de la variation, de l'équation
      faible et de l'espace stationnaire, pour toute mesure. Cette moyenne ne
      rend pas la frame elle-même intrinsèquement PT-équivariante.
      - [x] Dériver le Hessien de flux de cette même action PT, l'identifier à
        la linéarisation exacte du pairing faible, prouver symétrie, covariance
        PT et positivité de sa partie cinétique ; dériver aussi le Hessien brut
        de la métrique auxiliaire sans sur-revendiquer la positivité totale.
      - [x] Dans le secteur strictement positif `llMeasure > 0` et pour une
        mesure finie positive sur les ouverts, construire le Hilbert d'énergie
        dont le produit scalaire est exactement ce Hessien, son domaine lisse
        dense, l'extension faible, le représentant de Riesz fort et
        l'équivalence forte/faible avec noyau trivial. Aucune formule
        différentielle de type Stokes ni équivalence Sobolev externe n'est
        revendiquée.
        - [x] Prolonger ce représentant au complété comme opérateur borné
          identité du Hilbert d'énergie, puis prouver auto-adjonction, noyau
          nul, image totale fermée, critère Fredholm, indice zéro et égalité
          du pairing avec la linéarisation du Hessien de la même action. Ni
          résolvante compacte ni identification D10 n'est affirmée.
- [x] Prouver l'existence d'une branche throat non vide compatible avec les
  deux secteurs gravitationnels.
- [ ] Dériver les conditions de jonction et l'équilibre des flux.
  - [x] Pour deux champs scalaires globaux restreints à la vraie gorge,
    construire une action Robin quadratique, dériver sa première variation et
    prouver que la stationnarité impose la balance faible intégrée des deux
    flux ainsi que l'annulation intégrée du carré du résidu. Les conditions
    d'Israel, les dérivées normales géométriques et le cas nul restent ouverts.
    - [x] Dériver le Hessien bilinaire exact de cette même action, prouver sa
      symétrie, son signe et son noyau selon `k_+ + k_-`, puis l'identifier au
      linéarisé exact de l'opérateur de balance faible.
      - [x] Réaliser ce Hessien sur le vrai `L²` du throat comme
        `(k_+ + k_-) Id`, prouver auto-adjonction, noyau, image fermée, critère
        Fredholm explicite et indice zéro lorsque la somme est non nulle, puis
        identifier son pairing lisse au Hessien de la même action.
      - [x] Prouver sous mesure PT-invariante la covariance exacte des traces,
        flux, résidu, action, première variation et Hessien Robin avec échange
        `+/-` et `k_+/k_-`, puis entrelacer l'opérateur `L²` par l'isométrie PT.
  - [x] Construire le vrai flux normal scalaire comme `dφ` évalué sur un
    représentant du quotient tangent normal, avec splitting algébrique
    fibre-par-fibre, signe tordu à un tour, appariement global avec une section
    normale lisse, action et balance faible par stationnarité. Le pont vers la
    loi Robin est explicite et conditionnel ; splitting lisse, normal unitaire,
    Israel et jonctions nulles restent ouverts.
- [ ] Étendre le Stokes fini à une formule de Stokes géométrique pour données
  variables et toutes les strates.
  - [x] Assembler en un résidu stratifié fini unique les faces non nulles
    EH/GHY et les faces nulles/joints, puis prouver que ce résidu est nul.
- [ ] Classifier les termes de bord/null/joint admissibles à divergence près.

**Acceptation** : la variation complète bulk+frontières+LL ne laisse aucun flux
non contrôlé et produit les conditions de jonction annoncées.

## 6. Verrou 4 — complexe concret `K/J`, cohomologie et quotient

- [ ] Définir le vrai opérateur de compatibilité géométrique `K` sur les
  bundles Janus.
- [ ] Calculer sa dérivée de Fréchet `J` sur les espaces fonctionnels choisis.
  - [x] Dans le secteur LL différentiel PT construit, empaqueter le vrai
    opérateur d'Euler faible comme fonctionnelle linéaire sur les tests et son
    opérateur de Jacobi bilinéaire, prouver la linéarisation affine exacte,
    la symétrie de `J` et leur identification à la variation/Hessien de la même
    action. La topologie du dual, le `K` géométrique complet et `R/B` restent
    ouverts.
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
- [x] Prouver la fermeture de l'image dans le modèle pondéré choisi et isoler exactement le zéro-mode.
- [x] Construire le pairing/Hessien cible `H`, continu et auto-adjoint, sur l’échelle Sobolev de coefficients choisie.
  - [x] Sur l'échelle de coefficients Sobolev décalée, prendre le Hessien cible
    identité, continu, auto-adjoint et positif.
- [x] Instancier le pullback `Jᵀ H J` complet dans ce modèle de coefficients.
  - [x] Construire réellement `J† H J` comme opérateur continu, prouver la
    formule de pairing, symétrie, positivité, noyau égal à celui de `J` et
    positivité définie après retrait du zéro-mode.
  - [ ] Identifier ce pullback au Hessien de la même action Janus globale.
- [x] Construire le quotient normé topologique par `ker J` dans ce modèle périodique.
  - [x] Dans le modèle périodique de coefficients Sobolev décalés, construire
    une projection bornée du mode zéro, la scission topologique et le quotient
    normé par `ker J`, continûment linéairement équivalent aux représentants
    sans mode zéro.
- [x] Prouver continuité et non-dégénérescence de la forme descendue sur ce quotient périodique.
  - [x] Prouver la non-dégénérescence du pullback continu `J†J` sur ces
    représentants canoniques; l'identification au quotient global Janus reste
    ouverte.

**Acceptation** : un complexe global avec bord, cohomologie contrôlée et
Hessien physique réellement descendu.

## 7. P-D/P-E — classification naturelle globale

- [ ] Définir la catégorie Janus et les bundles source/cible naturels.
- [ ] Vérifier localité, régularité et réalisations holonomiques requises.
- [x] Construire le groupoïde différentiable des jets structurés.
  - [x] Construire la catégorie et le groupoïde d'action effectifs de deck D8,
    avec égalité dans le quotient caractérisée par l'existence d'une flèche.
  - [x] Construire les familles dépendantes source/cible, leur transport et le
    foncteur de représentation fourni vers les jets structurés.
  - [x] Prouver que chaque composante source/cible du groupoïde de deck est un
    difféomorphisme local sur les covers analytiques 4D et du throat 3D.
- [ ] Déterminer sa stratification d'isotropie.
- [ ] Construire les revêtements Spin de dimension pertinente.
- [ ] Dériver les données Cech/SpinC depuis l'atlas réel, et non depuis des
  transitions fournies.
- [ ] Construire les bundles vectoriels et principaux Janus globaux.
- [ ] Prouver l'accord des classes caractéristiques Spin/déterminant.
- [ ] Construire la descente effective et le théorème d'intégrabilité des jets
  d'ordre supérieur.
  - [x] Prouver existence et unicité de la descente `C∞` de toute application
    lisse invariante sous le deck vers le vrai quotient D8.
  - [x] Descendre les familles holonomiques structurées d'ordre bas fournies et
    préserver explicitement leur condition d'holonomie.
  - [x] Descendre leur réduction fournie `(II,F)` et prouver sa lissité sur le
    quotient effectif.
  - [ ] Étendre aux jets d'ordre supérieur arbitraire, à la représentation
    SpinC physique et à l'intégrabilité/extension à travers les isotropies.
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
- [x] Vérifier abstraitement que les variations induites utilisent la règle de chaîne et ne créent pas d’équations supplémentaires.
- [ ] Calculer la dérivée de l'opérateur d'Euler sur le domaine global.
- [ ] Prouver les conditions de Helmholtz non linéaires bloc par bloc.
- [ ] Reconstruire ou identifier l'action globale normalisée à partir de ces
  données.
- [ ] Prouver l'identité de Noether pour les difféomorphismes diagonaux.
- [ ] Dériver les deux identités de Bianchi avec échange matière/interaction et
  flux de frontière.
- [x] Déterminer dans le modèle réduit exact quand les conservations sectorielles se séparent réellement.
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
- [x] Descendre la seconde variation sur le quotient contraint périodique construit.
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
- [x] Identifier, pour l'opérateur diagonal du cercle sur tout `ℓ²(ℤ,ℂ)`, le
  domaine maximal du générateur fort à droite avec le domaine spectral de
  `D²`, prouver que ce dernier est exactement le domaine de composition
  `D ∘ D`, et identifier le générateur à `-D²`.
- [x] Prouver l'égalité avec le calcul fonctionnel abstrait `exp(-t D²)`.
  Pour le Dirac diagonal du cercle, le calcul spectral pur-point contractif
  est construit indépendamment du semigroupe, avec lois unité, produit et
  adjoint, puis son exponentielle gaussienne est identifiée exactement au
  semigroupe de chaleur. Cela ne fournit pas une API Borel générale pour tout
  `LinearPMap` auto-adjoint.
- [ ] Prouver les propriétés trace-class requises.
  - [x] Pour tout temps strictement positif du cercle normalisé, construire une
    expansion en opérateurs Fourier de rang un, prouver la sommabilité de leurs
    normes opérateur, l'égalité en norme de leur somme avec le semi-groupe et
    l'égalité de la trace nucléaire avec la trace spectrale déjà construite.
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
  - [x] Pour la transformée bornée du cercle, construire chaque vraie fibre
    `Hom(det coker, det ker)`, un frame algébrique non nul et la transition
    linéaire bijective de grande jauge entre les deux fibres d'extrémité.
  - [x] Topologiser ces fibres réelles, installer un `FiberBundle` et un
    `VectorBundle` complexes Mathlib, promouvoir la transition de grande jauge
    en homéomorphisme et descendre le clutching sur `AddCircle 1`.
  - [ ] Construire la ligne/gerbe globale et sa géométrie de
    Quillen/Bismut--Freed.
    - [x] La composante topologique de ligne est construite et globalement
      trivialisée pour le secteur cercle borné normalisé.
    - [x] Sur cette ligne cercle/Fourier choisie, construire une métrique
      hermitienne explicite et un clutching isométrique.
    - [x] Construire une connexion plate compatible et calculer exactement son
      transport et son holonomie unitaire `λ / |λ|`.
    - [x] Calculer la norme et la dérivée covariante de la section déterminante
      régularisée dans cette trivialisation.
    - [ ] Identifier cette géométrie choisie à la connexion de
      Quillen/Bismut--Freed d'une famille Janus globale et à son indice local.
- [ ] Calculer l'anomalie locale dans le régulateur commun.
- [ ] Calculer l'holonomie eta et l'anomalie globale.
- [ ] Comparer le représentant eta à la classe d'inflow.
- [ ] Prouver l'annulation PT/inflow pour le contenu de champs complet.
- [ ] Construire et trivialiser la section de partition lorsque permis.
  - [x] Construire sur la famille cercle une section déterminante régularisée
    distincte du frame Fourier, nulle aux crossings, non nulle à l'intérieur,
    à coordonnée continue et compatible au clutching d'extrémité.
- [x] Distinguer explicitement, dans les modèles finite-mode et cercle, le déterminant spectral positif D7 de la ligne déterminante.
  - [x] Séparer formellement la magnitude spectrale positive finite-mode de la
    section à valeurs dans la vraie ligne extérieure finite-mode.
  - [x] Sur la famille cercle infinie bornée, distinguer le frame Fourier
    partout non nul de la section déterminante régularisée qui s'annule aux
    crossings spectraux.
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

- [x] l'énoncé exact et sa portée sont documentés ;
- [x] le théorème compile sans `sorry`, `admit` ni axiome métier ajouté ;
- [x] les hypothèses restantes sont visibles dans le type du théorème ;
- [x] le gate est importé par la façade appropriée ;
- [x] le statut de façade correspond à la portée réelle du théorème ;
- [x] le build focalisé est vert ;
- [x] l'audit d'intégrité est vert ;
- [x] roadmap, dashboard et document canonique sont alignés ;
- [x] aucune conclusion globale n'est tirée d'un modèle fini, axial,
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
