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

Comptage mécanique de toutes les cases Markdown, à tous les niveaux :
**501 fermées sur 626 ; 125 ouvertes**.

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
        - [x] Promouvoir les équivalences linéaires fibre par fibre et leurs
          inverses en sections analytiques des deux hom-bundles ; dans chaque
          carte transportée, leurs matrices sont exactement l'identité. Le
          bundle transporté est donc lissement isomorphe au vrai normal.
        - [x] Pour toute forme quadratique continue intrinsèque sur ce bundle,
          construire les strates spacelike, timelike, null, non-null et joint,
          prouver ouverture/fermeture, disjonction, couverture, stabilité par
          changement d'échelle et inclusion du joint dans le null.
        - [x] Depuis l'unique contrat
          `ContinuousOrthogonalDifferentialNormalLift`, instancier cette forme
          par la vraie métrique Lorentz intrinsèque, prouver la loi quadratique,
          l'indépendance du représentant ambiant et fermer toute la
          stratification causale.
        - [x] Réduire la construction du relèvement orthogonal continu à un
          unique lemme local de projection dans les cartes normales : classe
          quotient préservée, orthogonalité métrique et continuité locale du
          carré. Le recollement global et la stratification en découlent.
        - [x] Construire le vecteur tangent de latitude sur le vrai cover du
          throat et calculer sa dérivée ambiante explicite : la direction
          normale standard brute est exactement `(e₀, 0)`.
        - [x] Rendre publiques l'application ambiante de la sphère et sa
          régularité, puis factoriser exactement la dérivée ambiante intrinsèque
          par la dérivée des coordonnées produit, avec une formule pointwise.
        - [x] Identifier explicitement l'image du tangent de latitude par la
          différentielle équivalente des coordonnées produit, calculer son
          image ambiante exacte `(e₀, 0)` et prouver que cette image et le
          vecteur tangent canonique sont non nuls.
        - [x] Pour la vraie métrique Lorentz intrinsèque du cover, prouver que
          ce vecteur est orthogonal à toute la différentielle du throat, que
          son carré vaut exactement `1`, et donc qu'il est spacelike et
          non-null. La projection régulière vers le quotient reste séparée.
        - [x] Construire explicitement ce lemme sur chaque carte normale
          canonique : la classe du normal quotient est non nulle, sa
          coordonnée scalaire est bijective, le relèvement représente la
          classe, est métriquement orthogonal et son carré vaut exactement le
          carré scalaire, dont le modèle local est continu.
          - [x] Prouver les lois exactes sous un tour de deck : renversement du
            paramètre normal, signe du tangent quotient après transport
            dépendant, invariance du modèle quadratique sous le cocycle
            `-id`, et égalité des carrés des deux relèvements locaux. Le
            recollement continu en une section globale reste ouvert.
            - [x] Étendre la loi de deck de la courbe quotient à tout
              `winding : ℤ` par le caractère `normalSignRepresentation` : les
              enroulements pairs agissent trivialement et les impairs par
              renversement du paramètre ; étendre aussi le `HEq` tangent et
              l'invariance du modèle scalaire quadratique à tout winding. Le
              recollement vectoriel global n'est pas revendiqué.
            - [x] Éliminer le cast caché au niveau cover en prouvant par `HEq`
              que le normal de latitude nommé est exactement sa dérivée brute
              transportée le long de l'égalité à latitude zéro.
            - [x] Combiner ce transport avec la règle de chaîne de la
              projection quotient pour identifier par `HEq` le normal
              quotient canonique et le tangent de la courbe de latitude.
            - [x] Transporter explicitement le tangent quotient vers la fibre
              canonique à latitude zéro, prouver que ce transport commute au
              `SMul ℝ`, puis établir le cocycle de signe du normal quotient
              canonique pour tout `winding : ℤ`. Le cocycle de la classe/lift
              et le recollement continu global restent ouverts.
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
  - [x] Construire depuis les cartes réelles du quotient les transitions
    tangentes ambiantes, leur différentielle inversible, le signe exact du
    déterminant et le cocycle d'orientation `ZMod 2`. La réduction quadratique,
    son identification au cocycle normal et le relèvement `Pin/SpinC` restent
    explicitement séparés par des contrats minimaux.
    - [x] Construire une forme quadratique euclidienne réelle 4D positive et
      non dégénérée sur le modèle, la transporter par chaque vraie transition
      tangente et obtenir les isométries quadratiques exactes. La compatibilité
      globale orthonormale et les lifts `Pin/SpinC` restent des contrats exposés.
      - [x] Construire depuis l'algèbre de Clifford la vraie action du groupe
        Spin sur les vecteurs, son équivalence linéaire, la préservation
        quadratique et le morphisme `Spin(Q) →* GL(4)`. L'extension Pin est
        isolée par son action tordue exacte ; seuls les lifts de transitions et
        leur cocycle Čech atlas-spécifique restent à fournir.
        - [x] Prouver le cocycle strict des vraies transitions tangentes et de
          leur réduction `O(4)`, composer tout lift Spin fourni, puis montrer
          que son défaut Čech appartient exactement au noyau de la projection.
          - [x] Prouver réellement que toute image de
            `ambientSpinProjection` a déterminant `+1`, par induction sur le
            groupe de Lipschitz et exclusion du grade impair Clifford.
            - [x] En déduire que tout lift d'une transition réduite impose
              effectivement `det = +1` et exclure tout lift Spin lorsque ce
              déterminant vaut autre chose.
          - [x] Prouver la surjectivité sur `SO(4)` par décomposition paire en
            réflexions non isotropes, puis construire les lifts de l'atlas.
            - [x] Isoler le datum exact de relèvement `SO(4) → Spin(4)` et
              prouver son équivalence à la surjectivité ; sous ce datum,
              caractériser point par point la liftabilité par `det = +1` et
              l'existence d'un choix atlas-wide par l'orientation de toutes
              les transitions. La régularité et la cohérence Čech des choix
              atlas-wide restent ouvertes.
              - [x] Construire explicitement dans l'algèbre de Clifford le
                relèvement Spin de toute paire de réflexions unitaires,
                identifier sa projection au produit exact des réflexions,
                puis étendre ce relèvement à toute liste finie de paires.
                Toute factorisation paire fournit ainsi un vrai lift Spin.
              - [x] Prouver Cartan--Dieudonné en dimension quatre avec la
                parité du déterminant, afin de fournir cette factorisation
                paire pour tout élément de `SO(4)`, puis construire sans
                hypothèse la surjectivité `Spin(4) → SO(4)` et une fonction de
                relèvement via `LinearIsometryEquiv.reflections_generate_dim`.
          - [ ] Trivialiser cohérement le défaut Čech noyau des lifts choisis.
            - [x] Sur chaque triple overlap fixé et pour trois lifts arbitraires,
              annuler exactement le défaut par la correction noyau canonique
              du troisième lift. La cohérence commune sur tout l'atlas reste
              ouverte.
              - [x] Prouver que cette correction canonique est l'unique
                translation noyau du troisième lift annulant le défaut local.
              - [x] Identifier structurellement le troisième lift ainsi corrigé
                au lift composé des deux autres overlaps.
                - [x] En déduire que cette correction canonique est indépendante
                  du lift initial choisi sur l'arête composée. Les changements
                  des deux arêtes constituantes et les quadruples overlaps
                  restent ouverts.
                - [x] Relever au sous-groupe noyau les lois de cobord sous
                  translation des deux arêtes constituantes, avec la conjugaison
                  exacte par le lift intermédiaire.
                  - [x] Prouver que le noyau commute avec toute l'algèbre de
                    Clifford, donc est central et abélien ; construire le défaut
                    d'un choix atlas-wide, son critère exact de complétion en
                    cocycle et la loi de Čech sur les quadruples overlaps. Il
                    reste à construire et régulariser ce choix puis à trivialiser
                    globalement ses défauts.
                  - [x] Empaqueter exactement normalisation et trivialité des
                    défauts noyau en une complétion Čech algébrique, puis
                    prouver son équivalence à un vrai lift de transitions et
                    qu'elle force l'orientation. Aucune continuité/lissité des
                    lifts choisis n'est déduite.
                  - [x] Utiliser la surjectivité `Spin(4) → SO(4)` pour choisir
                    automatiquement tous les lifts pointwise d'un atlas
                    orienté, construire leurs 1-cochaînes noyau et prouver le
                    critère exact de trivialisation. Il reste l'orientation
                    globale, cette classe Čech unique et la régularité.
- [ ] Identifier les classes caractéristiques et prouver les compatibilités
  entre racine déterminante, Spin et twist monopolaire.
  - [x] Prouver au niveau du relèvement normal que les deux caractères quart
    associés au fibré principal `Pin⁻(1)` construisent de vrais
    `FiberBundleCore`, reproduisent les deux cocycles racines, se carrent en
    demi-tour d'orientation pour tout enroulement et sont échangés par PT.
    Les classes du fibré tangent ambiant et le twist monopolaire restent ouverts.
    - [x] Prouver en outre que le produit des deux caractères normaux opposés
      vaut exactement `1` pour tout enroulement.
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
  - [x] En dimension quatre, couvrir tout point muni d'une diagonalisation
    réelle explicite à spectre strictement positif : construire la racine par
    similarité, prouver la positivité de ses quatre valeurs propres et son
    carré exact. L'indépendance du choix de base, le recollement global et les
    blocs de Jordan 4D généraux restent ouverts.
    - [x] Prouver que la racine par similarité est inchangée sous toute
      renormalisation inversible de la base propre qui commute avec la racine
      diagonale positive. L'indépendance sous changements de base généraux et
      le recollement restent ouverts.
      - [x] Montrer qu'il suffit que la renormalisation commute avec la matrice
        diagonale des valeurs propres : la positivité force alors la commutation
        avec sa racine positive et donne la même racine par similarité.
      - [x] Autoriser tout changement inversible mélangeant arbitrairement les
        vecteurs à l'intérieur d'un même espace propre répété et prouver que
        la racine par similarité reste inchangée.
      - [x] Comparer deux diagonalisation du même opérateur ayant le même
        spectre positif ordonné et prouver que leurs racines par similarité
        coïncident exactement. Le recollement global reste ouvert.
      - [x] Prouver la loi de conjugaison de la racine diagonale par toute
        matrice de permutation et l'invariance de la racine par similarité sous
        permutation cohérente de la base, de son inverse et du spectre.
        - [x] Construire explicitement la diagonalisation permutée, certifier
          ses deux identités d'inverse et sa cible, puis comparer deux
          diagonalisation arbitraires de même cible dont les spectres positifs
          diffèrent par permutation. Le recollement global reste ouvert.
  - [x] Construire une vraie strate de Jordan lorentzienne en dimension quatre,
    issue de deux métriques symétriques indépendantes : la racine réelle
    explicite se carre exactement au produit relatif et, pour paramètre non
    nul, celui-ci n'est pas diagonalisable. La classification et le recollement
    de tous les types de Jordan admissibles restent ouverts.
    - [x] Certifier réellement la signature `(3,1)` de toute cette famille par
      un repère nul inversible explicite et une congruence exacte avec
      `diag(-1,1,1,1)` pour chacune des deux métriques.
    - [x] Prouver la régularité de Sylvester sur toute cette strate : construire
      l'inverse bilatère fini de `H ↦ XH+HX`, identifier la tangente de racine
      comme vraie dérivée de Fréchet et prouver son unicité, y compris aux
      points non diagonalisables.
    - [x] Étendre cette racine à tout le locus invariant par similarité
      `(A-I)²=0`, prouver carré, continuité par strate et Sylvester bijectif,
      puis la recoller au sélecteur positif diagonalisable sur leur intersection
      exacte `{I}`. Les blocs d'indice supérieur et spectres non unipotents
      restent hors de cette union.
    - [x] Étendre encore au locus entier `(A-I)³=0` avec la racine
      `I+N/2-N²/8`, un témoin strict `N³=0, N²≠0`, un inverse de Sylvester
      polynomial, et un sélecteur continu par strate qui étend exactement le
      recollement d'indice deux. Seuls l'indice quatre et les spectres Jordan
      non unipotents restent hors de l'union actuelle.
    - [x] Fermer l'ultime locus unipotent possible en dimension quatre,
      `(A-I)⁴=0`, par `I+N/2-N²/8+N³/16` : carré, similarité, témoin strict,
      inverse de Sylvester polynomial, continuité, classification et extension
      exacte du recollement d'indice trois. Toutes les strates unipotentes
      `4×4` sont ainsi couvertes ; les spectres non unipotents restent ouverts.
    - [x] Rescaler cette fermeture à toute valeur propre réelle `λ>0` : pour
      `(A-λI)⁴=0`, construire la racine binomiale normalisée, prouver carré,
      similarité, continuité jointe en `(λ,A)`, Sylvester bijectif et accord
      exact à `λ=1`. Les spectres à plusieurs valeurs propres ou non positifs
      restent ouverts.
    - [x] Fermer la strate multi-valeurs propres de partition `2+2` : deux
      blocs Jordan à valeurs strictement positives arbitraires, racines
      binomiales bloc par bloc, transport/rebase par similarité, continuité et
      inverse de Sylvester par série finie. Les partitions positives `3+1` et
      `2+1+1`, ainsi que les spectres non positifs/complexes, restent ouvertes.
    - [x] Fermer les deux partitions positives restantes `3+1` et `2+1+1` :
      racines bloc par bloc, carré, rebase/similarité, continuité de strate et
      inverses de Sylvester par séries de Neumann finies. Toutes les partitions
      Jordan réelles strictement positives de dimension quatre sont couvertes
      par une présentation explicite ; l'existence d'une telle présentation
      pour toute matrice admissible reste à relier à l'API spectrale générale.
    - [x] Regrouper les cinq partitions `4`, `3+1`, `2+2`, `2+1+1` et
      `1+1+1+1` dans un type de présentation unique ; construire le sélecteur,
      prouver carré et Sylvester globalement sur cette somme, continuité sur
      chaque strate et exhaustivité combinatoire des partitions de quatre.
    - [ ] Déduire `HasPositiveRealJordanPresentation` d'hypothèses spectrales
      intrinsèques sur une matrice brute, sans fournir sa base de Jordan.
      - [x] Définir le charpoly scindé à racines réelles positives, dériver le
        même scindage/positivité pour le minpoly, exposer la décomposition
        Jordan--Chevalley disponible et réduire toute la fermeture brute à
        l'unique pont `PositiveRealJordanBasisBridge4`. Mathlib ne fournit pas
        actuellement la construction de la base de chaînes de Jordan.
      - [x] Pour le besoin plus faible d'existence d'une racine, fermer sans
        présentation tout le locus brut positif semi-défini par `CFC.sqrt`,
        carré exact, et réduire le résidu à spectre réel positif mais non PSD.
      - [x] Fermer en plus un vrai locus brut positif non PSD sans présentation :
        pour `(A-λI)(A-μI)=0`, `λ,μ>0`, construire la racine affine exacte
        `(A+√λ√μ I)/(√λ+√μ)`. Le cas `λ=μ` couvre un bloc Jordan répété de
        taille deux ; `canonicalJordan211Target λ λ λ` certifie explicitement
        que ce gain est non hermitien et non PSD.
      - [x] Fermer tout le locus brut à valeur propre positive unique
        `(A-λI)^4=0` par le polynôme de Taylor cubique exact de `sqrt`. Le bloc
        Jordan strict de taille quatre est dans ce locus et est prouvé non
        hermitien, non PSD et hors de toute relation quadratique.
      - [x] Fermer le vrai locus multivaleur
        `(A-λI)²(A-μI)²=0`, `λ,μ>0`, `λ≠μ`, par l'interpolant d'Hermite
        cubique explicite qui matche valeurs et dérivées de `sqrt`. Prouver
        `natDegree q ≤ 3`, la divisibilité de `q²-X` par les deux facteurs
        carrés puis par le minpoly, et `q(A)²=A`. Le témoin Jordan canonique
        `2+2` est non hermitien, non PSD et hors des loci quadratique et
        mono-valeur quartique.
      - [x] Fermer le locus `3+1` distinct positif
        `(A-λI)³(A-μI)=0` par le cubique qui matche le jet d'ordre deux de
        `sqrt` en `λ` et sa valeur en `μ`. Prouver les trois jets nuls du résidu,
        la divisibilité cubique puis linéaire, le passage au minpoly et
        `q(A)²=A`. Le témoin Jordan canonique `3+1` est non hermitien, non PSD
        et hors des loci quadratique, mono-valeur quartique et double-double.
        Le résidu exact est maintenant
        `PositiveOutsideKnownLociAndTripleSingleRootResidual4`.
      - [x] Construire uniformément l'interpolant cubique pour tout profil de
        multiplicité d'un minpoly scindé positif : `natDegree q ≤ 3` et
        `minpoly A ∣ q²-X`.
        - [x] Fermer le profil `2+1+1` par l'interpolant d'Hermite qui matche
          valeur et dérivée au nœud double et les valeurs aux deux nœuds
          simples, puis réduire le résidu exact au profil quatre-simples.
        - [x] Fermer le profil `1+1+1+1` par l'interpolant de Lagrange cubique,
          prouver les quatre évaluations, la divisibilité du résidu et
          `q(A)²=A` sans base propre choisie.
        - [x] Extraire les quatre racines positives avec multiplicité depuis le
          charpoly scindé, utiliser Cayley--Hamilton et classifier
          exhaustivement leurs égalités pour obtenir l'un des cinq
          annihilateurs déjà fermés. L'existence brute d'une racine réelle est
          ainsi inconditionnelle sur `PositiveRealSplitCharpoly4`.
        - [x] Renforcer cette fermeture brute en un sélecteur de racine
          Sylvester-régulière sans base de Jordan. Pour les quatre profils
          polynomiaux, `R=p(A)`, `R²=A` et `RX+XR=0` impliquent que `X` commute
          avec `A`, donc avec `R`; l'inversibilité issue du spectre strictement
          positif donne `X=0`, puis la dimension finie donne la bijectivité.
          Le profil mono-valeur quartique réutilise son inverse Sylvester
          explicite. Ainsi `HasSylvesterRegularRealSquareRoot` est clos sur
          tout `PositiveRealSplitCharpoly4`, sans résiduel de Jordan.
        - [x] Construire l'atlas IFT local associé à ce sélecteur régulier :
          ouverts source/cible à chaque centre, valeur centrale, carré exact
          et continuité sur l'ouvert cible, dérivée inverse-Sylvester au centre.
          Construire aussi l'ouvert de recouvrement où les deux branches
          restent dans leurs voisinages d'unicité croisés et y prouver leur
          égalité exacte. Aucun sélecteur global continu n'est déduit.
      - [x] Fermer le sous-secteur hermitien à spectre strictement positif par
        le théorème spectral de Mathlib : construire la présentation diagonale
        depuis `eigenvectorUnitary`, prouver sa cible exacte, en déduire
        `HasPositiveRealJordanPresentation` et une racine Sylvester-régulière.
        Cela couvre notamment toute matrice `PosDef` et réduit exactement le
        pont de présentation restant au secteur brut non hermitien ; seule
        cette forme explicite reste ouverte en général.
      - [x] Réduire ce dernier secteur à l'unique contrat plus élémentaire
        `PositiveRealNonHermitianJordanChainBasisResidual4` : une matrice réelle
        inversible de vecteurs de chaînes, son équation d'entrelacement et une
        des cinq partitions de `Fin 4`. À partir de ce contrat, dériver
        l'inverse et `HasPositiveRealJordanPresentation`. La racine exacte et
        la bijectivité de Sylvester sont désormais disponibles sans ce contrat.
      - [ ] Construire cette base réelle de chaînes `Fin 4` pour toute matrice
        non hermitienne dont le charpoly est scindé à racines strictement
        positives. Mathlib expose les espaces propres généralisés mais ne
        choisit pas encore leurs chaînes ; c'est uniquement le résidu de forme
        de Jordan explicite du secteur brut positif, pas un résidu d'existence
        ou de régularité Sylvester.
    - [x] Pour les spectres réels non positifs, prouver l'obstruction
      déterminant négatif et le no-go plus fort d'une valeur propre négative
      simple, exhiber un contre-exemple de déterminant positif sans racine,
      construire les racines réelles des blocs négatifs appariés diagonaux et
      Jordan `2+2`, puis formuler le critère exact de parité des blocs négatifs
      et d'admissibilité des blocs nuls. Son équivalence pour une matrice brute
      est réduite à l'unique pont de classification Jordan absent de Mathlib.
    - [x] Pour les paires propres complexes conjuguées, construire la
      représentation réelle `2×2`, la racine principale hors coupure et sa
      fermeture explicite sur l'axe négatif, prouver carré et continuité hors
      coupure, singularité/Sylvester à zéro, sommes `2+2`, bloc Jordan complexe
      non semi-simple et transport par similarité. Le passage d'un charpoly
      brut à cette présentation purement non réelle est isolé dans l'unique
      pont `PureNonrealJordanPresentationBridge4` absent de Mathlib.
      - [x] Éviter néanmoins toute présentation sur le locus brut vérifiant
        `(A-aI)²=-b²I`, `b≠0`, par une racine affine polynomiale exacte ; y
        inclure le bloc complexe répété `2+2` et isoler le seul complément.
    - [x] Unifier les régimes positif, réel non positif et purement non réel
      dans un certificat spectral direct, avec sélecteur de racine, transport
      par similarité, carré exact, classification de frontière et critère brut
      conditionnel exactement aux trois ponts de présentation ci-dessus.
      - [x] Remplacer, lorsque seule l'existence de racine est consommée, les
        deux ponts de présentation par `ReducedRawRootResiduals4`; réduire le
        critère Jordan à sa nécessité brute et à la suffisance hors des loci
        PSD/quadratique déjà fermés, avec sélecteur et carré exact.
- [x] Prouver l'inversibilité de Sylvester sur tout le domaine diagonal retenu.
  - [x] Construire un inverse continu bilatère de Sylvester en chaque point du
    sous-domaine diagonal global, par division par les sommes de racines
    propres strictement positives.
  - [x] Transporter explicitement cet inverse diagonal par similarité à toute
    présentation diagonalisable réelle à spectre strictement positif, et
    prouver les identités bilatères ainsi que la bijectivité de Sylvester.
    - [x] Promouvoir cet inverse en application linéaire continue, construire
      le témoin bilatère consommé par la théorie de Fréchet et obtenir la
      formule exacte de dérivée pour toute sélection locale différentiable.
- [x] Recoller les branches IFT locales sur tout le locus réel
  diagonalisable à spectre strictement positif (domaine admissible de ce
  sous-problème, sans extension aux strates de Jordan ni au domaine physique
  général).
  - [x] À chaque présentation réelle diagonalisable explicite à spectre
    strictement positif, construire la vraie branche IFT locale, prouver son
    carré exact au voisinage et identifier sa dérivée stricte à l'inverse de
    Sylvester transporté. Leur recollement sur le locus positif diagonalisable
    est clos ci-dessous.
    - [x] Prouver l'égalité des germes de deux branches ayant la même racine,
      notamment pour deux présentations de même cible à spectres positifs
      égaux ou permutés. Le recollement global sur le locus positif
      diagonalisable est clos ci-dessous.
      - [x] Déduire automatiquement la permutation de l'égalité des polynômes
        caractéristiques, supprimer l'hypothèse de correspondance spectrale,
        puis construire un sélecteur algébrique global indépendant de toute
        présentation sur le locus diagonalisable positif. Sa continuité et sa
        régularité restent séparées.
        - [x] Caractériser exactement la continuité du sélecteur global par
          l'accord local avec les branches IFT, prouver l'indépendance de
          présentation de l'inverse de Sylvester et obtenir la dérivée de
          Fréchet restreinte dès que cette continuité est fournie. Le seul
          input analytique restant est la stabilité spectrale locale qui
          implique cet accord.
          - [x] Réduire cette continuité matricielle à quatre fonctions
            scalaires : reconstruire exactement la racine globale comme
            fonction rationnelle de la cible et des quatre coefficients non
            dominants de son polynôme caractéristique, puis prouver que le
            dénominateur est partout inversible grâce au spectre positif. Il
            reste uniquement à prouver la continuité de ces coefficients
            symétriques du spectre racine non ordonné ; Mathlib ne fournit pas
            la continuité des racines d'un polynôme variable.
            - [x] Réduire encore les quatre continuités scalaires à une seule :
              dériver les quatre relations polynomiales exactes entre les
              coefficients caractéristiques de la cible et ceux de sa racine,
              prouver directement la continuité de `c₀`, puis celle de `c₁`
              et `c₂` dès que `c₃` est continue. Le résidu est exactement
              `c₃ = -tr(√A)`, sélectionné comme racine strictement négative
              d'une équation scalaire explicite à coefficients continus.
              - [x] Prouver sa continuité sans base propre continue : normaliser
                le spectre positif dans le cube compact `[0,1]⁴`, descendre la
                somme des racines carrées par le quotient des coefficients
                symétriques, puis dénormaliser. Les quatre coefficients de la
                racine sont donc continus sans hypothèse.
                - [x] Réinjecter ces coefficients dans la formule rationnelle
                  globale, prouver la continuité du sélecteur matriciel sur tout
                  le locus positif diagonalisable, sa stabilité IFT locale et
                  sa dérivée inverse-Sylvester exacte.
  - [x] Le recollement local et la dérivabilité inverse-Sylvester sont prouvés
    le long de tout relèvement continu fourni qui reste ponctuellement
    Sylvester-régulier.
  - [x] Recoller l'atlas IFT en un relèvement continu global unique sur le
    locus réel diagonalisable à spectre strictement positif : le sélecteur
    canonique y donne un carré exact, coïncide avec chaque branche IFT locale
    et est unique sur ce locus. Ceci ne construit aucun relèvement sur les
    strates de Jordan, les spectres non positifs ou le domaine physique général.
- [x] Contrôler, dans un certificat unique, la suite explicite retenue de
  témoins de frontière spectrale et de changements de branche : faces
  diagonales zéro/infini, collisions Jordan canonique, à similarité fixe,
  cisaillement mobile et double, régularisation par cadre singulier et deux
  changements de type. Ce certificat ne prétend pas classifier les chemins
  arbitraires.
  - [x] Pour toute présentation réelle diagonalisable à spectre strictement
    positif, construire un chemin continu remplaçant une valeur propre par
    zéro, prouver le carré exact jusqu'au bord et exhiber un noyau non nul de
    Sylvester au point limite.
    - [x] Sur le même locus, construire le chemin spectral `t⁻¹`, prouver son
      carré exact et montrer que sa coordonnée propre conjuguée vaut
      `√(t⁻¹)` et tend vers `+∞` lorsque `t → 0⁺`.
  - [x] Fermer le témoin canonique de collision Jordan
    `J₂(t) ⊕ 1 ⊕ 1`, `t → 0⁺` : construire la racine Hermite exacte avec
    coefficient nilpotent `1/(2√t)`, prouver la divergence de ce coefficient
    et de la norme, l'absence de limite ou prolongement matriciel fini, puis
    l'effondrement du mode de Sylvester `E₀₁` avec valeur propre `2√t → 0`.
    Ceci ne classe pas les collisions Jordan générales ni les `0/0` arbitraires.
    - [x] Transporter toute cette obstruction par une similarité réelle fixe
      arbitraire : carré, mode non nul, naturalité de Sylvester, absence de
      limite finie et de prolongement continu sont invariants par conjugaison.
    - [x] Fermer la collision simultanée à deux paramètres
      `J₂(t) ⊕ J₂(s) → J₂(0) ⊕ J₂(0)` : les deux coefficients nilpotents
      divergent indépendamment et deux modes de Sylvester linéairement
      indépendants dégénèrent. Similarités mobiles et changements de type
      Jordan restent ouverts.
    - [x] Fermer une première similarité mobile non constante explicite : le
      cisaillement polynomial `P(t)=I+tE₂₀` a un inverse exact, transporte
      le carré et le mode de Sylvester, conserve la divergence du coefficient
      `1/(2√t)` et exclut toute limite ou extension finie. Les similarités
      singulières ou non bornées, les cadres mobiles généraux et les changements
      de type Jordan restent ouverts.
    - [x] Fermer une première régularisation par cadre singulier explicite :
      `P(t)=diag(t,1,1,1)` transforme la divergence canonique en une limite de
      racine nilpotente finie non nulle. Son inverse diverge et son mode de
      Sylvester dégénère. Les cadres singuliers arbitraires et changements de
      type Jordan restent ouverts.
    - [x] Fermer deux témoins explicites de changement de type Jordan :
      `I+tE₀₁ → I` passe d'un bloc non semi-simple à l'identité avec racine
      affine lisse `I+(t/2)E₀₁` et valeur propre de Sylvester constante `2` ;
      en contraste, `t(I+E₀₁) → 0` a une racine exacte tendant vers zéro et
      une valeur propre de Sylvester tendant vers zéro. Ceci ne constitue ni
      une classification générale ni un atlas de branches.
  - [x] Sur le sous-domaine diagonal global, construire les chemins vers les
    deux faces : numérateur vers zéro donne une extension continue de la
    racine vers zéro et une dégénérescence explicite de Sylvester ; dénominateur
    vers zéro avec numérateur positif fait diverger ratio et racine vers
    `+∞`. L'unicité positive exclut tout changement de branche dans la
    composante. Les cas `0/0` et les matrices générales restent ouverts.
- [ ] Étendre la suite explicite retenue à tous les chemins matriciels `0/0`,
  aux similarités mobiles ou cadres singuliers arbitraires, puis classifier
  les changements généraux de type Jordan et construire l'atlas de branches.
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
    - [x] Étendre PT/échange à tout le paquet des champs indépendants
      actuellement construit, prouver l'involutivité et identifier exactement
      `PTMatchedIndependent` à son lieu de points fixes.
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
      - [x] Construire un témoin matriciel des relations attendues de deux
        coefficients formellement impairs (carrés nuls et anticommutation),
        puis prouver que le coefficient de crochet et son facteur BRST `-1/2`
        sont non nuls et de carré nul dans ce témoin. Ce modèle n'est pas une
        algèbre `Z₂` formelle avec règle de Koszul ; ce grading, le couplage au
        ghost tangent global, la nilpotence complète et BV restent ouverts.
      - [x] Descendre le ghost analytique au niveau `C∞`, fermer les vrais
        champs tangents globaux sous le crochet de Lie intrinsèque et prouver
        antisymétrie, bilinéarité et Jacobi. Le couplage gradué et la
        différentielle BRST non linéaire restent ouverts.
        - [x] Coupler réellement ce crochet et l'algèbre impaire par produit
          tensoriel, étendre le différentiel de coefficient à tout cet espace
          ghost gradué et prouver que son carré y est nul.
          - [x] Prouver que le terme quadratique tensoriel hérite exactement de
            l'identité de Jacobi du crochet lisse de ghosts.
          - [x] Construire sur les vrais scalaires `C∞` l'action bilinéaire des
            ghosts tangents, le différentiel de Chevalley--Eilenberg de degré
            zéro, puis son tensorisé avec le témoin matriciel de ces relations,
            son action sur le terme quadratique et l'entrelacement des
            différentiels nilpotents. Ce tensorisé n'est pas encore un module
            `Z₂` avec règle de Koszul.
          - [x] Pour l'algèbre de Lie tangentielle ordinaire, prouver
            `[L_X,L_Y]=L_[X,Y]` intrinsèquement via Leibniz, Jacobi et la famille
            tangentielle finie couvrante ; construire `d_CE¹` et fermer
            `d_CE¹ ∘ d_CE⁰ = 0` sur les vrais scalaires `C∞`. Le BRST non
            linéaire avec grading/Koszul et BV restent ouverts.
            - [x] Instancier ces vrais ghosts et scalaires comme algèbre de Lie
              et module de Lie Mathlib, identifier le `d_CE¹` construit au
              différentiel alterné standard et fermer aussi
              `d_CE² ∘ d_CE¹ = 0` pour toute 1-cochaîne. Ce complexe reste
              ordinaire : il ne fournit ni grading de Koszul ni antifields BV.
            - [x] Remplacer le témoin matriciel par une vraie algèbre extérieure
              graduée par `ZMod 2`, prouver par l'API Clifford que les
              générateurs sont impairs, non nuls, nilpotents et
              anticommutatifs, puis tensoriser le vrai crochet tangent D8 avec
              ses signes de Koszul. Le terme pur-ghost
              `s c = -1/2[c,c]` est explicite et son obstruction cubique de
              Jacobi est nulle. Le prolongement en dérivation sur tous les
              champs et le complexe BV restent ouverts.
              - [x] Sur la plus petite superalgèbre scalaire carrée-nulle
                réellement engendrée, construire un différentiel `Z₂` impair
                global avec involution de parité, règle de Leibniz de Koszul et
                carré nul ; relier son générateur à l'algèbre extérieure, puis
                fermer le carré BRST du scalaire à deux ghosts par l'identité
                `[L_X,L_Y]=L_[X,Y]` et l'obstruction cubique pure-ghost.
                - [x] Étendre ce calcul aux trois générateurs extérieurs et à
                  trois ghosts D8 lisses arbitraires : calculer les trois
                  crochets pairs, prouver l'annulation de l'obstruction
                  cubique totale et fermer exactement le carré BRST sur les
                  scalaires. Le prolongement en une dérivation globale sur
                  tous les champs, ainsi que BV, restent ouverts.
                  - [x] Pour toute triple de ghosts D8 fermée munie de ses
                    constantes de structure et de son différentiel CE,
                    construire sur
                    `ExteriorAlgebra ℝ (Fin 3 → ℝ) ⊗ C∞(D8)` la vraie
                    parité, le candidat BRST non nul, sa règle de Koszul et le
                    théorème ramenant la nilpotence globale aux deux facteurs
                    générateurs ; produire alors le vrai différentiel gradué
                    carré-nul sous ces données exactes.
                  - [ ] Construire une triple non abélienne fermée explicite de
                    ghosts lisses globaux sur le quotient D8 et décharger les
                    obligations Koszul, puis étendre ce différentiel aux
                    métriques, jauges, auxiliaires, antifields et à BV.
                    - [x] Construire les trois rotations spatiales `so(3)` sur
                      le cover, prouver tangence à `S³`, équivariance deck,
                      table de crochet et non-abélianité ; construire en plus
                      la descente lisse injective de toute section cover
                      équivariante et le pont vers les données Koszul fermées.
                    - [x] Réaliser effectivement ces rotations comme trois
                      sections tangentes `C∞`, prouver leur équivariance pour
                      tout deck, fidélité et non-nullité.
                    - [x] Prouver la naturalité du crochet sous la projection
                      quotient par un difféomorphisme radial local, puis
                      instancier sans hypothèse le triple quotient `so(3)`
                      fermé, fidèle, non nul et non abélien.
                    - [x] Construire pour ce triple le différentiel CE sur
                      l'algèbre extérieure : règles explicites des générateurs,
                      parité impaire, Leibniz de Koszul, carré nul et règle
                      ghost non linéaire ; instancier sans hypothèse
                      `ClosedThreeGeneratorGhostKoszulData`.
                    - [x] Corriger la convention de signe du différentiel total
                      par `D⊗id + action`, prouver parité, Leibniz et carré nul
                      global, l'instancier sans hypothèse et isoler exactement
                      le no-go de l'ancien signe sur les scalaires.
                    - [ ] Étendre ce différentiel corrigé aux métriques, jauges,
                      auxiliaires, antifields et à BV.
                      - [x] L'étendre composante par composante aux secteurs
                        linéaires actuels matière, coordonnées de jauge, ghosts
                        internes et auxiliaires ; prouver le carré nul par
                        secteur, sur leur produit et sur le pont issu de
                        `IndependentFields`.
                      - [x] Encoder les trois blocs LL/throat et ramener leur
                        carré nul à `LLThroatBRSTCompletion`.
                      - [x] Décharger la nilpotence explicite sur le throat.
                        - [x] Prouver que les trois flows de rotation préservent
                          l'équateur, commutent au deck, descendent au vrai
                          quotient throat et gardent la table `so(3)` ; construire
                          leur action scalaire, le différentiel corrigé et
                          l'instanciation conditionnelle des trois blocs LL.
                        - [x] Prouver l'unique contrat restant
                          `ThroatCorrectedKoszulNilpotence.square_zero` pour ce
                          différentiel explicite afin de rendre
                          `LLThroatBRSTCompletion` inconditionnel.
                      - [x] Restreindre les huit magnitudes métriques diagonales
                        positives au throat, passer aux coordonnées logarithmes,
                        construire l'action `L_X log m`, sa courbe exponentielle
                        globalement positive et le BRST métrique impair,
                        Leibniz et carré nul, puis le combiner aux trois blocs LL.
                      - [x] Construire un premier doublet fini champ/antifield à
                        parité décalée, son BRST impair carré nul et son pairing
                        canonique bilinéaire.
                      - [x] Fermer un vrai modèle maître BV fini de dimension
                        `32` : complexe CE métrique non nul, anticrochet impair
                        canonique en coordonnées de Darboux, action maîtresse
                        non triviale, équation maîtresse classique `(S,S)=0`,
                        génération du BRST carré nul et plongement exact dans
                        le doublet throat champ/antifield.
                        - [x] Promouvoir ce modèle fibre par fibre aux champs
                          `C∞` du vrai throat : BRST lisse carré nul, densité
                          maîtresse lisse, CME et génération hamiltonienne
                          pointwise, action intégrée canonique et témoin non nul.
                          - [x] Dériver exactement la première variation de
                            l'action intégrée sur les lignes affines, l'identifier
                            aux gradients/BRST, construire l'anticrochet impair
                            des fonctionnelles ultralocales analytiques et
                            prouver la CME intégrée.
                          - [x] Fermer le dernier contrat de mesure : prouver
                            que le PT du throat préserve la mesure canonique
                            depuis sa présentation `S² × Ioc`, puis rendre
                            inconditionnelles la covariance PT de l'action
                            maîtresse intégrée, de sa première variation, de la
                            valeur fonctionnelle représentée, de l'anticrochet
                            et de la CME intégrée.
                        - [x] Promouvoir séparément la même fibre BV finie de
                          dimension `32` aux champs `C∞` du vrai quotient
                          spacetime D8, avec BRST lisse carré nul, compatibilité
                          de restriction au throat, action canonique non nulle
                          et CME pointwise/intégrée. Cette étape reste
                          ultralocale à fibre constante et ne construit pas le
                          BV des métriques tensoriales générales.
                          - [x] Dériver sur le spacetime la première variation
                            pointwise et intégrée, l'expansion quadratique et la
                            vraie dérivée directionnelle ; transporter aussi
                            l'anticrochet des fonctionnelles analytiques
                            ultralocales et prouver leur CME intégrée.
                          - [x] Prouver que la réflexion ronde `S³` et
                            `t ↦ period-t` préservent la mesure spacetime
                            canonique poussée au quotient, puis rendre
                            inconditionnelles l'involution PT, sa commutation
                            au BRST, la covariance de l'action maîtresse et la
                            CME intégrée de ce modèle ultralocal.
                            - [x] Fermer les lois PT fibre exactes de la première
                              variation, de la valeur ultralocale représentée et
                              de l'odd antibracket, puis leur covariance intégrée
                              et celle de la CME avec la même mesure canonique.
                      - [x] Étendre cette fermeture au vrai cône spacetime
                        diagonal strictement positif : huit logarithmes lisses,
                        ghosts et antifields couplés, BRST corrigé carré nul,
                        odd bracket, action non nulle, CME pointwise/intégrée et
                        covariance PT exacte.
                      - [ ] Étendre la fermeture tensorielle générale désormais
                        ultralocale aux termes dérivatifs et aux fonctionnelles
                        non locales/complétées avec équation maîtresse
                        fonctionnelle.
                        - [x] Installer le premier niveau tensoriel général :
                          variations symétriques lisses et antifields, doublet
                          BRST impair carré nul, pairing pointwise relevé par
                          la métrique de fond et odd antibracket gradué, puis
                          l'attacher au paquet indépendant. Les variations
                          affines ne sont pas prouvées lorentziennes et aucune
                          CME fonctionnelle n'est revendiquée.
                          - [x] Munir ce premier niveau d'un PT/échange
                            involutif commutant au BRST et prouver la covariance
                            pointwise du pairing relevé et de l'odd bracket.
                            - [x] Construire le master bulk tensoriel général
                              ultralocal `1/2 ⟨h⁺,h⁺⟩` avec les vraies métriques
                              de fond : opérations affines et bilinéarité,
                              expansion exacte et vrai `HasDerivAt`, génération
                              de `(h⁺,0)`, témoin intrinsèque d'action `4 ≠ 0`,
                              covariance PT/échange et CME pointwise.
                            - [x] Intégrer ce master et son odd bracket représenté
                              contre `intrinsicCanonicalLorentzVolumeMeasure` :
                              obligations `L¹` et contrat de continuité
                              explicites, expansion affine et gradient intégrés,
                              covariance PT/échange par préservation de mesure et
                              CME intégrée. Les termes dérivatifs/non locaux et la
                              CME fonctionnelle générale restent ouverts.
                            - [x] Restreindre réellement variations et
                              antifields par l'inclusion du throat en tenseurs
                              symétriques lisses ; prouver le BRST de bord carré
                              nul, sa commutation à la trace, le matching
                              PT/échange fonctionnel, le transport de la
                              condition de Dirichlet du paquet complet et la
                              covariance de l'odd bracket pointwise au niveau
                              du paquet.
                              - [x] Sur la trace non dégénérée de la métrique
                                intrinsèque PT-fixe, instancier le vrai inverse
                                musical pointwise, relever variations et
                                antifields, définir le pairing et l'odd bracket
                                intrinsèques, prouver leur compatibilité avec
                                les traces bulk et leur covariance PT/échange,
                                puis construire l'action ultralocale
                                `S∂ = 1/2 ⟨h⁺,h⁺⟩`. Prouver la bilinéarité du
                                pairing, son expansion quadratique exacte sur
                                toute ligne affine et le vrai `HasDerivAt`
                                égal au pairing avec `antifieldGradient` ;
                                exhiber le témoin métrique intrinsèque avec
                                action `3 ≠ 0`, puis fermer la génération du
                                doublet `(h⁺,0)` et la CME pointwise.
                                L'antibracket fonctionnel, les termes dérivatifs
                                et la CME fonctionnelle restent ouverts.
                                - [x] Isoler l'obligation exacte `L¹` des
                                  densités et un contrat global de continuité
                                  suffisant, puis intégrer contre la mesure
                                  canonique l'action et l'odd bracket
                                  représenté. Sous les trois hypothèses `L¹`
                                  base/base, base/variation et
                                  variation/variation, fermer l'expansion
                                  quadratique intégrée et le vrai `HasDerivAt`
                                  égal au pairing avec `antifieldGradient` ;
                                  prouver aussi la covariance PT/échange et la
                                  CME intégrée représentée. Le contrat de
                                  continuité/champ inverse lisse n'est pas
                                  déchargé et aucune CME fonctionnelle générale
                                  ou dérivative n'est revendiquée.
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
        intrinsèque reste ouverte ; la trace du graphe `H¹` pour les volumes
        canoniques physiques est maintenant fermée ci-dessous.
      - [x] Instancier le graphe `H¹` avec les volumes canoniques physiques du
        spacetime et du throat, prouver densité/complétude et ramener exactement
        l'existence de la trace continue à l'unique inégalité lisse
        codimension-un `CanonicalPhysicalH1TraceBound`, puis prouver cette
        inégalité et construire la trace canonique inconditionnelle.
        - [x] Prouver l'inégalité de trace ponctuelle FTC exacte en dimension
          normale un, puis sa version intégrée fibre-par-fibre par Fubini.
          - [x] Construire la latitude équatoriale tordue, son signe sous la
            réflexion/deck, le collier quotient analytique et ses slices
            normales à dérivée continue.
          - [x] Identifier le volume canonique du throat au pushforward exact
            de `S² × I_t`, prouver l'intégrabilité du carré de trace et son
            identité de norme `L²` avec l'intégrale latitude.
          - [x] Reconstruire exactement la dérivée normale par le repère global
            fini, prouver somme des poids égale à un, poids maximal au moins
            `1/card`, puis la borne ponctuelle par la norme du frame et la norme
            `L1` des coefficients normaux locaux.
          - [x] Instancier `CanonicalLatitudeCoareaBound` par la formule de
            coaire physique pour `Measure.toSphere`.
            - [x] Construire la mesure produit du collier, prouver la
              continuité jointe de la latitude, l'intégrabilité
              inconditionnelle de l'énergie de frame, la réduction Fubini/map,
              l'identité avec la norme du premier jet et la borne de densité
              `≤ 3 × jet`; en déduire `CanonicalLatitudeCoareaBound` depuis
              une unique domination de mesures explicite.
            - [x] Prouver
              `CanonicalLatitudeMeasureToSphereCoareaDomination`, c'est-à-dire
              la domination du pushforward du collier par
              `cos(1)⁻² • intrinsicCanonicalLorentzVolumeMeasure`, via une
              désintégration radiale/sphérique puis polaire explicite.
              - [x] Factoriser exactement le collier par le quotient, identifier
                le volume intrinsèque comme pushforward du domaine fondamental
                et réduire ce contrat à
                `CanonicalLatitudeFundamentalMeasureDomination` avant quotient.
              - [x] Réassocier exactement les trois facteurs, conserver la
                mesure temporelle par produit et déduire
                `CanonicalLatitudeFundamentalMeasureDomination` d'une unique
                inégalité de latitude sphérique pure.
              - [x] Réduire `CanonicalPositiveLatitudeMeasureDomination` à
                la formule de pushforward pondérée exacte, en prouvant la
                minoration uniforme du jacobien `cos(normal)²` sur `Ioc(0,1)`.
                - [x] Réduire `CanonicalPositiveLatitudeWeightedMapFormula`
                  à `CanonicalPositiveLatitudeEuclideanConeJacobianFormula`,
                  une identité de volume du cône euclidien 4D sans mesure
                  sphérique cible ; `Measure.toSphere_apply'` ferme ensuite
                  formellement toute la chaîne.
                  - [x] Caractériser exactement l'image comme la bande
                    `x₀ ∈ Ioc(0,sin 1)`, construire l'inverse `arcsin`/queue,
                    l'homéomorphisme et l'équivalence mesurable du collier.
                  - [x] Fermer directement le cône par le split orthonormal
                    `ℝ⁴ ≃ ℝ³ × ℝ`, la désintégration `S² × r²dr`, les
                    coordonnées polaires planes, l'identification exacte de
                    l'image et `∫₀¹ r³ dr = 1/4`. Le certificat de chart
                    générique reste une API alternative, pas une obligation.
          - [x] Instancier `CanonicalNormalFrameReconstructionBound` par une
            borne compacte uniforme des coefficients normaux et leur
            intégrabilité ; sa recombinaison avec la coaire est déjà fermée.
            - [x] Sous `CanonicalLatitudeNormalLiftContinuous`, prouver par
              compacité la borne uniforme des coefficients, l'intégrabilité,
              la domination énergétique et construire tout le package B.
            - [x] Identifier `canonicalLatitudeNormalLift` au `tangentMap` du
              collier sur la section verticale lisse et réduire sa continuité
              au caractère `C¹` joint de la latitude sphérique élémentaire.
              - [x] Prouver `EquatorialLatitudeJointContMDiffOne` en fait en
                classe `C∞`, puis construire B inconditionnellement.
          - [x] Combiner la reconstruction normale inconditionnelle et la
            coaire pondérée en la borne et l'opérateur de trace canoniques,
            prouver l'accord sur les champs lisses et l'existence, désormais
            sans argument conditionnel grâce à la formule radiale--polaire.
          - [x] Définir l'espace de Dirichlet physique homogène comme le noyau
            de cette trace, puis prouver fermeture, complétude, non-vacuité,
            caractérisation exacte et accord avec les champs lisses de trace
            canonique `L²` nulle.
          - [x] Construire une renormation hilbertienne canonique du graphe
            de premier jet par produits finis `ℓ²`/`WithLp 2`, fermer l'image
            des jets lisses et prouver une équivalence linéaire continue avec
            la graph-norme existante, compatible avec l'inclusion lisse. Cela
            ne constitue pas encore une identification Sobolev intrinsèque.
            - [x] Transporter la trace physique dans cette renormation,
              prouver que son noyau de Dirichlet est un Hilbert fermé, construire
              sa projection orthogonale contractante et la décomposition
              orthogonale, puis l'identifier exactement au noyau graph-normé.
      - [x] Plonger le vrai cœur scalaire statique dans le graphe `H¹`
        existant, prendre sa clôture complète et prouver que le pont continu
        depuis le Hilbert d'énergie existe si et seulement si la borne de
        comparaison des deux normes est satisfaite. L'égalité avec tout le
        graphe est exactement équivalente à une densité statique séparée ;
        aucune identification Sobolev n'est postulée.
      - [x] Remplacer la borne brute énergie-vers-graphe par un contrat
        d'ellipticité uniforme ponctuel : dériver les minorations positives
        uniformes des coefficients, construire la racine de densité dans
        `L²`, prouver l'égalité exacte de norme puis le pont continu vers le
        graphe `H¹`. Seule l'instanciation géométrique des coefficients locaux
        du repère tangent fini dans les directions holonomes reste à dériver.
        - [x] Dériver automatiquement les bornes supérieures uniformes des
          magnitudes et la coercivité holonome, puis prouver qu'un contrat
          purement géométrique de contrôle du repère tangent implique le
          contrat d'ellipticité uniforme. L'instanciation du changement de
          repère continu uniformément borné reste ouverte.
        - [x] Réduire ce dernier changement de repère à des coefficients
          continus sur un recouvrement fermé fini : la compacité produit
          automatiquement une borne carrée uniforme et ferme le pont jusqu'à
          l'ellipticité. Seule la construction de ces données depuis les
          trivialisations locales actuellement privées reste ouverte.
        - [x] Exposer les supports fermés finis de la partition tangentielle et
          réduire leur instanciation à
          `FiniteSmoothTangentFrameRawPatchContinuity`, qui ferme ensuite
          automatiquement les coefficients locaux et l'ellipticité uniforme.
        - [x] Reformuler le côté graphe dans les trivialisations fixes : prouver
          l'égalité pointwise exacte entre la norme du jet du vrai repère fini
          et le jet des composantes localisées par la partition, sans hypothèse
          de continuité des coordonnées brutes.
        - [x] Construire une densité intrinsèque positive de remplacement,
          uniformément équivalente à la densité fixe-localisée sur le quotient
          compact, puis en déduire sans hypothèse la domination d'énergie et
          l'ellipticité uniforme du graphe pour le repère lisse fini.
        - [ ] Identifier en plus cette densité de remplacement à la densité
          jacobienne holonome historique fondée sur `chartAt p`. Ce verrou est
          exactement la transition variable `fixed anchor → chartAt p`, que
          Mathlib ne contrôle que lorsque les deux cartes sont fixes.
          - [x] Réduire ce verrou à la continuité de chaque coefficient
            holonomique scalaire du générateur partitionné uniquement sur son
            propre support fermé ; cette hypothèse suffisante localisée produit par
            compacité une borne globale explicite, le contrôle quadratique et
            toute la domination d'énergie. Seule cette continuité localisée
            reste à extraire de l'API `chartAt` variable.
            - [x] Prouver sans hypothèse que les coordonnées dans chaque
              trivialisation fixe sont `C∞`, que tous les changements entre
              deux centres fixes sont continus, et identifier exactement le
              coefficient brut à la diagonale variable
              `p ↦ tangentCoordChange anchor p p`. La continuité de cette
              diagonale à second centre variable est désormais l'unique input
              de ce sous-verrou et implique directement la domination.
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
  - [x] Sur les vrais deux-tenseurs covariants du quotient, définir la courbe
    de pullback et son générateur infinitésimal tensoriel comme dérivée de
    Fréchet, avec sa formule d'évaluation sous le contrat différentiable exact.
- [x] Définir exactement la symétrie PT/échange sur tous les champs de
  coefficients construits et une condition de Dirichlet lisse PT-compatible.
  - [x] Définir cette symétrie comme une équivalence involutive exacte sur les
    paires de champs de coefficients lisses du quotient 4D.
  - [x] Identifier les paires PT-matched aux points fixes de cette équivalence
    et prouver leur non-vacuité.
  - [ ] Étendre l'action aux métriques générales, matière, jauge, ghosts,
    auxiliaires et conditions au bord retenues.
    - [x] Étendre simultanément PT/échange aux métriques diagonales, matière,
      jauge, ghosts, auxiliaires et blocs LL/throat du paquet indépendant
      actuel ; construire leurs données de bord lisses composante par
      composante, prouver l'équivariance exacte de la trace et la préservation
      de la condition de Dirichlet complète. Les métriques tensoricielles
      générales et les antifields/BV restent séparés.
    - [x] Remplacer les deux métriques diagonales de ce paquet par deux
      `SmoothGeneralLorentzMetric`, étendre simultanément PT/échange à tous les
      secteurs indépendants non métriques et prouver involutivité, équivariance
      de leurs traces au throat et stabilité de leurs conditions de Dirichlet.
      La restriction/trace au bord des métriques générales est maintenant
      incluse dans le paquet et sa naturalité tensorielle PT/échange est
      fermée ci-dessous ; le paquet de bord variations/antifields est fermé
      dans le bloc BV. L'inverse, le pairing/bracket et la CME ultralocale sont
      maintenant fermés pour la trace non dégénérée de la métrique intrinsèque
      retenue ; l'inversion des restrictions générales, l'antibracket
      fonctionnel et les termes dérivatifs restent explicitement ouverts.
    - [x] Restreindre tout `SmoothGeneralLorentzMetric` par le `mfderiv` de la
      vraie inclusion du throat en un deux-tenseur covariant symétrique `C∞`,
      étendre le paquet de bord par les deux traces métriques, et prouver que
      leur non-dégénérescence équivaut exactement à l'absence de radical
      tangentiel.
      - [x] Prouver pointwise la naturalité PT de la restriction métrique via
        la différentielle équivariante de l'inclusion, puis la loi exacte
        PT/échange des deux traces.
        - [x] Définir une relation fonctionnelle de références métriques au
          bord par leurs valeurs PT/échange pointwise, prouver unicité du
          résultat lisse, préservation de la non-dégénérescence et transport
          exact de la condition de Dirichlet du paquet complet. Le pullback
          lisse arbitraire de tenseurs du throat n'est pas construit.
        - [x] Prouver que la différentielle PT est une équivalence linéaire,
          que le pullback tensoriel pointwise préserve et reflète la
          non-dégénérescence, puis que `HasNoTangentialRadical` est invariant
          sous PT et sous PT/échange. Le pullback lisse d'un tenseur de throat
          arbitraire reste séparé.
      - [x] Pour la métrique Lorentz intrinsèque retenue, utiliser le normal
        quotient local explicite pour scinder tout tangent ambiant et prouver
        `HasNoTangentialRadical`, la non-dégénérescence de sa trace au throat
        et son empaquetage en `SmoothNondegenerateThroatMetric`. La
        classification de toutes les métriques générales reste ouverte.
        - [x] Prouver la naturalité publique de la dérivée ambiante sous
          renversement du temps, l'isométrie exacte du tenseur cover et la
          naturalité des différentielles de projection ; par unicité de la
          descente, conclure que la métrique intrinsèque et la paire de deux
          secteurs sont des points fixes PT, et que sa trace throat reste fixe
          et non dégénérée.
    - [x] Sur les champs bruts de deux-tenseurs covariants généraux, construire
      le pullback par la vraie involution PT analytique, prouver l'involution
      différentielle exacte, l'échange des deux secteurs et la préservation de
      la symétrie, de la non-dégénérescence et de la signature `(3,1)`.
      - [x] Bundler ce pullback en section `C∞` sous l'unique contrat local
        `AnalyticPTTensorPullbackLocalSmoothness`, puis prouver involution et
        préservation du sous-domaine lorentzien lisse.
      - [x] Décharger inconditionnellement ce contrat local dans les
        trivialisations du bundle `Hom(TM, Hom(TM, ℝ))` : les coordonnées
        de `mfderiv PT` sont lisses et le pullback est la double précomposition
        exacte dans le bundle Hom imbriqué. Le musical tensoriel lisse et BV
        restent séparés.
        - [x] Transporter aussi l'équivalence musicale attachée au même
          tenseur, construire le pullback PT involutif de la vraie
          `SmoothGeneralLorentzMetric`, l'échange des deux secteurs et prouver
          la covariance pointwise de la densité scalaire holonomique avec
          champ et famille tangentielle transportés.
          - [x] Intégrer cette densité contre la mesure lorentzienne canonique
            du quotient, prouver le transport exact de l'intégrabilité et
            l'invariance PT de l'action générale. La famille tangentielle reste
            un input explicite et cette mesure de référence n'est pas déclarée
            volume canonique de toute métrique générale.
            - [x] À métrique générale et famille tangentielle fixes, dériver
              l'expansion quadratique pointwise et intégrée de la ligne
              scalaire affine sous le contrat minimal d'intégrabilité des
              trois coefficients, identifier la première variation à la vraie
              dérivée de l'action et prouver sa covariance PT pointwise,
              intégrée et au niveau de l'intégrabilité.
- [x] Construire l'action matière holonomique covariante en dimension quatre.
  - [x] Pour une métrique lorentzienne tensorielle générale munie de son
    isomorphisme musical exact, construire pointwise l'inverse, le Gram,
    `sqrt(|det|)`, `p = dφ`, la densité scalaire du même champ et son expansion
    variationnelle quadratique exacte.
    - [x] Prouver la naturalité exacte de la contraction, du Gram, du
      déterminant-volume et de la densité sous changement de frame, puis la
      spécialiser au vrai `mfderiv` d'un difféomorphisme D8 et à la règle de
      chaîne de `dφ`.
      - [x] Sous le contrat exact fournissant le pullback lisse de la métrique
        générale, transporter simultanément tenseur/musical, scalaire, famille
        tangentielle et mesure poussée par l'inverse ; prouver la covariance
        pointwise, le transport iff de l'intégrabilité, l'invariance intégrée
        et le corollaire direct PT/difféomorphisme plus échange des secteurs.
      - [x] Sur une orbite lisse fournie avec certificats de pullback métrique
        à tout paramètre, prouver la constance et la dérivée nulle de l'action,
        puis identifier cette dérivée au pairing de l'opérateur de Noether
        scalaire sous le contrat exact et non vacu de première variation.
      - [x] Construire sans contrat le pullback tensoriel lisse pour tout
        difféomorphisme D8, transporter l'isomorphisme musical et la signature
        lorentzienne, puis fournir automatiquement le certificat métrique exact.
      - [x] Définir `sharp(dφ)`, une interface intrinsèque divergence/flux avec
        identité d'IPP exacte, puis prouver sous son contrat que la première
        variation générale vaut le pairing Euler faible plus le flux, que flux
        nul équivaut à la stationnarité faible, et spécialiser le tout à la
        métrique intrinsèque D8.
      - [ ] Décharger géométriquement cette interface par une vraie formule de
        Stokes/IPP et le flux normal retenu, puis promouvoir l'identité de
        Noether intégrée en courant local avec assez de ghosts tests.
        - [x] Construire le flux normal concret sur le throat,
          `trace(ψ) · dφ(n) = trace(ψ) · g(sharp(dφ), n)`, puis prouver son
          annulation pointwise et intégrée pour toute variation Dirichlet
          homogène; raccorder cette annulation au gate Euler faible dès que le
          boundary functional fourni est réalisé par ce flux.
        - [x] Sur le collier latitude canonique, appliquer la vraie IPP
          `intervalIntegral` fibre par fibre puis contre la mesure canonique,
          identifier le terme intérieur à `mvfderiv` sur le normal et obtenir
          l'IPP faible sans bord pour les variations Dirichlet aux extrémités.
          Le Stokes global sur tout le bulk reste séparé.
          - [x] Identifier le pairing métrique `g(sharp(dφ), n)` à cette
            dérivée normale, construire le flux orienté aux deux extrémités et
            l'interface divergence/bord exacte du collier, puis prouver la
            stationnarité fibre par fibre et mesurée sous Euler--Dirichlet.
            L'adaptateur vers une interface globale reste conditionné à sa
            spécialisation ; le Stokes global et un normal métrique global du
            throat one-sided ne sont pas affirmés.
        - [x] Construire sur ce collier le courant scalaire antisymétrique de
          Green--Wronskian et prouver que sa dérivée est exactement le pairing
          antisymétrique des deux résidus d'Euler de même masse.
          - [x] En déduire sa constance pointwise puis mesurée pour deux
            solutions d'Euler de même masse.
          - [x] Identifier son saut entre les extrémités à
            l'antisymétrisation du boundary functional concret de l'IPP.
          - [x] Prouver son annulation pointwise puis mesurée pour deux
            solutions d'Euler homogènes de Dirichlet.
          - [x] Promouvoir ce Wronskien en véritable courant tangent du
            quotient le long du collier latitude canonique, porté par son
            normal intrinsèque unitaire spacelike ; prouver que son flux
            métrique est exactement le courant de Green, qu'il est localement
            conservé pour deux solutions d'Euler et qu'au throat il s'identifie
            au pairing concret des `mvfderiv` normaux. Ceci ne construit pas un
            courant covariant en dimension quatre.
        - [x] Construire sur ce collier l'énergie scalaire autonome
          `(φ')² + m²φ²` et prouver que sa dérivée est exactement
          `2φ'` fois le résidu d'Euler.
          - [x] En déduire sa conservation fibre par fibre puis après
            intégration sur la base pour toute solution d'Euler, ainsi que son
            saut nul entre les extrémités.
          - [x] Prouver sa positivité lorsque `m² ≥ 0`.
          Ce résultat est uniquement un témoin local unidimensionnel de
          conservation stress-énergie, pas la divergence covariante du tenseur
          de stress en dimension quatre.
          - [x] Identifier exactement cette énergie à deux fois la composante
            normale-normale du tenseur de stress scalaire général sur le jet
            projeté du collier, puis prouver que cette composante a dérivée
            nulle et reste constante sous l'équation d'Euler du collier.
            Cette conservation est strictement locale au collier.
        - [ ] Étendre le courant tangent canonique du collier en courant de
          Noether local covariant en dimension quatre sur le bulk, avec assez
          de ghosts tests, puis établir le Stokes global correspondant.
    - [x] Définir l'espace fonctionnel régulier où sharp, frame, volume et
      différentielle scalaire varient lissement, prouver la lissité et
      l'intégrabilité de la densité sur toute mesure finie, construire l'action
      globale et dériver sa variation intégrée exacte. Le témoin métrique
      global provenant de la branche diagonale reste à construire.
    - [x] Isoler l'obstruction déterminantielle à une frame globale
      deck-compatible sur D8, puis la remplacer par les frames tangentes
      locales canoniques, une partition de l'unité lisse subordonnée et une
      régularisation locale non vide avec musical, sharp, tenseur et volume.
      Le recollement en un unique tenseur lorentzien global est fermé
      intrinsèquement ci-dessous.
      - [x] Construire sur le cover le cocycle lorentzien produit non vide :
        tangent de `S³` orthogonal, musical non dégénéré, frame d'inertie
        `(3,1)` et isométrie exacte sous la réflexion génératrice. Les deux
        ponts vers la section tensorielle intrinsèque puis sa descente lisse
        quotient sont typés explicitement mais restent à décharger.
        - [x] Construire la vraie section tensorielle intrinsèque lisse sur le
          cover depuis `mfderiv` de l'immersion, prouver la naturalité exacte
          sous la dérivée deck et son invariance lorentzienne. Sa descente
          tensorielle lisse quotient est maintenant fermée ; la certification
          intrinsèque de signature lorentzienne reste séparée.
          - [x] Étendre l'invariance au vrai `mfderiv` de tout enroulement,
            construire l'équivalence tangentielle de la projection quotient,
            isoler les données exactes de descente, prouver leur unicité et la
            symétrie automatique du tenseur quotient.
          - [x] Construire `IntrinsicTensorQuotientDescent` par les inverses
            locaux de `mappingTorusMk`, malgré l'absence de descente générique
            Mathlib pour une `ContMDiffSection` bilinéaire dépendante.
            - [x] Construire dans chaque fibre quotient la valeur canonique via
              l'inverse de la vraie dérivée de projection, prouver son pullback
              exact et son indépendance sous tout changement de lift par deck ;
              assembler ensuite ces valeurs par `Quotient.hrecOn`, prouver leur
              expression lisse dans chaque inverse local et produire la vraie
              section `C∞` globale, canonique et unique.
          - [x] Construire `IntrinsicCoverLorentzCertificate`, puis transporter
            musical, non-dégénérescence et signature via
            `quotientProjectionDerivativeEquiv` afin d'obtenir la vraie
            `SmoothGeneralLorentzMetric` quotient.
            - [x] Prouver déjà que tout certificat cover fourni se transporte
              canoniquement par l'équivalence différentielle de projection en
              une preuve `IsEverywhereLorentzian` du tenseur quotient descendu.
              Le certificat cover est maintenant construit à partir de
              l'équivalence tangent-produit, de la dérivée de la sphère vers
              son orthogonal et d'une base orthonormale spatiale ; la signature
              `(3,1)` du tenseur quotient canonique est donc inconditionnelle.
              - [x] Instancier ce tenseur quotient comme une vraie
                `SmoothGeneralLorentzMetric`, prouver sa non-dégénérescence
                globale et spécialiser la densité scalaire, sa première
                variation et son reste quadratique pointwise.
                - [x] Supprimer ensuite l'exigence erronée d'une frame globale
                  en séparant le scalaire intrinsèque
                  `g⁻¹(dφ,dφ)/2 - m²φ²/2` de sa mesure d'intégration. Pour toute
                  mesure de Borel finie non nulle, prouver l'intégrabilité et
                  construire une action intrinsèque effectivement non nulle.
                  Une mesure de Dirac n'est utilisée que comme témoin formel
                  dans ce gate intermédiaire.
                  - [x] Isoler ce contrat comme un atlas fini de mesures
                    coordonnées pondérées par `sqrt(|det g|)` et compatibles
                    sur les recouvrements ; construire par cellules disjointes
                    l'unique mesure globale, prouver ses restrictions locales,
                    sa finitude et sa non-nullité, puis instancier l'action
                    intrinsèque non nulle sans Dirac.
                    - [x] Construire inconditionnellement la mesure canonique
                      depuis `Measure.toSphere` sur `S³`, Lebesgue sur un
                      domaine temporel fondamental et le pushforward au
                      quotient ; produire l'atlas fini compatible, identifier
                      la mesure recollée et obtenir une action intrinsèque
                      constante non nulle.
  - [x] Construire sur le vrai quotient D8 compact une action scalaire globale
    à repère diagonal fixé : valeur, différentielle de variété, contraction par
    l'inverse de la même métrique et volume métrique proviennent des mêmes
    objets ; la covariance tensorielle générale reste ouverte.
  - [x] À métrique et mesure globales fixes, varier le même champ scalaire par
    une courbe affine, prouver l'affinité exacte de sa différentielle, puis la
    dérivée pointwise et intégrée de l'action sous un contrat d'intégrabilité
    explicite. Le pont Euler--flux covariant faible est désormais fermé sous
    l'interface IPP/flux exacte ; sa décharge géométrique reste ouverte.
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
  - [x] Promouvoir le pont à une métrique lorentzienne générale via le vrai
    `sharp(dφ)` et une interface intrinsèque divergence/flux : obtenir
    variation = pairing Euler covariant faible + flux, l'équivalence
    stationnaire sous flux nul et la spécialisation D8.
  - [x] Déduire l'annulation du flux normal concret des conditions homogènes
    de Dirichlet, pointwise puis contre la mesure canonique du throat.
  - [ ] Identifier le boundary functional abstrait à ce flux concret et
    décharger l'interface par une formule géométrique de Stokes/IPP avec un
    normal métrique canonique.
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
- [x] Prouver leurs lois de covariance et d'échange, regroupées dans un
  certificat inconditionnel unique couvrant covariance pointwise, pairing
  mesuré, difféomorphisme plus échange et variation intégrée.
  - [x] Prouver l'invariance par échange des deux secteurs pour l'action
    intégrée et sa variation de stress.
  - [x] Prouver que l'induction des deux métriques diagonales et des deux
    traces matière commute exactement avec PT/échange. La racine relative,
    la covariance difféomorphe et les conservations restent séparées.
  - [x] Prouver point par point que PT/échange inverse exactement le ratio
    spectral positif et que le produit des deux racines principales diagonales
    correspondantes est l'identité.
  - [x] Prouver que l'induction des deux métriques diagonales, de la racine
    principale et des deux traces matière commute exactement avec l'action
    difféomorphe diagonale restreinte déjà définie.
  - [x] Prouver pointwise la covariance difféomorphe du tenseur de stress
    scalaire contravariant intrinsèque sous transport simultané de la métrique,
    de `dφ` et des covecteurs tests.
  - [x] Intégrer ce tenseur contre deux champs cotangents tests et une mesure
    Borel arbitraire, transporter l'intégrabilité iff et prouver l'invariance
    exacte sous difféomorphisme simultané et échange des deux secteurs.
  - [ ] Déduire les identités locales de conservation à partir des équations
    covariantes et de l'identité de Noether locale ; le certificat de
    covariance/échange ne les affirme pas. L'identité locale du collier
    `E = 2 T_nn` et la constance de `T_nn` n'établissent pas cette divergence
    covariante en dimension quatre.
    - [x] Au niveau d'un jet scalaire covariant d'ordre deux dans un repère
      normal 4D, développer explicitement `∇_μ T^{μν}` et prouver
      `div T = (□φ - V'(φ)) sharp(dφ)`, puis sa nullité sous l'équation
      d'Euler. Raccorder exactement les conventions de potentiel du stress
      fibre et du stress matriciel existants. La connexion lisse, le champ de
      jets global et le théorème global `div_g T = 0` restent ouverts.
      - [x] Transporter cette identité en coordonnées locales arbitraires sous
        une interface de jet de connexion métrique-compatible et sans torsion :
        construire le Hessien covariant symétrique, réaliser
        `∇T = ∂T + ΓT + ΓT`, annuler exactement les corrections de Christoffel
        et déduire conservation sous Euler. La décharge algébrique ponctuelle
        de cette interface est fermée ci-dessous ; sa réalisation par une
        connexion et des champs lisses globaux, puis `div_g T = 0`, reste
        ouverte.
        - [x] À partir d'une métrique symétrique non dégénérée et d'un premier
          jet métrique symétrique dans ses indices métriques, construire les
          coefficients locaux de Levi-Civita, prouver l'absence de torsion,
          les compatibilités covariante et contravariante, et la formule exacte
          `∂g⁻¹ = -g⁻¹(∂g)g⁻¹`; instancier le jet de connexion et en déduire la
          conservation locale ponctuelle sous Euler. Aucun champ, connexion
          lisse ou théorème de divergence global n'est affirmé.
          - [x] Pour une `SmoothGeneralLorentzMetric` et un patch holonome lisse
            fourni, construire la matrice métrique locale, prouver sa lissité
            et sa non-dégénérescence, puis construire son inverse, `dMetric` et
            les coefficients de Christoffel lisses. Instancier en chaque point
            le jet de Levi-Civita et déduire la conservation locale sous Euler.
            La construction générique du patch, les compatibilités d'overlap,
            le recollement et la connexion globale restent ouverts.
            - [x] Tirer tout vrai `SmoothScalarField` quotient sur ce patch,
              prouver sa régularité `C∞` ainsi que celle du gradient et du
              Hessien brut, fermer la symétrie de Schwarz et obtenir un vrai
              `CoordinateScalarJet2`. Construire le jet covariant, le résiduel
              d'Euler, le gradient relevé et la divergence de stress locale
              canoniquement réalisée, tous `C∞`, puis prouver l'identité exacte
              `div T = EulerResidual · raisedGradient` et la conservation sous
              Euler. Les compatibilités d'overlap, le recollement et le théorème
              global `div_g T = 0` restent ouverts.
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
  - [x] Prouver que le renversement d'orientation échange les joints initial et
    final avec signe opposé, inverse la transgression de face et rend le ledger
    total impair, donc toujours nul, dans le modèle endpoint fini.
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
  - [x] Sur le vrai quotient lisse D8, construire concrètement
    `R_φ(c) = L_c φ` pour chaque composante scalaire matière indépendante et
    l'opérateur de Noether `B_φ(E) = E ∘ R_φ`. Les secteurs métrique, jauge et
    LL du vrai `R/B` global restent ouverts.
    - [x] Assembler ces huit composantes en un unique multiplet matière et
      construire les opérateurs globaux de bloc `R_matter` et
      `B_matter = R_matterᵀ E_matter`.
  - [x] Pour le secteur `U(1)^2` global lisse, construire le vrai générateur
    linéaire `R_A(c) = dc`, sa version par paire, l'action affine correspondante
    et l'opérateur de Noether `B_A(E) = E ∘ R_A`.
    - [x] Assembler `R_matter ⊕ R_A` sur un même espace de paramètres et de
      variations globales, construire `B(E) = E ∘ R` et caractériser exactement
      son annulation par l'annihilation de l'image de `R`. Le pont identifiant
      `E` à la dérivée d'une action invariante reste à établir avant d'appeler
      cette condition une identité de Noether dynamique.
      - [x] Sur l'espace affine de variations matière + `U(1)^2` à background
        fixé, identifier `E` à la vraie dérivée le long de chaque droite et
        prouver que l'invariance finie par toutes les translations engendrées
        équivaut à `B(dS)=0` en tout point. L'action Janus non linéaire sur le
        paquet complet métrique/LL reste à construire.
      - [x] Ajouter les deux variations métriques intrinsèques comme vraies
        sections lisses symétriques issues d'un flot de pullback, puis les
        combiner aux blocs matière et `U(1)^2` dans un unique générateur
        linéaire et son opérateur `B`. L'intégration ghost → flot complet et la
        dépendance linéaire du flot sont isolées dans un contrat explicite ;
        elles ne sont pas encore construites sans hypothèse.
        - [x] Construire néanmoins un premier flot Janus géométrique concret :
          la translation réelle du temps sur le cover commute avec tout deck,
          descend en une action réelle analytique complète sur le vrai quotient
          D8, chaque tranche est un difféomorphisme analytique, et le demi-période
          agit non trivialement. L'intégration d'un ghost arbitraire reste
          ouverte.
          - [x] Renforcer l'analyticité tranche par tranche en analyticité
            jointe de l'application d'action `ℝ × D8 → D8` par descente locale
            à travers la projection quotient.
          - [x] Restreindre le même flot analytique au throat, prouver qu'il
            préserve l'inclusion, puis le faire agir sur les huit blocs du
            paquet `IndependentFields`. Fermer zéro/addition/inverse,
            conjugaison PT et compatibilité avec les cinq champs induits.
          - [x] Descendre un champ cosinus périodique explicite et prouver que
            la translation de demi-période l'envoie sur un champ distinct :
            la représentation de pullback sur les champs est non triviale.
            - [x] Injecter ce mode dans la première composante matière et
              exhiber une configuration `IndependentFields` complète déplacée
              par la demi-période.
          - [x] Construire le setoid et le quotient du paquet complet
            `IndependentFields` par cette action temporelle concrète, puis
            identifier exactement les fonctions sur les orbites aux fonctions
            invariantes. Aucune topologie d'orbites n'est revendiquée.
        - [x] Identifier ensuite le covecteur combiné à la vraie dérivée
          linewise d'une action affine à background fixé et prouver que
          l'invariance finie par toutes les translations engendrées équivaut à
          `B(dS)=0` en tout point. Le contrat d'intégration des ghosts et
          l'action Janus non linéaire complète restent explicitement ouverts.
  - [x] Dans le modèle fonctionnel diagonal abstrait déjà formalisé, restreindre
    le générateur par toute reparamétrisation linéaire continue et prouver la
    naturalité exacte de la contrainte adjointe ainsi que la préservation de
    l'invariance infinitésimale. Le vrai `R/B` géométrique global reste ouvert.
    - [x] Prouver que ces deux propriétés deviennent des équivalences exactes
      lorsque la reparamétrisation est surjective.
  - [x] Pour tout flot de jauge complet déjà fourni, construire son générateur
    diagonal à paramètre réel et identifier exactement invariance par le flot,
    annulation de sa vitesse et identité infinitésimale diagonale. La
    construction du flot Janus géométrique global reste ouverte.
    - [x] Calculer explicitement sa contrainte adjointe `RᵀE`, puis prouver
      directement que son annulation équivaut à l'annulation du générateur et
      à l'invariance de l'action sous le flot fourni.
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
  - [x] Construire la catégorie de symétrie du background D8 fixé, à un objet
    et avec tous les auto-difféomorphismes lisses comme morphismes; construire
    pour toute fibre normée le foncteur contravariant exact des champs lisses
    et prouver ses lois d'identité/composition. La catégorie de modules de tous
    les backgrounds Janus et ses bundles SpinC restent ouvertes.
  - [x] Spécialiser ce cadre aux métriques Lorentz générales lisses : prouver
    les lois d'identité/composition du pullback tensoriel et métrique, puis
    construire leur foncteur contravariant sur la seule catégorie D8 fixée.
    La catégorie globale des géométries Janus reste ouverte.
- [ ] Vérifier localité, régularité et réalisations holonomiques requises.
- [x] Construire le groupoïde différentiable des jets structurés.
  - [x] Construire la catégorie et le groupoïde d'action effectifs de deck D8,
    avec égalité dans le quotient caractérisée par l'existence d'une flèche.
  - [x] Construire les familles dépendantes source/cible, leur transport et le
    foncteur de représentation fourni vers les jets structurés.
  - [x] Prouver que chaque composante source/cible du groupoïde de deck est un
    difféomorphisme local sur les covers analytiques 4D et du throat 3D.
- [ ] Déterminer sa stratification d'isotropie.
  - [x] Pour le vrai groupoïde effectif de deck D8, prouver que tout
    endomorphisme est l'identité, identifier chaque stabilisateur à un
    singleton et conclure qu'il existe une unique strate d'isotropie de deck,
    partout triviale. L'isotropie résiduelle des fibres de jets SpinC reste
    ouverte et ne doit pas être confondue avec l'isotropie du quotient D8.
  - [x] Prouver que toute représentation fonctorielle du deck sur les jets
    structurés envoie encore chaque endomorphisme sur l'identité : aucune
    isotropie de jet ne peut être créée par l'action de deck elle-même.
  - [x] Construire explicitement l'équivalence entre les stabilisateurs de
    deck en deux points arbitraires et exclure ainsi tout saut de type
    d'isotropie sur le quotient effectif D8.
- [ ] Construire les revêtements Spin de dimension pertinente.
- [ ] Dériver les données Cech/SpinC depuis l'atlas réel, et non depuis des
  transitions fournies.
  - [x] Sur les triples intersections du vrai atlas D8, prouver que deux
    relèvements Spin fournis composent en un troisième relèvement dont le
    défaut de Cech est exactement trivial. L'existence et le choix global lisse
    des relèvements restent ouverts.
  - [x] Pour deux relèvements Spin d'une même transition réelle de l'atlas,
    construire leur différence dans le noyau de la projection Spin et prouver
    qu'elle est triviale exactement lorsque les deux relèvements coïncident.
  - [x] Construire l'action du noyau de la projection Spin sur les relèvements
    d'une transition fixée et prouver sa liberté/transitivité explicite :
    l'ambiguïté locale des relèvements forme un torsor sous ce noyau.
    - [x] Vérifier explicitement les lois d'identité et de composition de
      l'action ainsi que son injectivité en chaque relèvement choisi.
    - [x] Prouver que le noyau est stable par conjugaison Spin et que la
      différence de deux relèvements se transforme par conjugaison sous une
      translation commune, donnant la covariance exacte du torsor local.
    - [x] Empaqueter cette conjugaison comme un automorphisme multiplicatif du
      noyau, avec inverse donné par la conjugaison Spin inverse.
    - [x] Assembler ces automorphismes en une représentation multiplicative du
      groupe Spin ambiant sur le noyau de sa projection.
    - [x] Prouver le critère exact : l'automorphisme de conjugaison d'un
      élément Spin est trivial si et seulement si cet élément commute avec
      tout le noyau. La centralité dimensionnelle devient ainsi l'unique verrou
      Clifford restant de cette étape.
    - [x] Étendre ce critère à la représentation entière : elle est triviale
      si et seulement si tout élément Spin commute avec tout élément du noyau.
    - [x] Dériver la loi de cobord locale exacte : translater le lift de
      l'arête composée par un élément du noyau multiplie le défaut de Cech à
      droite par l'inverse de cet élément.
    - [x] Dériver les deux autres lois sans supposer le noyau central : une
      translation sur l'arête `second→third` multiplie le défaut à gauche,
      tandis qu'une translation sur `first→second` introduit à gauche le
      noyau conjugué par le lift adjacent.
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
    - [x] Identifier directement la trace nucléaire PT à la trace nucléaire
      positive correspondante.
    - [x] Sur chaque demi-droite `t ≥ ε > 0`, dominer uniformément les
      coefficients et les normes des termes de rang un par la série sommable
      au temps `ε`, puis prouver la continuité de la trace nucléaire réelle et
      sa covariance PT.
      - [x] Absorber uniformément le facteur spectral de la dérivée par une
        gaussienne au demi-temps, prouver la sommabilité uniforme des
        dérivées, dériver la trace terme à terme pour tout temps positif,
        identifier la vraie `deriv`, prouver sa continuité sur chaque
        demi-droite positive et conserver la covariance PT. Le passage au vrai
        opérateur Janus global reste ouvert.
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
  - [x] Sur la somme directe bosonique réduite bulk scalaire + jonction Robin
    + LL PT-symétrique, assembler l'opérateur de Jacobi bloc-diagonal, prouver
    que son pairing est exactement la somme des trois Hessians naturels,
    établir symétrie, bijectivité, noyau nul, image totale fermée et indice
    zéro. Les blocs métrique, jauge, ghosts et la famille paramétrique restent
    ouverts.
    - [x] Munir cette somme réduite de la vraie structure hilbertienne ℓ² via
      `WithLp`, transporter l'opérateur bloc et prouver son auto-adjonction
      effective, tout en conservant pairing Hessien, bijectivité, image fermée
      et indice zéro.
- [ ] Instancier le complexe D9/BRST avec les vrais champs, ghosts, symboles,
  domaines et cohomologie de modes zéro.
  - [x] Injecter le vrai ghost `U(1)` Programme P dans le champ ghost D9 avec
    composante difféomorphe explicitement nulle, calculer son symbole principal
    et prouver l'annulation de la composante `U(1)` dans son noyau à covecteur
    non nul.
  - [x] Injecter fidèlement le vrai ghost tangent lisse du throat D8 dans la
    composante difféomorphe D9, transporter explicitement son crochet de Lie,
    calculer son symbole principal et caractériser exactement son noyau
    ponctuel à covecteur non nul. Les domaines et la cohomologie de mode zéro
    restent ouverts ; le complexe D9/BRST global n'est donc pas fermé.
  - [x] Calculer le sous-complexe du symbole ghost D9 au covecteur nul : son
    différentiel est nul, son noyau contient les quatre coordonnées ghosts,
    son image est nulle et son quotient cohomologique est linéairement
    équivalent à cet espace de coordonnées. Les domaines et la cohomologie
    du vrai opérateur différentiel global restent ouverts.
    - [x] Remplacer la coordonnée `U(1)` isolée par le vrai doublet issu des
      secteurs Programme P `.plus/.minus`, conserver les trois coordonnées
      difféomorphes construites, puis calculer exactement le complexe nul à
      cinq coordonnées, son noyau total, son image nulle et son quotient. Les
      domaines et la cohomologie du vrai opérateur global restent ouverts.
      - [x] Au covecteur non nul, construire le symbole apparié sur ces cinq
        coordonnées et prouver que son noyau est nul. Pour les vrais bridges,
        caractériser son annulation par l'annulation simultanée des deux
        ghosts `U(1)` et du ghost tangent au point inspecté. Les domaines du
        vrai opérateur global restent ouverts.
        - [x] Prouver en outre que ce symbole non nul est surjectif, que son
          image est totale et donc qu'il est bijectif. Cette exactitude reste
          celle du modèle algébrique ponctuel, sans assertion sur l'opérateur
          différentiel global. Son inverse linéaire est construit explicitement
          et ses deux identités de composition sont prouvées ; noyau et image
          sont également classifiés dans les cas covecteur nul et non nul.
          - [x] Construire le conoyau du symbole apparié et prouver qu'au
            covecteur non nul toute classe y est nulle. Il s'agit uniquement
            de la cohomologie du symbole ponctuel, pas du complexe BRST global.
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
    - [x] Identifier exactement son ensemble de zéros aux deux représentants
      d'extrémité, prouver que les deux crossings sont simples avec dérivées
      `±2π`, et montrer que leur multiplicité simple est préservée par le
      clutching et le transport parallèle plat choisis. Aucune identification
      à la connexion globale de Quillen/Bismut--Freed n'est revendiquée.
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
