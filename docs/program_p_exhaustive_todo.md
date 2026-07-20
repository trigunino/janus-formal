# Programme P — TODO exhaustive de fermeture

Date de référence : 2026-07-17.

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
**1058 fermées sur 1165 ; 107 ouvertes** (90,82 %).

Documents de référence :

- `docs/program_p_operational_todo.md` — file courte distribuable aux LLM et
  compteur fixe des 14 portes terminales ;
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
    - [x] Assembler sur le même quotient effectif D8 la métrique lorentzienne
      intrinsèque lisse, sa mesure d'action finie non nulle, les
      difféomorphismes PT ambiant/throat, l'embedding lisse du throat et le
      vrai bundle principal ambiant `Pin⁻(4)`. Les champs matière, `U(1)^2`,
      `PinC` et l'action complète restent hors de ce paquet canonique.
      - [x] Étendre ce même paquet par deux métriques Candidate A conformes
        positives `g₊=a g₀`, `g₋=b g₀`, leur racine intrinsèque sur chaque
        fibre tangentielle et leur densité ; prouver le carré exact et l'accord
        avec le potentiel matriciel isotrope dans toute frame. Les paires de
        métriques générales non conformes restent ouvertes.
        - [x] Promouvoir le coefficient `sqrt(b/a)` en vrai champ scalaire
          lisse global et identifier la racine ponctuelle à ce champ multiplié
          par l'identité tangentielle. La famille conforme de racines est donc
          lisse ; la famille non conforme générale reste ouverte.
          - [x] Construire l'opérateur linéaire induit sur les sections
            tangentielles globales lisses et prouver point par point qu'il est
            exactement la racine intrinsèque déjà construite.
            - [x] Construire sur les mêmes sections l'opérateur relatif
              `(b/a) id` et prouver globalement que la composition de
              l'opérateur racine avec lui-même lui est exactement égale.
              - [x] Prouver que l'échange des deux facteurs conformes positifs
                fournit une famille inverse lisse, avec compositions gauche
                et droite exactement égales à l'identité sur les sections.
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
- [x] Compléter la géométrie du throat par sa stratification non-nulle/null/joint.
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
  - [x] Construire la stratification non-nulle/null/joint de l'embedding lisse.
    - [x] Sur le bundle normal différentiel réel effectivement construit,
      séparer les strates intrinsèques zéro/non-zéro : elles sont disjointes
      et couvrantes, la section zéro est analytique et plongée, son image est
      fermée, le complément est ouvert, et le `Diffeomorph` normal transporte
      exactement les deux strates. La forme quadratique lorentzienne canonique
      et sa classification causale sont fermées plus bas.
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
    - [x] Construire l'atlas du bundle normal quotient, promouvoir cette
      équivalence algébrique en équivalence lisse globale et construire les
      strates non-nulles/nulles/joints.
      - [x] Transporter la topologie du vrai normal analytique sur le total
        dépendant différentiel, construire l'homéomorphisme total
        base-préservant et les trivializations, puis installer les instances
        `FiberBundle`, `VectorBundle` et `ContMDiffVectorBundle ω` avec le même
        cocycle de signe. Les strates causales sont fermées ci-dessous.
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
            `-id`, et égalité des carrés des deux relèvements locaux. Le choix
            algébrique global et sa continuité sont traités ci-dessous.
            - [x] Étendre la loi de deck de la courbe quotient à tout
              `winding : ℤ` par le caractère `normalSignRepresentation` : les
              enroulements pairs agissent trivialement et les impairs par
              renversement du paramètre ; étendre aussi le `HEq` tangent et
              l'invariance du modèle scalaire quadratique à tout winding. Le
              choix global est traité séparément ci-dessous.
            - [x] Éliminer le cast caché au niveau cover en prouvant par `HEq`
              que le normal de latitude nommé est exactement sa dérivée brute
              transportée le long de l'égalité à latitude zéro.
            - [x] Combiner ce transport avec la règle de chaîne de la
              projection quotient pour identifier par `HEq` le normal
              quotient canonique et le tangent de la courbe de latitude.
            - [x] Transporter explicitement le tangent quotient vers la fibre
              canonique à latitude zéro, prouver que ce transport commute au
              `SMul ℝ`, puis établir le cocycle de signe du normal quotient
              canonique pour tout `winding : ℤ`.
            - [x] Choisir le relèvement orthogonal global comme opérateur
              fibre-linéaire indépendant de l'ancre du cover, puis prouver
              qu'il représente la classe quotient et est orthogonal au
              tangent du throat. Ce n'est ni une section normale globale non
              nulle ni le record dépendant final.
            - [x] Définir son carré métrique global, prouver dans chaque carte
              transportée la formule exacte `scalar²`, décharger
              `CanonicalGlobalNormalMetricSquareLocalRegularity` et en déduire
              sa continuité globale. Le record dépendant générique reste
              volontairement séparé de cette fermeture directe.
            - [x] Définir directement depuis ce carré les strates globales
              spacelike, timelike, null, non-null et joint, puis prouver
              inconditionnellement leur ouverture/fermeture, couverture et
              l'inclusion du joint dans le null. Le wrapper canonique final est
              une `def`, sans empaquetage du record dépendant générique.
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
- [x] Étendre ce relèvement normal au fibré tangent ambiant par une structure
  `Pin` compatible. Les réalisations ambiantes orientées `Spin/SpinC` sont
  exclues par la non-orientabilité prouvée ci-dessous. Une équivalence radiale
  du vrai espace tangent du cover vers `ℝ⁴` est maintenant construite depuis
  la véritable dérivée d'immersion, avec loi exacte sous tout enroulement de deck.
  Elle envoie aussi la normale canonique réelle du throat sur le premier
  vecteur ambiant. Sur un vrai overlap d'atlas, les deux lifts sont aussi prouvés
  localement égaux au translate par le winding réel figé ; après différentiation
  et transport dépendant des fibres, le vrai Jacobien d'atlas est exactement la
  puissance de réflexion correspondante dans les frames radiales. La dépendance
  lisse atlas-wide et la réduction orthogonale Čech sont construites ; leur lift
  principal `Pin⁻` reste à construire.
  - [x] Conjuguer tout enroulement de deck par le split radial/référence fixe et
    identifier le vrai `mfderiv` de transition d'atlas à la phase canonique
    `O(4)` du même winding dans les frames radiales de coordonnées.
  - [x] Prouver la dépendance `C∞` jointe des frames radiales et de leur famille
    inverse, puis les empaqueter en réduction orthonormale lisse dont les
    transitions sont exactement la phase canonique du vrai winding.
  - [x] Prouver que la descente déterminantielle ambiante est vide, exhiber
    l'obstruction d'un overlap renversant l'orientation et en déduire
    l'inexistence de réalisations Čech continues orientées `Spin` ou `SpinC`.
    La cohérence Čech purement algébrique reste conditionnelle et le bon verrou
    constructif restant est le relèvement ambiant `Pin`.
  - [x] Construire depuis les cartes réelles du quotient les transitions
    tangentes ambiantes, leur différentielle inversible, le signe exact du
    déterminant et le cocycle d'orientation `ZMod 2`. La réduction quadratique,
    son identification au cocycle normal et le relèvement `Pin/SpinC` restent
    explicitement séparés par des contrats minimaux.
    - [x] Construire une forme quadratique euclidienne réelle 4D positive et
      non dégénérée sur le modèle, la transporter par chaque vraie transition
      tangente et obtenir les isométries quadratiques exactes. Une réduction
      orthonormale atlas-wide pointwise est maintenant construite par choix
      d'un lift de référence et cocycle tangent strict.
      - [x] Construire une réduction orthonormale atlas-wide `C∞` honnête :
        forme de Whitney, repères de Gram--Schmidt et transitions orthogonales
        sont conjointement lisses sur leurs vrais domaines de cartes. Les
        lifts `Pin/SpinC` restent des contrats séparés.
      - [x] Construire depuis l'algèbre de Clifford la vraie action du groupe
        Spin sur les vecteurs, son équivalence linéaire, la préservation
        quadratique et le morphisme `Spin(Q) →* GL(4)`. L'extension Pin est
        isolée par son action tordue exacte ; seuls les lifts de transitions et
        leur cocycle Čech atlas-spécifique restent à fournir.
        - [x] Construire inconditionnellement la projection tordue du groupe
          ambiant `Pin⁻(4)` vers les automorphismes réels, avec générateur de
          réflexion de carré central non trivial et loi exacte d'ordre quatre.
          - [x] Munir ce vrai sous-groupe de Clifford de la topologie normée
            finie-dimensionnelle héritée de ses seize coordonnées PBW via la
            représentation régulière gauche fidèle, puis prouver la continuité
            de la conjugaison, les lois de groupe topologique et du caractère
            de référence `ZMod 4`. Le lift Whitney et son cocycle restent ouverts.
          - [x] Prouver que l'action tordue est conjointement continue et que la
            projection existante `Pin⁻(4) → GL(4)` est continue ; munir `O(4)`
            de sa topologie sous-espace, en déduire la continuité des vraies
            transitions de la réduction Whitney `C∞`, puis réduire le critère
            de lift local à l'hypothèse explicite de sections locales. Aucune
            projection générale `Pin⁻(4) → O(4)` ni section locale n'est
            revendiquée.
            - [x] Prouver la parité homogène de tout élément du vrai groupe
              `Pin⁻(4)`, en déduire la préservation exacte de la forme
              quadratique euclidienne par l'action tordue, puis empaqueter une
              projection continue et surjective `Pin⁻(4) →* O(4)`. Aucune
              section locale, propriété de revêtement ni donnée Čech n'en est
              déduite.
              - [x] Munir cette cible orthogonale concrète de sa vraie structure
                de groupe topologique pour la topologie matricielle induite, en
                prouvant directement la continuité du produit et de l'inversion,
                ainsi que la propriété de Hausdorff par ses plongements fidèles.
                Ce prérequis ne fournit encore ni propriété de Baire/compacité
                utile à l'open mapping, ni section locale de la projection
                `Pin⁻(4) → O(4)`, ni propriété de revêtement.
        - [x] Réduire tout relèvement ambiant normal-compatible à un unique
          choix Čech continu normalisé, avec lois de projection, parité et
          restriction normale exactes. L'existence de ce choix continu reste
          une hypothèse et n'est pas revendiquée.
          - [x] Calculer explicitement la réflexion `O(4)` du générateur
            `Pin⁻`, prouver son caractère d'orientation sur les quatre phases
            `ZMod 4`, corriger la restriction normale pour ne demander les
            coordonnées que sur les vrais overlaps et isoler l'unique loi de
            réduction orthogonale exacte.
            - [x] Construire le vrai winding Čech ambiant depuis les sections
              locales couvrantes, puis prouver la naturalité throat→ambient et
              son égalité au winding normal sur l'overlap charté compatible.
              Le raffinement lisse est fermé. La parité du vrai Jacobien, la
              loi `O(4)` de référence et le lift `Pin⁻` ambiant restent ouverts.
              - [x] Prouver le no-go de jauge de cartes : retourner
                l'orientation d'une seule carte par la réflexion ambiante
                conserve le winding mais inverse exactement le déterminant et
                sa parité. Toute comparaison Jacobien/winding exige donc un
                choix supplémentaire d'orientations de cartes compatibles.
              - [x] Prouver séparément le no-go de jauge de repères : le
                changement central `-id` préserve exactement la forme
                euclidienne mais modifie toute transition orthogonale. Le
                winding et sa parité ne sélectionnent donc pas une matrice
                `O(4)` unique sans jauge de repères locale. Plus précisément,
                formaliser que la loi de réduction de référence force deux
                transitions réduites de même winding à être exactement égales.
              - [x] Construire et caractériser l'unique jauge orthogonale
                pointwise `actual⁻¹ ∘ expected` qui transforme exactement une
                transition réduite en la matrice de référence demandée. Le
                résidu est désormais la régularité et la cohérence Čech
                globale de cette famille de jauges.
                - [x] Dériver la loi de cocycle Čech tordue exacte de ces
                  jauges d'arêtes et prouver sa réciproque : elle équivaut au
                  cocycle strict des transitions cibles. Il reste à réaliser
                  cette loi par une famille lisse et normal-compatible.
                  - [x] Caractériser exactement la réalisation par jauges de
                    repères aux sommets : elle préserve automatiquement le
                    cocycle strict, induit la jauge d'arête conjuguée attendue
                    et détermine uniquement la jauge source lorsque la cible
                    est fixée. Reste le choix global lisse compatible au normal.
                    - [x] Relever cette algèbre abstraite au vrai record
                      `AmbientOrthonormalAtlasReduction` : transformer ses
                      repères par toute jauge `O(4)` aux sommets et prouver que
                      chaque transition obtenue est exactement la transition
                      vertex-gaugée, avec corollaire direct vers toute cible
                      réalisée.
                    - [x] Construire explicitement la propagation depuis une
                      carte racine sur tout sous-atlas étoilé et prouver que
                      les cocycles stricts réel et cible forcent toutes les
                      transitions demandées. Restent l'indépendance globale
                      des chemins, la lissité et la restriction normale.
                      - [x] Identifier exactement l'obstruction de monodromie :
                        la propagation revient à la jauge racine si et seulement
                        si celle-ci entrelace les holonomies réelle et cible ;
                        l'égalité des transports sur deux chemins implique leur
                        indépendance. Reste à décharger ce critère sur l'atlas.
                        - [x] Pour la monodromie cyclique du mapping torus,
                          prouver qu'entrelacer l'unique générateur suffit pour
                          tous les windings entiers, positifs ou négatifs, et
                          force la fermeture de la jauge propagée sur chaque
                          boucle. Reste l'identification au générateur réel.
                          - [x] Prouver l'identification exacte dans tout repère
                            normal-aligné : la conjugaison orthogonale inverse
                            le normal aligné, entrelace le générateur réel et la
                            réflexion `Pin⁻` de référence, puis ferme tous les
                            windings. Reste à construire ce repère lisse réel.
                            - [x] Construire pointwise un tel repère pour tout
                              normal unitaire, par transitivité orthogonale sur
                              les niveaux de la forme quadratique, puis obtenir
                              simultanément inversion du normal et fermeture
                              de tous les windings. Reste la dépendance lisse.
                              - [x] Remplacer le choix de Householder singulier
                                par le repère quaternionique canonique : il est
                                orthogonal, envoie l'axe de référence sur tout
                                normal unitaire et son application est
                                globalement polynomiale donc conjointement
                                `C∞`. Son instanciation atlas est fermée ci-dessous.
                                - [x] Fermer aussi la normalisation : tout champ
                                  normal `C∞` non nul se normalise `C∞` pour la
                                  forme euclidienne positive puis produit ce
                                  repère quaternionique conjointement `C∞`.
                                  - [x] Construire sur des domaines couvrant le
                                    vrai atlas les coordonnées du normal de
                                    latitude, prouver leur régularité `C∞` et
                                    leur non-annulation, puis celle de leur
                                    normalisation et de chaque composante du
                                    repère quaternionique. Reste l'egalité
                                    exacte avec les transitions `O(4)`.
                                    - [x] Empaqueter ce repère en vraie
                                      isométrie `O(4)` et prouver, pour tout
                                      winding entier, qu'il entrelace
                                      exactement la projection du lift normal
                                      local avec la phase de référence
                                      canonique. Reste l'identification de la
                                      transition réduite réelle à cette
                                      projection locale.
                                  - [x] Prouver la loi d'overlap signée exacte :
                                    normalisation et repère quaternionique
                                    entrelacent `n ↦ -n`, ce dernier changeant
                                    par la jauge centrale `-id`. Cette loi est
                                    prête pour le cocycle normal non trivial.
                                    - [x] Étendre cette loi à tout winding
                                      entier avec le vrai caractère
                                      `normalSignRepresentation` : normalisé et
                                      repère portent exactement le même cocycle
                                      signé que la ligne normale construite.
                                      - [x] Prouver que la réflexion alignée
                                        conjuguée est insensible à cette jauge
                                        centrale : les choix locaux `n` et
                                        `-n` définissent exactement la même
                                        réflexion ambiante, donc celle-ci
                                        descend malgré la ligne non triviale.
                                        - [x] Empaqueter la réflexion directement
                                          depuis tout normal local non nul et
                                          prouver sa descente pour chaque winding
                                        via `normalSignRepresentation`, sans
                                          dépendre du choix de signe local.
                                          - [x] Construire honnêtement dans
                                            l'algèbre de Clifford le générateur
                                            `Pin⁻(4)` de tout normal euclidien
                                            unitaire et prouver que `n ↦ -n`
                                            le multiplie par le signe central.
                                            - [x] Normaliser tout normal local
                                              non nul et prouver le cocycle
                                              `Pin⁻` exact pour chaque winding
                                              entier, pair ou impair.
                                              - [x] Prouver que la projection
                                                orthogonale de ces lifts est
                                                invariante sous tout ce cocycle
                                                de signe. Reste à fournir le
                                                champ normal du vrai atlas et
                                                l'égalité aux transitions.
                                                - [x] Construire pour chaque
                                                  normal local le lift cyclique
                                                  entier `w ↦ g(n)^w`, prouver
                                                  son cocycle additif strict et
                                                  identifier sa projection à
                                                  la puissance correspondante
                                                  de la réflexion locale.
                                                  - [x] Identifier exactement
                                                    la projection Clifford à
                                                    la réflexion alignée du
                                                    repère quaternionique,
                                                    d'abord par une formule
                                                    rank-one puis pour tous les
                                                    windings entiers.
                                                    - [x] Instancier ce lift
                                                      sur le vrai normal de
                                                      latitude du cover du
                                                      throat : sa coordonnée
                                                      produit est non nulle,
                                                      son lift cyclique est
                                                      strict et sa projection
                                                      est la réflexion alignée.
                                                      - [x] Prouver la vraie
                                                        loi à deux windings :
                                                        un winding choisit le
                                                        signe du normal local,
                                                        l'autre la phase liftée,
                                                        et le changement de
                                                        carte vaut exactement
                                                        le central à la puissance
                                                        de cette phase.
                                                        - [x] Prouver sur le
                                                          vrai cover que tout
                                                          changement d'ancre
                                                          entier conserve la
                                                          coordonnée normale
                                                          produit, le générateur
                                                          et tous ses lifts ;
                                                          le signe est donc
                                                          localisé honnêtement
                                                          dans la transition.
                                                      - [x] Évaluer le
                                                        normal au vrai lift
                                                        local de chaque
                                                        carte du throat,
                                                        construire le lift
                                                            `Pin⁻(4)` depuis le
                                                            winding Čech réel et
                                                            prouver normalisation,
                                                            cocycle strict sur
                                                            triples overlaps et
                                                            projection alignée ;
                                                        prouver aussi la loi
                                                        d'inverse et le carré
                                                        central non trivial
                                                        du tour générateur.
                                                        - [x] Composer le vrai
                                                          winding ambiant avec
                                                          le caractère de
                                                          référence `ZMod 4`
                                                          pour obtenir un
                                                          cocycle `Pin⁻(4)`
                                                          normalisé, continu et
                                                          strict sur les vrais
                                                          overlaps ; prouver sa
                                                          restriction exacte au
                                                          cocycle normal sur le
                                                          raffinement throat et
                                                          l'accord du caractère
                                                          d'orientation. Reste
                                                          l'égalité métrique à
                                                          la réduction `O(4)`.
                                                          - [x] Construire la
                                                            jauge d'arête
                                                            canonique entre la
                                                            réduction `O(4)` et
                                                            la projection du
                                                            cocycle `Pin⁻(4)`,
                                                            prouver sa loi de
                                                            Čech tordue exacte
                                                            et identifier la
                                                            loi de réduction
                                                            restante à la
                                                            trivialité de toutes
                                                            ces jauges.
                                                            - [x] Empaqueter la
                                                              projection du
                                                              cocycle `Pin⁻`
                                                              canonique comme
                                                              vrai cocycle `O(4)`
                                                              normalisé et strict,
                                                              avec égalité exacte
                                                              des applications
                                                              linéaires.
                                                              - [x] Prouver sa
                                                                restriction exacte
                                                                au raffinement du
                                                                throat, l'accord de
                                                                sa projection
                                                                Clifford et celui
                                                                du caractère
                                                                d'orientation avec
                                                                la réduction normale.
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
          - [x] Rejeter la trivialisation globale du défaut Čech de lifts Spin
            ambiants : la non-orientabilité prouvée interdit déjà leur
            existence continue. Le problème constructif correct est le choix
            Čech `Pin⁻` normal-compatible isolé ci-dessus.
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
  entre racine déterminante, `Pin⁻`/`PinC` et twist monopolaire.
  - [x] Prouver au niveau du relèvement normal que les deux caractères quart
    associés au fibré principal `Pin⁻(1)` construisent de vrais
    `FiberBundleCore`, reproduisent les deux cocycles racines, se carrent en
    demi-tour d'orientation pour tout enroulement et sont échangés par PT.
    Les classes du fibré tangent ambiant et le twist monopolaire restent ouverts.
    - [x] Prouver en outre que le produit des deux caractères normaux opposés
      vaut exactement `1` pour tout enroulement.
  - [x] Sur le vrai atlas du throat, construire le lift ambiant `Pin⁻(4)` de
    la normale latitude canonique, prouver son cocycle Čech, sa projection sur
    la réflexion orthogonale alignée et le carré central non trivial du tour
    fondamental. Le twist monopolaire et les classes globales restent ouverts.
  - [x] Relier l'entier de Chern monopolaire au caractère de transition
    `Pin⁻(4)` : PT donne l'inverse, les charges opposées se compensent et tout
    secteur primitif se projette sur la réflexion avec carré central non
    trivial. Ce pont porte seulement sur l'entier de transition ; le vrai
    bundle principal `U(1)` monopolaire et ses classes globales restent ouverts.
- [ ] Fixer les domaines géométriques sur lesquels métriques, racines,
  opérateurs et conditions au bord sont simultanément définis.
  - [x] Assembler sans champ de statut la géométrie décorée canonique, le
    domaine commun champs/LL/D7/D9/D10/bord et l'inclusion linéaire injective
    des variations indépendantes dans le tangent complet. La configuration
    canonique est effectivement PT-fixe et conserve son carré de racine et sa
    vraie trace de bord. L'accord action/Hessien/Fredholm reste ouvert.
    - [x] Remplacer dans ce noyau le scaffold métrique diagonal par deux vraies
      métriques lorentziennes générales intrinsèques sans dupliquer les champs
      non métriques ; prouver PT-fixité du paquet et de sa trace de bord.
      Une paire générale distincte et sa racine restent ouvertes.
      - [x] À partir de tout facteur conforme positif, construire son partenaire
        par pullback PT, prouver la naturalité PT de la métrique conforme, puis
        assembler une paire potentiellement distincte avec racine/densité
        Candidate A, champs non métriques inchangés et bord PT-fixe.
        Le secteur non conforme général reste ouvert.
        - [x] Construire un facteur positif explicite `2 + sin(2πt/T)`,
          prouver qu'il diffère de son partenaire PT, puis que les deux
          métriques du paquet canonique sont réellement distinctes.

  Le package typé `ProgramPCommonGeometricDomain4D` est maintenant non vide et
  force une même configuration pour les métriques diagonales, la racine
  principale, le domaine `LLH1`, la trace de bord et les accès D7/D9/D10. La
  case reste ouverte : `RemainingProgramPD7D9D10DomainAgreement4D` isole encore
  l'accord avec le tangent de l'action, le Hessien, la diagonalisation D10, le
  régulateur et les domaines de bord/Fredholm. Ce contrat est renforcé par des
  égalités, lois linéaires/isométriques, densité modale et équivalences de
  domaines explicites ; aucun champ libre de type `Prop` ne peut le fermer.

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
- [x] Inclure, pour l'existence d'une racine réelle Sylvester-régulière, tout
  `PositiveRealSplitCharpoly4` et les strates de Jordan explicitement
  admissibles. La construction d'une base brute de chaînes de Jordan reste le
  résidu de présentation explicite ci-dessous.
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
    - [x] Retirer `HasPositiveRealJordanPresentation` du chemin critique brut :
      `positiveRawSylvesterRegularRootClosure` construit directement, sous les
      seules hypothèses spectrales positives scindées, une racine réelle exacte
      dont l'opérateur de Sylvester est bijectif, sans base de Jordan.
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
      - [x] Classer la base réelle explicite de chaînes `Fin 4` comme donnée de
        présentation facultative : Mathlib ne choisit pas ces chaînes, mais
        elles ne sont plus requises pour l'existence de la racine ni pour la
        régularité de Sylvester, toutes deux fermées par la construction
        polynomiale brute précédente.
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
      - [x] Étendre ce calcul à `P_k(t)=diag(t^k,1,1,1)` pour tout entier
        `k≥0` : la conjugaison décale exactement l'ordre nilpotent de `k` et
        classifie limite nulle, limite critique non nulle ou divergence selon
        la comparaison de `m` avec `n+k`.
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
    composante. Les autres cas `0/0` et les matrices générales restent ouverts.
    - [x] Au même point diagonal `0/0`, construire un chemin à taux égaux et
      un chemin à numérateur quadratique : la racine sélectionnée tend
      respectivement vers `1` et `0`, ce qui exclut tout prolongement continu
      monovalué coïncidant avec la branche intérieure. Cette obstruction porte
      exactement sur ces deux chemins, pas sur les chemins matriciels ou les
      strates de Jordan généraux.
    - [x] Classifier tous les chemins diagonaux monomiaux positifs
      `(t^m,t^n)`, `m,n>0` : au même point `0/0`, la racine tend vers `1` si
      `m=n`, vers `0` si le numérateur s'annule plus vite, et vers `+∞` si le
      dénominateur s'annule plus vite. Les chemins non linéaires, matriciels et
      les dégénérescences de Jordan arbitraires restent hors de cette famille.
      - [x] Étendre exactement cette trichotomie à tous les exposants réels
        strictement positifs, avec chemin continu jusqu'au même coin `0/0`.
        Les fonctions positives arbitraires restent hors de cette famille.
        - [x] Pour deux fonctions scalaires arbitraires tendant vers zéro,
          construire le chemin diagonal commun et classifier la limite de la
          racine par la limite finie ou infinie de leur ratio. Ceci ne classe
          toujours pas les chemins matriciels non diagonaux.
          - [x] Sous une similarité mobile régulière, promouvoir toute limite
            finie du ratio en limite explicite de la matrice-racine entière et
            exclure toute limite matricielle finie lorsque le ratio diverge.
- [ ] Étendre la suite explicite retenue à tous les chemins matriciels `0/0`,
  aux similarités mobiles ou cadres singuliers arbitraires, puis classifier
  les changements généraux de type Jordan et construire l'atlas de branches.
  - [x] Exclure toute extension matricielle continue monovaluée qui contient
    la famille diagonale et coïncide avec sa racine principale intérieure : sa
    restriction hérite des deux limites diagonales incompatibles au même coin.
    Ceci est une obstruction universelle, pas une classification des chemins.
  - [x] Pour toute conjugaison réelle fixe munie d'un inverse, reconstruire
    exactement le spectre diagonal, transporter la trichotomie monomiale et
    exclure le prolongement continu sur cette classe simultanément
    diagonalisable. Les similarités mobiles sont traitées séparément.
  - [x] Pour toute similarité mobile régulière dont le changement de base et
    l'inverse convergent, transporter les limites matricielles et prouver que
    la trichotomie monomiale `0/0` reste exactement inchangée après extraction
    dans le repère mobile. Les cadres singuliers arbitraires restent ouverts.
    - [x] Pour les deux branches à limite finie, promouvoir cette convergence
      coordonnée en convergence du spectre entier puis de la matrice-racine
      conjuguée, avec limite explicite dans le repère mobile limite.
    - [x] Pour la branche à dénominateur plus rapide, exclure toute limite
      matricielle finie : sa conjugaison inverse aurait une entrée diagonale
      finie, contrairement à la divergence extraite vers `+∞`.
  - [x] Pour les cadres diagonaux singuliers à exposants entiers, classifier
    exactement l'existence d'une limite finie de toute matrice monomiale par
    la non-négativité de ses valuations actives, y compris coefficients signés ;
    étendre le critère suffisant et l'obstruction aux sommes monomiales finies
    à terme dominant non nul. Les cadres singuliers non diagonaux et séries
    non analytiques restent ouverts.
    - [x] Pour les sommes monomiales finies à terme dominant non nul, promouvoir
      convergence et obstruction en une équivalence exacte entre existence
      d'une limite matricielle finie et non-négativité de toutes les valuations.
    - [x] Étendre l'équivalence monomiale à tout cadre singulier obtenu par
      conjugaison fixe inversible d'un cadre diagonal : la limite finie existe
      exactement sous la même condition de valuations et vaut la conjugaison
      fixe de la limite diagonale. Les cadres singuliers dont les directions
      propres varient avec le paramètre restent ouverts.
      - [x] Étendre le même critère exact aux sommes monomiales finies à terme
        dominant non nul : une conjugaison fixe inversible conserve
        l'équivalence entre valuations non négatives et limite finie.
      - [x] Autoriser une conjugaison extérieure mobile régulière, avec matrice
        et inverse convergentes : pour les matrices monomiales et polynomiales
        finies, elle préserve et reflète exactement l'existence d'une limite
        finie du transport singulier intérieur. Les directions propres sans
        limite ou à inverse extérieur divergent restent ouvertes.
        - [x] Identifier la limite dans les deux cas : elle est exactement la
          conjugaison de la limite de valuation diagonale par les limites de
          la base extérieure mobile et de son inverse.
    - [x] Étendre le critère exact de valuation à toute matrice dont chaque
      entrée possède un terme dominant asymptotique non nul certifié : les
      valuations non négatives sont équivalentes à l'existence d'une limite
      matricielle finie. Cela couvre les séries convergentes une fois leur
      asymptotique dominante fournie, sans classifier les cadres arbitraires.
      - [x] Autoriser un masque actif abstrait : les entrées actives gardent
        un terme dominant non nul certifié, les entrées inactives sont
        éventuellement nulles et n'imposent aucune valuation.
        - [x] Transporter ce critère actif abstrait par toute base extérieure
          mobile régulière convergente, avec limite conjuguée explicite et
          équivalence nécessaire/suffisante conservée.
      - [x] Pour tout germe de série convergente non nul, extraire
        automatiquement son ordre, factoriser l'entrée par la puissance
        dominante et fournir le résidu continu non nul requis par le critère.
        - [x] Autoriser aussi les entrées à série identiquement nulle : elles
          sont inactives et n'imposent aucune valuation, tandis que les entrées
          analytiques actives conservent le critère nécessaire et suffisant.
          - [x] Transporter ce critère analytique avec entrées nulles par toute
            base extérieure mobile régulière dont la matrice et l'inverse
            convergent, avec limite conjuguée explicite.
      - [x] Transporter exactement ce critère par toute base extérieure mobile
        régulière dont la matrice et l'inverse convergent ; identifier la limite
        à la conjugaison de la limite de valuation par les deux limites de base.
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
    - [x] Construire le vrai Hessien de cette même densité globale à huit
      composantes, dériver la première variation intégrée dans une seconde
      direction sous domination explicite et prouver sa symétrie sous C².
      - [x] Sommer ce Hessien aux vrais Hessians matière, Robin et LL sur le
        paquet sectoriel commun, puis identifier la dérivée de l'Euler de la
        même action à cette somme symétrique.
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
    - [x] construire le ghost difféomorphe, le BRST non abélien/BV et leur
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
                  - [x] Construire une triple non abélienne fermée explicite de
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
                    - [x] Étendre ce différentiel corrigé aux métriques, jauges,
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
                      - [ ] Étendre la fermeture tensorielle générale aux
                        termes dérivatifs et aux fonctionnelles arbitraires ou
                        complétées avec équation maîtresse fonctionnelle. Le
                        modèle non local rang-un est fermé ci-dessous.
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
                              CME intégrée. Les termes dérivatifs et les
                              fonctionnelles arbitraires/complétées restent
                              ouverts ; le rang-un est fermé ci-dessous.
                              - [x] Décharger le contrat bulk par les
                                trivialisations tangent/cotangent, l'inversion
                                lisse du musical local et l'invariance de la
                                trace : tous les pairings de tenseurs lisses sont
                                continus et `L¹`, donc intégrabilité,
                                développement affine et `HasDerivAt`/gradient
                                intégrés sont inconditionnels. Les termes
                                dérivatifs et les fonctionnelles arbitraires ou
                                complétées restent ouverts.
                              - [x] Construire de vraies observables
                                fonctionnelles bulk à gradients certifiés, leur
                                odd bracket fonctionnel et le master non local
                                rang-un : dérivée affine, CME, génération et
                                carré nul du BRST, avec témoin intrinsèque non
                                nul. Les noyaux dérivatifs, espaces complétés et
                                fonctionnelles arbitraires restent ouverts.
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
                                Les termes dérivatifs et les fonctionnelles
                                arbitraires ou complétées restent ouverts.
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
                                  continuité est encore isolé à cette étape et
                                  aucune CME fonctionnelle générale ou
                                  dérivative n'est revendiquée.
                                  - [x] Décharger ce contrat par les
                                    trivialisations tangent/cotangent,
                                    l'inversion continue du musical local et
                                    l'invariance de la trace : toute densité de
                                    pairing de tenseurs lisses est continue et
                                    `L¹`. Rendre ainsi inconditionnelles
                                    l'intégrabilité action/bracket, l'expansion
                                    affine et les `HasDerivAt` intégrés. La CME
                                    fonctionnelle générale et les termes
                                    dérivatifs restent ouverts.
                                  - [x] Construire les observables fonctionnelles
                                    intrinsèques du throat avec gradients
                                    certifiés, odd bracket et master non local
                                    rang-un : dérivée affine, CME, génération et
                                    carré nul du BRST, avec témoin throat non
                                    nul. Aucun terme dérivatif, espace complété
                                    ni fonctionnelle arbitraire n'est fermé.
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
      - [x] Quotienter le graphe `H¹` canonique par le noyau de sa projection
        continue vers le `L²` physique, obtenir un quotient complet à
        réalisation `L²` injective et conserver la densité des champs lisses ;
        prouver aussi que la trace canonique descend exactement si elle
        s'annule sur ce noyau vertical. Cette annulation et les ordres
        Sobolev supérieurs restent ouverts.
        - [x] Prouver dans une vraie carte euclidienne de dimension finie la
          formule d'intégration par parties pour `ρ c η · D_v f`, avec test
          `C∞` à support compact, intégrabilité effectivement déduite et adjoint
          pondéré explicite `-ρ⁻¹ D_v(ρ c η)` lorsque `ρ` ne s'annule pas. Le
          changement de variables de la mesure canonique dans les cartes et
          l'identification avec `frameDerivative` restent à construire avant
          toute conclusion de closabilité globale sur le quotient D8.
          - [x] Identifier exactement, par la chaîne de Fréchet de variété, le
            gradient scalaire de cette carte au différentiel intrinsèque du même
            champ sur son repère holonome, puis le relier à `frameDerivative`
            sous l'égalité tangentielle ponctuelle explicite du générateur.
            L'identité de changement de mesure et cette égalité pour la frame
            globale canonique restent ouvertes.
            - [x] Pour la famille génératrice finie effectivement construite,
              identifier son ouvert à la source de `chartAt` et son vecteur
              local à la dérivée `mfderivWithin` de la carte inverse, puis
              spécialiser la formule précédente. L'accord de ce vecteur avec
              le repère holonome total fourni reste une hypothèse ponctuelle
              explicite, et non une fermeture globale de l'IPP.
              - [x] Éliminer cette hypothèse pour la formule complète en
                décomposant chaque vecteur de la frame finie dans une vraie base
                holonome : `frameDerivative` est exactement la somme pondérée
                des quatre gradients locaux, et un tel patch total existe à
                chaque point. Le changement de variables de la mesure canonique
                dans ces patches reste le verrou de l'IPP globale.
                - [x] Sur le collier de latitude positive, identifier la densité
                  canonique au Jacobien exact `ENNReal.ofReal (cos²)`, prouver
                  l'IPP pondérée sur chaque fibre puis son identité mesurée sur
                  la vraie base `S² × temps`, et exprimer ponctuellement la
                  dérivée normale par la somme des quatre gradients locaux d'un
                  patch holonome total existant. Le patch reste dépendant du
                  point : aucune sélection mesurable ni IPP globale dans une
                  carte `Vector4` unique n'est affirmée.
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
        Preuve d'appui : `P0EFTJanusMappingTorusH1FrameIndependence4D` prouve
        l'équivalence des normes et complétés pour deux familles reliées, dans
        les deux sens, par des coefficients lisses uniformément bornés sur un
        recouvrement compact fini ; il raccorde aussi la frame physique aux
        composantes localisées de l'atlas fixe.
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
                - [x] Conserver cette régularité `C∞` sur le collier quotient
                  complet et prouver que son lift normal bundlé, obtenu par le
                  tangent map sur la section verticale, est conjointement `C∞`.
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
        - [x] Sur l'atlas fixe, construire le jet holonome `ℓ²`, l'identifier
          exactement au jet du graphe fini et prouver les deux dominations
          uniformes entre leurs densités. Le pont vers la densité historique à
          second centre variable reste séparé et conditionnel.
        - [x] Retirer du chemin critique la densité historique fondée sur le
          choix variable `chartAt p` : la densité de l'atlas fixe est désormais
          identifiée exactement au graphe fini et lui est uniformément
          équivalente. Aucune égalité artificielle avec ce choix de carte
          discontinu n'est requise ni revendiquée.
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
  - [x] Étendre l'involution PT/échange du paquet aux métriques générales,
    matière, jauge, ghosts, auxiliaires, antifields/BV de premier niveau et
    conditions au bord retenues. Les inversions de traces métriques générales,
    termes dérivatifs et fonctionnelles arbitraires restent séparés.
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
      retenue ; les masters fonctionnels rang-un bulk/throat sont fermés, mais
      l'inversion des restrictions générales, les termes dérivatifs et les
      fonctionnelles arbitraires/complétées restent explicitement ouverts.
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
          - [x] Sous l'unique contrat Green--Stokes 4D explicite, identifier ce
            boundary functional au flux normal tangent concret et fermer les
            formules de première variation, stationnarité et Euler faible sous
            Dirichlet. Le contrat Green--Stokes lui-même reste à prouver.
            - [x] Fermer le ledger de signe des deux lifts du throat coupé : le
              deck inverse simultanément le courant scalaire et l'orientation
              sortante, donc les contributions orientées sont égales, leur
              somme vaut deux fois un lift et leur différence est nulle. La
              variété coupée et Stokes global restent ouverts.
              - [x] Identifier le bord topologique correct du cut comme le
                double revêtement d'orientation connexe du throat one-sided,
                prouver que son image est exactement le throat et que chaque
                fibre contient deux lifts distincts échangés par le deck. La
                structure de variété à bord reste à construire.
                - [x] Construire le bulk coupé topologique comme mapping torus
                  de l'hémisphère positif fermé à période doublée, prouver
                  sa surjectivité vers le bulk initial, l'injectivité de son
                  double bord et la commutation du carré bord/bulk. La
                  structure lisse à bord et Stokes restent ouverts.
                  - [x] Prouver que l'inclusion compacte du double bord dans
                    le bulk coupé hausdorff est un plongement fermé. Le
                    recollement lisse reste ouvert.
                  - [x] Construire le collier fini du double bord comme vrai
                    4-manifold analytique à bord, identifier exactement sa
                    frontière aux deux faces lisses injectives throat/interface.
                    Le recollement au reste du bulk et Stokes restent ouverts.
                    - [x] Attacher le collier de latitude `[0,1]` au bulk coupé
                      par un plongement fermé, identifier sa face zéro à
                      l'inclusion du double throat et sa face un à une interface
                      extérieure explicite plongée fermée. La compatibilité
                      lisse globale et Stokes restent ouverts.
                      - [x] Faire descendre la latitude au quotient, identifier
                        exactement l'image du collier à la bande fermée
                        `0 ≤ latitude ≤ sin 1` et l'interface extérieure au
                        niveau `latitude = sin 1`.
                        - [x] Décomposer le bulk coupé en deux fermés couvrants,
                          collier et reste extérieur, dont l'intersection est
                          exactement l'interface latitude `sin 1`.
                          - [x] Retirer la face artificielle et identifier le
                            collier ouvert au vrai ouvert intrinsèque
                            `latitude < sin 1` par un plongement ouvert.
                            - [x] Munir le collier ouvert de l'atlas analytique
                              induit du collier fini et prouver l'analyticité
                              de son inclusion.
                            - [x] Construire le cap ouvert `latitude > 0`,
                              prouver qu'il couvre le bulk avec le collier et
                              identifier l'overlap à `0 < latitude < sin 1`.
                              - [x] Construire le modèle du cap comme mapping
                                torus analytique 4D de l'hémisphère strictement
                                positif, avec projection locale difféomorphe.
                                - [x] L'identifier par plongement ouvert au cap
                                  intrinsèque `latitude > 0` et construire
                                  l'homéomorphie canonique correspondante.
                                  - [x] Transporter l'atlas analytique sur le
                                    cap intrinsèque et prouver l'analyticité
                                    de cette homéomorphie dans les deux sens.
                                    - [x] Restreindre le difféomorphisme
                                      tubulaire à `0 < normal < 1` et prouver
                                      la transition `C∞` collier–calotte
                                      dans les deux sens sur les revêtements.
                                      - [x] Identifier exactement son image à
                                        `0 < latitude < sin 1`.
                                      - [x] Prouver le lemme générique de
                                        descente lisse d'une application de
                                        revêtements équivariante sous les decks.
                                        - [x] Construire le foncteur lisse
                                          des mapping tori à monodromie
                                          identité et son action sur les
                                          difféomorphismes de fibres.
                                          - [x] L'instancier sur la transition
                                            tubulaire et descendre le
                                            difféomorphisme `C∞` aux deux
                                            mapping tori de l'overlap.
                                            - [x] Plonger ouvertement et `C∞`
                                              le mapping torus de bande stricte
                                              dans la calotte lisse complète.
                                              - [x] Identifier exactement son
                                                image intrinsèque à
                                                `0 < latitude < sin 1`.
                                                - [x] Transporter cette image
                                                  intrinsèque exacte au modèle
                                                  lisse de l'overlap collier.
                                                  - [x] Factoriser ce modèle
                                                    par plongement ouvert dans
                                                    le collier intrinsèque.
                                                    - [x] Descendre la
                                                      coordonnée normale en
                                                      fonction `C∞` quotient.
                                                      - [x] Descendre la
                                                        projection vers le
                                                        bord du collier en
                                                        application `C∞`.
                                                        - [x] Assembler les
                                                          deux composantes et
                                                          identifier la carte
                                                          canonique `C∞` vers
                                                          le collier intrinsèque.
                                                          - [x] Identifier les
                                                            paramètres stricts
                                                            au produit bord ×
                                                            `Ioo(0,1)` par un
                                                            difféomorphisme `C∞`.
                                                            - [x] Prouver que
                                                              le mapping torus
                                                              identité commute
                                                              `C∞` au facteur
                                                              produit passif.
                                                              - [x] Instancier
                                                                ce résultat et
                                                                identifier
                                                                l'overlap à bord
                                                                × `Ioo(0,1)`.
                                                                - [x] Identifier
                                                                  ce produit au
                                                                  sous-ouvert
                                                                  intrinsèque
                                                                  `normal > 0`
                                                                  dans les deux
                                                                  sens `C∞`.
                                                                  - [x] Identifier
                                                                    le modèle
                                                                    euclidien du
                                                                    cap à
                                                                    l'intérieur du
                                                                    modèle demi-espace
                                                                    du collier dans
                                                                    les deux sens
                                                                    `C∞`.
                                                                    - [x] Recharter
                                                                      le modèle du
                                                                      cap dans ce
                                                                      modèle commun
                                                                      demi-espace.
                                                                      - [x] Composer
                                                                        l'atlas du
                                                                        cap intrinsèque
                                                                        avec ce modèle
                                                                        commun et
                                                                        prouver sa
                                                                        compatibilité
                                                                        `C∞`.
                                                                        - [x] Relever
                                                                          les cartes
                                                                          des deux
                                                                          ouverts et
                                                                          installer
                                                                          l'atlas
                                                                          topologique
                                                                          global.
                    - [x] Descendre le courant tordu en vrai scalaire lisse sur
                      le double bord : invariance sous les windings pairs et
                      anti-invariance sous le deck résiduel prouvées.
                      - [x] Identifier le deck résiduel à la translation de
                        demi-période, prouver l'invariance de la mesure
                        canonique et l'annulation de l'intégrale scalaire non
                        orientée. Le flux orienté de Stokes reste distinct.
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
                Preuve d'appui supplémentaire :
                `P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D`
                construit globalement sur D8 le secteur conforme positif
                `a g₀,b g₀`, sa racine Candidate A intrinsèque et son accord
                dans toute frame avec la spécialisation `Matrix4` isotrope.
                Cette note n'ajoute aucune unité au compteur historique.
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
                      - [x] Prouver que cette même mesure lorentzienne canonique
                        est préservée par chaque tranche du vrai flot temporel
                        complet D8 : wrap du domaine fondamental, monodromie par
                        réflexion aux enroulements impairs, skew-product
                        mesure-préservant et semiconjugaison exacte au quotient.
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
    - [x] Promouvoir les quatre coefficients du repère holonomique fixé en une
      équivalence linéaire continue exacte avec l'espace tangent modèle.
    - [x] Construire le sharp diagonal explicite dans ces coordonnées, prouver
      son identité d'inverse et retrouver exactement le terme cinétique sous
      le pont de composantes du covecteur modèle.
    - [x] Promouvoir le flat diagonal en application linéaire continue, prouver
      sa bijectivité par le sharp et obtenir le musical continu exact vers le
      dual du tangent modèle.
    - [x] Construire la frame continue obtenue par racines carrées des quatre
      magnitudes positives et identifier exactement le pairing diagonal au
      pairing de Minkowski d'inertie `(3,1)`.
    - [x] Identifier la matrice de Gram holonomique à la matrice lorentzienne
      diagonale et prouver l'égalité exacte de sa densité `sqrt |det|` avec le
      facteur de volume de l'action globale.
    - [x] Tirer le musical diagonal vers chaque trivialisation tangente
      canonique, obtenir un vrai tenseur local inversible sur la fibre tangente
      et certifier son inertie lorentzienne par une frame locale explicite.
    - [x] Prouver que l'accord de deux tenseurs locaux sur un overlap équivaut
      exactement à la préservation du pairing diagonal par la transition de
      frames, puis formuler le contrat cocycle global correspondant.
    - [x] Assembler canoniquement une famille ponctuelle globale par les patches
      centrés, prouver sa non-dégérescence et son inertie lorentzienne, puis son
      accord avec toute réalisation locale sous le cocycle.
    - [x] Isoler l'interface de réalisation tensorielle lisse exacte et prouver
      qu'elle produit automatiquement un vrai `SmoothGeneralLorentzMetric`
      avec le musical et l'inertie déjà certifiés.
    - [ ] Achever la complétion Sobolev intrinsèque et l'équation d'Euler
      covariante avec les conditions au bord retenues.
      - [x] Dans le quotient fonctionnel `H¹` canonique déjà complet, définir
        le domaine de Dirichlet comme l'image du vrai noyau de trace graphé,
        y faire entrer toute variation lisse de trace nulle, puis prouver que,
        sur exactement ce cœur de bord, l'Euler faible est la stationnarité de
        la même action scalaire globale et que son Hessien réel est le Jacobi
        symétrique. La continuité de l'Euler sur tout le quotient et la
        dynamique lorentzienne restent ouvertes.
      - [x] Prouver inconditionnellement que tout jet limite vertical, nul sous
        la projection valeur vers le `L²` physique, a une trace physique nulle :
        établir une estimation de trace interpolée à échelle arbitraire sur le
        cœur lisse, l'étendre par densité au graph-`H¹`, puis faire tendre
        l'échelle vers zéro. La trace radiale-polaire descend ainsi au vrai
        quotient fonctionnel, sans affirmer que tout jet vertical est nul.
- [ ] Dériver les équations matière covariantes.
  - [x] Sur le vrai quotient D8 et la même action scalaire globale, construire
    `K` faible et son Jacobi `J` symétrique pour tous les champs lisses sous le
    contrat commun d'intégrabilité, puis les identifier exactement à la
    première et seconde variation. Isoler le coefficient temporel lorentzien
    strictement négatif ; sur le seul secteur statique positif, construire le
    Hilbert d'énergie, le Riesz fort, son domaine dense, son noyau nul et
    l'équivalence stationnaire/faible/forte. La dynamique lorentzienne complète
    n'est pas déclarée positive.
    - [x] Définir la dérivée directionnelle effective par `deriv` de cette action
      globale inchangée, l'identifier au pairing Euler faible, puis prouver que
      sa dérivée le long d'une seconde courbe affine est exactement le pairing
      Jacobi et qu'elle est symétrique : celui-ci est donc une vraie seconde
      variation mixte de la même
      action D8, sans revendication sur le Hessien périodique `J†HJ`.
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
  - [x] Déduire les identités locales de conservation à partir des équations
    covariantes et de l'identité de Noether locale. Les boules du modèle
    `S³ × ℝ` possèdent maintenant des paramétrisations totales par `R⁴`, ce qui
    construit un atlas holonome couvrant indépendant des champs. Sur cet atlas,
    les équations d'Euler scalaires impliquent la nullité de la divergence de
    stress dans chaque carte et en chaque point du quotient. Cette fermeture
    est coordinate-global ; elle ne construit pas un second champ abstrait de
    dérivée covariante indépendamment de ces représentants locaux.
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
            La construction générique d'un patch passant par chaque point est
            désormais fournie par l'atlas total ci-dessous. Une connexion
            globale abstraite indépendante des représentants locaux n'est pas
            ajoutée.
            - [x] Tirer tout vrai `SmoothScalarField` quotient sur ce patch,
              prouver sa régularité `C∞` ainsi que celle du gradient et du
              Hessien brut, fermer la symétrie de Schwarz et obtenir un vrai
              `CoordinateScalarJet2`. Construire le jet covariant, le résiduel
              d'Euler, le gradient relevé et la divergence de stress locale
            canoniquement réalisée, tous `C∞`, puis prouver l'identité exacte
            `div T = EulerResidual · raisedGradient` et la conservation sous
            Euler. La réalisation générique de l'atlas holonome est désormais
            déchargée par les paramétrisations totales ; le recollement est
            fermé ci-dessous.
              - [x] Prouver la compatibilité finie sur un overlap fourni : si
                les deux représentants ont la même matrice métrique et son
                premier jet, ainsi que le même champ scalaire, gradient et
                second jet brut, alors coïncident exactement les Christoffel,
                le jet scalaire covariant, le résidu d'Euler, le gradient relevé
                et la divergence de stress.
              - [x] Prouver l'analyticité des transitions locales du vrai
                quotient, fermer les lois réflexive/symétrique/transitive des
                jets rebasés et en déduire l'accord des divergences de stress.
                Une famille couvrante de vrais patches holonomes est maintenant
                construite inconditionnellement.
              - [x] Sous ce seul pont d'atlas couvrant, recoller le résidu
                d'Euler, le gradient relevé et la divergence de stress en champs
                globaux indépendants du patch, puis prouver pointwise
                `div_g T = EulerResidual · raisedGradient` et `div_g T = 0` sous
                les équations d'Euler locales. Le pont d'atlas est maintenant
                réalisé par l'atlas total canonique.
                - [x] Réduire plus précisément ce pont à l'existence d'un patch
                  holonome passant par chaque point : Euler implique alors
                  pointwise `div_g T = 0` sans imposer l'égalité des tableaux de
                  jets bruts. Ces patches existent désormais à chaque point.
- [ ] Définir le contenu de champs exact qui sera utilisé par D9/D10 et par le
  régulateur quantique.
  - [x] Projeter de façon typée la même variation indépendante globale vers
    les slots D9 effectivement fournis (métrique diagonale induite, jauge
    tangentielle, ghost `U(1)`, matière), et prouver que cette projection
    métrique n'est pas surjective vers les tenseurs symétriques D9 généraux.
    - [x] Injecter fidèlement toute paire de directions jauge dans ce même
      `IndependentFieldVariation` et calculer sa projection : D9 reçoit
      exactement les trois lignes spatiales de la colonne sectorielle choisie,
      tandis que ses slots matière, ghost et métrique restent nuls. L'action
      Maxwell correspondant à cette direction n'est pas encore construite.
      - [x] Caractériser un noyau temporel concret de cette projection : toute
        direction jauge dont les trois composantes spatiales au throat sont
        nulles a une projection D9 jauge nulle, bien que son injection dans
        l'espace commun reste non nulle lorsqu'elle l'est. D9 perd donc
        honnêtement cette information temporelle.
    - [x] Injecter fidèlement toute paire de directions ghost `U(1)` dans ce
      même `IndependentFieldVariation` et calculer sa projection : le slot
      ghost D9 est exactement la composante au throat et à la colonne choisie,
      tandis que les slots métrique, jauge et matière restent nuls. Ce pont
      structurel ne ferme pas le complexe BRST global.
    - [x] Injecter fidèlement toute paire de directions auxiliaires dans ce
      même `IndependentFieldVariation` et prouver que les quatre slots D9
      actuellement exposés (métrique, jauge, ghost `U(1)`, matière) sont nuls.
      La perte d'information est celle de la projection D9 actuelle ; aucun
      complexe auxiliaire global n'est revendiqué.
    - [x] Injecter fidèlement toute direction de métrique diagonale lisse dans
      ce même `IndependentFieldVariation` et calculer sa projection D9 : le
      bloc métrique contient exactement les trois vitesses diagonales spatiales
      sélectionnées, les termes hors diagonale et les slots jauge, ghost et
      matière étant nuls. Cela ne couvre pas un tenseur métrique D9 général.
      - [x] Caractériser le noyau temporel correspondant : une direction
        métrique diagonale non nulle dont les trois vitesses spatiales au throat
        s'annulent reste distincte du zéro dans l'espace commun mais possède la
        même projection métrique D9 nulle.
    - [x] Assembler simultanément les six directions déjà construites
      (métrique, matière, jauge, ghost, auxiliaire et LL) dans une unique
      variation commune, prouver l'injectivité du paquet et les quatre formules
      D9 bloc par bloc. Les directions auxiliaire/LL et les blocs temporels
      invisibles sont isolés explicitement, sans conclure à un contenu D9 complet.
      - [x] Empaqueter les quatre sorties D9 visibles et caractériser exactement
        l'égalité de deux projections combinées par l'égalité de ces quatre
        blocs ; en particulier, toute modification auxiliaire/LL seule conserve
        la projection.
        - [x] Quotienter les directions communes par l'égalité de cette
          observation D9 ponctuelle, faire descendre la projection injectivement
          et prouver que les modifications auxiliaire/LL à données visibles
          fixées ont la même classe. Ce n'est pas un quotient de jauge global.
      - [x] Relier la même action matière globale à cette variation combinée :
        l'extraction des huit composantes et la courbe d'action coïncident avec
        la courbe matière seule, le vrai `HasDerivAt` se transporte, et les cinq
        autres directions n'affectent pas cette action sectorielle.
      - [x] Relier de même l'action LL différentielle et sa première variation
        à la direction LL extraite du paquet combiné, puis transporter les
        vrais théorèmes de dérivée et Hessien de cette même action LL.
        - [x] Reconstruire exactement la courbe de cette action PT globale le
          long d'une vraie direction LL jusqu'au degré quatre : identifier le
          coefficient linéaire au véritable Euler LL et deux fois le coefficient
          quadratique au Hessien LL diagonal de la même action, en conservant
          explicitement les coefficients cubique et quartique intégrés. Ce
          résultat n'affirme aucune reconstruction depuis le seul Hessien.
          - [x] En déduire les dérivées itérées diagonales exactes d'ordres
            trois et quatre de cette vraie courbe d'action : elles valent
            respectivement `6 C3` et `24 C4`, sous mesure finie.
          - [x] Spécialiser les coefficients intégrés `C1/C2` à la même
            direction LL complète et prouver directement `∫C1 = Euler` et
            `∫C2 = Hessien(direction,direction)/2`.
    - [x] Injecter toute direction LL lisse dans ce même vrai type
      `IndependentFieldVariation`, avec toutes les autres directions nulles,
      puis prouver que la courbe globale simultanée obtenue est exactement la
      courbe LL utilisée par l'action et son Hessien ; transporter sur cette
      courbe les deux théorèmes `HasDerivAt` effectifs. Sur le domaine commun,
      action, Hessien et D9 partent donc de la même configuration et consomment
      le même type de variation dans cette direction.
      - [x] Calculer honnêtement la projection D9 de cette direction LL seule :
        ses composantes métrique, jauge, ghost `U(1)` et matière sont toutes
        nulles. Le Hessien LL est donc actuellement invisible dans les slots D9
        fournis ; ce calcul isole un vrai contenu manquant au lieu de conclure
        frauduleusement à l'accord complet.
        - [x] Prouver que l'injection de la direction LL dans l'espace commun
          est fidèle, mais que tous les slots D9 actuellement fournis identifient
          deux directions LL quelconques. La perte d'information est ainsi
          localisée dans la projection D9, et non dans l'espace de variations.
    - [x] Munir le vrai `IndependentFieldVariation` de sa structure de module
      réel composante par composante, rendre linéaires les extractions matière
      et LL, puis empaqueter le Hessien matière+LL de la même action comme une
      vraie forme bilinéaire symétrique sur ce tangent commun et l'identifier à
      la seconde variation mixte déjà prouvée sur le paquet à six directions.
      Ce pont reste sectoriel : il n'ajoute ni terme EH, ni Maxwell, ni BRST.
      Preuve d'appui supplémentaire : le gate
      `P0EFTJanusCompleteVariationModuleCore4D` étend cette structure au vrai
      `ProgramPCompleteVariation4D`, rend linéaire son inclusion canonique et
      ses lectures normales, ghosts tangents et métriques locales. Cette note
      n'ajoute aucune unité au compteur historique.
      - [x] Identifier le sous-module exact annulant simultanément les lectures
        matière et LL, prouver que le Hessien réel l'annule dans ses deux
        arguments, puis le faire descendre en une forme bilinéaire symétrique
        sur le quotient algébrique. Toute direction du slot jauge y appartient
        parce que Maxwell est absent ; ce quotient sectoriel n'est donc pas
        présenté comme le vrai quotient de jauge du Programme P.
        - [x] Raffiner vers le noyau des quatre blocs réellement lus par la même
          courbe d'action (matière, métrique auxiliaire LL, mesure LL et champ
          LL), prouver l'invariance exacte de cette courbe sous toute translation
          du noyau, puis faire descendre le Hessien symétrique au même quotient.
          Cette factorisation commune reste celle du secteur matière+LL seul.
          - [x] Attacher au même `ProgramPCompleteVariation4D` le doublet BV de
            métrique tensorielle générale, puis prouver que son BRST carré-nul
            laisse exactement inchangés la courbe, la première variation et le
            Hessien matière+LL tout en préservant le domaine de bord actuel.
            L'absence de dynamique EH/Maxwell dans ces égalités reste explicite.
            - [x] Identifier sur ce même tangent complet l'action et le Hessien
              descendus au quotient visible matière+LL, tout en calculant la
              lecture métrique D9 du slot BV et son appartenance au domaine de
              bord. Ce pont reste sectoriel et n'ajoute ni EH ni Maxwell.
            - [x] Relever le même doublet métrique BV dans le wrapper complet
              enrichi par Robin, conserver exactement ce slot Robin, calculer
              les lectures D9 du tenseur puis de l'antichamp et prouver que le
              BRST carré-nul laisse inchangés action, Euler, Hessien
              matière+Robin+LL et domaine de bord actuel. Ce pont n'ajoute ni
              EH, ni Maxwell, ni opérateur BRST global/non linéaire.
          - [x] Relever dans le même `ProgramPCompleteVariation4D` les seules
            coordonnées ghosts du bloc BRST linéaire `U(1)^2` plus ghost tangent
            lisse du throat, identifier exactement leur lecture D9, transporter
            le carré nul, prouver l'admissibilité au bord de l'image BRST et
            l'invariance de la courbe, de la première variation et du Hessien
            matière+LL. Les potentiels abéliens intrinsèques ne sont pas insérés
            dans le slot de jauge coordonné ; Maxwell et le BRST difféomorphe
            non linéaire/global restent donc explicitement hors de cet énoncé.
            - [x] Relever ce même bloc BRST linéaire dans le wrapper complet
              enrichi par Robin à vitesse Robin nulle, conserver son carré nul
              et son admissibilité au bord, puis prouver l'invariance exacte de
              l'action et du Hessien matière+Robin+LL actuels. Aucun potentiel
              abélien, Maxwell, bloc Fredholm ghost, régulateur ou résultat
              d'anomalie globale n'est ajouté.
  - [x] Construire les modes D10 tronqués comme de vraies troncatures des
    `ProductDiracMode`, avec multiplicité sphérique, période `|period|`, action
    PT exacte, spectre envoyé au régulateur et annulation chirale régulée finie.
  - [x] Alimenter localement le mode normal D9 par une vraie section lisse du
    fibré normal D8 ; prouver que la transition après un tour vaut `-1` et que
    le carré de chaque multiplicateur `Z4` reproduit ce signe. Aucune
    coordonnée scalaire globale canonique n'est revendiquée.
  - [x] Insérer le vrai ghost difféomorphe tangent lisse dans le package local
    D9 déjà alimenté par la section normale, avec composantes normale et ghost
    exactes. Seule l'identification matière--spineur subsiste dans ce résidu local.
    La fibre matière réelle est maintenant identifiée aux coordonnées réelles
    du spineur carré. Les six composantes spatiales d'un vrai tenseur symétrique
    global remplissent aussi le slot métrique D9 dans une carte holonome choisie
    automatiquement à chaque point du throat. Cela ne les identifie pas encore
    au tangent de l'action globale.
  - [ ] Fournir l'identification `Pin⁻`/`PinC`, les métriques hors diagonale,
    puis prouver l'accord entre action, Hessien, développement modal et domaines
    au bord dans les contrats résiduels.
    - [x] Sur le même `ProgramPCompleteVariation4D`, joindre une vraie section
      de la ligne normale, la métrique BV générale et le champ D9, puis prouver
      que le mode normal change exactement par la réduction d'orientation du
      fibré principal `Pin⁻(1)` construit, tandis que l'action et le Hessien
      matière+LL descendus ainsi que le domaine de bord lisent la même direction.
      Ce pont reste normal et sectoriel : `Pin⁻(4)` tangent, `PinC`, EH/Maxwell
      et l'accord modal D10 restent ouverts.

**Acceptation** : un espace de champs unique sert à l'action, au Hessien, au
complexe BRST, aux anomalies et aux conditions au bord.

## 5. Verrou 3 — bulk, frontières, joints et worldvolume LL

- [ ] Construire l'action EH des deux métriques sur la géométrie globale.
- [ ] Dériver sa première variation en coordonnées arbitraires.
- [x] Construire et varier les termes GHY sur toute famille finie de faces non nulles en jauge normale de Gauss.
  Preuve d'appui locale :
  `P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D` identifie le
  1-jet du collier de latitude canonique à des données Gaussian-normal avec
  `∂ₙh|₀ = 0`, seconde forme et trace nulles, et lifts normaux opposés. Cela ne
  constitue pas une intégration EH/GHY globale.
  - [x] Pour toute famille finie pondérée de faces en jauge normale de Gauss,
    construire les courbes GHY exact-inverse et sommer leurs vraies dérivées.
- [x] Prouver l'annulation intégrée du flux EH+GHY pour ces faces et conditions au bord retenues.
  - [x] Prouver face par face puis après toute somme finie que la dérivée GHY
    annule exactement le flux de Palatini--Einstein en jauge normale de Gauss.
- [x] Construire les termes de frontière nulle : inaffinité, expansion et
  contre-terme de reparamétrisation.
  Dans le modèle fini le long des générateurs fournis, l'action assemble
  l'intégrale d'inaffinité, le contre-terme d'expansion à extension continue
  et les joints d'extrémité. Sa loi de reparamétrisation finie et son
  annulation avec les joints sont exactes. La géométrie ambiante doit encore
  fournir aire, générateurs et `NullFaceIntervalIntegrability`.
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
    l'action LL physique, puis dériver la vraie PDE forte covariante sans
    contrat géométrique résiduel.
    - [x] Sur le vrai throat compact, construire sans hypothèse une famille
      tangentielle lisse finie génératrice, l'énergie différentielle LL et une
      dépendance non triviale à la métrique auxiliaire ; dériver les variations
      intégrées et l'équation faible stationnaire exacte. L'identification
      covariante sans frame, la contraction lorentzienne intrinsèque et les
      flux géométriques restent ouverts.
      Preuve d'appui intrinsèque :
      `P0EFTJanusMappingTorusIntrinsicLLKineticAction4D` remplace le poids
      scalaire auxiliaire par l'inverse musical de la vraie métrique du throat,
      dérive la première variation et le Hessien symétrique, puis prouve la
      covariance PT canonique intégrée. La PDE forte et les flux restent ouverts.
    - [x] Pour la mesure canonique réelle du throat, prouver sans hypothèse sa
      positivité sur tout ouvert non vide, donc son support complet.
    - [x] Construire l'opérateur d'Euler fort par divergence de la frame et
      prouver faible ↔ fort ainsi que stationnaire ↔ fort sous le contrat
      analytique explicite, la formule globale d'intégration par parties et
      le flux de bord nul. Ce résultat reste conditionnel : il ne ferme ni le
      Stokes global ni l'action parente LL covariante complète.
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
  - [x] Regrouper les résidus boîte/stratifié/action nulle dans un ledger
    canonique, prouver leur annulation et déduire l'équivalence faible/forte LL
    sous le contrat exact à deux champs : vraie IPP continue et identification
    du flux géométrique au ledger fini. Ces deux champs géométriques restent à
    construire ; aucun Stokes global inconditionnel n'est revendiqué.
    - [x] Exploiter l'annulation du ledger pour prouver que ce contrat
      géométrique existe exactement si l'unique IPP globale pondérée à bord nul
      existe, puis en déduire faible ↔ fort.
      - [x] Remplacer la frame locale pondérée par les trois rotations
        canoniques de `S²` et la translation quotient, prouver que ces quatre
        générateurs lisses engendrent chaque tangent et que leurs flots
        préservent la mesure canonique.
      - [x] Identifier exactement la dérivée le long de chaque flot à
        `throatFrameDerivative`, puis prouver l'adjoint antisymétrique de chaque
        générateur et l'IPP globale brute du flux LL pondéré.
      - [x] Effectuer le changement de variable PT, sommer les deux IPP et
        construire sans hypothèse
        `canonicalDivergenceFreeLLFrame_globalIPP`, donc le contrat de Stokes
        à ledger vide pour cette frame canonique. Le Stokes géométrique général
        pour données variables et toutes les strates reste ouvert.
        - [x] Empaqueter ce résultat en contrat géométrique canonique effectif,
          puis prouver sans hypothèse supplémentaire les équivalences exactes
          faible ↔ forte et stationnaire ↔ forte pour l'action LL PT retenue.
      - [x] Isoler le défaut d'adjoint formel exact de l'opérateur LL brut :
        toute correction lisse qui le représente donne faible ↔ fort corrigé,
        et cette correction est nulle exactement lorsque l'IPP globale brute
        est satisfaite. Pour la frame canonique désormais retenue, l'IPP brute
        est prouvée directement et la correction est donc exactement nulle ;
        le Stokes géométrique général sur toutes les strates reste distinct.
- [ ] Classifier les termes de bord/null/joint admissibles à divergence près.

**Acceptation** : la variation complète bulk+frontières+LL ne laisse aucun flux
non contrôlé et produit les conditions de jonction annoncées.

## 6. Verrou 4 — complexe concret `K/J`, cohomologie et quotient

- [ ] Définir le vrai opérateur de compatibilité géométrique `K` sur les
  bundles Janus.
  - [x] Au niveau strictement symbolique Fourier fini, instancier `K` par le
    vrai symbole de Saint-Venant, prouver `K ∘ R = 0` pour le symbole
    Lorentz--Gram et en déduire les deux symétries de Helmholtz restreintes.
    Aucun complexe différentiel global `K/J` sur les bundles Janus n'est fermé.
    - [x] Former le quotient algébrique finite-mode par les fibres de ce `K`,
      faire descendre `K` injectivement et son pairing symétrique, puis prouver
      que toute image du symbole Lorentz--Gram représente la classe zéro.
      Ce quotient n'est ni le quotient de jauge ni le quotient Sobolev global.
      - [x] Caractériser l'égalité des classes par l'égalité de leurs
        images Saint-Venant, prouver que le noyau du morphisme quotient est la
        seule classe zéro et, sous non-dégénérescence explicite sur l'image,
        que le pairing descendu sépare les classes. La dernière conclusion est
        conditionnelle, sans certificat global supposé.
      - [x] Identifier canoniquement ce quotient finite-mode à l'image exacte
        du symbole Saint-Venant par une bijection explicite. Il s'agit d'une
        équivalence de types ; aucune structure linéaire globale n'est inventée.
        - [x] Transporter le pairing de compatibilité sur cette image, prouver
          sa formule sur les représentants, sa symétrie et sa séparation sous la
          même non-dégénérescence explicite. La séparation reste conditionnelle.
- [ ] Calculer sa dérivée de Fréchet `J` sur les espaces fonctionnels choisis.
  - [x] Sur chaque fibre du vrai cover D8, exprimer le véritable dérivé
    d'immersion dans les coordonnées du modèle, construire les composantes
    scalaires de `K(F) = F*η`, calculer leur vraie dérivée de Fréchet `J_F`
    et prouver que `K` au dérivé d'immersion redonne exactement le tenseur
    lorentzien intrinsèque lisse déjà construit. Ce pont reste ponctuel sur le
    cover ; il ne construit ni opérateur fonctionnel global, ni quotient, ni bord.
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
        - [x] Spécialiser cette identité dynamique à la vraie action
          matière+LL sur les champs matière et potentiels `U(1)^2`
          intrinsèques : avec LL gelé et Maxwell absent, sa dérivée Euler
          réelle annule `B(dS)` sur tout pur paramètre `U(1)^2`. Les blocs
          métrique, Maxwell et difféomorphisme diagonal restent ouverts.
          - [x] Extraire ces mêmes paramètres `U(1)^2` du doublet BRST linéaire
            apparié porté par `ProgramPCompleteVariation4D`, identifier leurs
            générateurs intrinsèques aux deux potentiels `dc` de son image BRST,
            puis transporter l'invariance et `B(dS)=0`. Aucun accord avec le
            slot jauge coordonné D9 ni bloc Maxwell n'est revendiqué.
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
          - [x] Extraire de cette action jointe le vrai ghost lisse de
            translation temporelle, prouver qu'il est exactement la vitesse du
            flot, puis restreindre honnêtement les blocs
            métrique+matière+`U(1)^2` à `ℝ × U(1)^2`. Le générateur
            linéaire, `B = E ∘ R`, son critère d'annulation et l'identité de
            Noether sur le sous-groupe temporel sont fermés. Pour une paire de
            métriques arbitraire, la régularité lisse/symétrique des deux
            dérivées reste l'entrée d'un contrat explicite ; aucun flot pour
            ghost tangent arbitraire ni bloc LL n'est revendiqué.
            - [x] Pour la paire canonique formée de deux métriques intrinsèques
              égales, prouver l'isométrie sous toute translation temporelle,
              l'annulation du générateur métrique et instancier sans hypothèse
              le contrat par les deux variations nulles. La première variation
              de l'action et son invariance restent les hypothèses explicites
              de l'identité de Noether spécialisée.
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
  - [x] Pour les trois vrais générateurs de rotation spatiale `so(3)` déjà
    intégrés en ghosts lisses du cover D8, relever leur action linéaire à
    l'espace ambiant lorentzien, prouver son antisymétrie, puis
    `J_F(R(F)) = 0` pour chaque composante du Gram, notamment au véritable
    dérivé d'immersion. Le générateur d'axe zéro est prouvé non nul. Cette
    identité reste ponctuelle sur les jets du cover ; `B ∘ K` et le complexe
    fonctionnel global restent ouverts.
  - [x] Pour chaque axe spatial fixé, promouvoir la direction
    `A_axis ∘ dι` en une vraie section lisse de bundle-hom sur le cover,
    prouver que sa linéarisation de Gram est la fonction lisse identiquement
    nulle, puis vérifier son cocycle exact sous le générateur deck. L'action de
    tout `ℤ` sur la direction bundle-hom, sa propre descente au quotient,
    `B ∘ K` et le complexe global restent ouverts.
    - [x] Pour la seule sortie scalaire déjà nulle `J_F(R(F))`, construire
      l'invariance deck pour tout winding, la descendre par `descendSmooth` au
      vrai quotient D8 et prouver qu'elle y reste identiquement nulle. La
      direction bundle-hom `R(F)` est descendue séparément ci-dessous, mais
      aucun complexe fonctionnel global `K/J` n'est encore affirmé.
      - [x] Écrire la direction `A_axis ∘ dι` comme la différentielle d'un
        potentiel ambiant lisse fixé par tout winding, descendre ce potentiel
        au vrai quotient D8, puis construire sa section bundle-hom lisse dont
        le pullback est exactement la direction cover initiale. Cette descente
        concerne seulement les trois rotations spatiales concrètes.
        - [x] Sur le domaine réel où la linéarisation de Gram d'une section
          quotient produit un champ cover lisse et deck-invariant, construire
          l'opérateur quotient `J`, prouver que les trois sections de rotation
          appartiennent à ce domaine par le calcul de noyau effectif, puis
          établir littéralement `J ∘ R = 0` comme champ lisse sur D8, pour
          chaque composante de Gram. Ce sous-complexe restreint ne construit
          ni `B ∘ K`, ni le complexe fonctionnel global, ni sa cohomologie.
  - [x] Pour la vraie sortie Lorentz--Gram déjà descendue comme tenseur lisse
    sur le quotient D8, définir l'identité algébrique d'ordre zéro `B_sym` par
    antisymétrisation, caractériser son noyau comme les tenseurs symétriques,
    identifier le pullback de `K` à la formule de Gram du dérivé d'immersion,
    puis prouver `B_sym(K) = 0` comme champ global. Ce n'est ni l'opérateur de
    Bianchi différentiel, ni le complexe global `B ∘ K`, ni un résultat Sobolev.
- [ ] Promouvoir l'exactitude symbolique non nulle vers un complexe
  différentiel lorentzien global.
  - [x] Sur les mêmes espaces réels pointwise `Fin 4`, identifier le symbole de
    déformation de Saint--Venant à la perturbation de jauge du symbole
    d'Einstein linéarisé et établir les trois compositions
    `K_SV ∘ R = 0`, `G ∘ R = 0` et `B ∘ G = 0`. Ce pont reste plat et au
    symbole principal : aucun complexe différentiel global, Sobolev ou de bord
    n'en est déduit.
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
    - [x] Sur la seule droite finite-mode du premier mode temporel, encoder
      l'amplitude physique dans le Hilbert pondéré, la récupérer exactement
      par le décodeur existant, puis identifier linéairement cette droite à
      celle du vrai champ cosinus `C∞` sur le quotient D8, avec formule upstairs
      et cocycle deck exacts. Les modes spatiaux, l'isométrie des normes et
      l'identification Sobolev globale des bundles restent ouverts.
      - [x] Étendre cette réalisation à toute suite complexe temporelle à
        support fini sur `ℤ` : construire le polynôme de Fourier `C∞` réellement
        descendu au quotient D8, prouver sa formule upstairs et son cocycle deck,
        puis récupérer chaque coefficient par l'intégrale de Haar et en déduire
        l'injectivité. Cela reste un sous-espace temporel finite-mode ; aucune
        série infinie, norme Sobolev, direction spatiale ni complétion de bundle
        n'est identifiée.
        - [x] Dans le seul secteur scalaire temporel spatialement constant,
          descendre le temps du vrai quotient D8 vers le cercle, calculer la
          marginale temporelle de la mesure lorentzienne canonique normalisée,
          puis réaliser isométriquement toute suite `ℓ²(ℤ, ℂ)` comme section
          quotient `L²`, avec convergence de la série infinie, récupération des
          coefficients avant pullback et compatibilité finite-mode. Construire
          aussi la complétion temporelle pondérée `H¹`, injectée dans les deux
          séries `L²` du champ et de sa dérivée spectrale. Les modes spatiaux,
          bundles non triviaux, recollements Sobolev intrinsèques et traces au
          bord restent ouverts.
          Preuve d'appui :
          `P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D` rend le
          cœur `Finsupp` dense dans ce graphe temporel et identifie sa dérivée
          synthétisée à `mvfderiv` et à la composante temporelle de `dc`.
- [ ] Contrôler convergence des séries, modes zéro et cohomologie globale.
  - [x] Réaliser injectivement les coefficients temporels complexes à support
    fini comme vrais ghosts lisses réels `U(1)^2`, identifier le mode zéro au
    ghost constant et prouver que sa plage est incluse dans le noyau du vrai
    opérateur exact `c ↦ dc`. Sur tous les ghosts lisses `U(1)^2` du vrai
    quotient D8 connecté, prouver aussi l'inclusion inverse : ce noyau est
    exactement l'espace des ghosts constants, et l'identifier par une équivalence
    explicite à l'algèbre de Lie `ℝ²`. La cohomologie globale complète et les
    séries infinies restent ouvertes.
    - [x] Sur ce seul sous-espace temporel finite-mode, identifier la dérivée
      ordinaire à `mvfderiv` sur la vraie vitesse de translation, calculer le
      multiplicateur exact `2π i n / T`, lire ce champ dérivé dans `dc`, puis
      prouver l'égalité exacte entre son noyau et la plage du mode zéro. Aucun
      résultat pour les ghosts lisses généraux, les séries infinies ou une
      complétion Sobolev n'en découle.
  - [x] Sur la seule complétion `H¹` du secteur scalaire temporel spatialement
    constant, inclure continûment le mode constant et prouver que sa plage est
    exactement le noyau du multiplicateur dérivé, puis transporter cette
    égalité de noyaux à la vraie section quotient `L²(D8)` par injectivité de la
    synthèse Fourier. Ce résultat ne calcule ni le complexe BRST Sobolev complet,
    ni les modes spatiaux, ni la cohomologie globale des ghosts.
- [ ] Imposer et analyser les conditions au bord du mapping torus/throat.
  - [x] Sur le sous-espace strictement temporel à support Fourier fini construit
    ci-dessus, composer avec la vraie restriction lisse au throat et prouver
    que cette trace est injective ; en particulier, la condition de Dirichlet
    homogène équivaut exactement à l'annulation de tous les coefficients. Ce
    résultat finite-mode ne traite ni séries infinies, ni conditions Robin,
    ni domaines Sobolev globaux.
- [x] Prouver la fermeture de l'image dans le modèle pondéré choisi et isoler exactement le zéro-mode.
- [x] Construire le pairing/Hessien cible `H`, continu et auto-adjoint, sur l’échelle Sobolev de coefficients choisie.
  - [x] Sur l'échelle de coefficients Sobolev décalée, prendre le Hessien cible
    identité, continu, auto-adjoint et positif.
- [x] Instancier le pullback `Jᵀ H J` complet dans ce modèle de coefficients.
  - [x] Construire réellement `J† H J` comme opérateur continu, prouver la
    formule de pairing, symétrie, positivité, noyau égal à celui de `J` et
    positivité définie après retrait du zéro-mode.
  - [ ] Identifier ce pullback au Hessien de la même action Janus globale.
    - [x] Dans le modèle périodique de coefficients uniquement, identifier le
      Hessien quotient à la seconde dérivée de Fréchet de cette même action de
      coefficients, puis à l'unique descente de `J†J`, et prouver sa
      non-dégénérescence. Le pont vers l'action Janus globale reste ouvert.
    - [x] Établir l'obstruction avec l'action globale réduite actuellement
      assemblée : son Hessien est nul sur tout slot métrique pur, tandis que le
      Hessien quotient périodique est non nul sur toute classe physique non
      nulle. Sans bloc Einstein--Hilbert ni application globale des classes
      périodiques vers les variations métriques, ces Hessians ne peuvent donc
      pas être identifiés.
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
  - [x] Promouvoir la période non nulle en donnée d'objet et construire la
    catégorie de tous les quotients effectifs D8 ainsi paramétrés, dont les
    morphismes sont les difféomorphismes lisses réels entre quotients; les
    géométries Janus générales et leurs décorations SpinC/Pin restent ouvertes.
  - [x] Construire sur cette catégorie globale le foncteur contravariant des
    champs lisses à fibre normée constante, avec lois exactes d'identité et de
    composition, puis son opérateur naturel identité scalaire. Les bundles
    SpinC/Pin et les fibres physiques non triviales restent ouverts.
  - [x] Construire le vrai bundle tangent de chaque quotient de la famille et
    son transport par la dérivée de tout morphisme, avec lois exactes
    d'identité et de composition entre trois périodes arbitraires non nulles.
  - [x] Construire les fibres cotangentes duales et leur pullback par
    l'équivalence linéaire tangente, avec lois contravariantes exactes
    d'identité et de composition. Les bundles principaux SpinC/Pin et leurs
    représentations physiques restent ouverts.
    - [x] Promouvoir ce transport en pullback de vraies 1-formes `C∞` entre
      backgrounds distincts, prouver sa régularité en coordonnées de bundle,
      ses lois exactes et sa localité sur toute image réciproque.
  - [x] Construire les vraies sections vectorielles tangentes `C∞` sur chaque
    background effectif, leur pullback intrinsèque par la différentielle
    inverse, les lois contravariantes exactes entre périodes distinctes et la
    localité de faisceau sur toute image réciproque.
    - [x] Coupler naturellement ces champs aux tenseurs symétriques et aux
      métriques lorentziennes : prouver que les facteurs différentielle et
      différentielle inverse s'annulent exactement dans `T(X,Y)` et `T(X,X)`.
    - [x] Prouver que l'abaissement d'indice métrique commute exactement avec
      les foncteurs tangent/cotangent globaux, puis l'unicité de la 1-forme
      pullback satisfaisant cette relation musicale.
    - [x] Construire les frames lisses ordonnées à quatre vecteurs et prouver
      la naturalité exacte de leur matrice de Gram métrique, de son déterminant,
      de la densité volume absolue et de sa non-annulation.
    - [x] Assembler la densité scalaire locale cinétique-plus-masse à partir
      d'un champ dérivé tangent explicitement fourni et prouver sa covariance
      exacte sous pullback simultané. Son identification holonomique à
      `sharp(dφ)` reste séparée et n'est pas supposée.
      - [x] Promouvoir `dφ` en vraie 1-forme globale `C∞` et prouver que sa
        construction commute exactement avec le pullback entre backgrounds
        effectifs.
      - [x] Empaqueter un champ tangent lisse muni du certificat intrinsèque
        `g♭X = dφ`, puis prouver la stabilité exacte de ce certificat et de
        sa densité sous pullback.
      - [x] Construire en trivialisation locale l'inverse musicale `C∞` de
        toute métrique lorentzienne générale lisse et promouvoir l'application
        d'une 1-forme lisse en vraie section tangente `C∞`.
      - [x] Instancier automatiquement le certificat par le champ global
        `sharp(dφ)`, prouver `g♭ sharp(dφ)=dφ` et sa naturalité exacte
        sous pullback entre backgrounds effectifs.
      - [x] Identifier la contraction inverse holonomique à
        `g(sharp(dφ),sharp(dφ))` et prouver la naturalité globale de la
        densité scalaire cinétique-moins-potentiel avec son signe physique.
  - [x] Construire les fibres réelles de tenseurs covariants d'ordre deux sur
    les vrais espaces tangents et leur pullback contravariant exact entre
    trois backgrounds effectifs arbitraires.
  - [x] Isoler le sous-espace pointwise des tenseurs covariants symétriques et
    prouver sa préservation par tout difféomorphisme de la catégorie globale.
  - [x] Promouvoir ce pullback en transport de vraies sections tensorisées
    symétriques `C∞` entre périodes distinctes et construire leur foncteur
    contravariant exact sur la catégorie globale.
  - [x] Transporter l'équivalence musicale et l'inertie lorentzienne `(3,1)`,
    construire le pullback des métriques lorentziennes générales `C∞` entre
    backgrounds distincts et leur foncteur contravariant global. Les bundles
    principaux SpinC/Pin et leurs représentations physiques restent ouverts.
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
  - [x] Prouver la localité de germe et la localité de faisceau sur toute
    région ouverte de `dφ`, `sharp(dφ)` et de la densité holonomique complète.
  - [x] Réaliser canoniquement tout champ scalaire global `C∞` comme
    `RegularHolonomicScalar` avec sa vraie différentielle lisse, et prouver la
    naturalité exacte des deux composantes sous pullback effectif D8.
  - [x] Aligner les champs scalaires et de throat « smooth » sur la régularité
    honnête `C∞`, puis construire `T(X,Y)` et `g(X,Y)` comme vrais champs
    scalaires `C∞` avec naturalité exacte sous pullback effectif D8.
  - [x] Promouvoir canoniquement `T(X,Y)` et `g(X,Y)` en scalaires
    holonomiques réguliers, avec naturalité exacte de leur champ et de leur
    vraie différentielle sous pullback effectif D8.
  - [x] Prouver leur localité de faisceau : l'accord de `T`, `X` et `Y` sur
    une région ouverte force l'accord de `T(X,Y)` et de sa vraie différentielle
    en tout point de cette région, avec spécialisation exacte à `g(X,Y)`.
  - [x] Pour les tenseurs symétriques et métriques lorentziennes générales sur
    la catégorie globale effective D8, prouver la régularité `C∞` du pullback
    et sa localité de faisceau exacte : l'accord sur une région cible implique
    l'accord des pullbacks sur toute son image réciproque. Les réalisations
    holonomiques physiques `Pin⁻` restent ouvertes.
- [x] Construire le groupoïde différentiable des jets structurés.
  - [x] Construire la catégorie et le groupoïde d'action effectifs de deck D8,
    avec égalité dans le quotient caractérisée par l'existence d'une flèche.
  - [x] Construire les familles dépendantes source/cible, leur transport et le
    foncteur de représentation fourni vers les jets structurés.
  - [x] Prouver que chaque composante source/cible du groupoïde de deck est un
    difféomorphisme local sur les covers analytiques 4D et du throat 3D.
- [x] Déterminer la stratification d'isotropie du seul groupoïde de deck
  effectif : elle a une strate unique et des stabilisateurs triviaux. Toute
  isotropie supplémentaire des fibres SpinC reste séparée.
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
- [x] Rejeter le revêtement Spin ambiant : la non-orientabilité du vrai
  mapping torus et l'overlap de déterminant négatif excluent toute réalisation
  continue orientée `Spin` ou `SpinC`; le remplacement géométrique pertinent
  est `Pin⁻`.
- [x] Dériver les données Čech `Pin⁻` depuis l'atlas réel, et non depuis
  des transitions fournies. L'égalité locale des vrais lifts avec le translate
  par le winding réel et sa dérivation tangentielle dans les frames radiales
  sont établies ; la réduction orthogonale Čech et le vrai bundle principal
  `Pin⁻(4)` sont construits. Les données orientées SpinC ne sont plus revendiquées.
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
  - [x] À partir de tout relèvement Čech ambiant `Pin⁻(4)` continu certifié,
    construire sur le vrai quotient 4D son `FiberBundleCore`, ses changements
    de cartes réels et l'action principale droite libre/transitive, puis
    empaqueter le bundle principal complet. L'existence inconditionnelle du
    relèvement Čech ambiant reste le verrou distinct.
- [ ] Prouver l'accord des classes caractéristiques `Pin⁻`/`PinC` et déterminant.
  - [x] Combiner les résultats existants de séparation du normal-root et du
    monopole avec la loi du déterminant `SpinC` : les magnitudes de Chern sont
    respectivement `0`, `1` et `2`, le déterminant est pair et les trois rôles
    sont distincts. L'identification des vrais bundles et classes globales
    `Pin⁻`/`PinC` reste ouverte.
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
  Pour le groupoïde de deck effectif, l'isotropie est désormais prouvée
  triviale à tout objet : la strate singulière est vide et restriction/extension
  des sections dépendantes est une équivalence avec extension unique. La case
  reste ouverte pour les isotropies internes `Pin⁻`/`PinC`, les frames et leurs
  conditions de régularité/holonomie.
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
  - [x] Assembler en une seule action réelle les huit coordonnées matière
    globales, la jonction Robin et le secteur LL différentiel moyenné PT, puis
    identifier son Euler à sa vraie dérivée simultanée. Les blocs EH métrique,
    Maxwell/jauge et ghosts ne sont pas remplacés par des termes nuls.
    - [x] Ajouter à cette courbe l'interaction métrique Candidate A diagonale
      intégrée sur le même `ProgramPRobinCompleteVariation4D`, identifier sa
      courbe métrique à la composante exacte de la courbe simultanée et prouver
      que l'Euler sommé est la vraie dérivée sous le contrat de domination
      existant. Les données matière ne sont pas encore reconstruites
      canoniquement depuis ces métriques ; EH, Maxwell, ghosts et le Hessien de
      l'interaction Candidate A restent absents.
      - [x] Spécialiser les huit données matière aux magnitudes plus/minus
        sélectionnées par leur vrai secteur depuis `fields.metrics`, avec la
        même mesure globale que l'interaction Candidate A, puis transporter le
        vrai théorème de dérivée. Ces magnitudes restent fixées à la métrique de
        base le long de la courbe matière : aucune variation croisée
        métrique--matière, ni EH/Maxwell/ghost/Hessien Candidate A, n'en découle.
        - [x] Au niveau de la densité pointwise D8, faire varier simultanément
          la magnitude métrique sectorielle exponentielle, le vrai champ
          matière affine et son covecteur `dφ` le long du même
          `ProgramPRobinCompleteVariation4D`, puis prouver le `HasDerivAt`
          explicite des termes volume, cinétique et masse. Le passage sous
          l'intégrale, le tenseur de stress covariant et le Hessien mixte de
          l'action globale Candidate A restent ouverts.
          - [x] Sous le contrat explicite de mesurabilité, intégrabilité,
            domination et Lipschitz local requis pour dériver sous l'intégrale,
            sommer les huit densités sur la même mesure et les mêmes masses,
            puis prouver que leur variation intégrée est le `HasDerivAt` de
            l'unique action métrique--matière sur la courbe commune. Au point
            de base, cette action est littéralement celle des données matière
            sectorielles Candidate A. Le résultat reste conditionnel ; stress
            covariant, Hessien mixte, EH, Maxwell et ghosts restent absents.
    - [x] Sur la même direction synchronisée, donner le Taylor exact de cette
      même action matière+Robin+LL : Euler assemblé réel, moitié du Hessien
      assemblé diagonal réel, puis coefficients cubique et quartique LL
      explicites. Aucun bloc Candidate A absent n'est ajouté.
      - [x] Calculer les dérivées itérées d'ordres trois et quatre de cette
        même action assemblée : elles valent exactement `6 C3` et `24 C4` du
        seul secteur LL, les secteurs matière et Robin étant quadratiques.
      - [x] Identifier publiquement les coefficients intégrés `C1/C2` de cette
        même action assemblée à son Euler réel et à la moitié de son Hessien
        diagonal réel, sur les mêmes champs et la même direction.
      - [x] Pour deux vraies directions synchronisées, dériver le coefficient
        linéaire de la première après déplacement selon la seconde et identifier
        exactement le coefficient mixte `s*t` au Hessien assemblé réel de la
        même action matière+Robin+LL.
        - [x] Prouver l'identité de Clairaut concrète : ce coefficient `s*t`
          est inchangé lorsque les deux vraies directions synchronisées sont
          échangées, par symétrie du Hessien de la même action, et en déduire
          l'égalité directe des deux valeurs `deriv` mixtes effectives.
        - [x] Prouver que ce coefficient mixte ne dépend que des projections
          actives des deux directions et l'identifier exactement au Hessien
          quotient sur leurs classes.
          - [x] L'identifier aussi directement au Hessien des deux observations
            D9 enrichies et prouver son invariance sous égalité séparée de
            leurs lectures actives, sans revendication BRST ni bijectivité globale.
          - [x] Au premier ordre, identifier de même le coefficient `C1` à
            l'Euler réel lu sur l'observation D9 enrichie de la même direction
            et prouver son invariance sous égalité de lecture active.
          - [x] Au second ordre diagonal, identifier `C2` à la moitié du
            Hessien de cette même observation enrichie dans ses deux slots et
            prouver son invariance sous égalité de lecture active.
            - [x] Réécrire le Taylor exact de la vraie action assemblée avec
              son Euler et son Hessien diagonal lus sur cette observation D9
              enrichie, tout en conservant explicitement les termes LL `C3/C4`.
              - [x] Réécrire aussi `C1/C2` par l'Euler et le Hessien quotient
                de la classe active du représentant, sans courbe ni structure
                additive inventée sur le quotient.
                - [x] Sur les vraies courbes représentantes, identifier
                  directement leurs dérivées au premier ordre à l'Euler quotient
                  et la dérivée de l'Euler au Hessien quotient diagonal.
                  - [x] Étendre cette dernière identification à deux directions
                    distinctes et prouver que les deux courbes représentantes
                    permutées donnent la même valeur par symétrie quotient.
                    - [x] Identifier directement ces deux valeurs dérivées au
                      coefficient Taylor mixte public, puis au Hessien quotient
                      des deux classes actives correspondantes.
              - [x] Sur l'inclusion lisse Robin+LL à matière nulle, identifier
                le terme quadratique au demi-pairing du vrai Jacobi Fredholm
                réduit, en conservant les termes linéaires Robin/LL et `C3/C4` LL.
                - [x] En déduire directement que la dérivée itérée d'ordre
                  deux à l'origine de cette vraie courbe vaut le pairing Jacobi
                  Fredholm réduit diagonal.
                  - [x] Calculer aussi ses dérivées itérées d'ordres trois et
                    quatre comme `6 C3_LL` et `24 C4_LL`, sans contribution
                    supérieure des secteurs matière ou Robin.
- [ ] Calculer l'opérateur d'Euler--Lagrange complet pour toutes les variables
  indépendantes.
  - [x] Pour les huit vraies coordonnées du multiplet matière extraites d'un
    même `IndependentFields`, sommer les huit actions scalaires globales avec
    leurs données analytiques fournies, puis prouver que la somme des Euler est
    la vraie dérivée de cette action unique. Les données ne sont pas encore
    identifiées aux deux métriques Candidate A par un choix canonique.
    - [x] Le long de la courbe affine des huit vraies directions matière,
      reconstruire exactement cette action globale comme sa valeur initiale,
      `t` fois son Euler réel et `t²/2` fois son Hessien réel.
    - [x] Sélectionner pour chaque composante la magnitude plus/minus de la
      même configuration selon son vrai secteur, prouver sa positivité et
      construire les huit données d'action avec une mesure commune sous le
      contrat exact d'intégrabilité des pairings. Le contrat analytique reste
      à décharger sur le domaine fonctionnel global retenu.
      - [x] Formaliser l'obstruction de signe entre cette densité globale et la
        densité covariante utilisée par Noether : à volume et cinétique
        identifiés, leur égalité équivaut à l'annulation du terme massif et
        échoue pour masse, champ et volume non nuls.
        - [x] Intégrer cette identité sous hypothèses explicites : la différence
          des deux actions globales est exactement l'intégrale du défaut
          massif, et leur égalité équivaut à l'annulation de cette intégrale.
          - [x] Sommer ce certificat sur les huit vraies composantes : sous les
            ponts masse, mesure, volume et cinétique composante par composante,
            la différence entre l'action Euler et l'action Noether est la somme
            exacte des huit défauts intégrés.
            - [x] Pour des masses carrées non négatives, prouver que ces huit
              défauts intégrés sont non négatifs et que leur somme s'annule si
              et seulement si chacun s'annule : aucune compensation entre
              composantes n'est possible.
              - [x] Sous masse strictement positive, volume strictement positif
                presque partout et intégrabilité, prouver qu'un défaut intégré
                s'annule si et seulement si le champ correspondant est nul
                presque partout ; tout champ non nul donne un défaut positif.
                - [x] En déduire, sous les ponts composante par composante,
                  qu'un seul champ de masse positive non nul presque partout
                  force l'inégalité des deux actions matière à huit champs.
      - [x] Injecter fidèlement toute paire de directions matière dans le même
        `IndependentFieldVariation` que D9 et LL, prouver que l'extraction des
        huit composantes commute exactement avec la courbe simultanée, puis
        transporter le `HasDerivAt` de l'action matière sur cette vraie courbe
        commune. Les autres directions y sont exactement nulles.
        - [x] Calculer sa projection D9 : le slot matière est exactement la
          trace au throat de la direction sectorielle sélectionnée, tandis que
          les slots métrique, jauge et ghost `U(1)` sont nuls. Contrairement au
          bloc LL, le contenu matière est donc effectivement visible par D9.
- [x] Vérifier abstraitement que les variations induites utilisent la règle de chaîne et ne créent pas d’équations supplémentaires.
- [ ] Calculer la dérivée de l'opérateur d'Euler sur le domaine global.
  - [x] Enrichir fidèlement le paquet commun des six secteurs par la direction
    Robin absente et transporter la dérivée de la même action assemblée
    matière+Robin+LL ainsi que la dérivée de son Euler vers son vrai Hessien.
    Les blocs métrique, jauge, ghost et auxiliaire sont conservés mais cette
    action sectorielle n'en dépend pas ; Candidate A complet reste ouvert.
    - [x] Transporter sur ces directions enrichies la symétrie de Helmholtz du
      vrai Hessien matière+Robin+LL et l'exprimer comme commutation des deux
      dérivées mixtes de l'Euler de cette même action.
      - [x] Pour le vrai Hessien LL complet, identifier exactement ses noyaux
        gauche et droit par cette symétrie, sans affirmer leur trivialité.
      - [x] Pour une direction dont la projection active est nulle, prouver que
        la vraie action assemblée reste constante sous toute translation affine,
        que sa dérivée et son Euler s'annulent. C'est un Noether fini du secteur
        inactif, pas une action du groupe de jauge global.
        - [x] Prouver algébriquement que le vrai Hessien assemblé annule toute
          telle direction dans chacun de ses deux slots, par additivité,
          factorisation active et symétrie.
          - [x] En déduire l'annulation du coefficient Taylor mixte et des
            dérivées des vraies courbes Euler représentatives lorsque l'une ou
            l'autre direction possède une projection active nulle.
            - [x] Transporter cette annulation au Hessien quotient et au Hessien
              des observations D9 enrichies, dans chacun des deux slots, pour
              les classes munies d'un représentant explicitement inactif.
            - [x] Au premier ordre, prouver aussi l'annulation de l'Euler
              quotient, du coefficient assemblé `C1` et de l'Euler lu sur
              l'observation D9 enrichie d'une direction explicitement inactive.
              - [x] Au second ordre diagonal, prouver l'annulation de `C2`, du
                Hessien quotient, du Hessien D9 enrichi et de la dérivée
                itérée seconde de la vraie courbe inactive.
                - [x] Montrer que l'inactivité annule les trois composantes LL,
                  puis les coefficients `C3/C4` et les dérivées itérées
                  d'ordres trois et quatre de cette même courbe.
                  - [x] Regrouper ces résultats en un certificat Taylor exact :
                    `C1` à `C4` nuls, action assemblée constante pour tout `t`
                    et dérivées itérées d'ordres un à quatre nulles.
                    - [x] Caractériser exactement l'inactivité par l'égalité à
                      la classe quotient active nulle et par la nullité de la
                      lecture active D9 enrichie, sans interprétation de jauge.
                      - [x] Injecter une vraie direction purement jauge du
                        domaine commun, prouver son inactivité pour l'action
                        matière+Robin+LL, la constance de cette action et les
                        annulations Euler/Hessien. Maxwell reste absent : aucune
                        invariance Candidate A complète n'est revendiquée.
                        - [x] Regrouper pour cette direction purement jauge la
                          classe quotient nulle, la lecture D9 active nulle,
                          `C1–C4` nuls, l'action sectorielle constante et les
                          dérivées un à quatre nulles, toujours sans Maxwell.
                          - [x] Raccorder sa lecture D9 gauge au vrai symbole
                            Maxwell gauge-fixé ponctuel : formule exacte, noyau
                            au covecteur non nul, inverse et antécédent dans
                            l'image. Aucun cokernel ni Maxwell global n'est affirmé.
                            - [x] Au covecteur nul, prouver le symbole gauge nul,
                              son noyau ponctuel total et son image exactement
                              réduite à `{0}`. Aucun cokernel artificiel n'est créé.
                              - [x] Assembler les lectures gauge et ghost du
                                domaine full dans un symbole D9 bloc-diagonal :
                                formule, inverse, noyau nul et image totale au
                                covecteur non nul; noyau total et image zéro au
                                covecteur nul. Aucun complexe global n'est affirmé.
                                - [x] Linéariser ce bloc et construire son
                                  conoyau ponctuel : nul au covecteur non nul,
                                  équivalent à toute la coordonnée au covecteur
                                  nul, avec lectures full raccordées.
                                  - [x] Caractériser aussi les noyaux comme
                                    `⊥` hors zéro et `⊤` au zéro-mode, puis
                                    agréger noyau, image et conoyau dans deux
                                    certificats pointwise exacts.
                                  - [x] Raccorder ces deux régimes à la lecture
                                    gauge+ghost du domaine full : classe nulle
                                    hors zéro, appartenance au noyau et
                                    récupération exacte du représentant au
                                    zéro-mode. Aucun complexe global n'en suit.
                                    - [x] Former la courte suite pointwise
                                      `V → V → coker`, prouver son exactitude
                                      au terme central et la surjectivité de la
                                      projection quotient pour tout covecteur.
                                    - [x] Hors zéro, construire l'inverse
                                      linéaire explicite du symbole, ses deux
                                      identités de composition et le certificat
                                      de scission; aucune exactitude globale ou
                                      BRST n'est affirmée.
                                      - [x] Au zéro-mode, prolonger en une suite
                                        pointwise `V --id→ V --0→ V → coker`
                                        et prouver l'exactitude aux trois termes
                                        accessibles ainsi que la surjectivité
                                        finale.
                                      - [x] Construire la section canonique du
                                        cokernel zéro-mode, prouver ses deux
                                        compositions identités et récupérer
                                        exactement la coordonnée gauge+ghost
                                        issue du domaine full.
                                        - [x] Unifier les branches zéro/non-zéro
                                          en une dichotomie pointwise pour toute
                                          lecture full, avec exactitude/scission
                                          dans la branche correspondante.
                                        - [x] Identifier par l'équivalence
                                          zéro-mode le rang fini du cokernel à
                                          celui de toute la coordonnée
                                          gauge+ghost, sans extrapoler une
                                          dimension globale.
                                          - [x] Calculer les rangs finis du
                                            noyau, de l'image et du cokernel
                                            hors zéro : respectivement
                                            `0`, rang total et `0`.
                                          - [x] Calculer les mêmes rangs au
                                            zéro-mode : rang total, `0` et rang
                                            total, uniquement depuis les
                                            équivalences pointwise existantes.
                                          - [x] En déduire rang–nullité du
                                            symbole gauge+ghost pour tout
                                            covecteur par dichotomie, sans
                                            conséquence globale.
                                            - [x] Donner la dichotomie exacte du
                                              rang fini du véritable terme de
                                              cohomologie/cokernel : rang total
                                              au zéro-mode et nul hors zéro.
                                            - [x] Définir l'indice pointwise
                                              `finrank ker − finrank coker` et
                                              prouver qu'il est nul pour tout
                                              covecteur, sans l'appeler indice
                                              d'un opérateur global.
                                            - [x] Agréger exactitude centrale,
                                              indice nul et lecture full : section
                                              récupérante au zéro-mode, classe
                                              cokernel nulle hors zéro.
                                              - [x] Définir la caractéristique
                                                d'Euler de la suite pointwise à
                                                trois termes et l'identifier au
                                                rang fini du cokernel.
                                              - [x] Calculer cet Euler : nul
                                                hors zéro, rang total au
                                                zéro-mode, et stable entre tous
                                                covecteurs non nuls.
                                              - [x] Pour la suite zéro-mode
                                                complétée par l'identité à gauche,
                                                calculer honnêtement la somme
                                                alternée et prouver qu'elle est
                                                nulle.
                                                - [x] Décomposer exactement le
                                                  rang fini du cokernel zéro-mode
                                                  en triplet gauge plus coordonnée
                                                  ghost appariée, et faire de même
                                                  pour son Euler pointwise.
                                                - [x] Projeter la section
                                                  zéro-mode raccordée au domaine
                                                  full et récupérer séparément la
                                                  lecture gauge et la lecture
                                                  ghost exactes.
                                                  - [x] Construire les inclusions
                                                    et projections linéaires des
                                                    blocs gauge et ghost dans le
                                                    cokernel zéro-mode, avec
                                                    rétractions et compositions
                                                    croisées nulles.
                                                  - [x] Reconstruire toute classe
                                                    comme somme de ses composantes
                                                    gauge et ghost et prouver
                                                    l'unicité directe de cette
                                                    décomposition pointwise.
                                                    - [x] Empaqueter cette somme
                                                      directe en une équivalence
                                                      linéaire explicite
                                                      `coker₀ ≃ gauge³ × ghost`,
                                                      avec formules d'application
                                                      et deux identités inverses.
                                                      - [x] Définir les sous-
                                                        modules images gauge et
                                                        ghost dans le cokernel
                                                        zéro-mode et prouver que
                                                        leur intersection est
                                                        `⊥` et leur somme `⊤`.
                                                        - [x] Identifier le noyau
                                                          de chaque projection au
                                                          bloc complémentaire et
                                                          prouver les deux
                                                          surjectivités.
                                                        - [x] Construire par le
                                                          premier théorème
                                                          d'isomorphisme les
                                                          équivalences pointwise
                                                          `coker₀/gauge ≃ ghost`
                                                          et `coker₀/ghost ≃ gauge³`,
                                                          avec formules sur classes.
                                                          - [x] Empaqueter
                                                            `gauge³ → coker₀ → ghost`
                                                            en courte suite pointwise
                                                            exacte et scindée, avec
                                                            composition nulle,
                                                            rétraction et section.
                                                          - [x] Construire
                                                            symétriquement la suite
                                                            scindée exacte
                                                            `ghost → coker₀ → gauge³`,
                                                            sans globalisation.
                                                            - [x] Séparer pour tout
                                                              covecteur les symboles
                                                              linéaires gauge et ghost
                                                              et prouver les quatre
                                                              entrelacements avec les
                                                              projections/inclusions
                                                              du bloc combiné.
                                                            - [x] Identifier exactement
                                                              noyau et image du symbole
                                                              combiné aux produits des
                                                              noyaux et images séparés,
                                                              sans quotient-produit de
                                                              cokernels inventé.
                                                              - [x] Caractériser
                                                                séparément noyau et
                                                                image des symboles gauge
                                                                et ghost hors zéro :
                                                                noyau nul et image totale.
                                                              - [x] Faire de même au
                                                                zéro-mode : noyau total
                                                                et image nulle pour les
                                                                deux blocs séparés.
                                                              - [x] Prouver pour tout
                                                                covecteur l'additivité des
                                                                rangs finis du noyau et
                                                                de l'image du bloc combiné
                                                                depuis les deux blocs.
                                                                - [x] Construire les
                                                                  cokernels gauge et ghost
                                                                  séparés et calculer leurs
                                                                  rangs finis : nuls hors
                                                                  zéro, totaux au zéro-mode.
                                                                - [x] Définir leurs indices
                                                                  pointwise, prouver chacun
                                                                  nul, puis l'additivité des
                                                                  rangs de cokernel et de
                                                                  l'indice du bloc combiné.
                                                                  - [x] Construire pour
                                                                    tout covecteur
                                                                    l'équivalence linéaire
                                                                    canonique entre cokernel
                                                                    du symbole combiné et
                                                                    produit des cokernels
                                                                    gauge/ghost, avec formule
                                                                    exacte sur les classes.
                                                                    - [x] Hors zéro,
                                                                      prouver que le produit
                                                                      des deux cokernels
                                                                      séparés est trivial; au
                                                                      zéro-mode, calculer
                                                                      l'équivalence directement
                                                                      composante par composante.
                                                                    - [x] Raccorder toute
                                                                      classe issue d'une
                                                                      coordonnée full empaquetée
                                                                      aux classes gauge et ghost
                                                                      séparées correspondantes.
                                                                      - [x] Prouver pour
                                                                        tout covecteur la
                                                                        commutation des deux
                                                                        carrés reliant projection
                                                                        cokernel combinée et
                                                                        projections gauge/ghost.
                                                                      - [x] Identifier les
                                                                        noyaux des projections
                                                                        cokernel séparées aux
                                                                        images des symboles et
                                                                        prouver leur surjectivité.
                                                                        - [x] Empaqueter pour
                                                                          chaque bloc séparé la
                                                                          suite pointwise
                                                                          `V → V → coker`, exacte
                                                                          au centre et surjective
                                                                          à droite.
                                                                        - [x] Prouver que sous
                                                                          l'équivalence de cokernels
                                                                          la projection combinée
                                                                          est exactement le produit
                                                                          des projections séparées.
                                                                        - [x] En déduire le
                                                                          certificat produit de
                                                                          courte exactitude du bloc
                                                                          combiné, toujours à
                                                                          covecteur fixé.
                          - [x] Prouver que l'ajout explicite d'une telle
                            direction pure jauge à toute direction conserve sa
                            projection active, sa classe quotient, sa lecture
                            D9 active, la courbe sectorielle et `C1/C2`. Cela
                            ne construit pas un quotient de jauge global.
                            - [x] Prouver en outre que `C3/C4` et les dérivées
                              itérées un à quatre restent inchangés sous cette
                              translation sectorielle purement jauge.
                              - [x] Assembler simultanément les quatre
                                translations inactives métrique, jauge, ghost et
                                auxiliaire et prouver l'invariance de la
                                projection, classe, lecture D9, courbe, `C1–C4`
                                et dérivées un à quatre. Candidate A reste ouvert.
                                - [x] Dans le premier, le second ou les deux
                                  slots, prouver aussi l'invariance du Hessien,
                                  du coefficient Taylor mixte et des dérivées
                                  Euler mixtes sous cette translation combinée.
                                  - [x] Transporter ces trois invariances au
                                    Hessien quotient et au Hessien D9 enrichi,
                                    sans élargir la portée à Candidate A.
                                  - [x] Caractériser exactement le noyau de la
                                    projection active par les quatre composantes
                                    libres métrique, jauge, ghost et auxiliaire,
                                    avec une équivalence ensembliste explicite.
                                    Ce produit n'est pas un groupe de jauge global.
                                    - [x] Caractériser chaque fibre par la
                                      `subDirection` de deux représentants, ses
                                      quatre différences inactives et l'égalité
                                      de leurs classes quotient, sans groupe de
                                      jauge implicite.
                                      - [x] Munir les quatre données inactives
                                        de leur translation additive explicite,
                                        prouver les lois identité/composition et
                                        identifier exactement ses orbites aux
                                        fibres actives/classes quotient. Cette
                                        action n'est pas un groupe de jauge.
                                        - [x] Factoriser par cette action
                                          structurée l'invariance de la courbe,
                                          des dérivées un à quatre, de l'Euler,
                                          de `C1–C4`, des Hessians assemblé,
                                          quotient et D9 enrichi.
                                          - [x] Former son quotient ensembliste,
                                            construire les équivalences explicites
                                            avec `ActiveDirection` et
                                            `ActiveQuotient`, et prouver la
                                            commutation des projections. Aucune
                                            topologie ni jauge globale n'est ajoutée.
                                            - [x] Y faire descendre par
                                              `Quotient.lift` la courbe d'action,
                                              l'Euler/`C1` et le Hessien mixte/
                                              `C2`, avec formules exactes sur les
                                              classes canoniques. La descente
                                              reste purement ensembliste.
                                              - [x] Y faire aussi descendre
                                                `C3/C4`, toutes les dérivées
                                                itérées et le Taylor quartique
                                                exact complet, sans structure
                                                analytique sur ce quotient.
                                                - [x] Définir la stationnarité
                                                  de la même action sur ce
                                                  quotient et prouver son
                                                  équivalence exacte avec
                                                  l'annulation du véritable
                                                  Euler sur toutes les directions.
                                                - [x] Transporter la symétrie
                                                  de Helmholtz du véritable
                                                  Hessien assemblé vers ses deux
                                                  arguments quotient, sans doter
                                                  le quotient d'une structure
                                                  analytique.
                                                  - [x] Identifier exactement
                                                    le Hessien quotient inactif
                                                    aux formes sur
                                                    `ActiveDirection` et
                                                    `ActiveQuotient` via les
                                                    équivalences canoniques.
                                                  - [x] Transporter ses noyaux
                                                    gauche et droit vers les
                                                    noyaux actifs et prouver
                                                    leur équivalence mutuelle
                                                    par symétrie de Helmholtz.
                                                    - [x] Identifier la
                                                      stationnarité quotient à
                                                      l'annulation exacte de
                                                      l'Euler sur toutes les
                                                      directions actives.
                                                    - [x] Définir la trivialité
                                                      du noyau gauche au zéro
                                                      actif et prouver son
                                                      équivalence exacte entre
                                                      Hessien quotient inactif
                                                      et Hessien actif.
                                                      - [x] Définir aussi la
                                                        trivialité du noyau droit
                                                        et prouver ses équivalences
                                                        gauche/droite quotient et
                                                        actives par symétrie.
                                                      - [x] Transporter la non-
                                                        dégénérescence droite puis
                                                        bilatérale entre Hessien
                                                        quotient inactif et Hessien
                                                        actif, toujours au niveau
                                                        ensembliste.
                                                        - [x] Définir le zéro
                                                          canonique de
                                                          `ActiveQuotient` et ses
                                                          non-dégénérescences
                                                          Hessiennes gauche, droite
                                                          et bilatérale.
                                                        - [x] Identifier les
                                                          certificats gauche et
                                                          droit de ce quotient à
                                                          ceux de la direction
                                                          active via l'équivalence
                                                          canonique.
                                                        - [x] Transporter enfin
                                                          les trois certificats
                                                          depuis le quotient des
                                                          translations inactives
                                                          vers `ActiveQuotient`,
                                                          sans structure analytique.
                                                          - [x] Définir l'Euler
                                                            et la stationnarité
                                                            directement sur
                                                            `ActiveQuotient`, puis
                                                            les identifier exactement
                                                            à leurs descentes par les
                                                            translations inactives.
                                                          - [x] Définir les lieux
                                                            critiques point par point
                                                            sur les deux quotients et
                                                            prouver leur équivalence,
                                                            sans déduire une fausse
                                                            unicité globale de la seule
                                                            non-dégénérescence Hessienne.
                                                            - [x] Transporter la
                                                              courbe d'action et
                                                              `C1–C4` vers
                                                              `ActiveQuotient`, avec
                                                              cinq formules exactes
                                                              sur les classes de
                                                              directions complètes.
                                                            - [x] Prouver sur ce
                                                              quotient ensembliste le
                                                              Taylor quartique exact
                                                              `base+tC1+t²C2+t³C3+t⁴C4`,
                                                              sans structure analytique.
                                                              - [x] Faire descendre
                                                                les dérivées itérées
                                                                et certifier les quatre
                                                                normalisations
                                                                `D1=C1`, `D2=2C2`,
                                                                `D3=6C3`, `D4=24C4`.
                                                              - [x] Identifier sur
                                                                `ActiveQuotient`
                                                                `C1` au véritable Euler
                                                                et `C2` à la moitié du
                                                                véritable Hessien
                                                                quotient diagonal.
                                                                - [x] Définir somme
                                                                  et différence de
                                                                  classes via leurs
                                                                  représentants actifs
                                                                  canoniques, sans déclarer
                                                                  une structure additive.
                                                                - [x] Polariser `C2`
                                                                  sur deux classes,
                                                                  l'identifier exactement
                                                                  au Hessien quotient mixte
                                                                  et prouver sa symétrie.
                                                                  - [x] Calculer somme
                                                                    et différence sur les
                                                                    classes représentées,
                                                                    puis identifier le
                                                                    Hessien diagonal à
                                                                    `2·C2`.
                                                                  - [x] Récupérer inversement
                                                                    `C2` comme quart de la
                                                                    différence des Hessians
                                                                    diagonaux polarisés.
                                                                    - [x] Prouver
                                                                      l'additivité exacte
                                                                      du Hessien quotient
                                                                      dans chacun de ses
                                                                      deux arguments pour
                                                                      la somme ensembliste
                                                                      canonique, sans
                                                                      inventer une homogénéité
                                                                      absente de l'infrastructure.
                                                                      - [x] En déduire la
                                                                        formule quadratique
                                                                        exacte
                                                                        `C2(x⊕y)=C2(x)+C2(y)+H(x,y)`,
                                                                        sans affirmer une
                                                                        additivité de l'Euler LL
                                                                        encore non prouvée.
                                                                        - [x] Définir les
                                                                          classes zéro et
                                                                          opposée via les
                                                                          représentants actifs
                                                                          canoniques, sans
                                                                          instance additive.
                                                                        - [x] Prouver que le
                                                                          Hessien quotient
                                                                          s'annule sur zéro et
                                                                          commute à l'opposé
                                                                          avec le signe attendu
                                                                          dans chacun des slots.
                                                                          - [x] Prouver les
                                                                            lois de soustraction
                                                                            du Hessien quotient
                                                                            dans chacun de ses
                                                                            deux arguments.
                                                                          - [x] Prouver
                                                                            `C2(-x)=C2(x)` et
                                                                            `C2(0)=0` sur les
                                                                            classes canoniques.
                                                                          - [x] Établir la
                                                                            formule exacte
                                                                            `C2(x⊖y)=C2(x)+C2(y)-H(x,y)`.
                                                                            - [x] Prouver
                                                                              l'identité du
                                                                              parallélogramme
                                                                              pour `C2` sur les
                                                                              classes canoniques.
                                                                            - [x] Récupérer le
                                                                              Hessien quotient par
                                                                              la polarisation inverse
                                                                              `H=(C2(x⊕y)-C2(x⊖y))/2`,
                                                                              sans positivité ajoutée.
                      - [x] Faire de même pour les vraies directions ghost et
                        auxiliaire du domaine commun : projection active nulle,
                        action sectorielle constante, Euler et Hessien nuls.
                        Aucun BRST ni Candidate A complet n'est fermé.
                        - [x] Regrouper pour chacune les annulations de l'Euler
                          quotient, de sa lecture D9 active, de `C1–C4` et des
                          dérivées un à quatre. Ces certificats restent
                          sectoriels et ne ferment aucun complexe BRST global.
                          - [x] Prouver que l'ajout ghost ou auxiliaire à toute
                            direction conserve projection active, classe quotient,
                            lecture D9, courbe sectorielle et `C1/C2`.
                            - [x] Prouver aussi l'invariance de `C3/C4` et des
                              dérivées itérées un à quatre sous chacune de ces
                              deux translations sectorielles.
                              - [x] Prouver dans chacun des deux slots
                                l'invariance ghost/auxiliaire du coefficient
                                Taylor mixte, du Hessien assemblé et des
                                dérivées Euler mixtes correspondantes.
                                - [x] Transporter ces invariances ghost et
                                  auxiliaire au Hessien quotient et au Hessien
                                  D9 enrichi, slot par slot puis simultanément.
                                - [x] Raccorder `ghostFullDirection` aux deux
                                  traces `U(1)` et au ghost géométrique du symbole
                                  D9 apparié; au covecteur non nul, caractériser
                                  exactement son noyau pointwise. Aucun complexe
                                  BRST global n'est affirmé.
                                  - [x] Au covecteur nul, prouver le symbole nul,
                                    retrouver exactement le représentant de la
                                    classe de cohomologie zéro-mode et caractériser
                                    sa classe nulle. La portée reste ponctuelle.
                                  - [x] Au covecteur non nul, récupérer
                                    exactement cette coordonnée par l'inverse du
                                    symbole, fournir son antécédent dans l'image
                                    et annuler sa classe de conoyau ponctuelle.
                      - [x] Faire encore de même pour une vraie direction de
                        métrique diagonale : injection exacte, action sectorielle
                        constante, Euler/Hessien nuls. Le bloc Einstein--Hilbert
                        reste absent, donc Candidate A complet reste ouvert.
                        - [x] Regrouper la classe quotient et la lecture D9
                          actives nulles, `C1–C4` et les dérivées un à quatre
                          nulles. Ce certificat demeure sans Einstein--Hilbert.
                          - [x] Prouver que l'ajout d'une direction métrique pure
                            conserve projection active, classe quotient, lecture
                            D9, courbe sectorielle et `C1/C2`, toujours sans EH.
                            - [x] Prouver aussi l'invariance de `C3/C4` et de
                              toutes les dérivées itérées, en particulier des
                              ordres un à quatre, toujours sans bloc EH.
                              - [x] Prouver l'invariance du coefficient Taylor
                                mixte, du Hessien assemblé et des dérivées Euler
                                mixtes lorsque cette direction métrique pure est
                                ajoutée dans l'un ou l'autre slot.
                                - [x] Transporter ces invariances au Hessien
                                  quotient et au Hessien D9 enrichi dans le
                                  premier, le second et les deux slots.
        - [x] Rendre publiques les compatibilités au zéro du pullback PT, de la
          moyenne PT et de la dérivée de frame, prérequis analytiques des
          identités de variation LL à direction nulle.
          - [x] En déduire l'annulation des densités de première variation
            cinétique/worldvolume, de leur moyenne PT, de leur intégrale et de
            la première variation LL assemblée à direction nulle.
            - [x] Transporter cette annulation à l'Euler LL, au coefficient
              Taylor intégré `C1`, à l'Euler Taylor et à la dérivée de la
              vraie courbe d'action LL nulle.
              - [x] Prouver que cette courbe LL nulle est constante, que son
                Hessien diagonal et `C2/C3/C4` intégrés sont nuls, et que son
                Taylor exact se réduit à la valeur initiale.
                - [x] Prouver aussi l'annulation du Hessien LL mixte lorsque
                  l'un des deux slots est la direction nulle et transporter
                  cette nullité aux deux dérivées correspondantes de l'Euler LL.
                  - [x] Transporter la direction LL nulle vers sa classe active
                    quotient et son observation D9 enrichie, puis prouver
                    l'annulation du Hessien dans les deux ordres.
      - [x] Pour le bloc cinétique PT intégré, rendre publiques la continuité,
        l'intégrabilité et l'additivité dans la première direction du vrai
        Hessien mixte. La polarisation full attend encore le bloc worldvolume.
        - [x] Prouver aussi l'additivité dans la première direction du Hessien
          worldvolume aux niveaux brut, moyenné PT et intégré, sans hypothèse
          supplémentaire.
          - [x] Assembler ces deux additivités pour le vrai Hessien LL complet,
            au moyen d'une addition explicite de toutes les composantes des
            directions, sans installer d'instance algébrique globale.
            - [x] Construire de même les négations explicites et prouver
              l'homogénéité par `-1` des blocs cinétique, worldvolume puis du
              vrai Hessien LL complet, sans instance globale.
              - [x] En déduire l'identité de polarisation exacte du vrai
                Hessien LL complet sur les directions explicites : reconstruire
                `H(x,y)` par un quart de `H(x+y,x+y)-H(x-y,x-y)`.
                - [x] Identifier ces deux diagonales aux coefficients `C2`
                  intégrés des vraies courbes de la même action LL globale et
                  obtenir `H(x,y) = (∫C2[x+y]-∫C2[x-y])/2`.
                - [x] Transporter les additions/négations explicites vers les
                  composantes matière et Robin et prouver l'additivité ainsi que
                  l'homogénéité par `-1` de leurs vrais Hessians.
                  - [x] Assembler la polarisation du vrai Hessien
                    matière+Robin+LL et reconstruire son terme mixte comme
                    `(C2[x+y]-C2[x-y])/2` depuis les coefficients diagonaux de
                    la même action globale assemblée.
                    - [x] Reformuler cette polarisation comme un quart de la
                      différence des Hessians enrichis D9 diagonaux observés sur
                      `x+y` et `x-y`, sans injectivité ni bijectivité D9.
                      - [x] Transporter cette formule sur les classes quotient
                        `⟦x⟧,⟦y⟧` via leurs représentants explicites et donner
                        sa lecture enrichie D9, sans structure additive du quotient.
    - [x] Reconstruire exactement cette même action matière+Robin+LL sur la
      direction radiale enrichie depuis sa constante Robin au zéro, son terme
      Euler affine et la moitié de son Hessien enrichi, sans nouvelle hypothèse.
    - [x] Prouver que toute direction enrichie purement métrique, jauge, ghost
      ou auxiliaire appartient aux noyaux gauche et droit du Hessien exact de
      cette action sectorielle. Cela constate les blocs absents et ne les
      remplace pas dans le Hessien Candidate A.
    - [x] Définir la projection active exacte matière--Robin--LL et prouver que
      l'Euler et le Hessien de cette même action se factorisent par elle, avec
      congruence dans chacune des deux directions du Hessien.
      - [x] Caractériser son noyau et toutes ses fibres : la fibre zéro laisse
        exactement libres les secteurs métrique, jauge, ghost et auxiliaire.
      - [x] Quotienter les directions enrichies par égalité de projection active,
        faire descendre le Hessien sur les deux classes et conserver sa symétrie.
        Ce quotient appartient à l'action matière+Robin+LL, pas à Candidate A.
        - [x] Reconstruire exactement ce Hessien quotient par l'équivalence
          canonique vers les directions actives et identifier son noyau gauche
          au noyau gauche actif. Aucune non-dégénérescence active n'est affirmée.
          - [x] Identifier de même son noyau droit au noyau droit actif, puis
            prouver l'équivalence exacte des noyaux gauche et droit par symétrie,
            sans affirmer que ces noyaux sont triviaux.
        - [x] Faire descendre aussi l'Euler sur ce quotient et transporter sa
          vraie dérivée sur les représentants vers le Hessien quotient. Aucune
          structure différentiable du quotient ensembliste n'est revendiquée.
          - [x] Reconstruire exactement cet Euler quotient via l'équivalence
            canonique vers la direction active de la même action.
            - [x] En déduire l'équivalence exacte de stationnarité quotient/
              active et identifier la dérivée de la courbe Euler représentative
              au Hessien actif sur les deux projections.
        - [x] Reformuler la reconstruction de la même action par la classe
          radiale et le Hessien quotient, en conservant explicitement la
          constante Robin et le terme Euler affine.
      - [x] Prouver que la projection active ne se factorise pas par le D9
        actuel : deux classes Robin distinctes ont la même observation D9, ce
        qui exclut toute reconstruction uniforme de la classe active depuis D9.
        - [x] Enrichir minimalement l'observation D9 par un vrai slot Robin,
          récupérer exactement cette direction et supprimer l'ambiguïté Robin.
          Les directions auxiliaire et LL restent explicitement invisibles.
    - [x] Sur le seul sous-bloc lisse Robin+LL commun aux deux constructions,
      identifier exactement le Hessien enrichi de l'action matière+Robin+LL au
      Hessien bosonique naturel réduit utilisé par la famille Fredholm. Les
      blocs matière et scalaire proviennent d'actions différentes et sont donc
      explicitement exclus de cette égalité.
      - [x] Identifier aussi le pairing du véritable opérateur de Jacobi
        Fredholm réduit au Hessien commun sur cette inclusion Robin+LL et
        transporter son certificat de noyau sous le couplage non nul déjà requis.
        - [x] Étendre ce pont au nouveau Hessien LL complet : lorsque les
          directions de métrique auxiliaire et de mesure LL sont nulles, il se
          réduit exactement au Hessien de flux puis au Hessien naturel Fredholm
          Robin+LL. La mesure LL est supposée finie pour cette comparaison.
          - [x] Transporter cette identification sur les classes du quotient
            actif issues des directions lisses Robin+LL : leur Hessien quotient
            est exactement le pairing du véritable Jacobi Fredholm réduit sur
            ces trois blocs, sans conclure au noyau sur la complétion.
            - [x] En déduire qu'une direction lisse Robin+LL appartenant au
              noyau du véritable Jacobi réduit annule le Hessien quotient contre
              toute l'image lisse Robin+LL. La réciproque complétée reste
              ouverte faute de densité du plongement Robin dans `L²`.
            - [x] Sur cette inclusion lisse Robin+LL, prouver explicitement que
              le bloc matière du coefficient mixte assemblé est nul, puis
              identifier ce coefficient et le Hessien quotient au pairing du
              véritable opérateur de Jacobi réduit avec entrée scalaire nulle.
              - [x] En déduire que toute telle inclusion appartenant au noyau
                du vrai Jacobi réduit annule le coefficient mixte et le Hessien
                quotient contre toute autre inclusion lisse, sans réciproque.
    - [x] Enrichir l'observation D9 Robin par un slot LL réel, récupérer exactement
      le champ LL fourni par le type source et supprimer son ambiguïté. Les
      vitesses de métrique auxiliaire LL et de mesure restent nulles car ce type
      enrichi ne les expose pas encore.
      - [x] Ajouter aussi la vraie paire auxiliaire bulk, caractériser l'égalité
        de la projection `visible+Robin+LL+auxiliaire` et prouver l'injectivité
        dans le slot auxiliaire à toutes les autres données fixées.
    - [x] Étendre fidèlement le domaine commun par les trois directions LL
      réelles (champ, métrique auxiliaire et mesure) en plus de Robin, et prouver
      l'extraction exacte de tous les secteurs depuis la variation indépendante.
      - [x] Projeter ces trois directions LL complètes, Robin et l'auxiliaire dans
        une observation D9 enrichie, caractériser son égalité et prouver
        l'injectivité du triplet LL à toutes les autres données fixées.
        - [x] Faire factoriser le vrai Hessien matière+Robin+LL par deux telles
          observations D9 enrichies et le reconstruire exactement sur
          l'inclusion active. Il s'agit d'une factorisation d'observation,
          pas d'un complexe D9/BRST global.
          - [x] Faire de même factoriser le vrai Euler matière+Robin+LL par
            l'observation D9 enrichie et le reconstruire exactement sur
            l'inclusion active, sans revendication BRST.
            - [x] Le long de la vraie courbe Euler représentative, identifier
              sa dérivée au Hessien factorisé sur les deux observations D9
              enrichies, sans inventer de structure différentiable sur celles-ci.
            - [x] Prouver l'équivalence de stationnarité avec l'Euler lu sur
              l'observation D9 enrichie et l'indépendance exacte de cette valeur
              vis-à-vis des composantes inactives, sans identifier les paquets.
            - [x] Prouver les congruences séparées du Hessien enrichi dans ses
              deux slots et l'invisibilité des composantes du noyau de projection
              active, sans conclure à la non-dégénérescence active.
            - [x] Envoyer canoniquement la lecture active de l'observation D9
              enrichie vers sa classe quotient et identifier exactement les
              Euler/Hessien enrichis aux formes quotient sur ces classes, sans
              bijectivité revendiquée du paquet D9 complet.
              - [x] Sur les observations enrichies issues des directions lisses
                Robin+LL, identifier directement leur Hessien au pairing du vrai
                Jacobi réduit, avec bloc scalaire `H¹` explicitement nul.
                - [x] Composer cette identification avec la vraie dérivée de la
                  courbe Euler représentative de l'action matière+Robin+LL : sur
                  cette tranche lisse, elle vaut exactement le pairing du Jacobi
                  Fredholm réduit. Les blocs métrique, Maxwell et ghosts ainsi
                  qu'une famille Fredholm globale restent absents.
                - [x] En déduire qu'une inclusion lisse Robin+LL dans le noyau
                  du vrai Jacobi réduit annule ce Hessien enrichi contre toute
                  observation lisse Robin+LL, sans réciproque.
                - [x] Sous mesure finie positive sur tout ouvert non vide,
                  prouver l'injectivité du plongement des champs Robin lisses
                  dans `L²`. Cette condition de support total ne fournit pas la
                  densité encore requise pour la réciproque du pairing.
                  - [x] Sous cette même condition de support total et couplage
                    Robin non nul, déduire qu'un vecteur lisse Robin+LL du noyau
                    du Jacobi réduit possède un champ Robin nul pointwise. Aucune
                    conclusion LL supplémentaire n'est affirmée.
                    - [x] Instancier l'injectivité Robin `L²` pour la vraie
                      mesure canonique du throat, dont la positivité sur les
                      ouverts est déjà prouvée depuis sa construction pushforward.
                      - [x] Pour cette mesure canonique et sous couplage Robin
                        non nul, déduire sans hypothèse de support résiduelle que
                        le champ Robin lisse d'un vecteur du noyau Jacobi est nul
                        pointwise. Aucune conclusion LL n'est ajoutée.
                        - [x] Identifier en outre la composante LL comme nulle
                          dans l'espace complété `LLH¹`; la nullité du paramètre
                          lisse et de sa lecture D9 requiert encore, à cette
                          étape, l'injectivité fermée ci-dessous.
                          - [x] Prouver cette injectivité du plongement lisse
                            dans la complétion `LLH¹` et en déduire que la
                            direction, son champ test, sa norme `H¹` et son
                            énergie diagonale sont effectivement nuls.
                            - [x] Sous mesure canonique et couplage Robin non nul,
                              conclure pour le noyau Jacobi réduit Robin+LL que
                              Robin, la direction LL lisse et sa lecture active
                              D9 enrichie sont nulles. Aucun noyau global n'est visé.
                              - [x] En déduire que cette inclusion Robin+LL
                                représente exactement la classe active quotient
                                nulle, sans conclusion hors du secteur réduit.
                                - [x] Remplacer en conséquence cette classe par
                                  la classe nulle dans l'Euler et le Hessien
                                  quotient contre toute autre classe, sans
                                  affirmer encore leur valeur numérique nulle.
                                  - [x] Prouver ensuite que l'Euler quotient et
                                    le Hessien quotient contre toute classe valent
                                    effectivement zéro, via les gates inactifs
                                    stabilisés et la mesure canonique finie.
                                    - [x] Transporter ces annulations numériques
                                      vers l'Euler et le Hessien des observations
                                      D9 enrichies Robin+LL correspondantes, sans
                                      élargir la portée au noyau global.
                                      - [x] En déduire l'annulation des
                                        coefficients assemblés `C1/C2` et des
                                        dérivées d'ordres un et deux de la vraie
                                        courbe canonique Robin+LL. Aucun `C3/C4`
                                        n'est annulé par cette hypothèse.
                                        - [x] Après les nullités réelles de
                                          Robin et LL, prouver aussi `C3/C4=0`,
                                          les dérivées d'ordres trois/quatre
                                          nulles et la constance de la vraie
                                          courbe assemblée pour tout paramètre.
                                          - [x] Sous couplage Robin non nul,
                                            prouver les équivalences exactes
                                            entre noyau du Jacobi réduit,
                                            `Robin=0 ∧ LL=0` et classe active
                                            Robin+LL nulle.
                                            - [x] Construire l'inclusion lisse
                                              Robin+LL comme application linéaire
                                              canonique et prouver que sa
                                              composition avec le Jacobi réduit
                                              est injective, de noyau `⊥`, sans
                                              affirmer la fermeture de son image.
                                              - [x] Construire l'équivalence
                                                linéaire canonique avec son
                                                `range` algébrique, avec inverse
                                                exact, sans affirmer que ce range
                                                est fermé ou complété.
                                                - [x] Identifier le Hessien
                                                  quotient Robin+LL au pairing
                                                  exact de l'opérateur sur les
                                                  inclusions lisses, construire
                                                  la forme pullback du produit
                                                  scalaire du range et prouver
                                                  son noyau trivial. Aucune
                                                  coercivité ni fermeture du
                                                  range n'est affirmée.
                                                  - [x] Prouver séparément que
                                                    la forme pullback du produit
                                                    scalaire du range est
                                                    symétrique, positive, définie
                                                    positive et bilatéralement
                                                    non dégénérée. Ne pas
                                                    transférer indûment cette
                                                    positivité au Hessien quotient.
                                                    - [x] Décomposer exactement
                                                      cette forme en norme carrée
                                                      de l'image Jacobi Robin et
                                                      norme énergétique `H¹` LL;
                                                      aucune borne inverse ni
                                                      coercivité Robin n'est
                                                      affirmée.
                                                      - [x] Au niveau complété,
                                                        borner le bloc Robin par
                                                        la norme de son opérateur,
                                                        identifier le bloc LL à
                                                        une isométrie et donner
                                                        la borne bilineaire exacte
                                                        du pairing. Aucune
                                                        coercivité n'en découle.
                                                        - [x] Empaqueter ce pairing
                                                          en application bilinéaire
                                                          continue et prouver la
                                                          borne ponctuelle explicite
                                                          `(‖R‖²+1)‖x‖‖y‖`, sans
                                                          norme d'opérateur ou
                                                          coercivité inventée.
                                                          - [x] Certifier pour
                                                            cette application
                                                            continue la symétrie,
                                                            la positivité diagonale
                                                            et l'identité exacte
                                                            avec la norme de graphe
                                                            Robin+LL, sans affirmer
                                                            d'autoadjonction typée.
                                                            - [x] Identifier
                                                              exactement l'annulation
                                                              diagonale et le radical
                                                              de ce pairing continu à
                                                              `ker R × {0}` : non-
                                                              dégénérescence LL, mais
                                                              seulement modulo le
                                                              noyau Robin.
                                                              - [x] Identifier
                                                                de même les radicaux
                                                                droit et bilatéral à
                                                                `ker R × {0}` par
                                                                symétrie, sans former
                                                                un quotient normé tant
                                                                que ce noyau n'est pas
                                                                prouvé fermé.
                                                                - [x] Construire
                                                                  néanmoins le
                                                                  quotient algébrique
                                                                  par ce radical et
                                                                  son équivalence
                                                                  linéaire avec le
                                                                  range du bloc
                                                                  `R × id_LL`.
                                                                - [x] Caractériser ce
                                                                  range exactement par
                                                                  `range(R) × LL`, sans
                                                                  topologie, fermeture,
                                                                  complétude ou
                                                                  coercivité ajoutée.
                                                                  - [x] Faire descendre
                                                                    intrinsèquement le
                                                                    pairing à ce quotient
                                                                    algébrique et donner
                                                                    sa formule exacte sur
                                                                    représentants.
                                                                  - [x] Prouver la
                                                                    symétrie et la non-
                                                                    dégénérescence de la
                                                                    forme descendue, sans
                                                                    propriété topologique
                                                                    ou coercive.
                                                                    - [x] Identifier
                                                                      exactement la
                                                                      diagonale quotient
                                                                      à la somme des
                                                                      carrés des composantes
                                                                      `range(R)` et LL.
                                                                    - [x] En déduire sa
                                                                      positivité et
                                                                      `Q(q,q)=0 ↔ q=0`,
                                                                      sans la confondre
                                                                      avec la norme produit
                                                                      `max` ni une coercivité.
                                                                      - [x] Définir la
                                                                        fonction norme de
                                                                        graphe quotient par
                                                                        `sqrt(Q(q,q))` et
                                                                        prouver l'inégalité
                                                                        de Cauchy–Schwarz du
                                                                        pairing, sans instance
                                                                        topologique ou complétude.
                                                                        - [x] Prouver
                                                                          positivité,
                                                                          carré diagonal
                                                                          et séparation
                                                                          de cette fonction
                                                                          norme de graphe.
                                                                        - [x] Prouver son
                                                                          homogénéité absolue
                                                                          depuis la bilinéarité
                                                                          du pairing quotient.
                                                                        - [x] Développer la
                                                                          diagonale d'une somme
                                                                          et en déduire l'inégalité
                                                                          triangulaire, sans
                                                                          remplacer l'instance
                                                                          normée existante.
                                                                          - [x] Empaqueter
                                                                            localement ces
                                                                            axiomes en une
                                                                            `Seminorm` réelle,
                                                                            prouver sa formule
                                                                            d'évaluation et son
                                                                            noyau trivial, sans
                                                                            installer d'instance
                                                                            globale ni comparer
                                                                            des normes non reliées.
                                                                            - [x] Sur un
                                                                              synonyme transparent,
                                                                              construire localement
                                                                              la structure de groupe
                                                                              normé induite et prouver
                                                                              que sa norme vaut
                                                                              exactement la graphNorm,
                                                                              sans instance globale
                                                                              ni complétude.
                                                                              - [x] Transporter
                                                                                le pairing sur
                                                                                ce synonyme normé,
                                                                                prouver sa symétrie
                                                                                et la borne exacte
                                                                                de constante `1`,
                                                                                sans empaqueter une
                                                                                continuité dont le
                                                                                `NormedSpace` n'est
                                                                                pas établi.
                                                                                - [x] Prouver
                                                                                  algébriquement
                                                                                  les identités de
                                                                                  diagonale pour
                                                                                  l'opposé et la
                                                                                  différence.
                                                                                - [x] En déduire
                                                                                  le parallélogramme
                                                                                  de la graphNorm et
                                                                                  la polarisation réelle
                                                                                  exacte récupérant le
                                                                                  pairing, sans installer
                                                                                  d'`InnerProductSpace`.
                                                                                  - [x] Définir
                                                                                    l'orthogonalité
                                                                                    algébrique par
                                                                                    `Q(x,y)=0`, prouver
                                                                                    sa symétrie et les
                                                                                    deux identités de
                                                                                    Pythagore au carré
                                                                                    pour somme/différence.
                                                                                    - [x] Exposer
                                                                                      l'additivité et
                                                                                      l'homogénéité dans
                                                                                      le premier slot puis
                                                                                      construire l'orthogonal
                                                                                      d'une classe comme
                                                                                      sous-module algébrique.
                                                                                    - [x] Prouver qu'une
                                                                                      classe appartient à
                                                                                      son propre orthogonal
                                                                                      ssi elle est nulle et
                                                                                      que l'orthogonal de
                                                                                      zéro est `⊤`.
                                                                                      - [x] Définir
                                                                                        l'orthogonal
                                                                                        algébrique d'un
                                                                                        sous-module et
                                                                                        prouver son
                                                                                        antitonicité.
                                                                                      - [x] Prouver que
                                                                                        l'intersection des
                                                                                        orthogonaux de toutes
                                                                                        les classes est `⊥`
                                                                                        et que l'orthogonal
                                                                                        d'une classe non nulle
                                                                                        est strictement propre.
                                                                                        - [x] Définir le
                                                                                          double orthogonal
                                                                                          algébrique et prouver
                                                                                          l'inclusion générale
                                                                                          `S ≤ S⊥⊥`, notamment
                                                                                          pour le span d'une classe.
                                                                                        - [x] Prouver
                                                                                          `⊤⊥ = ⊥` par non-
                                                                                          dégénérescence, sans
                                                                                          affirmer l'égalité au
                                                                                          double orthogonal faute
                                                                                          d'hypothèses suffisantes.
                                                                                          - [x] Prouver la
                                                                                            relation de Galois
                                                                                            `S ≤ T⊥ ↔ T ≤ S⊥`
                                                                                            pour les sous-modules.
                                                                                          - [x] En déduire
                                                                                            `S⊥⊥⊥=S⊥` et
                                                                                            l'idempotence du
                                                                                            double orthogonal,
                                                                                            purement algébriquement.
                                                                                            - [x] Définir le
                                                                                              prédicat de point
                                                                                              fixe du double
                                                                                              orthogonal et prouver
                                                                                              que `S⊥` et `S⊥⊥`
                                                                                              le satisfont.
                                                                                            - [x] Prouver que
                                                                                              `S⊥⊥` est le plus petit
                                                                                              point fixe contenant
                                                                                              `S`, sans interprétation
                                                                                              topologique de cette
                                                                                              fermeture algébrique.
                                                                                              - [x] Prouver la
                                                                                                monotonie du double
                                                                                                orthogonal et
                                                                                                l'empaqueter avec
                                                                                                extensivité/idempotence
                                                                                                en `ClosureOperator`
                                                                                                Mathlib, sans lois
                                                                                                sup/inf non générales.
                                                                                                - [x] Identifier
                                                                                                  `ClosureOperator.IsClosed`
                                                                                                  exactement au
                                                                                                  prédicat de point
                                                                                                  fixe orthogonal,
                                                                                                  au sens algébrique.
                                                                                                - [x] Prouver
                                                                                                  `⊥^⊥=⊤` puis calculer
                                                                                                  les clôtures double-
                                                                                                  orthogonales de `⊥`
                                                                                                  et `⊤` comme elles-mêmes.
                                                                                                  - [x] Prouver que
                                                                                                    l'infimum arbitraire
                                                                                                    d'une famille de
                                                                                                    sous-modules points
                                                                                                    fixes reste un point
                                                                                                    fixe, sans analogue
                                                                                                    faux pour le supremum brut.
                                                                                                    - [x] Définir le
                                                                                                      join fermé d'une
                                                                                                      famille arbitraire
                                                                                                      par double orthogonal
                                                                                                      de son supremum et
                                                                                                      prouver qu'il est fixe.
                                                                                                    - [x] Prouver qu'il
                                                                                                      contient chaque membre
                                                                                                      et qu'il est minimal
                                                                                                      parmi les majorants
                                                                                                      orthogonalement fixes.
                                                                                                      - [x] Spécialiser
                                                                                                        le join fermé au
                                                                                                        cas binaire et
                                                                                                        prouver sa
                                                                                                        commutativité.
                                                                                                      - [x] Prouver que
                                                                                                        le meet de deux
                                                                                                        points fixes est
                                                                                                        fixe et l'absorption
                                                                                                        du join fermé par
                                                                                                        ce meet sous les
                                                                                                        hypothèses exactes.
      - [x] Transporter la même action et son Hessien sur les trois directions LL
        simultanées : identifier la première variation PT complète au coefficient
        de la vraie action, puis prouver que sa dérivée est la Hessienne globale
        assemblée et symétrique.
        - [x] Empaqueter cette fermeture en une API `fullLLEuler/fullLLHessian`,
          avec courbe complète, dérivée de la vraie action, dérivée de l'Euler
          et symétrie de Helmholtz.
        - [x] Remplacer le bloc LL partiel dans l'action assemblée
          matière+Robin+LL par la vraie action LL complète, sur la courbe commune
          aux trois directions, et prouver le `HasDerivAt` de cette somme exacte.
          - [x] Assembler les vrais Hessians des huit composantes matière, de
            Robin et du bloc LL complet, identifier la première variation à
            l'Euler de cette même action, prouver sa dérivée vers le Hessien
            assemblé et la symétrie de celui-ci.
            - [x] Prouver que l'action, l'Euler et les deux slots du Hessien sont
              inchangés lorsque seules les directions métrique, jauge, ghost ou
              auxiliaire bulk varient ; ces quatre secteurs sont donc inactifs
              pour cette action exacte, sans être supprimés du domaine commun.
            - [x] Projeter exactement vers les cinq slots actifs
              matière--Robin--champ LL--métrique LL--mesure LL, caractériser le
              noyau inactif, factoriser Euler et Hessien et faire descendre le
              Hessien symétrique au quotient actif.
              - [x] Faire descendre aussi l'Euler sur ce quotient, transporter
                sa dérivée représentative vers le Hessien quotient et prouver
                la symétrie directement sur les classes.
              - [x] Comparer cette projection active au D9 enrichi : Robin et les
                trois slots LL sont récupérés exactement, mais la matière reste
                une trace sectorielle. Un champ constant dans le secteur opposé
                donne une projection active distincte avec le même D9 observé.
                - [x] Ajouter un vrai slot contenant la paire globale matière,
                  récupérer alors exactement les cinq directions actives et
                  construire un encodage injectif des données actives dans ce
                  D9 enrichi. Il s'agit encore d'un paquet de données, pas du
                  complexe différentiel global.
              - [x] Faire descendre la projection active au quotient et construire
                l'équivalence canonique bijective entre les classes de directions
                et le type des cinq directions actives, avec inverse explicite.
                - [x] Identifier ensuite ce quotient à l'image exacte des paquets
                  D9 globalement enrichis par une équivalence canonique composée,
                  avec formules explicites sur les classes et leur inverse.
        - [x] Au niveau de la densité différentielle brute, construire la courbe
          de mesure, son expansion affine, le Hessien mixte mesure--champ dans
          les deux ordres et prouver leur égalité ; le croisement
          mesure--métrique auxiliaire est exactement nul.
        - [x] Développer exactement le polynôme simultané du terme cinétique
          sous variation champ+métrique auxiliaire et identifier son coefficient
          linéaire à la première variation pointwise réelle.
        - [x] Développer séparément la densité monde-volume sous deux paramètres
          mesure+champ, avec tous les termes croisés, puis prouver le `HasDerivAt`
          de la courbe diagonale au zéro.
          - [x] Intégrer cette expansion brute sous mesure finie, prouver
            l'intégrabilité des six termes et transporter le `HasDerivAt`
            diagonal vers la vraie première variation globale brute.
        - [x] Moyenner le Hessien mixte mesure--champ par la vraie involution PT,
          prouver la symétrie dans les deux ordres, la nullité du croisement
          mesure--métrique auxiliaire, ainsi que continuité et intégrabilité du
          coefficient global. L'expansion intégrée simultanée reste ouverte.
        - [x] Moyenner aussi par PT le polynôme cinétique simultané
          champ--métrique auxiliaire, identifier son coefficient linéaire et
          prouver continuité et intégrabilité. L'identité de dérivée intégrée
          reste à formaliser.
          - [x] Prouver le lemme analytique générique requis : toute combinaison
            quartique de cinq fonctions intégrables est intégrable, son intégrale
            est le polynôme des cinq intégrales et sa dérivée au zéro vaut
            l'intégrale du coefficient linéaire.
          - [x] Appliquer ce lemme aux cinq coefficients PT cinétiques continus
            et intégrables, définir l'action cinétique PT intégrée et prouver
            son `HasDerivAt` simultané champ--métrique auxiliaire.
            - [x] Exposer les coefficients cinétiques PT `C3/C4`, prouver leur
              continuité et intégrabilité, l'expansion quartique intégrée et
              identifier les dérivées itérées d'ordres trois et quatre à
              `3! ∫ C3` et `4! ∫ C4`.
        - [x] Définir la courbe LL complète champ+métrique auxiliaire+mesure et
          décomposer exactement la vraie action différentielle PT le long de
          cette courbe en intégrale cinétique PT et terme monde-volume PT.
        - [x] Assembler ces deux termes intégrés sur une courbe commune et
          prouver le `HasDerivAt` simultané, avec dérivée égale à la somme
          exacte des variations cinétique et monde-volume PT.
          - [x] Intégrer explicitement la moyenne PT de l'expansion à six
            coefficients mesure--champ, prouver leur intégrabilité, la formule
            globale à deux paramètres et son `HasDerivAt` diagonal.
        - [x] Identifier exactement cette action assemblée et sa courbe complète
          à la vraie `globalPTSymmetricDifferentialLLAction`, puis transporter
          le `HasDerivAt` simultané vers cette action existante.
          - [x] Développer exactement la densité de cette vraie courbe jusqu'au
            degré quatre : première variation, demi-Hessien diagonal, puis
            coefficients cubique et quartique explicites.
            - [x] Moyenner par PT les coefficients complets cubique et quartique,
              prouver continuité et intégrabilité, définir leurs intégrales et
              certifier les normalisations `3!` et `4!` par dérivées itérées.
        - [x] Construire le Hessien PT monde-volume complet pour deux directions
          mesure+champ distinctes, l'identifier au coefficient linéaire de la
          seconde variation, prouver son intégrabilité et sa symétrie globale.
          - [x] Définir la première variation PT globale et prouver que sa
            dérivée le long d'une seconde direction vaut exactement ce Hessien
            monde-volume intégré.
          - [x] Construire le coefficient cubique monde-volume PT, prouver sa
            continuité et son intégrabilité, puis identifier la troisième
            variation diagonale globale à `3!` fois ce coefficient.
        - [x] Construire et intégrer le Hessien cinétique PT mixte pour deux
          directions champ--métrique auxiliaire distinctes, prouver sa linéarité
          dans la première direction et sa symétrie pointwise, PT et globale.
          - [x] Développer la densité cinétique sous deux paramètres indépendants
            et identifier exactement son coefficient `s*t` à la densité du
            Hessien mixte.
            - [x] Isoler l'expansion bilatère exacte de l'énergie de dérivée du
              throat et prouver publiquement la symétrie de son pairing, afin de
              normaliser les coefficients de la polarisation cinétique.
          - [x] Prouver que la dérivée de la vraie première variation cinétique
            PT intégrée le long d'une seconde direction vaut exactement le
            Hessien cinétique mixte global.
            - [x] Rendre publiques la continuité et l'intégrabilité de la
              densité Hessienne cinétique brute pour toute paire de directions,
              afin de permettre les comparaisons d'intégrales PT et Fredholm.
        - [x] Assembler les Hessiennes cinétique et monde-volume sur les trois
          directions LL extraites du domaine complet et prouver la formule et
          la symétrie de cette forme globale. Son origine variationnelle complète
          est cochée seulement composante par composante.
          - [x] Additionner les deux vraies dérivées de première variation et
            prouver que la dérivée de la première variation LL complète vaut
            exactement la forme Hessienne assemblée.
    - [x] Calculer sa visibilité D9 : la projection conserve exactement le paquet
      commun mais oublie Robin ; deux directions Robin distinctes restent
      distinguées par l'injection enrichie tout en donnant les quatre mêmes
      blocs D9 actuels.
      - [x] Exhiber deux directions Robin constantes distinctes mais de même
        projection D9 et en déduire qu'aucune reconstruction depuis les slots
        D9 actuels ne peut être inverse à gauche sur toutes les directions
        enrichies. Ce no-go ne concerne pas un futur D9 enrichi.
  - [x] Sur l'action bosonique réduite unique scalaire global + Robin + LL PT,
    prouver l'existence `HasDerivAt` de la dérivée de l'Euler sous variation
    simultanée des trois backgrounds et identifier cette dérivée à la vraie
    seconde variation mixte de la même action. Les blocs métrique, jauge et
    ghosts du domaine Candidate A global restent ouverts.
  - [x] Pour l'action globale du multiplet matière à huit composantes, prouver
    l'existence de la dérivée de son Euler, l'identifier à la somme des huit
    Hessians de la même action et établir sa symétrie de Helmholtz. Les blocs
    métrique, jauge et ghosts restent absents.
    - [x] Ajouter une vraie direction métrique diagonale au même objet : dériver
      pointwise l'Euler matière, identifier sa dérivée métrique à la seconde
      variation mixte de la même densité, puis passer les deux dérivées sous
      l'intégrale avec des contrats explicites de mesurabilité, intégrabilité
      et domination Lipschitz. Ce Hessien mixte intégré reste conditionnel et
      limité aux huit scalaires, sans EH, Maxwell, ghosts ni bord.
  - [x] Pour l'action unique matière complète + Robin + LL, prouver que la
    dérivée de son Euler est son Hessien assemblé et que celui-ci satisfait la
    symétrie de Helmholtz. Les secteurs EH, jauge et ghosts restent ouverts.
- [ ] Prouver les conditions de Helmholtz non linéaires bloc par bloc.
  - [x] Pour le bloc LL différentiel PT, définir la condition de Helmholtz
    directement comme la symétrie de la dérivée effective de l'opérateur
    d'Euler à tout background, sur le vrai type commun de variations, puis la
    prouver par les deux secondes variations mixtes de la même action globale
    LL. Les autres blocs Candidate A restent ouverts.
  - [x] Pour le bloc scalaire holonome global D8, définir pareillement la
    condition de Helmholtz à chaque champ de fond et la prouver par la symétrie
    de la vraie seconde variation mixte de la même action scalaire inchangée.
    Cette fermeture ne couvre ni les métriques, ni la jauge, ni les ghosts.
  - [x] Pour le bloc de jonction Robin, définir la condition de Helmholtz pour
    les dérivées effectives de l'Euler à toute jonction de fond, avec les mêmes
    traces bulk, et la prouver par les secondes variations mixtes de la même
    action Robin. Aucun terme de bord général supplémentaire n'est revendiqué.
  - [x] Sur l'unique action bosonique réduite assemblant scalaire global,
    jonction Robin et LL PT, prouver la symétrie de sa vraie seconde variation
    sous échange simultané des trois directions. Cette condition de Helmholtz
    assemblée reste réduite et ne contient aucun bloc métrique, jauge ou ghost.
  - [x] Pour le multiplet global des huit composantes matière, formuler la
    condition non linéaire directement comme l'égalité des deux dérivées de
    l'Euler à tout champ de fond et la prouver par leurs identifications au
    Hessien symétrique de la même action. Les blocs EH/métrique, Maxwell et
    ghosts gauge-fixés restent absents.
- [ ] Reconstruire ou identifier l'action globale normalisée à partir de ces
  données.
  - [x] Pour le bloc scalaire holonome global D8, reconstruire exactement
    l'action inchangée comme la moitié de la diagonale de sa vraie seconde
    variation mixte. Cette identité fixe la normalisation quadratique de ce
    bloc seulement ; elle ne reconstruit pas l'action Candidate A complète.
  - [x] Pour le bloc de jonction Robin affine, reconstruire exactement l'action
    inchangée comme sa valeur au champ nul, plus son Euler au champ nul évalué
    sur la jonction, plus la moitié de son vrai Hessien diagonal. Les termes
    constant et linéaire dépendant des traces bulk sont ainsi conservés.
  - [x] Pour le bloc LL différentiel, prouver pointwise puis après intégration
    que l'action brute est la moitié de son Hessien de flux diagonal, et
    transporter exactement cette reconstruction à l'action moyennée PT. Les
    champs auxiliaires et la mesure restent le même background fixé.
  - [x] Pour l'unique action bosonique réduite assemblée, reconstruire
    exactement sa valeur comme le terme constant Robin, l'Euler Robin à
    l'origine, puis la moitié de la diagonale simultanée de son vrai Hessien
    scalaire + Robin + LL. Aucun bloc Candidate A supplémentaire n'est inclus.
  - [x] Pour l'action globale unique des huit coordonnées matière, prouver
    qu'elle est exactement la moitié de la diagonale de son Hessien sommée,
    puis spécialiser cette reconstruction aux champs réellement extraits d'un
    même `IndependentFields`. Les secteurs non matière restent ouverts.
  - [x] Pour l'action élargie matière complète + Robin + LL, reconstruire
    exactement sa valeur comme les termes constant et linéaire Robin plus la
    moitié de la diagonale de son Hessien assemblé. Cette normalisation ne
    couvre toujours pas EH, Maxwell ni les ghosts.
- [ ] Prouver l'identité de Noether pour les difféomorphismes diagonaux.
  - [x] Regrouper métrique lorentzienne générale, scalaire, frame et mesure
    dans une même configuration D8, prouver l'invariance finie inconditionnelle
    de son action scalaire globale sous leur pullback diagonal simultané, puis
    obtenir `HasDerivAt ... 0 0` et `deriv = 0` sur le vrai flot complet de
    translation temporelle. Ce sous-groupe scalaire n'identifie pas encore
    l'adjoint d'Euler, les Bianchi, un courant local ni l'action Programme P
    complète.
    - [x] Spécialiser ce résultat à la vraie mesure lorentzienne canonique et
      prouver d'abord que son pullback par chaque tranche temporelle lui est
      littéralement égal ; l'action scalaire globale reste alors constante et
      sa dérivée s'annule en ne transformant que métrique, champ et frame, avec
      la mesure physique laissée fixe. Aucun courant local, adjoint d'Euler ni
      bloc Candidate A supplémentaire n'est obtenu.
  - [x] Étendre l'invariance diagonale finie et sa dérivée temporelle nulle aux
    huit vraies composantes matière extraites d'un même `IndependentFields`,
    avec métrique, frame et mesure communes. Ce résultat porte sur la somme des
    huit actions scalaires covariantes ; son identification à
    `globalMatterMultipletAction`, ainsi que les blocs EH, Maxwell, ghosts et
    bord, restent ouverts.
    - [x] Remplacer la seule orbite de translation temporelle par toute courbe
      de difféomorphismes lisses D8 : l'action covariante des huit scalaires
      reste exactement constante et sa dérivée est nulle en tout paramètre.
      Aucun adjoint d'Euler, courant local ni bloc non matière n'est obtenu.
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
  - [x] Dans la réduction FLRW Candidate-A seulement, dériver la transformée de
    Legendre de la même action sous la forme exacte `H = N₊ C₊ + N₋ C₋` pour
    tous lapses, puis identifier ses deux dérivées partielles aux contraintes
    primaires `C₊` et `C₋`. Les shifts, l'ADM covariant et le domaine global
    restent ouverts.
- [ ] Calculer les contraintes secondaires et leur rang générique.
  - [x] Dans la réduction FLRW Candidate-A fournie, prolonger le témoin isolé
    en une famille affine dont le locus paramétrique de mineur `3 x 3` non nul
    est ouvert et non vide, puis prouver l'indépendance des trois covecteurs
    sur ce locus et sur un voisinage du témoin. Le rang générique global, la
    dérivation ADM/covariante et l'exclusion du mode de Boulware--Deser restent
    ouverts.
- [ ] Prouver la fermeture du crochet fonctionnel avec dérivées spatiales.
  - [x] Sur le seul réseau scalaire à deux sites `Fin 2`, introduire une vraie
    différence spatiale nearest-neighbour dans le même Hamiltonien, prouver
    que le covecteur affiché est sa dérivée effective sur toute ligne affine,
    factoriser exactement le crochet de deux smearings en coefficient
    antisymétrique fois courant spatial et exhiber un témoin non nul. Ce modèle
    finite-lattice ne ferme ni le crochet ADM continuum, ni l'algèbre des
    hypersurfaces, ni l'analyse du mode de Boulware--Deser.
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
  - [x] Sur le vrai Hilbert spectral infini du throat produit, définir le
    Dirac-carré diagonal non borné sur son domaine maximal, prouver densité,
  fermeture du graphe et auto-adjonction effective, puis identifier son
  exponentielle spectrale positive à l'opérateur chaleur nucléaire déjà
  construit. Cela ne construit pas encore le Dirac géométrique Janus 4D.
  - [x] Sur ce même Hilbert spectral du throat produit, construire le Dirac
    diagonal du premier ordre sur son domaine maximal, prouver sa densité et
    son auto-adjonction, puis identifier exactement le domaine de `D²` au
    domaine itéré de `D ∘ D`. Cela reste distinct du Dirac géométrique Janus
    global.
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
- [x] Prouver les propriétés trace-class requises.
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
        demi-droite positive et conserver la covariance PT. La série dérivée
      est absolument sommable à tout temps positif et la dérivée spectrale,
      donc la vraie dérivée, est non positive. Le passage au vrai opérateur
      Janus global reste ouvert.
      - [x] Absorber deux facteurs spectraux par deux demi-temps gaussiens,
        prouver la sommabilité uniforme de la seconde série dérivée, dériver
        une seconde fois terme à terme, identifier la vraie dérivée de la
        première trace dérivée, prouver sa positivité, sa continuité locale
        uniforme loin de zéro et sa covariance PT.
        - [x] Absorber un troisième facteur spectral, dériver une troisième
          fois terme à terme, prouver le signe alterné non positif et la
          covariance PT de cette dérivée, puis certifier `C³` de la trace
          nucléaire réelle sur tout temps strictement positif.
          - [x] Remplacer l'itération ordre par ordre par une absorption
            gaussienne inductive valable pour toute puissance spectrale,
            justifier toutes les dérivations sous la somme, prouver
            l'alternance des signes et la covariance PT à tout ordre, puis
            certifier `C∞` de la trace nucléaire sur `t > 0`.
            - [x] Identifier ces sommes dérivées aux `iteratedDeriv` réelles,
              empaqueter la monotonie complète sur `t > 0` et en déduire
              honnêtement que la trace nucléaire est globalement décroissante
              et convexe sur tout l'intervalle positif.
    - [x] Prouver que toute multiplicité interne naturelle finie préserve
      l'expansion nucléaire concrète du cercle : sommabilité des composantes
      et de leurs normes, somme opérateur égale au multiple fini exact du
      semi-groupe, trace multipliée et covariance PT conservée. Cette étape ne
      construit pas encore l'opérateur Janus global.
      - [x] Remplacer le facteur formel par le véritable produit hilbertien sur
        un type interne fini : construire l'opérateur chaleur diagonal, ses
        composantes rang-un indexées par composante interne et mode Fourier,
        prouver leur sommabilité en norme et l'égalité de leur somme avec
        l'opérateur produit, puis identifier la trace à la dimension interne
        fois la trace du cercle avec covariance PT.
        - [x] Autoriser un fold et un twist distincts sur chaque composante
          interne finie, construire le vrai opérateur bloc-diagonal et son
          expansion nucléaire hétérogène, puis prouver que le renversement PT
          simultané de tous les folds conserve la trace nucléaire totale.
          - [x] Prouver pour cette famille hétérogène la continuité de la trace
            totale sur chaque demi-droite positive, sa dérivabilité terme à
            terme, l'identification et la continuité de la dérivée, son signe
            non positif et la covariance PT simultanée de la trace et de sa
            dérivée.
    - [x] Combiner la série infinie monopolaire déjà convergente sur `S²` avec
      l'expansion nucléaire du cercle : prouver la sommabilité absolue de la
      série produit sur `ℕ × ℤ`, factoriser exactement la trace du throat
      `S² × S¹`, établir sa positivité et sa covariance PT. Le passage au vrai
      opérateur Janus 4D global reste ouvert.
      - [x] Construire le véritable Hilbert spectral `ℓ²` conservant chaque
        niveau monopolaire, sa multiplicité exacte et chaque mode Fourier,
        puis construire l'opérateur chaleur diagonal contractif et identifier
        sa trace sommable à la trace nucléaire produit précédente.
      - [x] Construire la base hilbertienne de ce même espace, les projections
        spectrales rang-un, prouver la sommabilité de leurs normes et l'égalité
        en norme d'opérateur de leur somme avec l'opérateur chaleur ; empaqueter
        le certificat nucléaire avec l'égalité de trace.
      - [x] Étendre la régularité temporelle à la vraie série double du throat
        produit `ℕ × ℤ` : identifier l'énergie totale sphère+cercle, absorber
        toute puissance spectrale, dériver terme à terme à tout ordre, prouver
        `C∞`, monotonie complète et covariance PT de chaque dérivée.
        - [x] Étendre aussi l'expansion rang-un du véritable opérateur chaleur
          produit à tout temps réel : sommer uniformément en norme opérateur
          chaque ordre spectral sur les demi-droites positives, dériver la
          série terme à terme, certifier la famille `C∞` sur `t > 0` et
          identifier exactement son ordre zéro à l'opérateur chaleur existant ;
          à tout ordre, la somme diagonale sur les labels de dégénérescence est
          exactement la dérivée nucléaire correspondante et conserve PT.
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
  - [x] Pour le Dirac spectral non borné du throat produit à fold et holonomie
    fixés, exploiter le gap sphérique strict pour construire son inverse
    spectral borné, prouver injectivité, surjectivité, noyau nul, image totale
    fermée, critère de Fredholm et indice zéro. La dépendance lisse en
    paramètres et le Dirac géométrique Janus global restent ouverts.
    Preuve de portée : `P0EFTJanusProductThroatDiracSignScope4D` montre que la
    racine positive signée garde strictement le signe du fold pour tous les
    modes ; elle n'a donc aucun crossing de signe interne à fold fixé. Elle ne
    réalise pas, à elle seule, le vrai Dirac géométrique signé.
    - [x] À géométrie produit et fold fixés, représenter la valeur propre par
      un vecteur spectral complexe, en déduire la borne 1-Lipschitz exacte en
      holonomie, construire la perturbation diagonale bornée et prouver que
      toutes les holonomies ont exactement le même domaine maximal. La
      différentiabilité de la famille et l'espace global de paramètres Janus
      restent ouverts.
      - [x] Prolonger l'holonomie à un paramètre réel, prouver que chaque
        valeur propre produit dépend `C∞` de ce paramètre, calculer sa dérivée
        exacte, borner uniformément sa valeur absolue par `1` et construire le
        multiplicateur dérivé borné de norme au plus `1` sur le Hilbert
        spectral. La différentiabilité en norme d'opérateur sur le domaine de
        graphe et la famille Janus géométrique restent ouvertes.
        - [x] Calculer la seconde dérivée spectrale exacte, la borner
          uniformément par l'inverse du gap sphérique, appliquer le théorème
          des accroissements finis et prouver que la famille des opérateurs
          dérivés est Lipschitz en norme d'opérateur avec cette constante.
          - [x] Calculer la troisième dérivée spectrale exacte, la borner par
            `3 gap⁻²`, rendre la seconde dérivée scalaire Lipschitz et
            construire son multiplicateur diagonal borné de norme au plus
            `gap⁻¹`; un reste de Taylor quadratique uniforme prouve que ce
            multiplicateur est exactement la dérivée en norme d'opérateur de
            la première famille.
          - [x] Construire la perturbation diagonale bornée relativement à une
            holonomie de référence, établir un reste de Taylor quadratique
            uniforme et en déduire sa dérivabilité en norme d'opérateur, avec
            pour dérivée le multiplicateur spectral explicite. Le passage à
            la famille Janus géométrique globale reste ouvert.
            - [x] Munir le graphe fermé à une holonomie de référence de sa
              norme complète, y réaliser toute la famille réelle sur un même
              domaine, transporter le reste de Taylor et prouver que cette
              famille est `C¹` en norme d'opérateur avec dérivée Lipschitz.
              La variation de la géométrie produit reste ouverte.
              - [x] Transporter aussi le multiplicateur de seconde dérivée au
                graphe commun, établir son contrôle Lipschitz et le reste de
                Taylor de la première dérivée, puis certifier honnêtement la
                régularité `C²` de la famille réelle en holonomie.
                La quatrième dérivée scalaire est maintenant explicite et
                bornée par `15 gap⁻³`; le troisième multiplicateur borné, son
                reste de Taylor et son transport au graphe commun renforcent
                cette même famille en `C³`.
              - [x] Identifier chaque fibre d'holonomie admissible au vrai
                Dirac maximal après rebasing canonique du domaine, puis
                transporter le gap strict pour prouver bijectivité, noyau nul,
                image totale fermée, critère de Fredholm et indice zéro sur le
                domaine de graphe commun.
                - [x] Étendre le gap et l'inverse spectral à toute holonomie
                  réelle, placer cet inverse dans le domaine de référence et
                  construire l'équivalence linéaire continue inverse de chaque
                  fibre réelle ; l'indice reste identiquement nul sur `ℝ`.
                  - [x] Identifier l'inverse borné de chaque fibre à la
                    symétrique de cette équivalence et prouver la continuité
                    globale de la famille inverse en norme d'opérateur. La
                    variation géométrique produit reste ouverte.
                    - [x] En déduire que la norme de la famille inverse est
                      uniformément bornée sur un voisinage de chaque holonomie
                      réelle.
                      - [x] Restreindre au corps réel la régularité complexe de
                        l'application d'inversion et prouver que la famille
                        inverse canonique est `C¹` en norme d'opérateur. La
                        restriction des séries de Taylor complexes au corps
                        réel et la régularité `C³` du graphe direct renforcent
                        désormais cette famille inverse en `C³`.
                        - [x] Construire la dérivée de Fréchet complexe exacte
                          de l'opération d'inversion entre les deux espaces
                          d'opérateurs, la transporter honnêtement aux structures
                          réelles canoniques et fermer le chaînage holonomique
                          explicite `d(A⁻¹)/dh = -A⁻¹ A'(h) A⁻¹`; cette
                          famille dérivée explicite est continue en norme
                          d'opérateur, localement uniformément bornée, tandis
                          que `‖A'(h)‖ ≤ 1`; elle recertifie directement la
                          régularité `C¹`.
                          - [x] Consolider le modèle à géométrie produit fixe en
                            un certificat Fredholm `C³` unique : domaine de
                            graphe commun, familles directe et inverse `C³`,
                            lois d'inverse bilatères et indice nul pour toute
                            holonomie réelle. L'inversion est en outre fermée
                            uniformément à tout ordre : toute promotion `C∞` de
                            la famille directe promeut automatiquement son
                            inverse canonique en `C∞` réel. Pour la famille
                            directe, une boule analytique uniforme de rayon
                            `gap/4` est maintenant prouvée : l'incrément carré
                            relatif est factorisé exactement, borné indépendamment
                            du mode et strictement dans le disque binomial unité.
                            - [x] Sommer effectivement la série binomiale de
                              racine dans la norme des opérateurs diagonaux sur
                              le Hilbert produit et identifier sa somme, mode par
                              mode, à la racine carrée positive exacte.
  - [ ] Passer à l'opérateur Janus global non borné, avec domaine commun et
    dépendance lisse sur le vrai espace de paramètres.
- [ ] Relier cette famille au Hessien naturel de l'action Programme P.
  - [x] À géométrie produit, fold et holonomie fixés, restreindre la fibre
    Dirac Fredholm au même domaine de graphe commun réel, dériver sa symétrie
    de l'auto-adjonction formelle, construire son action quadratique canonique
    et prouver que son pairing est exactement la vraie seconde dérivée de
    Fréchet de cette même action ; la fibre est simultanément bijective et
    d'indice zéro. Cette action spectrale propre à la fibre n'est pas l'action
    naturelle globale Programme P et ne varie ni géométrie ni bord.
  - [x] Sur la somme directe bosonique réduite bulk scalaire + jonction Robin
    + LL PT-symétrique, assembler l'opérateur de Jacobi bloc-diagonal, prouver
    que son pairing est exactement la somme des trois Hessians naturels,
    établir symétrie, bijectivité, noyau nul, image totale fermée et indice
    zéro. Les blocs métrique, jauge, ghosts et la famille paramétrique restent
    ouverts.
    - [x] Sur les trois secteurs lisses, définir par `deriv` les premières puis
      secondes variations effectives des actions scalaire globale D8, jonction
      Robin et LL PT-symétrique inchangées, puis identifier exactement chaque
      bloc du pairing Fredholm réduit à ces Hessians d'actions. Aucun bloc
      métrique, jauge, ghost ni Hessien Candidate-A complet n'est revendiqué.
      - [x] Assembler ces trois termes en une seule action bosonique réduite,
        dériver simultanément ses trois champs le long de courbes affines et
        prouver que le pairing Fredholm sur le secteur lisse dense est
        exactement son Hessien mixte effectif. Cette action réduite n'est pas
        l'action Programme P complète.
        - [x] En faisant varier uniquement le couplage Robin `kPlus` sur les
          mêmes espaces réduits fixés, construire une famille `C∞` en norme
          d'opérateur, prouver bijectivité, image fermée et indice algébrique
          nul lorsque `kPlus + kMinus ≠ 0`, puis identifier le pairing de chaque
          membre au Hessien mixte de la même action réduite au même couplage.
          Ce n'est ni la famille naturelle globale, ni une variation de la
          géométrie, des domaines, de la jauge ou des ghosts.
        - [x] Injecter exactement le champ LL stocké dans son domaine lisse
          `LLH¹`, puis prouver que la diagonale du pairing Fredholm réduit
          reconstruit cette même action assemblée, après ajout des seuls termes
          constant et linéaire Robin requis. Cette identité reste limitée au
          secteur lisse diagonal du modèle bosonique réduit.
          - [x] Sur le seul bloc LL lisse dense, injecter fidèlement `LLH¹` dans
            le vrai `ProgramPCompleteVariation4D`, puis identifier exactement le
            pairing Fredholm réduit au Hessien LL de la même action et à sa
            seconde variation effective sur ce tangent. Le corollaire
            matière+LL utilise une direction matière nulle; les directions
            scalaire et Robin réduites sont nulles, et aucun bloc EH, Maxwell ou
            ghost n'est ajouté.
          - [x] Étendre minimalement ce vrai tangent par un slot Robin lisse,
            y transporter le domaine de bord actuel et la même action avec son
            Euler et son Hessien matière+Robin+LL, puis identifier sur la
            projection lisse Robin+LL son pairing au Fredholm réduit. Le scalaire
            réduit est nul et les blocs EH, Maxwell, ghost et bulk auxiliaire
            restent absents.
            - [x] Placer les ghosts linéaires appariés `U(1)²` et
              difféomorphisme dans ce même wrapper Robin-complet, prouver que
              la projection, le vecteur et le pairing Fredholm réduits sont
              invariants sous leur différentielle BRST, puis identifier le
              Hessien réduit après `Q` au pairing Fredholm avant `Q`. Cette
              invariance vient exactement de la projection qui élimine les
              ghosts : aucun bloc Fredholm ghost ni BRST non linéaire global
              n'est construit.
    - [x] Munir cette somme réduite de la vraie structure hilbertienne ℓ² via
      `WithLp`, transporter l'opérateur bloc et prouver son auto-adjonction
      effective, tout en conservant pairing Hessien, bijectivité, image fermée
      et indice zéro.
- [ ] Instancier le complexe D9/BRST avec les vrais champs, ghosts, symboles,
  domaines et cohomologie de modes zéro.
  - [x] Identifier canoniquement la fibre matière réelle de rang quatre de D9
    à la fibre de coordonnées réelle du spinor carré D11, et remplir ainsi le
    résidu du record de champ local. Cette fermeture est au niveau des
    coordonnées ; elle ne construit pas un bundle SpinC géométrique.
  - [x] Ajouter six coefficients métriques symétriques locaux indépendants,
    prouver leur projection surjective sur toutes les perturbations métriques
    D9 et assembler le champ local complet à données non métriques fixées.
    Ces coefficients ponctuels ne sont pas encore un tangent de l'action
    globale Programme P.
  - [x] Relier ces six coefficients à un vrai tenseur covariant symétrique
    lisse via un chart holonome fourni, prouver leur régularité `ContDiff` et
    leur projection exacte dans le slot métrique D9 au point compatible du
    throat. Le chart et l'égalité coordonnée/inclusion restent des hypothèses,
    et ce tenseur n'est pas encore un tangent de l'action globale Programme P.
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
  - [x] Pour le seul sous-complexe abélien temporel finite-mode, insérer le
    doublet de vrais ghosts lisses des secteurs plus/minus dans le bloc BRST/D9
    commun, identifier sa différentielle à la paire des vrais potentiels
    exacts `dc`, puis prouver que son noyau est exactement la paire des modes
    constants et que la coordonnée ghost D9 s'annule après une étape. Les
    domaines Sobolev, le ghost difféomorphe et la cohomologie globale restent
    ouverts.
    - [x] Sans troncature temporelle, sur la paire entière de ghosts abéliens
      lisses globaux du vrai quotient D8, prouver que les deux sorties
      potentielles du bloc BRST/D9 commun s'annulent exactement pour deux
      ghosts constants, et identifier linéairement ce noyau restreint à
      `ℝ² × ℝ²`. Ce
      résultat n'est ni le noyau du BRST complet, ni sa cohomologie Sobolev.
      Preuve d'appui :
      `P0EFTJanusCommonPairedD9LinearBRSTKernel4D` classe maintenant le noyau
      du bloc linéaire entier : les deux ghosts abéliens sont constants,
      tandis que les potentiels d'entrée et le ghost difféomorphe restent
      libres. Cela ne constitue toujours pas une cohomologie BRST complète.
- [ ] Fixer un régulateur commun à tous les secteurs physiques et ghosts.
  - [x] Au seul cutoff temporel fini, réaliser chaque mode non nul comme un
    vrai ghost lisse `U(1)^2` dans le même wrapper matière + Robin + LL,
    identifier son image BRST à `dc`, puis prendre comme valeur propre du
    régulateur la norme carrée du même multiplicateur Fourier et prouver son
    invariance PT. La chiralité reste une donnée explicite ; aucun domaine
    ghost complété, cutoff continuum ni calcul d'anomalie n'est affirmé.
- [ ] Insérer les multiplicités, statistiques et signes de tous les champs dans
  les coefficients de chaleur et le déterminant.
  - [x] Au cutoff D10 fini, coder les multiplicités et signes bosoniques,
    fermioniques et ghosts dans la trace thermique, utiliser un unique temps
    de chaleur pour toute liste finie de secteurs, et prouver que
    l'annulation chirale PT du vrai spectre D10 tronqué survit à ces poids.
    Aucun spectre ghost global ni passage à la limite du cutoff n'est revendiqué.
    - [x] Pondérer aussi le déterminant au cutoff par la multiplicité et la
      statistique (puissance bosonique, puissance réciproque fermionique/ghost),
      puis prouver additivité des multiplicités, invariance PT et non-annulation
      sur le disque déjà contrôlé. Cette convention finite-mode n'introduit ni
      demi-puissance gaussienne, ni limite, ni ligne de Quillen globale.
      Preuve d'appui spectrale :
      `P0EFTJanusFiniteModeSpectralStatisticalDeterminant4D` remplace le facteur
      de cutoff abstrait par le produit effectif des `shift + eigenvalueSq`,
      conserve les poids statistiques et prouve la multiplicativité des listes.
      Le témoin à un mode change effectivement avec la valeur propre ; aucune
      limite infinite-mode ni ligne de Quillen n'est obtenue.
    - [x] Pour une liste finie de secteurs partageant un même type de modes,
      prouver l'additivité exacte de la trace thermique commune sous
      concaténation et l'annulation de la somme des traces chirales PT signées,
      au même temps de régulation. Les types de modes différents et la limite
      globale restent hors de cette fermeture finite-mode.
      - [x] Construire le produit fini des déterminants statistiques à cutoff
        commun et prouver sa multiplicativité sous concaténation, son invariance
        PT et sa non-annulation sur le disque contrôlé. Le type de modes et le
        cutoff restent fixés ; aucun déterminant global n'est revendiqué.
    - [x] Permettre une liste finite-mode hétérogène en conservant pour chaque
      secteur son vrai type fini et ses vraies données pondérées, puis recalculer
      toutes les traces au même temps : la trace thermique est additive et la
      somme chirale PT est nulle. Aucun certificat `Prop` ne remplace les données.
      - [x] Construire aussi le produit des déterminants statistiques de cette
        liste hétérogène à cutoff et holonomie communs, avec multiplicativité,
        invariance PT et non-annulation sur le disque contrôlé. Aucun passage
        au cutoff infini n'est effectué.
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
    - [x] Construire le vrai quotient d'orbites de `ℝ × ℂ`, puis donner
      l'isomorphisme topologique au fibré descendu, compatible à la projection
      et complexe-linéaire sur chaque fibre.
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
  - [x] Dans le représentant cercle/zero-mode, identifier exactement le saut
    eta de grande jauge unité à `-2` fois le flux spectral unité, sa réduction
    modulo deux et l'annulation des deux sauts reliés par PT. Ce pont reste
    limité au cercle : il ne construit ni théorème APS, ni indice familial, ni
    classe d'inflow globale.
    - [x] Relier ce flux abstrait au crossing orienté déjà calculé pour la vraie
      famille bornée du cercle : le saut eta vaut `-2` fois l'incrément spectral
      affine exact de chaque mode, et les deux folds primitifs PT s'annulent.
      Cette identification reste propre au cercle normalisé.
    - [x] Construire l'eta thermique sectoriel du cercle à temps strictement
      positif comme la série effective `Σₙ λₙ exp(-t λₙ²)`, prouver sa
      sommabilité absolue, son oddité PT et le relabeling de grande jauge entre
      les deux extrémités. Aucun invariant APS, passage `t → 0`, eta global ou
      inflow géométrique n'en découle.
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
