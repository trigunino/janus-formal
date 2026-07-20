# Programme P — TODO opérationnelle distribuable aux LLM

Date de référence : 2026-07-19.

## 1. Rôle de ce document

Ce fichier est la file de travail courte de Programme P. Le registre détaillé
`docs/program_p_exhaustive_todo.md` reste le journal historique des preuves et
des sous-résultats.

État vérifié du registre historique : **1132/1238**, soit **91,44 %**, avec
**106 cases ouvertes**. Ce pourcentage n'est plus utilisé comme mesure de
fermeture globale : le nombre de cases ouvertes n'a pas diminué pendant
l'ajout de centaines de microlemmes.

La fermeture globale est mesurée uniquement par les **14 portes terminales**
de la section 7. État actuel : **0/14**. Une preuve locale, pointwise,
finite-mode, réduite ou conditionnelle ne ferme jamais une porte globale.

En cas de contradiction entre prose et code, le type exact du théorème Lean
compilé fait autorité.

## 2. Consigne à donner à chaque LLM

Copier ce bloc avec l'identifiant d'une seule carte :

> Travaille dans `C:\Users\alzie\Documents\Janus` sur la carte `<ID>` de
> `docs/program_p_operational_todo.md`. Ne traite aucune autre carte. Cherche
> d'abord dans tout le dépôt avec `rg`, puis lis uniquement les modules cités
> et leurs dépendances directes. Réutilise les théorèmes existants. Crée au
> plus un petit gate Lean, compile-le immédiatement, puis intègre-le seulement
> s'il compile. Aucun Git, `sorry`, `axiom`, `admit`, placeholder, certificat
> par simples champs `Prop`, ni hypothèse contenant la conclusion recherchée.
> Ne transforme jamais un résultat local, réduit, finite-mode, produit ou
> conditionnel en résultat global. Utilise `apply_patch` pour toute édition.
> Supprime les fichiers temporaires. Dans ton bilan, donne : énoncé réellement
> prouvé, portée, fichiers modifiés, commandes/tests, et porte terminale fermée
> — ou écris explicitement « aucune ».

Coordination dans un workspace partagé :

- plusieurs agents peuvent travailler en parallèle sur des gates distincts ;
- un seul intégrateur à la fois modifie la façade, l'audit et les deux TODO ;
- un agent ne coche jamais une carte qu'il n'a pas lui-même compilée ;
- les lemmes intermédiaires sont inscrits comme preuves d'appui sous la carte,
  sans créer de nouvelle unité de progression.

Première vague possible pour dix LLM : attribuer les dix cartes de la section
4, une par agent. Chaque agent construit et compile uniquement son gate ; un
coordinateur intègre ensuite les gates verts, un par un, dans la façade et
l'audit. Les cartes de la section 5 viennent seulement après cette vague ou
après satisfaction de leur dépendance explicite.

## 3. Portées et validation

Portées autorisées : `GLOBAL`, `SECTORIEL`, `RÉDUIT`, `FINITE-MODE`,
`POINTWISE`, `CONDITIONNEL`, `DOCUMENTAIRE`.

États autorisés : `READY`, `DÉPENDANCE`, `BLOQUÉ-PHYSIQUE`, `DONE`.

Une carte Lean est `DONE` seulement si :

1. le théorème prouve exactement le résultat annoncé avec sa portée dans le
   type ou dans le nom ;
2. ses hypothèses sont mathématiques et ne reformulent pas la conclusion ;
3. le gate focalisé compile ;
4. le gate est importé par la façade Programme P ;
5. l'audit contrôle le module et le théorème exacts ;
6. la façade compile et l'audit est vert ;
7. `#print axioms` ne révèle aucun axiome métier ajouté ;
8. aucun fichier temporaire ou module non compilé ne reste.

Commandes finales obligatoires :

```powershell
lake build <Nom.Du.Module>
lake env lean JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean
C:\Users\alzie\AppData\Local\Programs\Python\Python314\python.exe scripts/audit_janus_program_p.py
```

## 4. Cartes petites et parallélisables

Ces cartes produisent des ponts utiles, mais ne ferment une porte terminale
que si leur critère le dit explicitement.

### `P-CV-MODULE-01` — Noyau linéaire du tangent commun

- État : `DONE`. Portée : `GLOBAL`, algébrique.
- But : donner à `ProgramPCompleteVariation4D` ses structures
  `AddCommGroup`/`Module ℝ`, rendre `independentCompleteVariation` linéaire et
  prouver la linéarité de `normalModeAt`, `diffeomorphismGhostAt` et
  `metricPerturbationAt`.
- Départ : `P0EFTJanusProgramPCommonGeometricDomain4D`,
  `P0EFTJanusIndependentCompleteVariationEmbedding4D`.
- Gate proposé : `P0EFTJanusCompleteVariationModuleCore4D`.
- Acceptation : aucune hypothèse physique nouvelle ; seulement le noyau
  linéaire nécessaire aux Hessians/BRST communs.
- Porte terminale : aucune.
- Preuve d'appui : `P0EFTJanusCompleteVariationModuleCore4D` munit
  `ProgramPCompleteVariation4D` d'un `AddCommGroup` et d'un `Module ℝ`,
  empaquette `independentCompleteVariation` en application linéaire et prouve
  l'additivité/homogénéité des trois lectures locales annoncées.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucune porte
  terminale fermée.

### `P-INTRINSIC-ROOT-01` — Racine Candidate A conforme intrinsèque

- État : `DONE`. Portée : `SECTORIEL`, globale sur D8.
- But : pour `g₊ = a g₀`, `g₋ = b g₀`, avec `a,b>0` lisses, construire deux
  vrais `SmoothGeneralLorentzMetric`, l'endomorphisme relatif `(b/a) id`, sa
  racine `sqrt (b/a) id` et la densité Candidate A ; prouver l'accord dans tout
  repère avec la spécialisation isotrope du modèle `Matrix4`.
- Départ : `P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D`,
  `P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D`,
  `P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D`.
- Gate proposé : `P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D`.
- Acceptation : aucun frame global supposé ; ne revendique pas deux métriques
  générales.
- Porte terminale : aucune.
- Preuve d'appui : `P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D`
  construit `a g₀` et `b g₀` comme deux vrais
  `SmoothGeneralLorentzMetric`, identifie intrinsèquement `g₊⁻¹g₋` à
  `(b/a) id`, prouve le carré de `sqrt (b/a) id` et l'accord de la densité
  Candidate A, dans toute frame tangentielle, avec le potentiel `Matrix4`
  isotrope.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucune frame
  globale supposée et aucune porte terminale fermée.

### `P-H1-FRAME-01` — Indépendance du graphe H¹ par changement de frame

- État : `DONE`. Portée : `GLOBAL`, analytique.
- But : comparer deux familles tangentielles lisses finies génératrices,
  prouver l'équivalence des normes de graphe et des complétés, puis instancier
  le passage frame canonique ↔ atlas fixe.
- Départ : `P0EFTJanusMappingTorusH1GraphTrace4D`,
  `P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D`,
  `P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D`.
- Gate proposé : `P0EFTJanusMappingTorusH1FrameIndependence4D`.
- Acceptation : coefficients de changement de frame lisses et uniformément
  bornés sur un recouvrement fini compact.
- Porte terminale : aucune.
- Preuve d'appui : `P0EFTJanusMappingTorusH1FrameIndependence4D` compare les
  jets et leurs normes `L²` sous des changements bidirectionnels lisses,
  uniformément bornés sur un recouvrement compact fini, étend l'identité des
  champs lisses en équivalence continue des complétés et identifie la frame
  physique finie aux composantes localisées de l'atlas fixe, avec domination
  de densité dans les deux sens.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucune porte
  terminale fermée.

### `P4-H1-GRAPH-CLOSURE` — Cœur lisse du secteur temporel H¹

- État : `DONE`. Portée : `SECTORIEL`, spatialement constant.
- But : prouver que les modes temporels à support fini sont denses pour le
  graphe `(temporalH1FieldL2, temporalH1DerivativeL2)` et que la dérivée
  synthétisée coïncide sur ce cœur avec la vraie dérivée temporelle de `dc`.
- Départ : `P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D`,
  `P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D`.
- Gate proposé : `P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D`.
- Acceptation : ne pas appeler ce résultat « complexe Sobolev global ».
- Porte terminale : aucune.
- Preuve d'appui :
  `P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D` construit
  l'inclusion pondérée des coefficients `Finsupp`, prouve sa densité dans le
  graphe complété `(temporalH1FieldL2, temporalH1DerivativeL2)` et identifie,
  sur ce cœur, la dérivée synthétisée à la vraie dérivée `mvfderiv` le long de
  la translation temporelle ainsi qu'à la composante temporelle de `dc`.
- Validation : gate, façade et audit compilés le 2026-07-19 ; résultat limité
  au secteur temporel spatialement constant, aucune porte terminale fermée.

### `P-GHY-THROAT-01` — Gorge canonique dans le modèle Gaussian-normal

- État : `DONE`. Portée : `SECTORIEL`, géométrie locale du throat.
- But : identifier le collier de latitude aux données Gaussian-normal réelles,
  prouver `∂ₙh|₀ = 0`, donc l'annulation de la seconde forme fondamentale et de
  sa trace, avec les signes opposés des deux lifts.
- Départ : `P0EFTJanusGaussianNormalEmbeddedHypersurface`,
  `P0EFTJanusGaussianNormalEHGHYCancellation` et les gates du collier canonique.
- Gate proposé : `P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D`.
- Acceptation : prélude local seulement ; ne ferme ni EH ni GHY global.
- Porte terminale : aucune.
- Preuve d'appui :
  `P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D` identifie le
  1-jet du collier réel `cos(n)²` au modèle Gaussian-normal spacelike, prouve
  `∂ₙh|₀ = 0`, l'annulation de la seconde forme fondamentale et de sa trace,
  ainsi que l'opposition des lifts normaux sous le deck ; le normal réel a
  carré lorentzien `+1`.
- Validation : gate, façade et audit compilés le 2026-07-19 ; prélude local
  seulement, aucune fermeture EH/GHY globale et aucune porte terminale fermée.

### `P-LL-INTRINSIC-01` — Première action LL à contraction métrique réelle

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, vrai throat.
- But : remplacer le poids auxiliaire `1+‖llAuxMetric‖²` par la contraction via
  l'inverse d'une `SmoothNondegenerateThroatMetric`, puis dériver action,
  première variation, Hessien symétrique et covariance PT canonique.
- Départ : `P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D`,
  `P0EFTJanusMappingTorusDifferentialLLWeakEquation4D`.
- Gate proposé : `P0EFTJanusMappingTorusIntrinsicLLKineticAction4D`.
- Acceptation : aucune positivité lorentzienne ou PDE forte non prouvée.
- Porte terminale : aucune.
- Appui : `P0EFTJanusMappingTorusIntrinsicLLKineticAction4D` contracte les
  quatre différentielles LL par le vrai inverse musical de la métrique
  intrinsèque non dégénérée ; l'expansion quadratique donne la première
  variation et un Hessien symétrique, sans assertion de positivité.
- Validation : gate, façade et audit compilés le 2026-07-19 ; l'action
  canonique est PT-invariante via la vraie règle de chaîne et la mesure du
  throat. L'intégrabilité n'est supposée qu'au théorème de différentiation
  globale ; aucune PDE forte ni porte terminale n'est fermée.

### `P5-MATTER-ARBITRARY-DIFFEO-NOETHER` — Courbes difféomorphes arbitraires

- État : `DONE` (2026-07-20). Portée : `GLOBAL`, bloc matière huit scalaires.
- But : remplacer la seule orbite de translation temporelle par toute courbe
  `Real → SpacetimeDiffeomorphism`.
- Gate : `P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D`.
- Acceptation : l'orbite de l'action covariante est exactement constante ; sa
  dérivée est nulle en tout paramètre, sans hypothèse de régularité sur la
  courbe.
- Limite : aucun adjoint d'Euler, courant local, bloc EH, Maxwell, ghost ou
  bord ; aucune porte terminale fermée.

### `P5-MATTER-MASS-SIGN-NOGO` — Obstruction formelle de signe massif

- État : `DONE` (2026-07-20). Portée : `SECTORIELLE`, densité scalaire.
- But : formaliser le blocage du pont entre les deux actions matière.
- Gate : `P0EFTJanusMappingTorusMatterActionMassSignObstruction4D`.
- Acceptation : après identification explicite du volume et du terme cinétique,
  la différence des densités vaut exactement `volume * mass² * field²` ; leur
  égalité équivaut à l'annulation de ce terme, et échoue lorsque ses facteurs
  sont non nuls.
- Limite : ne choisit ni ne propage une convention physique commune.
- Porte terminale : aucune.

### `P5-MATTER-MASS-SIGN-INTEGRATED-NOGO` — Obstruction intégrée

- État : `DONE` (2026-07-20). Portée : `GLOBAL`, secteur scalaire.
- But : promouvoir le défaut ponctuel au niveau des deux actions globales.
- Gate : `P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D`.
- Acceptation : sous pont volume/cinétique et intégrabilité explicite, la
  différence des actions est l'intégrale exacte du défaut massif ; l'égalité
  équivaut à l'annulation de cette intégrale.
- Limite : ne résout pas le choix de signe ni le pont métrique diagonal.
- Porte terminale : aucune.

### `P5-MATTER-MULTIPLET-MASS-SIGN-NOGO` — Obstruction des huit champs

- État : `DONE` (2026-07-20). Portée : `GLOBAL`, multiplet matière.
- But : relier directement l'action Euler des huit champs à l'action Noether.
- Gate : `P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D`.
- Acceptation : sous ponts masse, mesure, volume et cinétique explicites pour
  chaque composante, la différence des actions est exactement la somme des
  huit défauts massifs intégrés ; leur égalité équivaut à l'annulation de cette
  somme.
- Limite : le choix de signe et la réalisation des ponts restent ouverts.
- Porte terminale : aucune.

### `P5-MATTER-MASS-SIGN-NO-CANCELLATION` — Absence de compensation

- État : `DONE` (2026-07-20). Portée : `GLOBAL`, multiplet matière.
- But : exclure une annulation artificielle entre les huit défauts massifs.
- Gate : `P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D`.
- Acceptation : pour des masses carrées non négatives, chaque défaut intégré
  est non négatif et leur somme est nulle si et seulement si chaque terme est
  nul ; un seul terme non nul rend le défaut total non nul.
- Limite : ne prouve pas encore qu'un champ massif non nul donne une intégrale
  strictement positive sans hypothèses de mesure supplémentaires.
- Porte terminale : aucune.

### `P5-MATTER-MASS-SIGN-AE-ZERO` — Critère presque-partout

- État : `DONE` (2026-07-20). Portée : `GLOBAL`, secteur scalaire mesuré.
- But : caractériser exactement quand un défaut massif intégré peut s'annuler.
- Gate : `P0EFTJanusMappingTorusMatterMassSignDefectAEZero4D`.
- Acceptation : sous masse strictement positive, volume strictement positif
  presque partout et intégrabilité, l'intégrale du défaut est nulle si et
  seulement si le champ est nul presque partout ; sinon elle est strictement
  positive.
- Limite : hypothèses de positivité/integrabilité explicites, non déchargées
  ici pour chaque donnée Candidate A.
- Porte terminale : aucune.

### `P5-MATTER-MASSIVE-FIELD-NOGO` — Témoin massif non nul

- État : `DONE` (2026-07-20). Portée : `GLOBAL`, multiplet matière.
- But : propager un témoin physique d'une composante jusqu'aux deux actions.
- Gate : `P0EFTJanusMappingTorusMatterMultipletMassiveFieldNoGo4D`.
- Acceptation : sous les ponts proposés, une composante de masse strictement
  positive et non nulle presque partout, avec volume positif presque partout
  et défaut intégrable, implique que `globalMatterMultipletAction` diffère de
  `sameConfigurationGeneralLorentzMatterAction`.
- Limite : confirme le no-go de la convention actuelle ; ne choisit pas le
  signe physique de remplacement.
- Porte terminale : aucune.

### `P5-HOLONOMIC-COORD-EQUIV` — Coordonnées holonomiques continues

- État : `DONE` (2026-07-20). Portée : `RÉDUIT`, espace tangent modèle.
- Gate : `P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D`.
- Résultat : les quatre vecteurs `tangentCoordinate` et les coefficients
  `holonomicVectorCoefficient` forment deux applications linéaires inverses,
  promues en une équivalence linéaire continue exacte.
- Limite : donnée de l'espace modèle ; aucun repère tangent global lisse sur
  le mapping torus n'est affirmé.
- Porte terminale : aucune.

### `P5-HOLONOMIC-DIAGONAL-SHARP` — Inverse diagonal exact

- État : `DONE` (2026-07-20). Portée : `RÉDUIT`, espace tangent modèle.
- Gate : `P0EFTJanusMappingTorusHolonomicDiagonalSharp4D`.
- Résultat : construction explicite du sharp diagonal, preuve qu'il inverse
  le pairing covariant pour toute magnitude non nulle, et identification du
  terme cinétique global à sa contraction dès qu'un covecteur modèle porte
  les composantes de la vraie différentielle holonomique.
- Limite : ne fournit pas la descente tensorielle lisse globale.
- Porte terminale : aucune.

### `P5-HOLONOMIC-DIAGONAL-MUSICAL` — Musical diagonal continu

- État : `DONE` (2026-07-20). Portée : `RÉDUIT`, espace tangent modèle.
- Gate : `P0EFTJanusMappingTorusHolonomicDiagonalMusical4D`.
- Résultat : le pairing diagonal exact définit un flat continu bijectif pour
  toute magnitude sans composante nulle, donc une équivalence linéaire
  continue entre l'espace tangent modèle et son dual ; la surjectivité utilise
  le sharp explicite de la carte précédente.
- Limite : aucun champ tensoriel global lisse n'est construit.
- Porte terminale : aucune.

### `P5-HOLONOMIC-DIAGONAL-LORENTZ-FRAME` — Inertie lorentzienne exacte

- État : `DONE` (2026-07-20). Portée : `RÉDUIT`, espace tangent modèle.
- Gate : `P0EFTJanusMappingTorusHolonomicDiagonalLorentzFrame4D`.
- Résultat : pour toute magnitude strictement positive, le changement de
  frame continu qui multiplie chaque coordonnée holonomique par sa racine
  carrée identifie exactement le pairing diagonal à `modelMinkowskiPair` ;
  son inertie `(3,1)` est donc certifiée dans la convention temps-premier.
- Limite : frame du seul espace tangent modèle, non section globale lisse.
- Porte terminale : aucune.

### `P5-HOLONOMIC-DIAGONAL-VOLUME` — Pont exact du volume

- État : `DONE` (2026-07-20). Portée : `RÉDUIT`, espace tangent modèle.
- Gate : `P0EFTJanusMappingTorusHolonomicDiagonalVolumeBridge4D`.
- Résultat : la matrice de Gram du pairing dans la base holonomique est
  exactement `lorentzMetric`; pour toute magnitude positive, sa densité
  `sqrt |det|` est exactement `diagonalMetricVolumeDensity`.
- Limite : identité du modèle diagonal, avant descente tensorielle globale.
- Porte terminale : aucune.

### `P5-HOLONOMIC-LOCAL-LORENTZ-METRIC` — Réalisation locale intrinsèque

- État : `DONE` (2026-07-20). Portée : `SECTORIEL`, patches tangents D8.
- Gate : `P0EFTJanusMappingTorusLocalHolonomicDiagonalLorentzMetric4D`.
- Résultat : sur chaque domaine de trivialisation tangent canonique, le
  musical holonomique est tiré vers la vraie fibre tangente ; le tenseur local
  résultant est inversible et lorentzien `(3,1)` avec frame explicite.
- Limite : les tenseurs locaux ne sont pas encore recollés entre patches.
- Porte terminale : aucune.

### `P5-HOLONOMIC-LOCAL-GLUING-IFF` — Critère exact de recollement

- État : `DONE` (2026-07-20). Portée : `SECTORIEL`, overlaps tangents D8.
- Gate : `P0EFTJanusMappingTorusLocalHolonomicDiagonalGluingCriterion4D`.
- Résultat : deux tenseurs diagonaux locaux coïncident sur un overlap si et
  seulement si la transition canonique des frames préserve le pairing
  diagonal ; le contrat cocycle global est équivalent à l'accord de toutes
  les réalisations locales.
- Limite : le contrat de préservation n'est pas encore déchargé.
- Porte terminale : aucune.

### `P5-HOLONOMIC-POINTWISE-LORENTZ-METRIC` — Assemblage ponctuel canonique

- État : `DONE` (2026-07-20). Portée : `POINTWISE`, vrai tangent D8.
- Gate : `P0EFTJanusMappingTorusPointwiseHolonomicDiagonalLorentzMetric4D`.
- Résultat : le patch centré en chaque point fournit une famille globale
  ponctuelle de musicals et tenseurs, non dégénérés et lorentziens ; sous le
  cocycle, elle coïncide avec toute réalisation locale contenant le point.
- Limite : aucune lissité de la famille assemblée n'est affirmée.
- Porte terminale : aucune.

### `P5-HOLONOMIC-SMOOTH-REALIZATION-INTERFACE` — Interface lisse exacte

- État : `DONE` (2026-07-20). Portée : `CONDITIONNEL`, vrai tangent D8.
- Gate : `P0EFTJanusMappingTorusSmoothHolonomicDiagonalRealization4D`.
- Résultat : toute section tensorielle symétrique lisse réalisant la famille
  ponctuelle fournit automatiquement un `SmoothGeneralLorentzMetric` avec le
  même musical, la même non-dégérescence et l'inertie `(3,1)` déjà prouvée.
- Limite : l'existence de cette section lisse n'est pas supposée démontrée.
- Porte terminale : aucune.

### `P5-MATTER-DIFFEO-ACTION-ID` — Même action matière pour Euler et Noether

- État : `BLOQUÉ-PHYSIQUE` (2026-07-19). Portée : `SECTORIEL`, huit scalaires.
- But : identifier `sameConfigurationGeneralLorentzMatterAction` à
  `globalMatterMultipletAction` avec mêmes champs, métrique, masses et mesure,
  puis transporter l'invariance difféomorphe vers l'action possédant déjà son
  Euler et son Hessien.
- Départ : `P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D`,
  `P0EFTJanusGlobalMatterMultipletActualEulerHessian4D`.
- Gate proposé : `P0EFTJanusMappingTorusActualMatterActionDiffeomorphismBridge4D`.
- Acceptation : égalité effective des densités ; pas de structure à champs
  `Prop` supposés.
- Porte terminale : aucune, mais dépendance directe de `T03` et `T05`.
- Blocage vérifié : `globalHolonomicScalarDensity` contient
  `+(massSquared / 2) * field²`, tandis que `holonomicScalarDensity`, donc
  `sameConfigurationGeneralLorentzMatterAction`, contient
  `-1 / 2 * massSquared * field²`. Avec la même masse, les densités ne peuvent
  coïncider hors secteur sans masse/champ nul. Il faut d'abord choisir et
  propager une convention de signe physique commune ; supposer directement
  l'égalité violerait l'acceptation de la carte.
- Certificats formels : `P0EFTJanusMappingTorusMatterActionMassSignObstruction4D`
  `P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D` et
  `P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D`, avec
  absence de compensation certifiée par
  `P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D`.
- Second prérequis : l'équivalence de coordonnées, le sharp, le musical, la
  frame lorentzienne et le volume diagonaux exacts sont construits par les
  cinq gates précédents, et la réalisation sur chaque patch tangent est faite
  par la sixième, et son critère exact de recollement par la septième. Il reste
  à décharger ce cocycle de préservation et l'existence de la section lisse
  désormais isolée par l'interface de réalisation ; le
  repère fixe global ne peut
  pas être déclaré lisse, par `P0EFTJanusMappingTorusLocalFrameNoGo4D`.

### `P9-BRST-FULL-LINEAR-KERNEL` — Noyau exact du bloc BRST linéaire

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, BRST linéaire.
- But : prouver `Q state = 0` si et seulement si les deux ghosts abéliens sont
  constants, en laissant explicitement libres potentiels initiaux et ghost
  difféomorphe.
- Départ : `P0EFTJanusCommonPairedD9LinearBRSTBlock4D` et le gate global H⁰
  abélien existant.
- Gate proposé : `P0EFTJanusCommonPairedD9LinearBRSTKernel4D`.
- Acceptation : ne pas appeler ce noyau « cohomologie BRST complète ».
- Porte terminale : aucune.
- Appui : `P0EFTJanusCommonPairedD9LinearBRSTKernel4D` prouve
  `Q state = 0` si et seulement si chacun des deux ghosts abéliens globaux
  est constant. Les potentiels initiaux et le ghost difféomorphe sont absents
  du membre droit, donc explicitement libres.
- Validation : gate, façade et audit compilés le 2026-07-19 ; noyau du seul
  bloc linéaire, aucune cohomologie BRST complète et aucune porte terminale.

### `P9-DIRAC-SIGN-SCOPE` — Portée exacte du Dirac spectral produit

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, modèle produit.
- But : prouver que `fold.sign * sqrt(D²)` garde le signe du fold et ne réalise
  pas les crossings du vrai Dirac géométrique signé.
- Départ : `P0EFTJanusProductThroatUnboundedDirac4D`,
  `P0EFTJanusProductThroatUnboundedDiracFredholm4D`.
- Gate proposé : `P0EFTJanusProductThroatDiracSignScope4D`.
- Acceptation : corriger la portée documentaire ; ne ferme pas le Dirac Janus.
- Porte terminale : aucune.
- Appui : `P0EFTJanusProductThroatDiracSignScope4D` prouve la stricte
  positivité des valeurs au fold positif, leur stricte négativité au fold PT,
  l'opposition exacte entre folds et l'absence de crossing de signe entre
  modes pour tout fold fixé.
- Validation : gate, façade et audit compilés le 2026-07-19 ; ce résultat
  borne explicitement la portée du modèle `sign * sqrt(D²)` et ne construit
  pas le Dirac géométrique Janus. Aucune porte terminale.

### `P9-FINITE-SPECTRAL-DET` — Déterminant finite-mode dépendant du spectre

- État : `DONE` (2026-07-19). Portée : `FINITE-MODE`.
- But : définir un déterminant utilisant réellement
  `sector.spectrum.eigenvalueSq`, avec shift positif explicite, puis prouver
  extensionalité, pondération statistique et produit des listes.
- Départ : `P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D`,
  `P0EFTJanusFiniteModeStatisticalDeterminant4D`.
- Gate proposé : `P0EFTJanusFiniteModeSpectralStatisticalDeterminant4D`.
- Acceptation : le déterminant change lorsque le spectre change ; aucune limite
  infinie ou ligne de Quillen revendiquée.
- Porte terminale : aucune.
- Appui : `P0EFTJanusFiniteModeSpectralStatisticalDeterminant4D` prend le
  produit réel des `shift + eigenvalueSq mode`, avec shift strictement positif,
  puis applique multiplicité et statistique. Il prouve extensionalité,
  non-annulation, addition des multiplicités et produit des listes.
- Validation : gate, façade et audit compilés le 2026-07-19 ; un spectre à
  un mode fournit un témoin injectif de dépendance spectrale. Aucune limite,
  ligne de Quillen ou porte terminale.

## 5. Cartes dépendantes — ordre critique

### `PE-RADIAL-SMOOTH-O4` — Réduction orthogonale radiale lisse — `DONE`

- État : `DONE` (2026-07-19). Portée : `GLOBAL`, vrai atlas tangent D8.
- But : empaqueter les frames radiales dans
  `AmbientContMDiffOrthonormalAtlasReduction` et identifier leur transition à
  la phase orthogonale du vrai winding.
- Départ : gates `AmbientAtlasRadialReferenceTransition4D`,
  `AmbientSmoothOrthonormalReduction4D` et
  `AmbientCanonicalReferenceOrthogonalCocycle4D`.
- Gate proposé : `P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D`.
- Acceptation : vraie régularité `ContMDiffOn`, sans contrat supposant la loi.
- Validation (2026-07-19) : la différentielle locale du vrai plongement donne
  une famille de frames `C∞`; l'inversion lisse des opérateurs prouve le
  `ContMDiffOn` joint de la famille inverse. Forme, frames et transitions sont
  empaquetées dans `ambientRadialReferenceContMDiffOrthonormalAtlasReduction`.
  Les overlaps restent exactement la phase `O(4)` du vrai winding, sans contrat.

### `PE-PIN-CANONICAL-BUNDLE` — Bundle principal Pin⁻ canonique réel — `DONE`

- État : `DONE` (2026-07-19). Portée : `GLOBAL`.
- But : projeter le lift canonique du winding sur cette réduction, prouver le
  cocycle, sa continuité et sa restriction au throat, puis construire le vrai
  bundle principal `Pin⁻(4)`.
- Départ : gates `AmbientCanonicalReferencePinMinusCech4D`,
  `AmbientCanonicalPinMinusEdgeGauge4D`, `AmbientPinMinusPrincipalBundle4D`.
- Gate proposé : `P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D`.
- Acceptation : aucune hypothèse `AmbientReferenceWindingOrthogonalReductionLaw`.
- Validation (2026-07-19) :
  `canonicalAmbientPinMinusPrincipalBundleCore` construit directement le vrai
  `FiberBundleCore` depuis le cocycle canonique continu. Son action droite est
  équivariante, libre et transitive ; la projection est exactement la réduction
  radiale lisse et la restriction au throat est le cocycle normal `Pin⁻(1)`.
  Aucun `AmbientReferenceWindingOrthogonalReductionLaw` n'est requis.

### `P-STOKES-CUT-01` — Green–Stokes sur le bulk coupé au throat

- État : `EN COURS` (2026-07-20). Portée : `GLOBAL` sur le domaine
  coupé.
- But : construire les deux lifts de bord, leurs orientations et la formule
  Green–Stokes ; déterminer si le flux quotient est somme, différence ou nul.
- Départ : `P0EFTJanusMappingTorusIntrinsicD8ScalarNormalStokes4D`,
  `P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D`.
- Gate proposé : `P0EFTJanusMappingTorusCutOpenScalarStokes4D`.
- Acceptation : ne jamais traiter le throat one-sided comme un bord ordinaire
  sans preuve.
- L'ancien blocage géométrique est levé : le quotient coupé est maintenant
  une variété `C∞` à bord. La formule Green–Stokes analytique reste à
  dériver ; `IntrinsicD8ScalarNormalStokesContract` contient cette conclusion
  comme champ `Prop` et ne doit toujours pas être instancié circulairement.
- Avancée (2026-07-20) :
  `P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D` ferme le ledger de
  signe sans supposer Stokes. Le générateur de deck inverse le courant scalaire
  et l'orientation sortante ; les deux contributions orientées sont donc
  égales, leur somme vaut deux fois un lift et leur différence est nulle.
  `P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D` identifie ensuite le
  bon bord topologique : une composante connexe double-couvrant le throat
  one-sided, avec deux lifts distincts échangés par le deck, et non deux copies
  quotient indépendantes.
  `P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D` construit le bulk coupé
  topologique comme mapping torus de l'hémisphère positif fermé à période
  doublée : sa projection vers le bulk initial est continue et surjective, le
  double bord s'y inclut injectivement et le carré bord/bulk commute.
  `P0EFTJanusMappingTorusCutBoundaryClosedEmbedding4D` renforce cette inclusion
  en plongement fermé : le double bord compact est fermé dans le bulk coupé
  hausdorff, condition topologique d'attachement sans recollement lisse affirmé.
  `P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D` construit un vrai
  collier analytique 4D à bord. Sa frontière est exactement l'union disjointe
  des images lisses injectives de la face throat et de l'interface extérieure.
  `P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D` réutilise la
  paramétrisation tubulaire et son inverse lisse déjà prouvés pour attacher ce
  collier au bulk coupé par un plongement fermé. La face zéro est exactement
  l'inclusion du double throat et la face latitude un fournit une interface
  extérieure explicite, elle-même plongée fermée.
  `P0EFTJanusMappingTorusCutBulkLatitudeBand4D` fait descendre la latitude au
  quotient et identifie exactement l'image du collier au niveau fermé
  `0 ≤ latitude ≤ sin 1`; l'interface extérieure est exactement le niveau
  `latitude = sin 1`.
  `P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D` décompose alors
  le bulk coupé en deux fermés couvrants, le collier et le reste extérieur,
  dont l'intersection est exactement cette interface. Le ledger de recollement
  topologique est ainsi fermé.
  `P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D` retire la face
  artificielle et identifie le collier ouvert au vrai ouvert intrinsèque
  `latitude < sin 1` par un plongement ouvert, fournissant la pièce d'atlas au
  bord.
  `P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D` munit ce collier ouvert
  de l'atlas analytique induit du collier fini et prouve l'analyticité de son
  inclusion.
  `P0EFTJanusMappingTorusCutBoundaryOpenCollarFace4D` inclut le double throat
  comme face zéro `C∞` du collier ouvert et identifie son attachement à
  `cutBoundaryInclusion`.
  `P0EFTJanusMappingTorusCutThroatOpenCollarBoundary4D` identifie exactement
  son bord de variété à la face normale zéro, la face artificielle normale un
  ayant bien disparu.
  `P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D` construit le cap intrinsèque
  ouvert `latitude > 0`; cap et collier couvrent tout le bulk coupé, avec
  overlap exact `0 < latitude < sin 1`.
  `P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D` construit le modèle
  du cap comme mapping torus analytique 4D de l'hémisphère strictement positif,
  à monodromie identité et période doublée; sa projection est localement un
  difféomorphisme analytique.
  `P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D` plonge ouvertement ce
  modèle dans le bulk coupé, identifie son image exactement au cap intrinsèque
  `latitude > 0` et construit l'homéomorphie canonique correspondante.
  `P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D` transporte ensuite
  l'atlas analytique sur le cap intrinsèque et prouve que cette homéomorphie
  canonique est analytique dans les deux sens.
  `P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D` restreint le
  difféomorphisme tubulaire existant à `0 < normal < 1` et prouve la transition
  `C∞` collier–calotte dans les deux sens au niveau des revêtements.
  `P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D` identifie ensuite
  exactement son image à la bande stricte `0 < latitude < sin 1`.
  `P0EFTJanusMappingTorusEquivariantSmoothDescent4D` prouve génériquement
  qu'une application lisse commutant aux decks entiers descend en application
  lisse entre les mapping tori munis de leurs atlas de revêtement, et qu'une
  application lisse invariante descend vers une cible lisse arbitraire, y
  compris avec un paramètre de variété lisse conservé pendant la descente.
  `P0EFTJanusIdentityMappingTorusSmoothFunctor4D` construit ces atlas lisses
  pour une monodromie identité et prouve qu'un difféomorphisme `C∞` de fibres
  induit un difféomorphisme `C∞` des mapping tori correspondants.
  `P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D` l'instancie
  sur le difféomorphisme tubulaire et obtient la compatibilité `C∞` descendue
  entre les deux mapping tori de l'overlap.
  `P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D` plonge ensuite
  ce mapping torus de bande stricte ouvertement et `C∞` dans la calotte lisse.
  `P0EFTJanusIdentityMappingTorusLocalDiffeomorph4D` montre génériquement
  qu'un difféomorphisme local de fibres induit un difféomorphisme local des
  mapping tori identité. Son instance
  `P0EFTJanusMappingTorusCutBulkCapOverlapLocalDiffeomorph4D` prouve que
  l'inclusion de l'overlap cap est un difféomorphisme local et que son inverse
  est `C∞` sur son image.
  `P0EFTJanusMappingTorusCutBulkIntrinsicCapOverlapDiffeomorph4D` compose cette
  inclusion avec l'identification du cap et obtient un difféomorphisme `C∞`
  explicite entre l'overlap quotient et le sous-ouvert du cap intrinsèque.
  `P0EFTJanusMappingTorusCutBulkCapOverlapExactIntrinsicRange4D` prouve que
  son image dans le bulk coupé est exactement `0 < latitude < sin 1`.
  `P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D` transporte
  ce résultat côté collier par le difféomorphisme tubulaire descendu.
  `P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D`
  factorise ce modèle quotient dans le vrai collier intrinsèque par un
  plongement ouvert canonique.
  `P0EFTJanusMappingTorusCutBulkCollarOverlapNormalSmooth4D` descend sa
  coordonnée normale en une fonction `C∞` sur l'overlap quotient.
  `P0EFTJanusMappingTorusCutBulkCollarOverlapBoundarySmooth4D` descend aussi
  sa projection vers le bord du collier en application `C∞`.
  `P0EFTJanusMappingTorusCutBulkCollarOverlapIntrinsicSmooth4D` assemble ces
  composantes, les identifie à la factorisation canonique et prouve celle-ci
  `C∞` vers le collier intrinsèque.
  `P0EFTJanusMappingTorusCutBulkPositiveUnitTubularProductDiffeomorph4D`
  identifie `C∞` les paramètres tubulaires stricts à
  `EquatorialTwoSphere × Ioo(0,1)`, première moitié de l'inverse local.
  `P0EFTJanusIdentityMappingTorusProductDiffeomorph4D` prouve génériquement
  que le mapping torus d'un produit à monodromie identité est `C∞`-difféomorphe
  au produit du mapping torus avec le facteur passif.
  `P0EFTJanusMappingTorusCutBulkCollarOverlapProductDiffeomorph4D` compose ces
  résultats et identifie l'overlap quotient à
  `CutThroatBoundary × Ioo(0,1)` par un difféomorphisme `C∞`.
  `P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D` identifie ce
  produit au sous-ouvert intrinsèque `normal > 0` du collier, dans les deux
  sens `C∞`, et retrouve exactement la factorisation canonique.
  `P0EFTJanusMappingTorusCutBulkInteriorModelDiffeomorph4D` identifie ensuite
  le modèle euclidien du cap à l'intérieur strict du modèle demi-espace du
  collier par un difféomorphisme `C∞`, inverse logarithmique compris.
  `P0EFTJanusMappingTorusCutBulkCapCommonModel4D` transporte cet atlas sur le
  modèle du cap et le promeut ainsi en variété `C∞` exprimée dans le même
  modèle demi-espace que le collier.
  `P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D` compose ce changement
  de modèle avec l'atlas intrinsèque du cap et prouve sa compatibilité `C∞`
  par transport des groupoïdes de changements de cartes.
  `P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D` prouve
  explicitement que l'identité entre les atlas standard et commun du cap est
  `C∞` dans les deux sens. Puis
  `P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonBoundaryless4D` empaquette
  cette identité en difféomorphisme et transporte l'absence de bord du cap
  standard vers l'atlas commun.
  `P0EFTJanusMappingTorusCutBulkCollarCapIntrinsicCompatibility4D` compose les
  difféomorphismes d'overlap et ferme la transition croisée collier–cap dans
  le modèle demi-espace commun; sa réalisation dans le bulk est prouvée
  exactement égale à l'attachement intrinsèque du collier.
  `P0EFTJanusMappingTorusCutBulkCollarCapPartialDiffeomorph4D` l'étend
  ensuite en difféomorphisme partiel `C∞` entre les ouverts complets collier
  et cap, et certifie ce changement de cartes comme structomorphisme local du
  groupoïde `C∞` de l'atlas.
  `P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D` relève alors les cartes
  des deux ouverts par leurs plongements ouverts et installe l'atlas
  topologique global préféré sur le bulk coupé.
  `P0EFTJanusMappingTorusCutBulkCollarCapAttachmentTransition4D` prouve que la
  transition topologique induite par ces plongements a exactement l'ouvert
  `normal > 0` pour source et coïncide sur cette source avec le
  difféomorphisme partiel `C∞` déjà certifié.
  `P0EFTJanusMappingTorusCutBulkCollarCapCoordinateCompatibility4D` en déduit
  la compatibilité dans le groupoïde `C∞` de toute paire de cartes locales
  collier–cap, puis des quatre changements de cartes globaux relevés.
  `P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D` assemble ces quatre cas et
  prouve enfin que le bulk coupé muni de l'atlas préféré est une variété
  `C∞` à bord dans le modèle demi-espace commun.
  `P0EFTJanusMappingTorusCutOpenCollarGlobalSmooth4D` réutilise ces transitions
  pour prouver que l'attachement du collier ouvert est `C∞` dans cet atlas.
  `P0EFTJanusMappingTorusCutBoundaryGlobalSmooth4D` en déduit que
  `cutBoundaryInclusion` est `C∞` dans le bulk global.
  `P0EFTJanusMappingTorusCutBulkGlobalBoundary4D` identifie ensuite son bord
  intrinsèque au niveau exact `latitude = 0`, lui-même exactement égal à
  l'image du double throat par `cutBoundaryInclusion`.
  `P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D` transforme cette
  égalité en homéomorphisme canonique du double throat sur le sous-type du
  bord global, dont l'application sous-jacente est exactement l'inclusion.
  `P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D` descend ensuite le
  courant tordu en vrai scalaire `C∞` sur ce double bord : les windings pairs
  agissent trivialement et le deck résiduel échange les deux lifts en changeant
  le signe du courant.
  `P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D`
  identifie le deck résiduel à la translation de demi-période, prouve qu'il
  préserve la mesure canonique du double bord et en déduit que l'intégrale
  scalaire non orientée du courant est nulle. Cette annulation n'est pas le flux
  orienté de Stokes, dont l'orientation normale inverse compense ce signe.
  `P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D` pousse cette mesure
  canonique sur le sous-type exact du bord global, prouve la formule de
  changement de variables et y transporte l'annulation scalaire non orientée.
  `P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D`
  prouve directement par FTC/Fubini que l'intégrale de la divergence sur le
  demi-collier positif vaut l'opposé du flux mesuré au throat ; aucune instance
  du contrat Stokes n'est utilisée.
  `P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D` identifie ce
  flux au courant scalaire descendu évalué sur la première feuille du bord
  coupé et réécrit la formule du demi-collier avec ce vrai bord.
  `P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D` ajoute
  la feuille deck-conjuguée : le courant et la normale sortante changent tous
  deux de signe, les flux orientés sont égaux et la formule intégrée acquiert
  exactement le facteur `2` attendu.
  `P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D` descend le même courant
  cutoff en scalaire continu sur tout le bulk coupé grâce aux windings pairs,
  et prouve que sa restriction par l'inclusion du bord est exactement le
  courant scalaire de bord déjà construit.
  `P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCapSmooth4D` et
  `P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCollarSmooth4D` prouvent sa
  lissité `C∞` séparément sur les deux ouverts qui couvrent le bulk global :
  la calotte intrinsèque et le collier, y compris sa fermeture finie.
  `P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D` expose les
  deux inclusions d'atlas comme difféomorphismes partiels `C∞` dans les deux
  sens. `P0EFTJanusMappingTorusCutBulkScalarCurrentGlobalSmooth4D` utilise ce
  certificat et le recouvrement ouvert pour recoller les deux preuves : le
  courant cutoff est désormais `C∞` sur tout le bulk coupé global. La gate
  `P0EFTJanusMappingTorusCutBulkLatitudeGlobalSmooth4D` promeut aussi la
  latitude positive de fonction continue en vraie fonction `C∞` globale. La
  gate `P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D` construit
  alors `bump(arcsin(latitude))`, traite le pôle où il est localement nul et
  retrouve exactement le bump initial sur le collier canonique.
  `P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D`
  identifie exactement son pullback sur le collier canonique à la densité
  cutoff de la formule FTC. Enfin,
  `P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D` prouve
  que sa dérivée le long du vrai chemin de bulk est exactement la divergence
  normale densitisée déjà intégrée dans la formule de demi-collier.
  `P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D` remplace alors
  cette densité par la dérivée du courant global sous l'intégrale et obtient
  l'identité exacte avec le courant du bord, d'abord sur la première feuille,
  puis sous la forme orientée à deux feuilles avec le facteur `2`.
  `P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D` pousse ensuite la
  mesure produit canonique sur le vrai bulk. La dérivée normale de la densité
  est prouvée conjointement `C∞` et intégrable par
  `P0EFTJanusCanonicalLatitudeScalarCurrentJointDivergenceSmooth4D`, puis
  `P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D` la transporte
  comme mesure vectorielle réelle signée. Sa masse totale satisfait sans
  hypothèse supplémentaire l'identité de Stokes orientée à deux feuilles.
  Les gates `P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D`,
  `P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D` et
  `P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D` prouvent maintenant
  que l'application naturelle du bulk coupé vers le tore quotient original
  est globalement `C∞`. Ce prérequis permet de tirer en arrière les objets
  métriques ambiants. La gate
  `P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D` construit déjà leur
  pullback tensoriel point par point par la vraie dérivée de variété et prouve
  la formule d'évaluation ainsi que la préservation de la symétrie. La gate
  `P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D` prouve en outre
  la non-dégénérescence et l'inertie lorentzienne dès que la dérivée naturelle
  est certifiée isomorphe. La gate
  `P0EFTJanusMappingTorusCutBulkOpenCapAmbientDerivativeIsomorphism4D` établit
  ce certificat sur la calotte analytique en factorisant la dérivée entre les
  projections quotient et l'inclusion ouverte du cover ;
  `P0EFTJanusMappingTorusCutBulkGlobalCapDerivativeIsomorphism4D` le transporte
  ensuite jusqu'à chaque point de la calotte ouverte de l'atlas global. Reste
  à traiter le collier. Son unique facteur non difféomorphe, l'inclusion normale
  `[0,1] → ℝ`, possède désormais une dérivée explicitement isomorphe, bord
  compris, grâce à
  `P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D`. La gate
  `P0EFTJanusMappingTorusCutCollarCoverNormalExtensionDerivativeIsomorphism4D`
  assemble aussi ce facteur avec l'identité du revêtement du bord. La gate
  `P0EFTJanusMappingTorusCutCollarTubularNormalLift4D` relève ensuite `[0,1]`
  dans le domaine ouvert de la carte tubulaire et certifie ce relèvement lisse
  avec une dérivée isomorphe. Enfin,
  `P0EFTJanusMappingTorusCutCollarTubularSphereDerivativeIsomorphism4D`
  compose ce certificat avec le difféomorphisme tubulaire sphérique, puis
  `P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D`
  ajoute la direction temps inchangée. Les gates
  `P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D` et
  `P0EFTJanusMappingTorusCutCollarProductToAmbientDerivativeIsomorphism4D`
  composent ensuite l'inclusion dans le cover, la projection quotient et la
  carte tubulaire complète. Les gates
  `P0EFTJanusMappingTorusCutCollarCoverToAmbientDerivativeIsomorphism4D` et
  `P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D`
  transportent ce certificat au vrai revêtement du bord puis le descendent au
  collier fini quotient, bord compris. Les gates
  `P0EFTJanusMappingTorusCutBulkOpenCollarAmbientDerivativeIsomorphism4D` et
  `P0EFTJanusMappingTorusCutBulkGlobalCollarDerivativeIsomorphism4D` le
  transportent désormais dans le collier ouvert puis dans l'atlas global du
  bulk. La gate `P0EFTJanusMappingTorusCutBulkGlobalDerivativeIsomorphism4D`
  recolle désormais les certificats du cap et du collier en un certificat
  global, et `P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackGlobalLorentz4D`
  en déduit la non-dégénérescence et l'inertie lorentzienne du pullback en tout
  point. La gate
  `P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D` promeut ce
  pullback en vraie section tensorielle symétrique `C∞`, puis
  `P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D` assemble
  cette section, sa signature et son équivalence musicale globale. Il reste à
  identifier la mesure transportée à la divergence covariante globale
  correspondante pour obtenir Green–Stokes complet. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D` établit aussi la
  lissité de la famille inverse musicale et fournit donc le `sharp` lisse
  nécessaire à cette dernière étape. Enfin, les gates
  `P0EFTJanusMappingTorusCutBulkMetricVolumeDensityNaturality4D` et
  `P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D` transportent
  exactement le déterminant de Gram, la densité volumique et la frame
  intrinsèque canonique vers le bulk. Il reste à promouvoir cette égalité
  ponctuelle en pont de mesures puis à l'identifier à la divergence globale.
  La gate `P0EFTJanusMappingTorusCutBulkSmoothScalarGradient4D` construit en
  parallèle les vrais champs scalaires, différentielles et gradients `C∞` du
  bulk, avec la règle de chaîne exacte depuis le quotient ambiant ; c'est le
  prérequis direct à la construction du courant vectoriel covariant. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D` construit désormais
  ce vrai courant `C∞`, prouve sa formule abaissée exacte et le spécialise à la
  métrique intrinsèque et aux champs ambiants. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothCutoffScalarGreenCurrent4D` construit le
  vrai champ vectoriel global `χJ`, prouve sa lissité et montre que son flux
  normal sur le collier canonique est exactement l'ancien courant scalaire
  cutoff descendu. La gate
  `P0EFTJanusMappingTorusCutBulkMetricMeasureDomination4D` identifie exactement
  le transport ambiant de la mesure du collier et lui applique la domination
  coarea déjà fermée par le volume lorentzien intrinsèque. La gate
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D`
  réalise maintenant l'expansion par produit de la divergence de Levi--Civita
  sur les vrais jets scalaires locaux et prouve l'identité de Green
  `div J = φ □ψ - ψ □φ`. La gate
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D`
  identifie en outre le jet de la métrique inverse à sa vraie dérivée de
  Fréchet locale, et
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D`
  en déduit la formule de Fréchet exacte du gradient scalaire relevé. La gate
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D`
  applique ensuite Leibniz au vrai courant et construit sa divergence brute
  `∂μJμ + Γμ_{μν}Jν`. Enfin,
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D`
  utilise la compatibilité métrique pour identifier cette vraie dérivée à
  la divergence jet et ferme donc localement
  `div J = φ □ψ - ψ □φ`. La gate
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D`
  prouve ensuite sur le vrai courant coordonné la règle covariante de Leibniz
  `div(χJ) = dχ(J) + χ div J`; sur deux solutions de même masse, seul le flux
  de gradient du cutoff subsiste. Il reste à instancier ce résultat par le
  cutoff global canonique puis à identifier sa densité à la mesure normale
  déjà construite. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCollarFlux4D`
  transporte maintenant exactement le flux du vrai courant intrinsèque du
  bulk coupé vers le Wronskien ambiant dans toute direction tangentielle
  transportée. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D`
  spécialise ce pont au normal canonique du collier et retrouve exactement le
  courant scalaire de Green--Wronskien déjà utilisé par les cartes de Stokes.
  La gate `P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D`
  identifie ensuite l'ancien courant scalaire global à `cutoff × flux normal`
  du vrai courant vectoriel et prouve que sa densité de divergence mesurée est
  la vraie dérivée normale de ce produit dans l'intérieur du collier. La gate
  `P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D` réécrit
  alors le Stokes mesuré positif et orienté à deux feuilles directement avec
  le flux normal du vrai courant vectoriel. La gate
  `P0EFTJanusMappingTorusCutBulkPointwiseScalarGreenDivergence4D` utilise la
  couverture holonome totale pour réaliser la vraie identité de divergence
  locale au-dessus de chaque point du quotient et donc de chaque point du bulk
  coupé. La gate
  `P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D`
  construit en outre la mesure globale dont la densité intérieure est la vraie
  dérivée normale de `cutoff × flux`, l'identifie exactement à la mesure de
  divergence canonique, puis lui applique le Stokes orienté. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenNormalDivergenceMeasure4D`
  remplace maintenant ce produit auxiliaire par le flux normal du vrai champ
  vectoriel global `χJ`, prouve que sa dérivée intérieure donne exactement la
  même densité et que la mesure résultante est égale à la mesure genuine déjà
  soumise à Stokes. Cette densité reste toutefois celle de la mesure produit
  non pondérée. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D`
  insère le jacobien métrique déjà prouvé `cos²(normal)` et montre que la vraie
  densité candidate est la dérivée de `cos² × flux(χJ)`, soit la densité nue
  multipliée par `cos²` plus son terme de dérivée. Ainsi aucune fausse égalité
  ponctuelle avec la mesure non pondérée n'est affirmée. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D`
  construit désormais la mesure pondérée correspondante, prouve son
  intégrabilité, le FTC sur chaque fibre, sa formule de masse totale et le
  Stokes orienté à deux feuillets. La gate
  `P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D`
  prouve ensuite que `cos²` est strictement positif sur le collier, extrait la
  contribution normale non densitisée et réidentifie exactement sa mesure à
  la mesure métrique précédente. La gate
  `P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D`
  décompose maintenant la vraie divergence locale en contributions normale et
  tangentielle et prouve que, si le courant de Green est conservé et le cutoff
  normal seulement, la divergence complète se réduit exactement à
  `dχ(normal) × J^normal`. La gate
  `P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarDerivative4D` prouve que le
  cutoff global possède précisément la dérivée du bump sur chaque fibre du
  collier et une dérivée nulle le long de toute courbe de base à normale fixe.
  La gate
  `P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D`
  isole ensuite exactement la compensation tangentielle du terme jacobien et
  prouve algébriquement que son ajout à la contribution normale redonne
  `cutoff' × flux`, densitisé ou non. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeCollarHolonomicCoordinateEquiv4D`
  construit le changement linéaire continu exact entre `R⁴` et les coordonnées
  du collier, avec l'indice `0` normal, `1,2` sphériques et `3` temporel. Il
  est instancié par la gate
  `P0EFTJanusMappingTorusCanonicalLatitudeHolonomicCutoffDerivative4D`, qui
  prouve dans `R⁴` que la dérivée d'indice `0` vaut exactement `cutoff'` et que
  les trois dérivées restantes sont nulles, satisfaisant ainsi le contrat
  `LocalCutoffNormalOnlyAt`; elle instancie aussi la règle de Leibniz covariante
  et réduit la divergence locale conservée à `cutoff' × J⁰`. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeNormalAdaptedHolonomicChart4D`
  reparamètre maintenant une vraie carte holonome totale en chaque point du
  collier de sorte que son vecteur de frame d'indice `0` soit exactement la
  normale canonique globale. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D`
  applique une correction linéaire inversible qui fixe cet axe normal et place
  exactement les trois autres vecteurs de frame dans le noyau de la covariable
  normale métrique. La gate
  `P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D` calcule désormais
  la différentielle manifold complète du vrai cutoff global tiré sur le produit
  du collier : elle vaut exactement `cutoff'` multiplié par la composante
  tangentielle normale. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeAmbientOrthogonality4D` généralise
  maintenant l'orthogonalité normale/tangentielle du throat à toute latitude
  non polaire du collier. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeNormalCovectorCollarDerivative4D`
  transporte cette formule par la dérivée du collier et prouve exactement que
  le vrai cutoff global vérifie `dχ = χ' · n♭` sur son intérieur. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeAdaptedHolonomicGreenCurrentFlux4D`
  prouve ensuite que la composante locale adaptée `J⁰` est exactement le flux
  normal du véritable courant global sur le bulk coupé. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D`
  reconnaît le cutoff holonome, y compris dans les cartes centrées à latitude
  arbitraire, comme le vrai pullback local du cutoff global ; elle en déduit que
  sa divergence locale libre au centre vaut exactement `cutoff' ×` le courant
  normal canonique. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeLocalGlobalCutoffDivergenceMetricBridge4D`
  identifie ensuite cette divergence locale totale à la somme de la divergence
  normale métrique et de la compensation jacobienne déjà construites. Cette
  formulation est invariante ; elle évite d'identifier séparément deux termes
  normal/tangentiels dépendant du second jet de la carte. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceGluing4D`
  définit enfin la valeur globale correspondante sur le collier canonique,
  prouve que tout représentant holonome adapté centré la calcule et en déduit
  l'indépendance exacte de la carte et du représentant tangentiel. Le recollement
  du secteur cutoff canonique du collier est ainsi fermé sans contrat de jets.
  La gate
  `P0EFTJanusMappingTorusCanonicalHolonomicAtlasScalarGreenDivergenceTransition4D`
  prouve désormais l'invariance exacte de la divergence réelle sur les overlaps
  sous les jets de transition rebasés de la métrique et des deux scalaires ; le
  verrou résiduel est donc la réalisation inconditionnelle de ce contrat de jets
  pour l'atlas canonique total. Sous ce contrat, la gate
  `P0EFTJanusMappingTorusGlobalScalarGreenDivergenceGluing4D` effectue déjà le
  recollement, prouve l'indépendance du représentant, retrouve la différence des
  ondes dans chaque carte et transporte le scalaire global au bulk coupé. Pour
  la conclusion physique de conservation, la gate
  `P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarGreenConservation4D`
  contourne légitimement ce contrat : deux équations d'Euler sans source et de
  même masse annulent la vraie divergence dans chaque carte de l'atlas total,
  donc au-dessus de chaque point du quotient et du bulk, sans hypothèse
  d'overlap ; elle construit aussi explicitement le scalaire global on-shell
  nul et prouve qu'il représente la divergence réelle dans toute carte. Le
  contrat rebasé ne reste nécessaire que pour recoller une valeur de divergence
  globale arbitraire non nulle. Enfin, la gate
  `P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D` montre
  que, pour deux solutions du collier sans source et de même masse, la densité
  mesurée se réduit exactement à `cutoff' × flux normal vrai` : il ne subsiste
  aucun terme de bulk et cette densité s'annule exactement dans le cœur où le
  cutoff est constant.

### `P5-CANDIDATEA-METRIC-HESSIAN` — Hessien de la même interaction — `DONE`

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, interaction Candidate A diagonale.
- But : dériver la première variation intégrée dans une seconde direction
  métrique, identifier le résultat au Hessien de cette même interaction et
  prouver sa symétrie sous les hypothèses analytiques visibles.
- Départ : `P0EFTJanusMappingTorusCandidateAFunctionalVariation4D`,
  `P0EFTJanusExplicitCandidatePointwiseEuler` et gates de seconde variation de
  Fréchet.
- Gate proposé : `P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D`.
- Acceptation : domaine ouvert de la racine et domination de seconde variation
  explicités ; aucun EH/Maxwell/ghost revendiqué.
- Validation (2026-07-19) : le second `fderiv` de la même densité globale sur
  `ScalePair` construit le Hessien à huit composantes. La première variation
  intégrée se dérive dans une seconde direction sous un contrat explicitant
  domaine positif, régularité C² et majorant intégrable ; le Hessien est
  symétrique. Aucun terme EH, Maxwell, ghost ou bord n'est revendiqué.

### `P5-PARTIAL-SAME-ACTION-HESSIAN` — Hessien de l'action sectorielle sommée — `DONE`

- État : `DONE` (2026-07-19).
- Portée : `SECTORIEL` sur `ProgramPRobinCompleteVariation4D`.
- But : sommer interaction Candidate A, matière, Robin et LL, puis prouver que
  la dérivée de l'Euler de cette même somme est son Hessien symétrique.
- Départ : `P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D`,
  `P0EFTJanusMatterRobinLLActualActionEulerHessian4D`.
- Gate proposé : `P0EFTJanusMappingTorusCandidateAPartialSameActionHessian4D`.
- Acceptation : le nom et le théorème disent explicitement « sectoriel » ;
  aucune fermeture de `hessianMatchesNaturalFredholmFamily`.
- Validation (2026-07-19) : le Hessien global Candidate A est sommé aux vrais
  Hessians matière, Robin et LL sur `ProgramPRobinCompleteVariation4D`.
  L'Euler de l'action sectorielle déjà prouvée se dérive vers cette somme,
  qui est symétrique. Aucun EH/Maxwell/ghost ni accord avec la famille de
  Fredholm naturelle complète n'est revendiqué.

### `P9-CIRCLE-CLUTCHING-QUOTIENT` — Vrai quotient de la ligne cercle — `DONE`

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, famille cercle.
- But : construire le quotient du total espace sur `[0,1]` par la transition
  d'extrémité et un isomorphisme de fibrés avec la ligne obtenue sur
  `AddCircle 1`.
- Départ : `P0EFTJanusCircleDeterminantLineFamily`,
  `P0EFTJanusCircleDeterminantTopologicalBundle`.
- Acceptation : le quotient/clutching est construit, pas déclaré trivial par
  définition ; aucune identification Quillen globale.
- Validation (2026-07-19) : le vrai quotient topologique de `ℝ × ℂ` par
  la monodromie exacte est relié à la ligne descendue sur `AddCircle 1` par un
  homéomorphisme explicite couvrant la projection. La jauge logarithmique
  neutralise exactement toute puissance entière de monodromie ; les formules
  fibre par fibre préservent addition et multiplication scalaire complexe.
  Aucune identification Quillen globale n'est revendiquée.

### `P9-CIRCLE-HEAT-ETA` — Eta thermique analytique du cercle

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, famille cercle.
- But : définir `η_t(a)=Σₙ λₙ(a) exp(-t λₙ(a)^2)` pour `t>0`, prouver
  sommabilité, covariance PT et relabeling de grande jauge.
- Départ : gates chaleur nucléaire du cercle,
  `P0EFTJanusCircleBoundedTransformSpectralFlow`.
- Acceptation : résultat thermique du cercle seulement ; aucun théorème APS,
  eta régularisé global ou inflow géométrique.
- Porte terminale : aucune.
- Appui : `P0EFTJanusCircleHeatEtaRegularization4D` définit la série effective
  `Σₙ λₙ exp(-t λₙ²)`, prouve sa sommabilité absolue à tout temps positif,
  son oddité PT et l'égalité exacte des holonomies unité/périodique après
  relabeling Fourier `n ↦ n+1`.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucun passage
  `t → 0`, invariant APS, eta global ou inflow n'est revendiqué.

### `P0-ROOT-REGULAR-MOVING-SIMILARITY` — Cadres mobiles réguliers `0/0`

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, chemins monomiaux diagonaux.
- But : transporter les limites de racines par une similarité mobile régulière
  et vérifier que la trichotomie `0/0` survit dans le repère mobile.
- Gate : `P0EFTJanusRegularMovingSimilarityZeroOverZero4D`.
- Acceptation : changement de base et inverse convergents ; aucune conclusion
  pour un cadre singulier arbitraire ou un changement général de type Jordan.
- Porte terminale : aucune.
- Validation : gate déjà importé et audité ; recompilation Lean, façade et
  audit verts le 2026-07-19.

### `P0-ROOT-UNIVERSAL-EXTENSION-NOGO` — Extension matricielle `0/0`

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, obstruction universelle.
- But : exclure une valeur matricielle continue monovaluée au coin `0/0`
  lorsqu’elle doit prolonger la racine principale sur la sous-famille diagonale.
- Gate : `P0EFTJanusMatrixZeroOverZeroUniversalExtensionNoGo4D`.
- Acceptation : restriction diagonale effective ; aucune classification des
  chemins matriciels ou des changements généraux de type Jordan.
- Porte terminale : aucune.
- Validation : gate déjà importé et audité ; recompilation Lean, façade et
  audit verts le 2026-07-19.

### `P0-ROOT-FIXED-SIMILARITY-NOGO` — Similarité fixe `0/0`

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, classe simultanément diagonalisable.
- But : transporter la classification monomiale et le no-go `0/0` par une
  conjugaison réelle fixe inversible.
- Gate : `P0EFTJanusFixedSimilarityMatrixZeroOverZeroNoGo4D`.
- Acceptation : similarité fixe ; aucune classification des cadres mobiles,
  singuliers ou des strates de Jordan générales.
- Porte terminale : aucune.
- Validation : gate déjà importé et audité ; recompilation Lean, façade et
  audit verts le 2026-07-19.

### `P0-ROOT-REGULAR-MOVING-FULL-LIMIT` — Limites matricielles complètes

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, chemins monomiaux diagonaux.
- But : pour les branches `m=n` et `n<m`, transporter sous similarité mobile
  régulière la limite du spectre entier et de la matrice-racine complète.
- Gate : `P0EFTJanusRegularMovingSimilarityFullMatrixLimit4D`.
- Acceptation : changement de base et inverse convergents ; le cas divergent
  est séparé ci-dessous, les cadres singuliers et chemins généraux restent ouverts.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade et audit
  vérifiés après intégration le 2026-07-19.

### `P0-ROOT-REGULAR-MOVING-NO-FINITE-LIMIT` — Branche divergente

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, chemins monomiaux diagonaux.
- But : exclure une limite matricielle finie sous similarité mobile régulière
  lorsque le dénominateur s'annule plus vite que le numérateur.
- Gate : `P0EFTJanusRegularMovingSimilarityFullMatrixLimit4D`.
- Acceptation : changement de base et inverse convergents ; aucune conclusion
  pour cadres singuliers ou chemins matriciels généraux.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade et audit
  vérifiés après intégration le 2026-07-19.

### `P0-ROOT-REAL-POWER-CLASSIFICATION` — Exposants réels au coin `0/0`

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, chemins diagonaux.
- But : étendre la trichotomie monomiale de `ℕ_{>0}` à deux exposants réels
  strictement positifs.
- Gate : `P0EFTJanusGlobalDiagonalRealPowerZeroOverZeroClassification4D`.
- Acceptation : chemin diagonal `t^m/t^n` seulement ; aucune fonction positive
  arbitraire, chemin matriciel général ou dégénérescence de Jordan.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade et audit
  vérifiés après intégration le 2026-07-19.

### `P0-ROOT-FUNCTIONAL-RATIO-CLASSIFICATION` — Chemins fonctionnels `0/0`

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, chemins diagonaux.
- But : pour deux fonctions positives arbitraires tendant vers zéro, ramener
  exactement la limite de la racine à celle de leur ratio.
- Gate : `P0EFTJanusGlobalDiagonalFunctionalZeroOverZeroClassification4D`.
- Acceptation : limite du ratio fournie, finie ou `+∞` ; aucune classification
  des chemins matriciels non diagonaux ou des ratios sans limite.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade et audit
  vérifiés après intégration le 2026-07-19.

### `P0-ROOT-FUNCTIONAL-MOVING-MATRIX` — Ratio fonctionnel en cadre mobile

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, classe simultanément diagonalisable.
- But : transporter la classification fonctionnelle vers la matrice-racine
  complète sous similarité mobile régulière.
- Gate : `P0EFTJanusRegularMovingSimilarityFunctionalZeroOverZero4D`.
- Acceptation : cadre et inverse convergents, ratio convergent ou divergent
  vers `+∞` ; aucun cadre singulier ni chemin matriciel général.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade et audit
  vérifiés après intégration le 2026-07-19.

### `P0-ROOT-SINGULAR-VALUATION-CRITERIA` — Cadres singuliers diagonaux

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, matrices monomiales/polynomiales.
- But : caractériser les limites finies sous conjugaison par un cadre diagonal
  singulier au moyen des valuations entrée par entrée.
- Gates : `P0EFTJanusGlobalMonomialMatrixValuationCriterion4D`,
  `P0EFTJanusSignedMonomialMatrixValuationCriterion4D` et
  `P0EFTJanusFinitePolynomialMatrixValuationCriterion4D`.
- Acceptation : exposants entiers et sommes finies à terme dominant certifié ;
  aucun cadre singulier non diagonal ni série infinie.
- Porte terminale : aucune.
- Validation : gates déjà importés et audités ; recompilation focalisée,
  façade et audit vérifiés le 2026-07-19.

### `P0-ROOT-FINITE-POLYNOMIAL-VALUATION-IFF` — Critère polynomial exact

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, sommes monomiales finies.
- But : rendre nécessaire et suffisante la condition de valuations non
  négatives pour l'existence d'une limite matricielle finie.
- Gate : `P0EFTJanusFinitePolynomialMatrixValuationCriterion4D`.
- Acceptation : terme dominant non nul et ordres entiers strictement séparés ;
  aucune série infinie ou annulation du terme dominant.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade et audit
  vérifiés après intégration le 2026-07-19.

### `P0-ROOT-ASYMPTOTIC-VALUATION-IFF` — Terme dominant asymptotique

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, critère entrée par entrée.
- But : remplacer les seules sommes finies par toute matrice dont chaque entrée
  admet un terme dominant asymptotique non nul certifié.
- Gate : `P0EFTJanusAsymptoticMatrixValuationCriterion4D`.
- Acceptation : équivalence exacte entre valuations non négatives et existence
  d'une limite matricielle finie, avec limite explicite.
- Limite : l'asymptotique dominante reste une hypothèse ; aucun cadre singulier
  arbitraire ni changement général de type Jordan n'est classifié.
- Porte terminale : aucune.
- Validation : gate compilé, façade, audit, usages et axiomes vérifiés après
  intégration le 2026-07-19.

### `P0-ROOT-ANALYTIC-VALUATION-IFF` — Germes de séries convergentes

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, entrées analytiques non nulles.
- But : déduire automatiquement le terme dominant et son coefficient non nul
  d'un germe de série convergente, y compris pour une série infinie.
- Gate : `P0EFTJanusAnalyticMatrixValuationCriterion4D`.
- Acceptation : factorisation analytique exacte, résidu continu non nul à zéro,
  puis équivalence entre valuations non négatives et limite matricielle finie.
- Limite : les entrées localement nulles, non analytiques et les cadres
  singuliers arbitraires restent hors portée.
- Porte terminale : aucune.
- Validation : gate focalisé compilé ; façade, audit, usages et axiomes vérifiés
  après intégration le 2026-07-19.

### `P0-ROOT-ACTIVE-ASYMPTOTIC-VALUATION` — Entrées asymptotiques inactives

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, critère entrée par entrée.
- But : autoriser des matrices partiellement creuses sans imposer un faux
  coefficient dominant non nul à leurs entrées inactives.
- Gate : `P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D`.
- Acceptation : les entrées actives ont une asymptotique dominante non nulle ;
  les autres sont éventuellement nulles et n'imposent aucune valuation.
- Limite : le masque actif et les asymptotiques restent des certificats fournis.
- Porte terminale : aucune.
- Validation : gate focalisé compilé ; façade, audit, usages et axiomes vérifiés
  après intégration le 2026-07-19.

### `P0-ROOT-ANALYTIC-ZERO-ENTRY-VALUATION` — Entrées inactives nulles

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, matrices analytiques.
- But : retirer l'hypothèse artificielle que chaque entrée matricielle possède
  un coefficient dominant non nul.
- Gate : `P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D`.
- Acceptation : une série formelle nulle marque une entrée inactive, n'impose
  aucune valuation et converge vers zéro ; le critère reste exact sur toutes
  les entrées actives.
- Limite : aucune entrée non analytique ni cadre singulier arbitraire.
- Porte terminale : aucune.
- Validation : gate focalisé compilé ; façade, audit, usages et axiomes vérifiés
  après intégration le 2026-07-19.

### `P0-ROOT-MOVING-ACTIVE-ASYMPTOTIC` — Masque actif en base mobile

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, base extérieure régulière.
- But : transporter le critère asymptotique actif abstrait sans revenir au cas
  analytique particulier.
- Gate : `P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D`.
- Acceptation : limite conjuguée explicite et équivalence exacte conservée pour
  les entrées actives, les entrées éventuellement nulles restant inactives.
- Limite : aucune base extérieure sans limite ou à inverse divergent.
- Porte terminale : aucune.
- Validation : gate focalisé compilé ; façade, audit, usages et axiomes vérifiés
  après intégration le 2026-07-19.

### `P0-ROOT-MOVING-ANALYTIC-ZERO-VALUATION` — Base mobile et entrées nulles

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, base extérieure régulière.
- But : transporter le critère analytique exact, entrées inactives comprises,
  par une base mobile dont la matrice et l'inverse convergent.
- Gate : `P0EFTJanusRegularMovingAnalyticMatrixWithZeroValuationCriterion4D`.
- Acceptation : équivalence nécessaire/suffisante conservée et limite conjuguée
  explicitement par les deux limites de base.
- Limite : aucune base sans limite ou à inverse divergent.
- Porte terminale : aucune.
- Validation : gate focalisé compilé ; façade, audit, usages et axiomes vérifiés
  après intégration le 2026-07-19.

### `P0-ROOT-MOVING-ASYMPTOTIC-VALUATION` — Base extérieure mobile

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, conjugaison extérieure
  régulière.
- But : transporter le critère asymptotique exact par une base mobile dont la
  matrice et l'inverse convergent.
- Gate : `P0EFTJanusRegularMovingAsymptoticMatrixValuationCriterion4D`.
- Acceptation : même équivalence nécessaire/suffisante et limite explicitement
  conjuguée par les limites de la base et de son inverse.
- Limite : aucune base extérieure sans limite ou à inverse divergent.
- Porte terminale : aucune.
- Validation : gate compilé, façade, audit, usages et axiomes vérifiés après
  intégration le 2026-07-19.

### `P0-ROOT-MONOMIAL-SINGULAR-JORDAN` — Cadres singuliers `diag(t^k)`

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, collision Jordan canonique.
- But : classifier la collision sous tout cadre singulier diagonal monomial
  `diag(t^k,1,1,1)`.
- Gate : `P0EFTJanusMonomialSingularSimilarityJordan4D`.
- Acceptation : un bloc Jordan canonique et un exposant entier ; aucun cadre
  singulier non diagonal ni changement général de type Jordan.
- Porte terminale : aucune.
- Validation : gate déjà importé et audité ; recompilation focalisée, façade et
  audit vérifiés le 2026-07-19.

### `P0-ROOT-FIXED-CONJUGATE-SINGULAR-VALUATION` — Cadres singuliers conjugués

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, conjugaison fixe inversible.
- But : étendre le critère exact de valuations aux cadres singuliers non
  diagonaux obtenus par conjugaison fixe d'un cadre diagonal monomial.
- Gate : `P0EFTJanusFixedConjugateSingularFrameValuationCriterion4D`.
- Acceptation : limite explicite et équivalence nécessaire/suffisante pour les
  matrices monomiales et sommes monomiales finies ; aucune direction propre
  mobile ou cadre singulier arbitraire.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `P0-ROOT-MOVING-CONJUGATE-SINGULAR-VALUATION` — Directions propres mobiles

- État : `DONE` (2026-07-19). Portée : `RÉDUIT`, conjugaison extérieure régulière.
- But : autoriser autour du cadre diagonal singulier une base mobile dont la
  matrice et l'inverse convergent.
- Gate : `P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D`.
- Acceptation : équivalence et limite explicite pour matrices monomiales et
  sommes finies ; aucune base extérieure sans limite ou à inverse divergent.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `PE-LATITUDE-PINMINUS-COMPATIBILITY` — Lift de la normale latitude

- État : `DONE` (2026-07-19). Portée : `SECTORIEL`, vrai atlas du throat.
- But : relier le lift ambiant `Pin⁻(4)` à la normale latitude canonique et à
  son tour fondamental.
- Gate : `P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D`.
- Acceptation : cocycle et projection sur le throat ; aucune classe
  caractéristique globale ni compatibilité avec le twist monopolaire.
- Porte terminale : aucune.
- Validation : gate déjà importé et audité ; recompilation focalisée, façade et
  audit vérifiés le 2026-07-19.

### `PE-PRIMITIVE-MONOPOLE-PINMINUS-CHARACTER` — Caractère monopolaire primitif

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, entier de transition.
- But : relier la charge de Chern primitive et sa conjugaison PT au caractère
  ambiant `Pin⁻(4)`.
- Gate : `P0EFTJanusPrimitiveMonopolePinMinusCharacterCompatibility4D`.
- Acceptation : PT donne l'inverse, les charges opposées se compensent, et une
  charge primitive se projette sur la réflexion avec carré central non trivial.
- Limite : aucun bundle principal `U(1)` monopolaire global n'est construit.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade, audit,
  usages et axiomes vérifiés après intégration le 2026-07-19.

### `PE-NORMALROOT-SPINC-CHERN-ARITHMETIC` — Séparation des nombres de Chern

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, arithmétique de Chern.
- But : combiner la racine normale plate, le twist primitif et le déterminant
  `SpinC` dans une même loi typée.
- Gate : `P0EFTJanusNormalRootSpinCDeterminantChernCompatibility4D`.
- Acceptation : magnitudes `0/1/2`, déterminant pair et rôles distincts.
- Limite : aucun accord de vrais bundles/classes globaux `Pin⁻`/`PinC`.
- Porte terminale : aucune.
- Validation : gate focalisé compilé en priorité `AboveNormal`; façade, audit,
  usages et axiomes vérifiés après intégration le 2026-07-19.

### `GEO-EFFECTIVE-DECORATED-CORE` — Noyau décoré canonique commun

- État : `DONE` (2026-07-19). Portée : `GLOBAL`, données géométriques D8.
- But : réunir sur un même quotient la métrique intrinsèque, la mesure
  canonique, PT, le throat lisse et le bundle principal ambiant `Pin⁻(4)`.
- Gate : `P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D`.
- Acceptation : objets réellement typés sur la même base, sans champs de statut.
- Limite : matière, `U(1)^2`, `PinC`, seconde métrique Candidate A générale et
  action complète non incluses ; `GEO-GLOBAL-01` reste ouvert.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `GEO-DECORATED-CONFORMAL-CANDIDATE-A` — Paire Candidate A conforme

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : étendre le noyau décoré par deux métriques conformes positives, leur
  racine intrinsèque et la densité Candidate A sur le même tangent.
- Gate : `P0EFTJanusCanonicalDecoratedConformalCandidateA4D`.
- Acceptation : carré exact et accord matriciel isotrope dans toute frame.
- Limite : aucune paire générale non conforme ; `GEO-GLOBAL-01` reste ouvert.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `GEO-CONFORMAL-ROOT-SMOOTH-FAMILY` — Lissité de la racine conforme

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : remplacer le seul coefficient ponctuel `sqrt(b/a)` par un vrai champ
  scalaire lisse et l'identifier à la famille de racines intrinsèques.
- Gate : `P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D`.
- Acceptation : ratio lisse positif, racine lisse, carré exact et identité avec
  la racine tangentielle déjà construite.
- Limite : ne prouve pas la lissité d'une racine générale non conforme.
- Porte terminale : aucune.
- Validation : gates compilés en priorité `AboveNormal`; façade, audit, usages
  et axiomes vérifiés après intégration le 2026-07-19.

### `GEO-CONFORMAL-ROOT-SMOOTH-OPERATOR` — Action lisse tangentielle

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : faire agir la racine conforme sur les vraies sections lisses du bundle
  tangent et obtenir un opérateur linéaire global.
- Gate : `P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D`.
- Acceptation : l'image de toute section lisse est lisse et l'évaluation
  ponctuelle coïncide exactement avec la racine intrinsèque.
- Limite : secteur conforme uniquement.
- Porte terminale : aucune.
- Validation : gates compilés en priorité `AboveNormal`; façade, audit, usages
  et axiomes vérifiés après intégration le 2026-07-19.

### `GEO-CONFORMAL-ROOT-GLOBAL-SQUARE` — Carré opératoriel global

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : construire l'opérateur relatif lisse `(b/a) id` sur les sections
  tangentielles et y promouvoir l'équation de carré de la racine.
- Gate : `P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D`.
- Acceptation : égalité de vrais opérateurs linéaires globaux, pas seulement
  égalité fibre par fibre.
- Limite : secteur conforme uniquement.
- Porte terminale : aucune.

### `GEO-CONFORMAL-ROOT-SMOOTH-INVERSE` — Inverse lisse global

- État : `DONE` (2026-07-20). Portée : `SECTORIELLE`, globale sur D8.
- But : certifier explicitement l'inverse de la famille conforme de racines.
- Gate : `P0EFTJanusMappingTorusSmoothConformalCandidateARootInverse4D`.
- Acceptation : la racine obtenue en échangeant les deux facteurs positifs est
  lisse et ses compositions gauche et droite avec la racine initiale valent
  l'identité sur les sections tangentielles lisses.
- Limite : secteur conforme uniquement ; aucune racine générale non conforme.
- Porte terminale : aucune.
- Validation : gates compilés en priorité `AboveNormal`; façade, audit, usages
  et axiomes vérifiés après intégration le 2026-07-19.

### `FIELD-DECORATED-COMMON-CORE` — Géométrie et champs sur la même base

- État : `DONE` (2026-07-19). Portée : `GLOBAL`, noyau canonique.
- But : réunir la géométrie décorée, le domaine champs/opérateurs/bord et le
  tangent complet dans un objet canonique unique.
- Gate : `P0EFTJanusCanonicalDecoratedProgramPFieldDomain4D`.
- Acceptation : configuration réelle PT-fixe, carré de racine, trace de bord
  et inclusion linéaire injective des variations, sans statut supposé.
- Limite : l'accord avec action, Hessien et domaine Fredholm reste ouvert ;
  `FIELD-GLOBAL-01` n'est pas fermé.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `FIELD-GENERAL-LORENTZ-CANONICAL-PACKET` — Champs à métriques générales

- État : `DONE` (2026-07-19). Portée : `GLOBAL`, configuration canonique.
- But : remplacer le scaffold diagonal par deux vraies métriques lorentziennes
  intrinsèques tout en conservant exactement les mêmes champs non métriques.
- Gate : `P0EFTJanusCanonicalDecoratedGeneralLorentzFieldPacket4D`.
- Acceptation : mêmes champs matière/jauge/ghosts/auxiliaires/LL, métriques du
  noyau décoré, paquet et trace de bord PT-fixes.
- Limite : les deux métriques canoniques sont égales ; paire générale distincte,
  racine et accord opératoriel encore ouverts. `FIELD-GLOBAL-01` reste ouvert.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `FIELD-PT-PAIRED-CONFORMAL-PACKET` — Deux métriques PT-appariées

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : produire depuis tout facteur conforme positif son partenaire PT et un
  paquet complet à deux métriques potentiellement distinctes.
- Gate : `P0EFTJanusCanonicalPTPairedConformalGeneralLorentzFieldPacket4D`.
- Acceptation : naturalité PT de la métrique conforme, racine opératorielle,
  mêmes champs non métriques, paquet et trace de bord PT-fixes.
- Limite : paire conforme seulement ; la paire non conforme générale et sa
  racine restent ouvertes. `GEO-GLOBAL-01` et `FIELD-GLOBAL-01` restent ouverts.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `FIELD-PT-PAIRED-CONFORMAL-DISTINCT-WITNESS` — Témoin distinct explicite

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : remplacer « potentiellement distinctes » par un exemple positif
  explicite donnant deux métriques PT-appariées réellement distinctes.
- Gate : `P0EFTJanusCanonicalPTPairedConformalGeneralLorentzFieldPacket4D`.
- Acceptation : mode sinus lisse descendu au quotient, facteur `2 + sin`
  strictement positif et non PT-fixe, injectivité du redimensionnement conforme,
  puis inégalité des deux métriques du paquet canonique explicite.
- Limite : le secteur non conforme général reste ouvert ; `GEO-GLOBAL-01` et
  `FIELD-GLOBAL-01` restent ouverts.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

## 6. Verrous globaux — ne pas distribuer comme petites cartes

Ces paquets exigent d'abord les ponts précédents. Un agent peut proposer un
lemme intermédiaire, mais ne doit pas annoncer leur fermeture partielle comme
fermeture globale.

| ID | Résultat global exigé | Dépendances principales |
|---|---|---|
| `GEO-GLOBAL-01` | Deux métriques Candidate A comme sections intrinsèques du même `T*⊗T*`, avec racine et densités identifiées aux modèles de coefficients. | `P-INTRINSIC-ROOT-01`, atlas tensoriel |
| `FIELD-GLOBAL-01` | Un espace de configurations/tangents unique pour métriques générales, matière, `U(1)^2`, ghosts, auxiliaires, LL, D9/D10 et bord. | `P-CV-MODULE-01`, `PE-PIN-CANONICAL-BUNDLE` |
| `ANALYSIS-GLOBAL-01` | Sobolev intrinsèque, trace du throat et domaines fermés communs. | cartes H¹ et Stokes |
| `BOUNDARY-GLOBAL-01` | EH+GHY+faces nulles+joints+LL sur la vraie géométrie, variation sans flux incontrôlé. | métriques intrinsèques, Stokes |
| `KJ-GLOBAL-01` | Opérateurs distincts `K_Gram`, `DK_Gram`, `K_SV`, `R`, `B_Noether`, `B_Bianchi` sur les vrais bundles. | champ/domaines communs |
| `KJ-GLOBAL-02` | Complexe global, identités, conditions au bord, cohomologie et quotient Sobolev. | `KJ-GLOBAL-01`, analyse globale |
| `NATURAL-GLOBAL-01` | Catégorie Janus, jets holonomes, bundles `Pin⁻`/`PinC` et classification naturelle finie des pairings/termes locaux. | bundle Pin réel, champs communs |
| `ACTION-GLOBAL-01` | Une action Candidate A covariante complète : EH, interaction, matière, Maxwell, LL et tous termes de bord. | géométrie, bord, classification naturelle |
| `EULER-GLOBAL-01` | Euler complet de cette action exacte sur toutes ses variables. | `ACTION-GLOBAL-01` |
| `NOETHER-GLOBAL-01` | Identités locales Noether/Bianchi pour ghosts arbitraires sur la même action. | Euler, `KJ-GLOBAL-01` |
| `HELMHOLTZ-GLOBAL-01` | Helmholtz non linéaire et reconstruction de cette même classe d'action. | Euler, Noether, complexe global |
| `VARCOH-GLOBAL-01` | Cohomologie variationnelle, lagrangiens nuls et ambiguïtés de bord classifiés. | classification naturelle, Helmholtz |
| `ADM-GLOBAL-01` | ADM dérivée, moments, contraintes primaires/secondaires, rang et crochet fonctionnel. | action/variation de bord |
| `STABILITY-GLOBAL-01` | Fermeture des contraintes, absence du mode BD ou rejet, stabilité du quotient, limite faible et PPN. | `ADM-GLOBAL-01` |
| `DIRAC-GLOBAL-01` | Vrai Dirac géométrique Janus signé, domaine global commun et famille Fredholm lisse. | champs/bundles/domaines communs |
| `BRST-GLOBAL-01` | Complexe BRST/BV non linéaire complet sur la même action et les mêmes conditions au bord. | champs, Noether, domaines |
| `HESSIAN-GLOBAL-01` | Seconde variation de la même action = opérateur Fredholm naturel gauge-fixé ; dégénérescence avant quotient et descente après quotient. | action, BRST, Sobolev, Fredholm |
| `REGULATOR-GLOBAL-01` | Régulateur commun, vrais spectres, multiplicités et statistiques de tous les secteurs/ghosts. | Dirac, Hessien, BRST |
| `QUILLEN-GLOBAL-01` | Indice familial et ligne/gerbe avec géométrie Quillen/Bismut–Freed naturelle. | famille Fredholm, régulateur |
| `ANOMALY-GLOBAL-01` | Anomalies locale/globale, eta analytique, APS/inflow et annulation PT pour le contenu complet. | Quillen, régulateur commun |
| `SCHEME-GLOBAL-01` | Contre-termes covariants, parties finies microscopiques et indépendance de schéma. | classification locale, anomalie globale, principe microscopique |
| `MICRO-GLOBAL-01` | Parent bulk/junction ou principe microscopique sélectionnant Candidate A. | entrée physique absente du dépôt actuel |
| `VACUUM-GLOBAL-01` | Action effective complète, branches stationnaires, vide unique et stabilité contrainte. | action, anomalies, schéma, sélection |
| `SCALE-GLOBAL-01` | Normalisation, unités et échelle absolue sans ajustement à un rayon observé. | principe microscopique, vide |

`MICRO-GLOBAL-01` et `SCALE-GLOBAL-01` sont actuellement
`BLOQUÉ-PHYSIQUE`. Aucun LLM ne doit les rendre vrais par définition ou par
choix arbitraire de constantes.

## 7. Les 14 portes terminales fixes

Le compteur global utilise uniquement cette liste. Une porte exige un
théorème concret sur les objets canoniques, pas un champ `Prop` supposé dans
un `ProgramStatus` arbitraire.

- [ ] `T01` — Revalider toutes les fondations et pairings par un certificat
  typé et compilé sur les objets globaux communs.
- [ ] `T02` — `invariantLocalFunctionalBasisClassified`.
- [ ] `T03` — `fullEulerLagrangeOperatorDerived`.
- [ ] `T04` — `nonlinearHelmholtzConditionsProved`.
- [ ] `T05` — `variationalBicomplexObstructionVanishing`.
- [ ] `T06` — `nullLagrangiansAndBoundaryTermsClassified`.
- [ ] `T07` — `anomalyConstraintsApplied`.
- [ ] `T08` — `parentBulkOrMicroscopicSelectionPrincipleDerived`.
- [ ] `T09` — `actionNormalizationDerived`.
- [ ] `T10` — `finiteCountertermsFixedMicroscopically`.
- [ ] `T11` — `globalActionClassReconstructed`.
- [ ] `T12` — `hessianMatchesNaturalFredholmFamily`.
- [ ] `T13` — `uniqueStableVacuumDerived`.
- [ ] `T14` — `absoluteScaleDerivedNoFit`.

Programme P atteint 100 % uniquement lorsque **T01–T14** sont toutes fermées
sur la même géométrie, le même espace de champs, la même action, les mêmes
domaines et le même régulateur.

## 8. Intégration et audit à renforcer

Carte `AUDIT-01`, état `DONE` (2026-07-19), portée `DOCUMENTAIRE/OUTILLAGE` :

- faire lire à `scripts/audit_janus_program_p.py` les identifiants `T01–T14` ;
- associer à chaque porte module, théorème pleinement qualifié, portée et type
  attendu ;
- rejeter une preuve constituée seulement d'un champ `Prop` supposé ;
- vérifier que chaque module est importé par la façade ;
- vérifier l'absence de `sorry`, `admit`, axiome métier et contrat contenant la
  conclusion ;
- générer un décompte unique réutilisé par roadmap, dashboard et TODO ;
- interdire qu'un nouveau microlemme modifie le dénominateur terminal.

Cette carte améliore la fiabilité du suivi mais ne ferme aucune porte
scientifique.

Validation : l'audit lit exclusivement la section fixe `T01–T14`, impose le
dénominateur `14`, affiche le décompte terminal `0/14` et rejette toute porte
cochée sans `TerminalGateEvidence`. Chaque évidence doit fournir module,
façade, théorème pleinement qualifié, portée et fragment de type ; le module
doit être importé, sans placeholder, et le théorème ne peut pas être un simple
contrat `ProgramStatus`. L'audit complet est vert le 2026-07-19. Aucune porte
terminale n'est fermée.
