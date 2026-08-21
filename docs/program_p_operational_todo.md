# Programme P — registre opérationnel canonique

Date de référence : 2026-07-26.

## 1. Rôle de ce document

Ce fichier est l'unique file de travail active de Programme P. L'ancien
registre exhaustif à cases a été supprimé : ses compteurs étaient obsolètes et
mesuraient surtout l'accumulation de microlemmes. Son historique reste
consultable dans Git.

La fermeture globale est mesurée uniquement par les **14 portes terminales**
de la section 7. État actuel : **0/14**. Une preuve locale, pointwise,
finite-mode, réduite ou conditionnelle ne ferme jamais une porte globale.

En cas de contradiction entre prose et code, le type exact du théorème Lean
compilé fait autorité.

### Synthèse active au 2026-08-19

Les quatorze portes restent la mesure finale. Leur travail restant se regroupe
maintenant en six lots, sans compter les adaptateurs déjà compilés :

1. **Validation globale (`T01`)** : reconstruire la façade Programme P et
   exécuter l'audit terminal sur l'ensemble du graphe, pas seulement les gates
   ciblées.
2. **Calcul variationnel global (`T02`--`T06`)** : promouvoir les résultats
   chartwise vers l'atlas physique brut, puis fermer Euler global, Helmholtz
   non linéaire, bicomplexe local et classification des lagrangiens nuls/bords.
3. **Hessien, Fredholm et déterminant (`T07`, `T12`)** : construire les trois
   données physiques restantes H10--H14 (famille locale `C²`, sept extensions
   continues, obstruction finie/coercivité), identifier la famille naturelle
   Candidate-A et compléter le vrai noyau/D11.
4. **Chaleur, Mellin et BF (`T07`, `T12`)** : instancier pour la référence de
   base et chaque cut local le spectre ProductThroat, l'identification de
   l'opérateur de chaleur, les expansions de Bochner et estimations
   insertion/primitive, le contre-terme court, la continuation Mellin
   paramétrique, puis les deux identités BF/families-index multidimensionnelles.
   Les assemblages génériques finite-part (avec propagation depuis un seul
   basepoint court), bord Green, identité Duhamel, continuité uniforme de la
   série longue, champ dérivé paramétrique, Schwarz et atlas base/local sont
   désormais construits et compilés. La continuité temporelle du reste court
   et un seul majorant intégrable au basepoint engendrent maintenant la
   mesurabilité et l'intégrabilité de toute la famille courte ; l'atlas ainsi
   obtenu utilise le poids Mellin canonique `t⁻¹` et est raccordé exactement
   au spectre ProductThroat Candidate-A, à son opérateur de chaleur par
   équivalence isométrique ; l'expansion réelle canonique en déduit désormais
   seule la trace nucléaire (facteur de réalification `2`), sans hypothèse de
   normalisation séparée. La dérivée nucléaire `(-t)D(t)` est aussi engendrée
   par le certificat de `D(t)`, et un commutateur nucléaire certifié force sa
   trace à zéro. La régularité temporelle de la trace est dérivée de la
   série spectrale lisse ; la combinaison finie des profils de contre-terme
   engendre aussi automatiquement sa continuité et sa dérivée paramétrique.
   Le reste sphérique existant fournit directement l'intégrabilité au
   basepoint, sans majorant auxiliaire, et les trois profils réduits
   `t⁻¹`, `1`, `t` sont continus sur l'intervalle court. Son paquet quadratique
   alimente désormais directement l'assembly Schwarz différentiable. Sur la
   partie longue, le facteur réel `2` engendre l'intégrabilité de la trace de
   chaleur depuis le gap spectral ; la continuité locale uniforme des termes
   de rang un et une borne intégrable sur la somme de leurs normes engendrent
   maintenant aussi l'intégrabilité Bochner de l'opérateur complet. En amont
   de la fermeture NamedKernel, le paquet H12 stable-physical-form existant et
   le transport D11 différentiable engendrent désormais directement une base de `ker(H₀)`,
   la famille complète des vrais noyaux, la régularité globale du Gram et la
   constance du rang. Les frontends plus primitifs acceptent alternativement
   une estimation globale de Gårding, ou l'orthogonalité interne aux secteurs
   avec le gap cinq-secteurs sur le complément du span ; l'orthogonalité entre
   secteurs est dérivée automatiquement du frontier.
   Les preuves concrètes précédentes restent les entrées mathématiques.
5. **Sélection microscopique (`T08`--`T11`)** : fournir un principe parent-bulk,
   fixer normalisation et contre-termes finis, puis sélectionner une unique
   classe d'action globale. Les no-go actuels interdisent de fermer ce lot par
   simple convention.
6. **Vide et échelle (`T13`, `T14`)** : démontrer la stabilité globale sur le
   quotient contraint et fournir une donnée dimensionnée indépendante fixant
   l'échelle absolue.

Aucun de ces regroupements ne modifie le compteur terminal tant que le gate
global correspondant n'est pas construit, importé et audité.

Les champs `Limite` des cartes `DONE` décrivent la frontière historique au
jour de leur validation. Ils ne constituent plus une tâche active lorsqu'une
carte ultérieure les ferme. L'arriéré actif est formé uniquement des cartes
dont l'état n'est pas `DONE`, des verrous globaux de la section 6 et des portes
terminales de la section 7.

## 2. Protocole de travail

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

Dans un workspace partagé, un seul intégrateur modifie la façade, l'audit et
ce registre. Une carte n'est déclarée fermée qu'après compilation directe de
son gate et de la façade.

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

## 4. Registre des cartes intermédiaires

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

### `P-STOKES-CUT-01` — Green–Stokes sur le bulk coupé au throat — `DONE`

- État : `DONE` (2026-07-21). Portée : `GLOBAL` sur le domaine
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
  cutoff est constant. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceMeasuredStokes4D`
  prolonge désormais la divergence locale recollée aux deux faces par la densité
  canonique, identifie sous Euler la mesure poussée obtenue à la mesure genuine
  déjà construite et lui applique le Stokes orienté à deux feuilles. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeMetricCollarMeasureBridge4D` montre
  ensuite que le collier muni du vrai jacobien `cos²(normal)` se pousse
  exactement sur le morceau positif du volume lorentzien intrinsèque, lequel
  est une sous-mesure du volume complet. Elle confirme aussi que la mesure nue
  précédente ne doit pas leur être identifiée. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D`
  pondère ensuite la divergence locale recollée par cette mesure exacte : sa
  densité est précisément la divergence normale densitisée plus la compensation
  tangentielle pondérée, et sa mesure intrinsèque positive est construite. Le
  contrat résiduel `CanonicalLatitudeCenteredMetricTangentialCancellation`
  isole exactement l'annulation intégrée manquante et implique immédiatement
  le Stokes complet. Ce contrat, puis le Stokes métrique complet, sont déjà
  prouvés sans hypothèse supplémentaire dans le sous-secteur Euler--Dirichlet,
  où le courant de Green est identiquement nul. Plus généralement, l'intégrale
  métrique complète se factorise sous Euler en un coefficient scalaire fois le
  flux de Green mesuré. Ce coefficient est prouvé strictement non dégénéré :
  le contrat tangentiel est donc exactement équivalent à la nullité du flux
  mesuré. Enfin, la gate
  `P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceFullEulerBridge4D`
  montre que les vraies équations d'Euler 4D sur l'atlas total annulent la
  divergence de Green dans toute carte adaptée et suppriment donc l'hypothèse
  locale `hFree`. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceOrientedBoundaryObstruction4D`
  identifie alors exactement le verrou : sous Euler, le Stokes métrique complet
  équivaut à la nullité du flux orienté à deux feuilles. L'annulation deck-odd
  déjà prouvée pour l'intégrale non orientée ne peut pas la remplacer. Il reste
  donc à obtenir la nullité du flux par le théorème de divergence global orienté
  sur le bulk coupé. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeEulerWronskianNoGo4D` formalise le
  contre-exemple élémentaire masse nulle `1`/`id` : les deux équations d'Euler
  normales sont satisfaites mais leur Wronskien vaut `1`. Une condition globale
  de secteur/cohomologie est donc nécessaire. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudeOrientedFluxOddSymmetry4D` donne un
  critère global non circulaire suffisant : une symétrie mesurable de la base,
  préservant la mesure et rendant le courant ponctuellement impair, annule le
  flux orienté et ferme le Stokes métrique sous Euler. Le prochain verrou est
  désormais partiellement levé par la gate
  `P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D` : elle prouve
  que PT inverse la coordonnée normale après retour au domaine fondamental et
  instancie le critère pour deux champs scalaires individuellement PT-fixes.
  Leur flux orienté est nul et le Stokes métrique est fermé sous Euler. Hors de
  ce secteur PT-fixe, il reste à fournir l'annulation de la classe de période
  par une condition globale admissible ou un argument cohomologique. La gate
  `P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D` construit en
  outre le projecteur canonique de Reynolds `½(id + PT)` sur ce secteur, prouve
  qu'il est idempotent et caractérise exactement ses points fixes. Le flux
  orienté de deux champs projetés est donc nul sans hypothèse supplémentaire ;
  la gate
  `P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjectionEuler4D` prouve
  maintenant que PT puis ce projecteur préservent exactement le résidu et les
  solutions d'Euler normales. Le Stokes métrique projeté est donc fermé à
  partir des seules équations d'Euler des champs initiaux, sans hypothèse Euler
  supplémentaire sur leurs projections. Enfin, la gate finale proposée
  `P0EFTJanusMappingTorusCutOpenScalarStokes4D` existe désormais : elle expose
  la formule mesurée générale, l'obstruction métrique exacte par la période
  orientée, et les fermetures concrètes Dirichlet, PT-fixe et PT-projetée. La
  carte est close sans instancier le contrat Stokes circulaire ; la période
  non nulle hors de ces secteurs reste explicitement une obstruction, pas une
  preuve manquante de cette carte.

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
- Limite historique : matière, `U(1)^2`, `PinC`, seconde métrique Candidate A
  et action complète n'étaient pas incluses. La géométrie globale est désormais
  portée par le domaine de racine admissible et l'action régulière est
  désormais fermée par `ACTION-GLOBAL-01`.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `GEO-DECORATED-CONFORMAL-CANDIDATE-A` — Paire Candidate A conforme

- État : `DONE` (2026-07-19). Portée : `SECTORIELLE`, globale sur D8.
- But : étendre le noyau décoré par deux métriques conformes positives, leur
  racine intrinsèque et la densité Candidate A sur le même tangent.
- Gate : `P0EFTJanusCanonicalDecoratedConformalCandidateA4D`.
- Acceptation : carré exact et accord matriciel isotrope dans toute frame.
- Limite : cette gate ne construit que le sous-domaine conforme. La gate
  globale accepte toute paire munie d'une racine réelle lisse; elle n'affirme
  pas la fausse existence universelle hors de ce domaine admissible.
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
- Limite historique : l'espace global unique, l'action, l'Euler et la
  Hessienne chartwise sont maintenant fermés. L'identification de cette
  Hessienne au domaine Fredholm géométrique reste séparée sous
  `HESSIAN-GLOBAL-01`; la composante DIRAC géométrique est fermée.
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
- Limite historique : les deux métriques de cette ancienne gate sont égales.
  Elle est désormais subsumée par la configuration globale à paire générale
  racine-admissible.
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
- Limite : paire conforme seulement; elle fournit un constructeur concret du
  domaine global racine-admissible, sans prétendre couvrir les paires frappées
  par l'obstruction spectrale réelle.
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
- Limite : témoin conforme explicite seulement; le domaine global autorise les
  autres paires exactement lorsqu'une racine réelle lisse est fournie.
- Porte terminale : aucune.
- Validation : gate compilé en priorité `AboveNormal`; façade, audit, usages et
  axiomes vérifiés après intégration le 2026-07-19.

### `P-T01-COMMON-VECTOR-PAIRING` — Pairing vectoriel sur le domaine commun

- État : `DONE` (2026-07-21). Portée : `POINTWISE/GLOBAL-TYPED`.
- Gate : `P0EFTJanusProgramPCommonVectorPairingBridge4D`.
- Résultat : équivalence exacte entre le modèle vectoriel P-D et la vraie
  coordonnée tangente D9 ; la classification invariante est transportée aux
  variations lisses complètes du domaine géométrique commun, avec certificat
  canonique compilé.
- Limite : les pairings spin-two, spinor et BRST, puis leur globalisation en
  module naturel, restent requis ; `T01` reste ouverte.
- Porte terminale : aucune ; prérequis direct de `T01`.

### `P-T01-COMMON-SPINTWO-PAIRING` — Pairing spin-two sur le domaine commun

- État : `DONE` (2026-07-21). Portée : `POINTWISE/GLOBAL-TYPED`.
- Gate : `P0EFTJanusProgramPCommonSpinTwoPairingBridge4D`.
- Résultat : changement de coordonnées exact entre le vrai tenseur traceless
  D9 et le modèle spin-two ; l’unique pairing invariant devient exactement le
  pairing de Frobenius, à une normalisation près, sur les variations métriques
  globales du domaine commun.
- Limite : les pairings spinor et BRST, puis la globalisation en module naturel,
  restent requis ; `T01` reste ouverte.
- Porte terminale : aucune ; prérequis direct de `T01`.

### `P-T01-COMMON-GHOST-PAIRING` — Pairing ghost sur le domaine commun

- État : `DONE` (2026-07-21). Portée : `POINTWISE/GLOBAL-TYPED`.
- Gate : `P0EFTJanusProgramPCommonGhostPairingBridge4D`.
- Résultat : les deux labels historiques sont reliés aux deux coordonnées de
  l’algèbre de Lie `U(1)²` D9 ; la classification du pairing dirigé est exacte.
  Ces labels ne sont pas un couple ghost/antighost nonminimal.
- Limite : les vrais types distincts `c/c̄/B` existent désormais dans les
  gauge fermions D9, mais leur chart lisse global et leur pairing intégré
  restent à construire ; `T01` reste ouverte.
- Porte terminale : aucune ; prérequis direct de `T01`.

### `P-T01-SPINOR-COORDINATE-NOGO` — Le rang quatre ne choisit pas le pairing

- État : `DONE` (2026-07-21). Portée : `RÉDUIT/GLOBAL-TYPED`.
- Gate : `P0EFTJanusProgramPCommonSquaredSpinorPairingNoGo4D`.
- Résultat : deux formes bilinéaires de formes différentes sont transportées
  par la même équivalence `MatterFiber ≃ D9SquaredSpinorCoordinateFiber` ; le
  simple raccord de coordonnées ne peut donc sélectionner le pairing spinor.
- Déverrouillage requis : construire l’action géométrique `SpinC`/Clifford et
  sa structure hermitienne sur le vrai bundle, puis classifier ses invariants.
- Porte terminale : aucune ; obstruction explicite sur le chemin de `T01`.

### `P-T01-RANKTWO-SPINC-HERMITIAN` — Pairing hermitien Clifford SpinC

- État : `DONE` (2026-07-21). Portée : `ALGÉBRIQUE/RANG-DEUX`.
- Gate : `P0EFTJanusProgramPRankTwoSpinCHermitianPairing4D`.
- Résultat : le caractère naturel `(spin, phase) ↦ spin·phase` tue le sous-groupe
  diagonal `(-1,-1)`, descend au vrai quotient `CliffordSpinC2` et agit
  unitairement sur une ligne complexe ; son pairing hermitien est invariant et
  non dégénéré.
- Limite : cette représentation algébrique locale n’est pas encore associée à
  un bundle `SpinC` global sur la géométrie Janus ni au `MatterFiber` commun.
- Porte terminale : aucune ; prérequis direct du pairing spinor de `T01`.

### `P-T01-RANKTWO-SPINC-CLASSIFICATION` — Unicité du pairing spinor local

- État : `DONE` (2026-07-21). Portée : `ALGÉBRIQUE/RANG-DEUX`.
- Gate : `P0EFTJanusProgramPRankTwoSpinCHermitianClassification4D`.
- Résultat : toute forme sesquilinéaire sur la ligne spinor complexe est un
  multiple unique du pairing hermitien canonique ; toute cette famille est
  invariante sous le caractère `CliffordSpinC2` construit précédemment.
- Limite : classification locale de fibre seulement ; descente sur le bundle
  Janus et identification au champ matière commun restent ouvertes.
- Porte terminale : aucune ; ferme la classification spinor locale requise par
  `T01`, sans fermer sa globalisation.

### `P-T01-RANKTWO-SPINC-CECH-DESCENT` — Descente Čech du pairing spinor

- État : `DONE` (2026-07-21). Portée : `CONDITIONNEL/MULTI-CHART`.
- Gate : `P0EFTJanusProgramPRankTwoSpinCCechHermitianDescent4D`.
- Résultat : toute présentation Čech principale `CliffordSpinC2` fournit la
  ligne complexe associée ; pour deux sections compatibles, le pairing
  hermitien est exactement indépendant de la carte sur chaque overlap.
- Limite : le théorème consomme une présentation Čech ; il ne dérive pas encore
  le bundle principal multi-chart de la géométrie Janus effective.
- Porte terminale : aucune ; réduit la globalisation spinor de `T01` à la
  construction du bundle principal Janus réel.

### `P-T01-NORMAL-Z4-HERMITIAN` — Métrique hermitienne de la racine normale

- État : `DONE` (2026-07-21). Portée : `GLOBAL/COL-EFFECTIF`.
- Gate : `P0EFTJanusProgramPNormalZ4RootHermitianMetric4D`.
- Résultat : les transitions de la vraie ligne complexe `NormalZ4Root` du col
  sont unitaires pour tout winding ; le pairing hermitien canonique est donc
  non dégénéré et exactement indépendant des coordonnées de bundle.
- Limite : cette ligne globale du col n'est pas encore identifiée au bundle
  spinor ambiant associé au bundle principal `Pin⁻(4)` de Janus.
- Porte terminale : aucune ; fournit le premier pairing hermitien sur un vrai
  bundle global Janus et rapproche `T01` du pont `Pin⁻ → PinC/spinor`.

### `P-T01-NORMAL-Z4-PIN-ASSOCIATION` — Ligne racine associée au Pin⁻ normal

- État : `DONE` (2026-07-21). Portée : `GLOBAL/COL-EFFECTIF`.
- Gate : `P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D`.
- Résultat : un caractère unitaire explicite `Pin⁻(1) ≃ ZMod 4 → U(1)`
  induit exactement tous les changements de cartes de la ligne complexe
  `NormalZ4Root`; le même winding est identifié à la restriction au col des
  transitions du vrai bundle principal ambiant `Pin⁻(4)`.
- Limite : l'association est prouvée sur la restriction normale cyclique ; une
  représentation spinor du groupe `PinC(4)` ambiant complet reste à construire.
- Porte terminale : aucune ; ferme le pont global `Pin⁻` normal vers la ligne
  hermitienne et isole désormais le vrai verrou `PinC(4)` ambiant.

### `P-T01-AMBIENT-PINC-CECH` — Extension PinC du cocycle ambiant

- État : `DONE` (2026-07-21). Portée : `GLOBAL/ALGÉBRIQUE-MULTI-CHART`.
- Gate : `P0EFTJanusProgramPAmbientPinCCechExtension4D`.
- Résultat : le groupe ambiant
  `PinC(4) := (Pin⁻(4) × U(1))/⟨(-1,-1)⟩` et son quotient diagonal sont
  construits ; le vrai cocycle multi-chart du bundle principal `Pin⁻(4)` est
  extrait de son `FiberBundleCore` puis poussé en un cocycle `PinC(4)` global.
- Limite : cette présentation Čech est algébrique ; continuité du quotient,
  vrai `FiberBundleCore PinC(4)` et représentation spinor restent ouverts.
- Porte terminale : aucune ; déverrouille la prochaine carte topologique puis
  l'association d'un vrai bundle spinor ambiant.

### `P-T01-AMBIENT-PINC-ACTUAL-BUNDLE` — Bundle principal PinC ambiant réel

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE`.
- Gate : `P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D`.
- Résultat : la topologie quotient rend `PinC(4)` groupe topologique ; le vrai
  cocycle continu `Pin⁻(4)` est poussé en un `FiberBundleCore PinC(4)` sur le
  quotient ambiant Janus, avec action droite équivariante, libre et transitive.
- Limite : la représentation spinor complexe de `PinC(4)`, son bundle associé
  et son pairing hermitien global restent à construire.
- Porte terminale : aucune ; ferme la globalisation principale `PinC(4)` et
  déplace le verrou de `T01` sur le module spinor ambiant associé.

### `P-T01-AMBIENT-PINC-DETERMINANT` — Secteur déterminant du PinC canonique

- État : `DONE` (2026-07-21). Portée : `GLOBAL/OBSTRUCTION-EXPLICITE`.
- Gate : `P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D`.
- Résultat : le caractère déterminant `PinC(4) → U(1)` est construit comme le
  carré de la phase et descend bien le quotient diagonal ; sur le bundle
  canonique induit par `(pin,1)`, toutes ses transitions valent exactement `1`.
- Limite : ce bundle ne porte donc pas encore le secteur monopole/déterminant
  non trivial requis par le modèle physique.
- Porte terminale : aucune ; isole le prochain verrou réel : construire un
  twist principal `U(1)` global compatible, puis le module spinor associé.

### `P-T01-AMBIENT-PINC-TWISTED-CECH` — Réduction au cocycle U(1) ambiant

- État : `DONE` (2026-07-21). Portée : `GLOBAL/ALGÉBRIQUE-CONDITIONNEL`.
- Gate : `P0EFTJanusProgramPAmbientPinCTwistedCechBundle4D`.
- Résultat : tout cocycle `U(1)` sur la couverture ambiante canonique se
  combine au vrai cocycle `Pin⁻(4)` en un cocycle `PinC(4)` ; son caractère
  déterminant est exactement le carré de la transition `U(1)`. Le twist
  trivial redonne transition par transition le bundle `PinC` canonique.
- Limite : aucun cocycle `U(1)` ambiant non trivial n'est encore construit ;
  les gates monopole existantes ne donnent que des données locales ou de
  Chern arithmétiques.
- Porte terminale : aucune ; réduit le prochain verrou à construire un vrai
  cocycle `U(1)` non trivial compatible avec la couverture ambiante.

### `P-T01-AMBIENT-U1-WINDING` — Bundle U(1) ambiant issu du winding

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE`.
- Gate : `P0EFTJanusProgramPAmbientCircleWindingBundle4D`.
- Résultat : le vrai winding entier des recouvrements ambiants, évalué dans
  chacun des deux caractères quart-de-tour, définit un `FiberBundleCore U(1)`
  continu et le cocycle exigé par le twist `PinC`. Sa restriction compatible
  au col est la racine normale existante, et le générateur a carré `-1`.
- Limite : la non-trivialité de sa classe de Chern ordinaire n'est pas
  affirmée ; cette phase est le secteur de winding/racine normale, pas encore
  une preuve du monopole primitif global.
- Porte terminale : aucune ; débloque la construction du vrai bundle
  principal `PinC(4)` twisté et de son déterminant non trivial.

### `P-T01-AMBIENT-PINC-WINDING-ACTUAL` — Bundle PinC twisté réel

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE`.
- Gate : `P0EFTJanusProgramPAmbientWindingTwistedPinCActualBundle4D`.
- Résultat : les transitions continues du vrai bundle `Pin⁻(4)` et du bundle
  `U(1)` de winding sont envoyées dans
  `(Pin⁻(4) × U(1))/⟨(-1,-1)⟩`, donnant un vrai `FiberBundleCore PinC(4)`.
  Son déterminant vaut transition par transition le carré de la phase de
  winding ; sur le recouvrement réel d'un tour de deck il vaut explicitement
  `-1`, contrairement au bundle canonique à phase unité.
- Limite : la classe de Chern monopole primitive et la représentation spinor
  complexe associée ne sont pas encore construites.
- Porte terminale : aucune ; débloque désormais la construction du module
  spinor ambiant associé et de son pairing hermitien.

### `P-T01-AMBIENT-PINC-DETERMINANT-LINE` — Ligne déterminant associée

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE-HERMITIEN`.
- Gate : `P0EFTJanusProgramPAmbientPinCDeterminantLineBundle4D`.
- Résultat : le caractère déterminant continu du vrai bundle `PinC(4)` twisté
  agit sur `ℂ` et construit un `FiberBundleCore` complexe associé. Son pairing
  hermitien est préservé par tous les changements de cartes et son changement
  de carte d'un tour vaut explicitement `-id`.
- Limite : cette ligne de rang un n'est pas le module spinor ambiant ; la
  représentation complexe Clifford-compatible de `PinC(4)` reste à fournir.
- Porte terminale : aucune ; ferme le secteur ligne déterminant et réduit le
  verrou spinor à la représentation ambiante elle-même.

### `P-T01-AMBIENT-CLIFFORD-GAMMA` — Représentation gamma ambiante

- État : `DONE` (2026-07-21). Portée : `GLOBAL/ALGÉBRIQUE`.
- Gate : `P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D`.
- Résultat : quatre matrices gamma complexes explicites satisfont la relation
  de Clifford quadratique ambiante et induisent un morphisme d'algèbres continu
  de l'algèbre de Clifford vers `Mat₄(ℂ)`.
- Limite : cette carte seule ne fournit ni la descente `PinC(4)` ni le bundle.
- Porte terminale : aucune ; fournit la représentation requise par la descente.

### `P-T01-AMBIENT-PINC-SPINOR-REP` — Représentation spinorielle PinC

- État : `DONE` (2026-07-21). Portée : `GLOBAL/ALGÉBRIQUE`.
- Gate : `P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D`.
- Résultat : l'action gamma de `Pin⁻(4)` et l'action scalaire de `U(1)` tuent
  explicitement `(-1,-1)` et descendent en une représentation de `PinC(4)` sur
  `ℂ⁴`, compatible avec la relation quadratique de Clifford.
- Limite : la préservation hermitienne globale reste une carte séparée.
- Porte terminale : aucune ; débloque le bundle spinor associé réel.

### `P-T01-AMBIENT-PINC-SPINOR-ACTUAL` — Bundle spinor ambiant réel

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE`.
- Gate : `P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D`.
- Résultat : les transitions continues du vrai bundle `PinC(4)` twisté agissent
  sur `ℂ⁴` et construisent un véritable `FiberBundleCore` spinoriel.
- Limite : l'invariance du pairing hermitien et la classe de Chern monopole
  primitive ne sont pas encore établies.
- Porte terminale : aucune ; réduit le prochain verrou spinor à l'hermiticité.

### `P-T01-AMBIENT-PINC-SPINOR-HERMITIAN` — Métrique spinorielle globale

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE-HERMITIEN`.
- Gate : `P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D`.
- Résultat : le pairing hermitien standard non dégénéré sur `ℂ⁴` est préservé
  par les quatre actions gamma du caractère `ZMod 4`, par toute phase `U(1)`
  et donc par chaque changement de carte du vrai bundle spinor ambiant.
- Limite : cette carte ne construit pas encore l'opérateur de Dirac global ni
  la classe de Chern monopole primitive.
- Porte terminale : aucune ; ferme le verrou du module spinor hermitien ambiant.

### `P-T01-AMBIENT-HALF-SPINOR-D9` — Pont spinoriel de rang D9

- État : `DONE` (2026-07-21). Portée : `GLOBAL/ALGÉBRIQUE-TYPÉE`.
- Gate : `P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D`.
- Résultat : le caractère `ZMod 4` ambiant préserve explicitement un bloc
  complexe de rang deux de la représentation Dirac `ℂ⁴`. Ce bloc possède le
  rang réel quatre attendu et une équivalence linéaire canonique explicite avec
  le `MatterFiber` D9.
- Limite : le `FiberBundleCore` global de ce demi-spinor et son transport vers
  le champ commun D9 restent à construire.
- Porte terminale : aucune ; ferme le mismatch de rang qui bloquait le pont D9.

### `P-T01-AMBIENT-HALF-SPINOR-ACTUAL` — Bundle demi-spinor réel

- État : `DONE` (2026-07-21). Portée : `GLOBAL/TOPOLOGIQUE-TYPÉE`.
- Gate : `P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D`.
- Résultat : l'inclusion et la projection linéaires continues du bloc `ℂ²`
  extraient du vrai bundle Dirac ambiant un `FiberBundleCore` complexe de rang
  deux ; chaque transition du bundle `ℂ⁴` préserve explicitement ce sous-bundle.
- Limite : son pairing doit encore être transporté vers le `MatterFiber` D9 et
  injecté dans le certificat du domaine commun.
- Porte terminale : aucune ; globalise le rang spinor exactement attendu par D9.

### `P-T01-D9-MATTER-SPINOR-HERMITIAN` — Pairing spinor du champ commun

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D`.
- Résultat : le pairing hermitien du demi-spinor global est non dégénéré puis
  transporté par l'équivalence linéaire canonique sur le vrai `MatterFiber`
  D9 ; le changement de carte correspondant préserve exactement ce pairing.
- Limite : le domaine commun doit encore enregistrer ce changement de carte
  comme bundle de champs/sections, au-delà de ses coefficients locaux.
- Porte terminale : aucune ; ferme le pairing spinor typé qui manquait à `T01`.

### `P-T01-D9-MATTER-SPINOR-ACTUAL` — Bundle spinor du champ D9

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorActualBundle4D`.
- Résultat : le bundle demi-spinor est transporté par l'équivalence linéaire
  continue en un vrai `FiberBundleCore MatterFiber`; son pairing hermitien D9
  reste invariant sous tous les changements de cartes.
- Limite : les coefficients `d9MatterCoefficient` restent des fonctions locales
  et doivent encore être empaquetés comme sections compatibles de ce bundle.
- Porte terminale : aucune ; fournit enfin l'objet bundle attendu par le domaine.

### `P-T01-THROAT-MATTER-SPINOR-PULLBACK` — Bundle spinor sur la gorge

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D`.
- Résultat : le bundle `MatterFiber` ambiant est tiré en arrière le long de
  l'inclusion canonique de la gorge en un vrai `FiberBundleCore`; son pairing
  hermitien reste invariant sous les changements de cartes tirés en arrière.
- Limite : il reste à remplacer les coefficients de matière triviaux par des
  sections compatibles avec ce bundle.
- Porte terminale : aucune ; fournit le bundle exact sur la base de D9.

### `P-T01-D9-MATTER-SPINOR-SMOOTH-BUNDLE` — Bundle vectoriel spinoriel lisse

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D`.
- Résultat : la représentation de monodromie `gamma × racine quartique`
  sur `MatterFiber` est réelle-linéaire et satisfait exactement le cocycle;
  chaque monodromie possède l'inverse continu explicite de winding opposé,
  et ces transitions localement constantes définissent un `VectorBundleCore`
  analytique, donc un vrai `ContMDiffVectorBundle` sur la gorge.
- Limite : identifier ce modèle lisse au pullback ambiant existant, puis choisir
  une connexion compatible avant de construire le Dirac.
- Porte terminale : aucune ; ferme la régularité du bundle nécessaire au
  terme cinétique spinoriel.

### `P-T01-D9-MATTER-SPINOR-SMOOTH-PULLBACK-BRIDGE` — Identification deck

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D`.
- Résultat : pour tout winding entier, le changement de carte du pullback
  ambiant est exactement la monodromie `gamma × racine quartique` du bundle
  lisse; cette action préserve le pairing et les sections spinorielles déjà
  migrées satisfont explicitement la même loi deck.
- Limite : construire une connexion hermitienne compatible et son action de
  Clifford avant de définir le Dirac géométrique.
- Porte terminale : aucune ; identifie les présentations utilisées par le bundle
  lisse, le pullback ambiant et l'espace de sections D9.

### `P-T01-D9-MATTER-SPINOR-FLAT-COVER-CONNECTION` — Connexion plate sur le revêtement

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D`.
- Résultat : la dérivée de variété ordinaire d'une section spinorielle lisse
  sur le revêtement est construite et satisfait exactement la covariance sous
  tout deck entier, avec la monodromie `gamma × racine quartique`.
- Limite : empaqueter cette loi comme dérivée covariante globale sur le bundle
  et ajouter l'action de Clifford.
- Porte terminale : aucune ; ferme la loi de recollement différentielle requise
  avant la construction du Dirac géométrique.

### `P-T01-D9-MATTER-SPINOR-FLAT-HERMITIAN` — Compatibilité hermitienne

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D`.
- Résultat : pour deux sections lisses arbitraires et toute direction tangente,
  la dérivée plate du pairing est exactement la somme des deux pairings avec
  la dérivée de chaque argument ; la connexion plate est donc hermitienne sur
  le revêtement.
- Limite : construire l'action de Clifford.
- Porte terminale : aucune ; ferme la compatibilité métrique requise avant le
  Dirac géométrique.

### `P-T01-D9-MATTER-SPINOR-GLOBAL-COVARIANT-DERIVATIVE` — Dérivée covariante globale

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorGlobalCovariantDerivative4D`.
- Résultat : une dérivée en coordonnées de trivialisation préférée est
  transportée dans chaque fibre et empaquetée comme un vrai
  `CovariantDerivative` Mathlib sur le bundle spinoriel D9 ; son additivité et
  sa règle de Leibniz sont prouvées pour toute section différentiable.
- Limite : prouver sa régularité comme `ContMDiffCovariantDerivative`.
- Porte terminale : aucune ; ferme le type global de connexion requis avant
  l'action de Clifford et le Dirac.

### `P-T01-D9-MATTER-SPINOR-SMOOTH-SECTION-DESCENT` — Descente lisse des sections

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D`.
- Résultat : toute section lisse deck-équivariante définit une vraie section
  dépendante du bundle quotient ; ses coordonnées dans chaque trivialisation
  sont exactement le lift composé avec l'inverse local, et sa section de
  l'espace total est lisse.
- Limite : empaqueter si nécessaire cette preuve dans l'API
  `ContMDiffSection` sans alourdir l'élaboration.
- Porte terminale : aucune ; ferme la descente lisse requise par la connexion.

### `P-T01-D9-MATTER-SPINOR-FLAT-GLOBAL-BRIDGE` — Identification des connexions

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorFlatGlobalConnectionBridge4D`.
- Résultat : sur toute section descendue, la dérivée covariante globale est
  exactement la dérivée plate du lift sur le revêtement, composée avec la
  dérivée de l'inverse local canonique du revêtement.
- Limite : régularité `ContMDiffCovariantDerivative`, action de Clifford puis
  opérateur de Dirac.
- Porte terminale : aucune ; ferme l'identification plate/globale.

### `P-T01-D9-MATTER-SPINOR-GLOBAL-HERMITIAN` — Compatibilité hermitienne globale

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorGlobalConnectionHermitian4D`.
- Résultat : pour deux sections descendues arbitraires et toute direction
  tangente, la dérivée globale du pairing est exactement la somme des pairings
  avec la dérivée covariante de chaque argument.
- Limite : migrer sections et connexion vers le bundle doublé construit par
  les cartes suivantes, puis définir l'opérateur de Dirac géométrique.
- Porte terminale : aucune ; ferme la compatibilité hermitienne globale.

### `P-T01-D9-MATTER-SPINOR-CLIFFORD-NOGO` — Obstruction de rang deux

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorCliffordActionNoGo4D`.
- Résultat : après retrait de la phase scalaire `U(1)`, la monodromie du
  demi-spinor est le générateur `J`; son centralisateur dans `M₂(ℂ)` est
  commutatif. Deux générateurs de Clifford inversibles et anticommutants ne
  peuvent donc pas tous commuter avec cette monodromie. Aucune action de
  Clifford 3D globale n'existe sur le seul demi-spinor D9 actuel.
- Limite : descendre le module doublé et son action de Clifford en bundle
  lisse, puis construire le Dirac.
- Porte terminale : aucune ; remplace une construction impossible par le
  verrou structurel exact.

### `P-T01-D9-MATTER-SPINOR-DOUBLED-CLIFFORD` — Frame de Clifford doublée

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D`.
- Résultat : le module `S ⊕ Sᵒᵖ` porte la transition normalisée
  `diag(J,-J)` et trois générateurs complexes linéaires explicites. Chacun
  carre à `-1`, ils anticommutent deux à deux et commutent exactement avec la
  transition deck doublée.
- Limite : migrer sections et connexion vers le vrai bundle lisse doublé,
  puis contracter Clifford avec la dérivée covariante pour le Dirac.
- Porte terminale : aucune ; fournit la première action de Clifford compatible
  avec la monodromie D9.

### `P-T01-D9-MATTER-SPINOR-DOUBLED-SMOOTH-BUNDLE` — Bundle lisse doublé

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D`.
- Résultat : le partenaire opposé est identifié à `oppositeRoot choice`; la
  somme des deux monodromies définit un vrai `VectorBundleCore` réel lisse.
  Après identification complexe, sa transition d'un tour est exactement la
  phase de racine multipliée par `diag(J,-J)`, donc par la transition compatible
  avec la frame de Clifford construite précédemment.
- Limite : descendre les paires de sections, transporter la connexion plate et
  globale, puis définir le Dirac.
- Porte terminale : aucune ; réalise géométriquement le module doublé.

### `P-T01-D9-MATTER-SPINOR-DOUBLED-SMOOTH-SECTIONS` — Sections lisses doublées

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D`.
- Résultat : toute paire de lifts lisses associés aux racines opposées
  satisfait la monodromie doublée et descend en une vraie section lisse du
  bundle doublé. Ses coordonnées dans chaque trivialisation locale sont
  exactement le lift local attendu.
- Limite : transporter la connexion plate et globale, puis construire le Dirac.
- Porte terminale : aucune ; fournit l'espace géométrique requis pour les
  champs de matière doublés.

### `P-T01-D9-MATTER-SPINOR-DOUBLED-GLOBAL-CONNECTION` — Connexion globale doublée

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D`.
- Résultat : le vrai bundle lisse doublé porte une `CovariantDerivative`
  globale canonique obtenue par dérivation dans la trivialisation locale ;
  les axiomes d'additivité et de Leibniz sont prouvés.
- Limite : identifier cette connexion à la connexion plate du revêtement,
  puis la contracter avec la frame de Clifford pour construire le Dirac.
- Porte terminale : aucune ; fournit la connexion globale requise par le Dirac.

### `P-T01-D9-MATTER-SPINOR-DOUBLED-FLAT-COVER-CONNECTION` — Connexion plate doublée

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D`.
- Résultat : la dérivée ordinaire de tout lift lisse doublé obéit à
  l'exacte covariance deck pour la monodromie doublée ; elle définit donc la
  connexion plate canonique sur le revêtement.
- Limite : prouver son identification avec la connexion globale du bundle,
  puis construire le Dirac.
- Porte terminale : aucune ; ferme la construction plate sur le revêtement.

### `P-T01-D9-MATTER-SPINOR-DOUBLED-FLAT-GLOBAL-BRIDGE` — Pont global/plat doublé

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D`.
- Résultat : sur toute section doublée descendue, la connexion globale est
  exactement la dérivée plate du lift composée avec la différentielle de
  l'inverse local de la projection du revêtement.
- Limite : contracter cette connexion avec la frame de Clifford compatible
  pour construire l'opérateur de Dirac D9.
- Porte terminale : aucune ; ferme l'identification connexion globale/plate.

### `P-T01-D9-MATTER-SPINOR-SECTION-NOGO` — Obstruction des champs actuels

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorSectionNoGo4D`.
- Résultat : une variation de matière constante explicitement admise par
  l'espace actuel échoue la transition spinorielle après un tour de gorge.
  Les `SmoothQuotientField MatterFiber` actuels ne peuvent donc pas servir
  directement de sections du bundle spinoriel non trivial.
- Limite : `T01` exige désormais une redéfinition ou une restriction typée du
  champ `matter` comme section compatible, puis la migration de ses usages.
- Porte terminale : aucune ; obstruction constructive et verrou suivant précis.

### `P-T01-THROAT-MATTER-SPINOR-SECTIONS` — Espace de sections spinorielles

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D`.
- Résultat : `SmoothThroatMatterSpinorLift` encode un coefficient lisse sur le
  revêtement de la gorge avec la loi d'équivariance exacte du bundle spinoriel;
  cet espace est non vide et contient la section nulle canonique.
- Limite : installer sa structure de module puis migrer le composant `matter`
  de `IndependentFieldVariation` et ses consommateurs D9/D10.
- Porte terminale : aucune ; fournit le type correct exigé par la migration.

### `P-T01-THROAT-MATTER-SPINOR-SECTION-MODULE` — Module des sections

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D`.
- Résultat : les changements de cartes `MatterFiber` sont explicitement
  additifs et réels-linéaires; les sections lisses équivariantes forment donc
  un `Module Real` utilisable comme espace de variations.
- Limite : migrer le composant `matter` sans casser les consommateurs existants.
- Porte terminale : aucune ; prérequis direct de la migration de `T01`.

### `P-T01-D9-MATTER-SPINOR-COEFFICIENT` — Coefficient D9 typé

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D`.
- Résultat : le nouveau coefficient D9 est évalué depuis une paire de sections
  spinorielles; sa loi de deck est prouvée et son pairing hermitien est invariant.
- Limite : remplacer progressivement l'ancien `d9MatterCoefficient` dans les
  assemblages de variation, d'action et de Hessien.
- Porte terminale : aucune ; premier pont de migration sans rupture d'API.

### `P-T01-SPINORIAL-COMPLETE-VARIATION` — Tangent complet spinoriel

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPSpinorialCompleteVariation4D`.
- Résultat : le nouveau tangent complet est le produit du tangent historique
  privé de sa matière triviale et de la vraie paire de sections spinorielles;
  il conserve une structure de module réelle et prouve l'ancienne matière nulle.
- Limite : migrer les consommateurs restants vers sa composante spinorielle.
- Porte terminale : aucune ; paquet de transition typé pour la migration.

### `P-T01-SPINORIAL-D9-ASSEMBLY` — Assemblage D9 migré

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D`.
- Résultat : le champ local D9 lit désormais son spinor depuis la vraie section;
  ses composantes bosoniques et ghost sont prouvées identiques à l'assemblage
  historique appliqué au tangent sans matière.
- Limite : migrer les usages d'action/Hessien et la branche D10.
- Porte terminale : aucune ; premier consommateur complet effectivement migré.

### `P-T01-SPINORIAL-D9-DOMAIN-REFINEMENT` — Contrat commun D9 raffiné

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPSpinorialD9DomainAgreementRefinement4D`.
- Résultat : tout contrat commun D7/D9/D10 existant reçoit un raffinement D9
  canonique sur le nouveau tangent spinoriel; les coordonnées normales et gauge
  restent celles du tangent historique sans matière, tandis que le spinor vient
  explicitement de la section équivariante.
- Limite historique : la coordonnée modale D10 et l'action/Hessien restaient
  sur l'ancien type. L'action globale consomme désormais le doublet SpinC;
  Hessien et famille D10 restent séparés.
- Porte terminale : aucune ; migre le point d'entrée central du domaine D9.

### `P-T01-D9-SPINOR-PAIRING-SMOOTH` — Pairing lisse des sections D9

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D`.
- Résultat : le pairing hermitien de deux vraies sections spinorielles est
  explicitement `C∞` sur le revêtement de la gorge; son auto-pairing est
  invariant sous tout winding deck et possède un certificat compilé.
- Limite : effectuer la descente lisse de cette densité vers le quotient gorge,
  puis l'utiliser dans l'action/Hessien migrés.
- Porte terminale : aucune ; ferme la régularité locale du pairing de `T01`.

### `P-T01-D9-SPINOR-PAIRING-DESCENT` — Descente globale du pairing D9

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorPairingDescent4D`.
- Résultat : l'auto-pairing lisse et deck-invariant descend effectivement en un
  `SmoothThroatField Complex` sur le quotient gorge; sa valeur sur un représentant
  est prouvée égale au pairing hermitien du coefficient spinoriel correspondant.
- Limite : injecter ce scalaire global dans l'action matière et sa variation.
- Porte terminale : aucune ; fournit la densité globale requise par `T01`.

### `P-T01-D9-SPINOR-REAL-DENSITY` — Densité réelle positive

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorRealDensity4D`.
- Résultat : la partie réelle de l'auto-pairing descendu définit un vrai
  `SmoothThroatField Real`; sa formule locale est exacte et sa positivité est
  démontrée par la somme des deux normes carrées complexes.
- Limite : choisir la mesure/couplage et intégrer cette densité dans l'action.
- Porte terminale : aucune ; fournit le terme scalaire positif de l'action D9.

### `P-T01-D9-SPINOR-MASS-ACTION` — Action de masse canonique

- État : `DONE` (2026-07-21). Portée : `GLOBAL/CHAMP-COMMUN`.
- Gate : `P0EFTJanusProgramPD9MatterSpinorMassAction4D`.
- Résultat : la densité spinorielle réelle est intégrable contre la mesure
  volumique canonique de la gorge; son intégrale pondérée par `m²/2` définit
  une action positive pour `m² ≥ 0`, nulle à masse ou variation nulle.
- Limite : construire le terme cinétique/Dirac, puis migrer variation et Hessien.
- Porte terminale : aucune ; fournit le premier terme d'action D9 authentiquement
  porté par les sections spinorielles globales.

### `P9-SPINC-GEOMETRIC-ZERO-MODE` — Mode zéro géométrique primitif

- État : `DONE` (2026-07-25). Portée : `GÉOMÉTRIQUE/PARTIELLE`.
- Gates : `P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D`.
- Résultat : les représentants lisses du mode monopolaire de Hopf et leur
  section SpinC globale sont construits dans les deux secteurs de racine. Le
  Dirac géométrique satisfait la règle de Leibniz locale, la section de Hopf
  satisfait son équation propre, et la synthèse finie du bloc zéro entrelace
  exactement le Dirac géométrique avec l'opérateur diagonal des fréquences
  normales corrigées.
- Limite : ce résultat réalise le bloc géométrique de valeur propre zéro, pas
  la tour géométrique complète ni son exhaustivité spectrale.
- Porte terminale : aucune ; avance `DIRAC-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-FIRST-POSITIVE` — Premier niveau positif géométrique signé

- État : `DONE` (2026-07-25). Portée : `GÉOMÉTRIQUE/PARTIELLE`.
- Gates : `P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereExhaustion4D`,
  `P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D`,
  `P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D`.
- Résultat : trois sections propres réelles linéairement indépendantes sont
  construites pour chacun des signes, non nulles, avec dégénérescence construite
  `3`; leur somme directe épuise exactement le bloc géométrique engendré de
  dimension `6`, et les équations propres de Dirac et de Dirac carré sont
  démontrées. Les six sections réalisent exactement les deux branches internes
  du spectre signé au premier niveau, indépendamment du secteur de racine.
  Leur synthèse à six coordonnées est injective et entrelace le vrai Dirac
  différentiel avec la diagonale signée, y compris après mise au carré.
- Limite : l'exhaustivité de l'espace propre, les niveaux positifs arbitraires et
  la complétude spectrale restent ouverts.
- Porte terminale : aucune ; avance `DIRAC-GLOBAL-01` et `REGULATOR-GLOBAL-01`.

### `P9-SPINC-LOW-ENERGY-FINITE-GEOMETRIC-FOURIER` — Pont Fourier géométrique fini

- État : `DONE` (2026-07-26). Portée : `GÉOMÉTRIQUE/MODES-FINIS`.
- Gates : `P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeFourierCoordinates4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeMovingLocal4D`,
  `P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeGeometricFourier4D`.
- Résultat : dans chaque secteur de racine fixé, tout paquet à support fini en
  modes du cercle du bloc zéro plus les deux blocs signés de première sphère
  possède une synthèse en vraies sections lisses qui est injective. Les deux
  témoins locaux mobiles et les quatre coordonnées complexes de fibre ramènent
  la séparation inter-modes au théorème Fourier fini existant; le vrai Dirac et
  son carré séparent ensuite les trois blocs, puis les témoins locaux existants
  récupèrent les sept coefficients complexes de chaque mode.
- Hypothèses : aucune nouvelle hypothèse physique ni aucun axiome métier.
- Limite : ce pont porte sur le bloc bas-énergie à support fini, pas sur les
  niveaux sphériques arbitraires, la complétion Hilbert/Sobolev, le domaine
  non borné commun ni l'exhaustivité spectrale.
- Porte terminale : aucune ; avance `DIRAC-GLOBAL-01`.

### `P9-SPINC-SIGNED-ABSTRACT-SPECTRUM` — Deux branches internes signées

- État : `DONE` (2026-07-26). Portée : `ANALYTIQUE/ABSTRAITE`.
- Gates : `P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D`,
  `P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D`,
  `P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D`,
  `P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D`.
- Résultat : le signe spectral interne `±` est séparé du fold PT; les carrés
  coïncident avec le spectre abstrait antérieur et les branches non nulles sont
  distinctes, sans doubler la tour zéro. Le spectre corrigé possède désormais
  une base de Hilbert complète, un domaine maximal dense, un opérateur
  auto-adjoint fermé et, dans le secteur quart-tordu physique, un gap `1/4`,
  une bijectivité, la propriété de Fredholm et l'indice nul.
- Limite : l'identification de cette base abstraite avec une famille complète
  de sections propres géométriques lisses reste le théorème de Fourier
  géométrique. Le segment à support fini des niveaux zéro et premier signés est
  maintenant fermé et la diagonalisation SpinC uniforme est traitée par la
  gate tous niveaux ci-dessous. Les niveaux `p=1`, `p=2` et `p=3` sont
  concrets; les deux derniers fournissent respectivement cinq quadratiques et
  sept cubiques sans trace linéairement indépendantes, avec leurs identités
  `D²` et leurs graines Dirac signées. Le paquet complexe est désormais
  construit uniformément à tout degré puis réalisé par de vraies sections
  lisses null-harmoniques. Sa récurrence donne `D²`, les graines signées,
  l’indépendance complexe exacte et une synthèse finie injective, désormais
  conjointement sur tous les niveaux positifs à secteur/mode fixé, avec
  entrelacement diagonal de `D²`. Les synthèses totales ci-dessous ferment
  aussi simultanément secteurs, modes, multiplicités et tour zéro. La
  complétion spectrale et l’analyse dense sont depuis fermées par
  `P9-SPINC-ALL-LEVEL-FINITE-HILBERT-COMPLETION`; reste l’égalité avec le
  produit géométrique intégral sur tout le cœur lisse.
- Porte terminale : aucune ; corrige la portée de `DIRAC-GLOBAL-01`.

### `P9-SPINC-COEFFICIENT-DOMAIN-UNITARY` — Domaine maximal SpinC/D10 étendu

- État : `DONE` (2026-07-27). Portée : `ANALYTIQUE/COEFFICIENTS`.
- Gate : `P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D`.
- Résultat : l’isométrie `L²` entre la tour SpinC complète et la somme du
  secteur sphérique zéro avec les modes D10 positifs transporte exactement le
  domaine maximal de `D²`. Elle conjugue les deux opérateurs non bornés et
  conserve leur énergie de graphe. Les poids des deux sommants sont identifiés
  respectivement au cercle quart-tordu et au spectre D10.
- Hypothèses : aucune nouvelle hypothèse physique ni aucun axiome métier.
- Limite : ce résultat ferme le transport unitaire du domaine de
  **coefficients**. Les eigenspinors géométriques lisses signés de niveau
  arbitraire sont désormais construits par
  `P9-SPINC-ALL-LEVEL-SIGNED-GEOMETRIC-REALIZATION`; leur comparaison
  hilbertienne intégrale reste séparée.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-FOURIER-COMPLETION` — Complétion canonique de l’analyse

- État : `DONE` (2026-07-27). Portée : `ANALYTIQUE/GÉOMÉTRIQUE`.
- Gate : `P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierCompletion4D`.
- Résultat : toute réalisation Fourier géométrique SpinC tous niveaux s’étend
  canoniquement en une équivalence isométrique réelle entre la complétion de
  son image lisse et le `L²` complet des coefficients. Le cœur lisse reste
  dense et injectif; le domaine maximal `H²`, l’opérateur `D²`, son accord sur
  le cœur et l’énergie de graphe sont transportés exactement. Le carré complété
  est en outre coercif et bijectif.
- Hypothèses : aucune au-delà de la réalisation géométrique déjà isolée; aucun
  axiome métier supplémentaire.
- Limite : cette gate ne construit pas la réalisation elle-même. Le paquet
  lisse tous degrés, son identité géométrique `D²`, son indépendance complexe
  inter-niveaux à secteur/mode fixé et sa synthèse finie diagonale injective
  sont maintenant construits. La séparation conjointe et la complétion
  spectrale sont depuis fermées; reste l’identification avec le produit
  géométrique intégral sur tout le cœur lisse.
- Porte terminale : aucune ; retire la complétion des résidus de
  `DIRAC-GLOBAL-01`.

### `P9-SPINC-ALL-LEVEL-HARMONIC-DIAGONALIZATION` — Diagonalisation géométrique uniforme

- État : `DONE` (2026-07-27). Portée : `DIRAC/GÉOMÉTRIQUE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D`.
- Résultat : pour tout niveau sphérique positif, les sections scalaire et
  gradient d’un germe harmonique forment un bloc Dirac exact `2×2`. Ses deux
  combinaisons canoniques sont des eigensections lisses de fréquences opposées;
  `D²`, le sous-espace engendré et l’accord exact avec le spectre D9/D10 complet
  sont démontrés. À multiplicité arbitraire, les blocs propres `±` sont
  disjoints et leur somme épuise exactement le paquet scalaire/gradient. Le
  bloc entier est en outre reconstruit à partir d’une seule section propre de
  `D²`; les deux équations du premier ordre ne sont donc pas des obligations
  indépendantes. L’action complexe intrinsèque fournit automatiquement les
  compagnons imaginaires et conserve la valeur propre sur toute la ligne
  complexe (fidèle dès que le générateur est non nul). Le niveau `p=1` redonne
  littéralement les eigensections déjà construites et habite aussi cette
  interface réduite. En outre, la multiplication globale d’une vraie section
  lisse par un scalaire lisse, son reste de Clifford-gradient et la règle de
  Leibniz sont maintenant construits. Appliqués au mode zéro de Hopf, ils
  démontrent sans hypothèse la première équation du bloc. Une tour de scalaires
  munie de la seule identité de Lichnerowicz/`D²` produit automatiquement la
  tour `D²`, la tour Dirac signée et ses paquets; les coordonnées `p=1`, les
  cinq quadratiques sans trace indépendantes de `p=2` et les sept cubiques
  sans trace indépendantes de `p=3` réalisent concrètement cette interface.
- Hypothèses : aucun axiome métier. La récurrence null-harmonique construit
  désormais elle-même l’identité géométrique de second ordre et les deux
  équations du premier ordre.
- Limite : le paquet complexe homogène est réalisé uniformément, pour tout
  `p`, par des sections lisses du fibré quotient. La croissance stricte de
  `p(p+1)` sépare les espaces propres de `D²` : l’indépendance et la synthèse
  finie diagonale sont donc fermées conjointement sur tous les niveaux
  positifs à secteur/mode fixé. La séparation conjointe et l’analyse dense
  complétée sont depuis fermées. Le raccord exact de ces branches aux labels
  signés complets est fermé par la gate suivante. Parseval et la complétion
  sont aussi fermés séparément sur chaque branche et chaque bloc signé.
  Restent leurs multiplicités attendues, leur orthogonalité inter-blocs,
  l’assemblage hilbertien conjoint et la densité.
  Les niveaux
  `p=1`, `p=2` et `p=3` ne sont plus des obligations distinctes.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` à la complétude
  analytique globale.

### `P9-SPINC-ALL-LEVEL-SIGNED-GEOMETRIC-REALIZATION` — Spectre signé géométrique complet

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/PREMIER-ORDRE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D`.
- Résultat : pour chaque niveau positif, secteur normal, mode cercle,
  multiplicité et branche interne `±`, la tour null-harmonique fournit une
  vraie section lisse du fibré SpinC quotient. Elle vérifie exactement
  l’équation de Dirac de premier ordre avec la valeur propre du modèle
  Fredholm signé. Les deux spans de branches d’un bloc sont disjoints et leur
  somme est exactement le bloc scalaire/Clifford-gradient. La tour sphérique
  zéro non doublée est également réalisée pour tout `period ≠ 0`; lorsque le
  period est positif, l’involution PT secteur/mode corrige exactement le signe
  orienté, et lorsque le period est négatif l’identité convient. Ainsi chaque
  label signé complet possède un représentant géométrique lisse exact.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier, aucune hypothèse
  de complétude ni choix d’orientation supplémentaire.
- Limite : chaque branche et chaque bloc signé possède ses coordonnées de
  Parseval, sa complétion fermée et son finrank physique exact. Les deux
  signes d’un label fixé et tous les labels signés distincts sont désormais
  orthogonaux; la somme jointe globale est construite. Reste seulement sa
  densité dans toute la complétion géométrique.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-SECOND-POSITIVE-SPHERE` — Paquet quadratique `p=2`

- État : `DONE` (2026-07-27). Portée : `DIRAC/GÉOMÉTRIQUE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D`.
- Résultat : les produits `nᵢnⱼψ` et leurs partenaires tangentiels satisfont
  un système Dirac exact. L’anticommutation Clifford donne la correction de
  trace `-2δᵢⱼψ`; elle s’annule sur cinq combinaisons quadratiques sans trace,
  qui vérifient `D²=(k²+6)`. Les cinq scalaires lisses associés et les cinq
  véritables sections propres lisses sont linéairement indépendants; le
  transfert aux sections utilise cinq valeurs locales non nulles du mode de
  Hopf et la même matrice d’évaluation rationnelle explicite. Leur cardinal
  vaut la dégénérescence `2p+1=5`, et chacun produit les deux branches propres
  signées via l’interface Lichnerowicz.
- Hypothèses : aucun axiome métier ni identité spectrale ajoutée.
- Limite : ce jalon est conservé comme contrôle réel explicite de `p=2`; la
  construction null-harmonique générique ferme maintenant tous les degrés
  géométriquement.

### `P9-SPINC-THIRD-POSITIVE-SPHERE` — Paquet cubique `p=3`

- État : `DONE` (2026-07-27). Portée : `DIRAC/GÉOMÉTRIQUE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCThirdPositiveSphereDirac4D`.
- Résultat : le bloc cubique brut et son partenaire tangentiel satisfont les
  deux équations de Dirac récursives. La correction de trace s’annule sur sept
  cubiques harmoniques réels sans trace, donnant sept véritables eigensections
  lisses avec `D²=(k²+12)`. Les scalaires et les sections sont linéairement
  indépendants par une matrice d’évaluation rationnelle à sept témoins locaux
  non nuls. Leur cardinal vaut `2p+1=7` et chacun engendre les deux graines
  Dirac signées.
- Hypothèses : aucun axiome métier ni identité spectrale ajoutée.
- Limite : ce jalon est conservé comme contrôle réel explicite de `p=3`; la
  construction null-harmonique générique ferme maintenant tous les degrés
  géométriquement. La complétude inter-niveaux reste globale.

### `P9-SPINC-ALL-LEVEL-SOLID-HARMONIC-PACKET` — Paquet uniforme tout degré

- État : `DONE` (2026-07-27). Portée : `DIRAC/ALGÉBRIQUE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D`.
- Résultat : la courbe nulle complexe
  `(1-t², I(1+t²), 2t)` engendre à tout degré `p` un paquet de cardinal
  physique exact `2p+1`. Chaque membre est homogène, son Laplacien ambiant
  est nul et l’opérateur sphérique algébrique `E(E+1)-r²Δ` donne exactement
  l’énergie `p(p+1)`. Une évaluation sur la même courbe réduit
  l’indépendance linéaire à une matrice de Vandermonde; elle est démontrée
  uniformément, sans développer `p=4`, `p=5`, etc.
- Hypothèses : aucun axiome métier ni identité spectrale ajoutée.
- Limite : la réalisation lisse complexe et son identification à `D²` sont
  fermées par la gate suivante. Une base réelle canonique n’est pas nécessaire
  pour la multiplicité complexe physique. La complétude globale reste ouverte.
- Porte terminale : aucune ; remplace tous les futurs paquets
  niveau-par-niveau par un unique pont géométrique.

### `P9-SPINC-ALL-LEVEL-NULL-HARMONIC-DIRAC` — Réalisation lisse uniforme

- État : `DONE` (2026-07-28). Portée : `DIRAC/GÉOMÉTRIQUE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D`.
- Résultat : les puissances de la forme linéaire nulle agissent directement
  sur le mode de Hopf dans le véritable fibré SpinC quotient. Une unique
  récurrence en `p` démontre les équations de premier ordre et l’identité
  géométrique `D²` à tout niveau, puis engendre les deux branches signées.
  L’évaluation locale et le paquet de Vandermonde prouvent que les `2p+1`
  sections sont complexes-linéairement indépendantes. La croissance stricte
  de l’énergie sphérique sépare les espaces propres de `D²`, donc ces paquets
  sont conjointement indépendants sur tous les niveaux positifs à
  secteur/mode fixé. Leur synthèse à support fini est injective et vérifie
  exactement `D² S = S Λ` pour l’opérateur diagonal explicite des
  coefficients. Avec la tour de Hopf zéro, chaque étiquette du spectre carré
  complet possède des représentants lisses réel et imaginaire intrinsèque.
- Hypothèses : aucun axiome métier et aucune hypothèse de Lichnerowicz ou de
  niveau supplémentaire.
- Limite : cette carte ferme l’axe inter-niveaux à secteur/mode fixé. La carte
  suivante ferme l’axe secteurs/modes à niveau fixé, puis la carte
  `P9-SPINC-ALL-POSITIVE-JOINT-SPECTRAL` combine les deux axes, puis la carte
  complète suivante ajoute la tour zéro. La carte de complétion finie ferme
  ensuite l’analyse dense et la complétion spectrale. Le raccord géométrique
  de premier ordre à tous les labels signés est désormais fermé; restent son
  orthogonalisation/intégration par blocs et la densité globale.

### `P9-SPINC-FIXED-LEVEL-JOINT-FOURIER` — Séparation conjointe à tout niveau fixé

- État : `DONE` (2026-07-28). Portée : `DIRAC/GÉOMÉTRIQUE/SUPPORT-FINI`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D`.
- Résultat : le doublement du temps de revêtement identifie les secteurs
  `positiveQuarter` et `negativeQuarter` aux indices Fourier impairs et pairs.
  L’index conjoint secteur–mode s’injecte donc dans `ℤ`. Pour tout niveau
  positif arbitraire `p`, l’évaluation locale mobile sépare simultanément les
  deux secteurs et tous les modes du cercle; la relation polynomiale
  null-harmonique annule ensuite les `2p+1` multiplicités. La synthèse complexe
  à support fini sur
  `(secteur × mode du cercle) × multiplicité` est injective, et la famille
  correspondante est complexe-linéairement indépendante.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier, aucune nouvelle
  condition physique et aucun développement niveau par niveau.
- Limite : le niveau est arbitraire mais fixé dans cette carte. La synthèse
  simultanée tous niveaux positifs est fermée par la carte suivante.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-ALL-POSITIVE-JOINT-SPECTRAL` — Synthèse spectrale positive totale

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/SUPPORT-FINI`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D`.
- Résultat : une seule famille lisse est indexée simultanément par les deux
  secteurs, tous les modes du cercle, tous les niveaux sphériques positifs et
  leurs `2p+1` multiplicités. La séparation par espaces propres de `D²`
  réduit chaque collision spectrale à un paquet à niveaux assignés, où le
  réindexage Fourier et le paquet null-harmonique donnent l’indépendance.
  La famille totale est donc complexe-linéairement indépendante, sa synthèse
  à support fini est injective et vérifie exactement `D² S = S Λ`.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni choix physique
  supplémentaire.
- Limite : cette carte porte seulement les niveaux positifs. La carte
  suivante ajoute la tour zéro. La carte de complétion finie ferme ensuite
  l’analyse dense et la complétion spectrale; reste l’égalité avec la norme
  géométrique intégrale globale.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-ALL-LEVEL-FULL-SPECTRAL` — Synthèse géométrique complète

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/SUPPORT-FINI`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D`.
- Résultat : le paquet à niveaux assignés est étendu à tout niveau
  sphérique non négatif. La séparation des collisions de `D²` donne alors
  l’indépendance complexe simultanée de la tour de Hopf zéro, de tous les
  niveaux positifs, des deux secteurs, de tous les modes du cercle et de
  toutes les multiplicités. Sur l’index canonique
  `PrimitiveSpinCGeometricFullMode`, la synthèse à support fini est injective
  et vérifie exactement `D² S = S Λ` pour le diagonal spectral complet déjà
  utilisé par la complétion.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni choix physique
  supplémentaire.
- Limite : l’indépendance algébrique et l’entrelacement sur le cœur fini sont
  fermés. La carte suivante ferme aussi sa complétion dans la norme spectrale.
  Le produit `L²` géométrique indépendant, Parseval par bloc et l’isométrie
  jointe vers son span fermé sont désormais construits pour la famille
  scalaire. Les branches signées/gradient possèdent aussi leur réalisation
  hilbertienne finie bloc par bloc, leurs finranks exacts, toute
  l’orthogonalité inter-labels et leur somme jointe globale. Reste leur
  densité dans tout le cœur SpinC complété.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-ALL-LEVEL-FINITE-HILBERT-COMPLETION` — Complétion du cœur spectral géométrique

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-SPECTRAL`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFiniteHilbertCompletion4D`.
- Résultat : la synthèse injective identifie les coefficients à support fini
  avec leur véritable span de sections SpinC lisses. L’analyse canonique de
  ce span est injective et dense dans le `L²` complet des coefficients. La
  norme induite en fait un cœur préhilbertien dont la complétion est
  canoniquement unitaire au `L²`. Le domaine maximal `H²` et `D²` sont
  transportés exactement; l’opérateur complété prolonge le vrai `D²`
  différentiel sur le cœur, est coercif et bijectif.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni choix physique
  supplémentaire.
- Limite : la norme utilisée est induite par les coefficients. Le produit
  géométrique indépendant, sa complétion et Parseval sur chaque bloc de
  multiplicité sont désormais construits. Les modes cercle distincts d’un
  même secteur, les secteurs opposés et les niveaux distincts à secteur/mode
  fixé sont orthogonaux et leur somme hilbertienne est une isométrie à image
  fermée exactement décrite pour les blocs scalaires. Les finranks, toute
  l’orthogonalité et l’assemblage signés sont également fermés, avec un
  unitaire inconditionnel sur leur image spectrale fermée. La gate de
  complétude Fourier--monopôle ci-dessous ferme ensuite sa densité ambiante.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-PAIRING-COMPLETION` — Produit et complétion `L²` géométriques

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D`.
- Résultat : le produit hermitien doublé descend à travers toutes les
  transitions du véritable fibré SpinC primitif. Son évaluation sur deux
  sections lisses est lisse et intégrable contre le volume canonique de la
  gorge. L’intégrale est sesquilinéaire, hermitienne et définie positive; elle
  induit une norme complexe et une complétion hilbertienne dans laquelle le
  cœur lisse est dense.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni définition par
  coefficients spectraux.
- Limite : Parseval est exact dans chaque bloc fini et entre modes cercle
  distincts d’un même secteur; les secteurs opposés sont également
  orthogonaux, ainsi que les niveaux distincts à secteur/mode fixé. Restent la
  densité spectrale dans cette complétion et l’équivalence unitaire globale.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-SIGNED-BRANCH-COMPLETION` — Complétion géométrique des blocs signés

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/PREMIER-ORDRE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D`.
- Résultat : à niveau positif, secteur et mode fixés, chaque branche signée
  engendre un sous-espace fini du véritable cœur SpinC. Sa base orthonormale
  canonique fournit Parseval, une isométrie vers la complétion géométrique,
  une image fermée et l’entrelacement exact avec le Dirac de premier ordre.
  Les branches `+` et `-` sont disjointes comme espaces propres de valeurs
  propres distinctes. Leur bloc total possède à son tour Parseval, une image
  complétée fermée et l’entrelacement exact avec `D²`.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni orthogonalité
  postulée.
- Limite : les bases sont indexées par le `finrank` géométrique démontré; son
  égalité à la multiplicité physique attendue est établie par la gate suivante.
  Les gates gradient/Casimir et jointe signée ferment l’orthogonalité dans
  chaque bloc, entre tous labels distincts et l’assemblage global. Reste la
  densité de son image fermée dans la complétion géométrique entière.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-SIGNED-MULTIPLICITY` — Multiplicités géométriques signées exactes

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/PREMIER-ORDRE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D`.
- Résultat : l’action radiale de Clifford sépare algébriquement la partie
  scalaire (`+i`) de la partie gradient (`-i`) dans toute relation signée.
  Comme le coefficient radial signé ne s’annule jamais et que le paquet
  scalaire nul est déjà indépendant, chaque famille signée brute est
  complexe-linéairement indépendante. Chaque signe a donc exactement le
  finrank physique `2p+1`, et le bloc deux signes exactement `2(2p+1)`.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier.
- Limite : la séparation radiale et la disjonction des espaces propres sont
  algébriques; l’orthogonalité intégrale des deux signes dans un bloc fixé est
  désormais fermée par la gate gradient/Casimir. Restent les labels spectraux
  distincts, la somme hilbertienne jointe et son exhaustion.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-BLOCK-ORTHONORMALIZATION` — Parseval géométrique par bloc

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/SPECTRAL`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D`.
- Résultat : pour chaque triplet niveau sphérique/secteur racine/mode cercle,
  Gram–Schmidt est appliqué au paquet nul canonique dans le véritable produit
  `L²` intégral. La famille obtenue est orthonormale, engendre exactement le
  même sous-espace lisse et chaque vecteur conserve la même équation
  géométrique `D²`. Sa synthèse depuis l’espace euclidien fini est une
  isométrie linéaire avec identité de Parseval et entrelacement exact.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni orthogonalité
  artificiellement postulée.
- Limite : l’orthogonalité pour des modes cercle distincts dans un même
  secteur, entre secteurs opposés et entre niveaux distincts à secteur/mode
  fixé est désormais fermée. Leur somme hilbertienne est construite par la
  gate jointe ci-dessous. Les blocs signés sont orthonormalisés séparément et
  leurs finranks sont exacts; les signes opposés d’un même label et tous les
  labels spectraux distincts sont orthogonaux. Leur somme jointe globale et
  son unitaire sur l’image fermée sont construits; la densité ambiante est
  fermée par la gate de complétude Fourier--monopôle ci-dessous.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-FOURIER-ORTHOGONALITY` — Orthogonalité Fourier géométrique

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/SPECTRAL`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D`.
- Résultat : le produit quotient intégral est réduit exactement au domaine
  fondamental sphère ronde × intervalle temporel canonique. Dans les deux
  cartes monopôle, chaque paquet nul possède le même facteur Fourier mobile.
  L’intégrale temporelle annule donc exactement deux modes cercle distincts
  d’un même secteur, quels que soient niveaux et multiplicités. Le résultat
  vaut pour les familles brutes, leurs spans et les synthèses orthonormales
  de blocs. Les deux plans demi-spinoriels Hopf sont en outre orthogonaux :
  les secteurs racine opposés s’annulent point par point puis dans `L²`, pour
  tous niveaux, modes et multiplicités.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni hypothèse
  d’orthogonalité ajoutée.
- Limite : l’axe niveau est fermé par la gate Casimir dédiée ci-dessous.
  L’assemblage scalaire est fermé par la gate d’isométrie jointe. Les
  isométries finies signées, leur orthogonalité complète et leur assemblage
  global sont fermés. L’unitaire sur l’image spectrale fermée est
  inconditionnel; sa densité ambiante est fermée par la gate de complétude
  Fourier--monopôle ci-dessous.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-LEVEL-ORTHOGONALITY` — Orthogonalité géométrique inter-niveaux

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/SPECTRAL`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D`.
- Résultat : les rotations standards de la sphère sont reliées à leur
  champ infinitésimal et à la mesure ronde invariante. L’intégration par
  parties rend le Casimir de rotation symétrique. Les puissances nulles de
  degré `p` ont exactement la valeur propre `p(p+1)`; deux degrés distincts
  sont donc orthogonaux sans hypothèse ajoutée. Le calcul local du germe Hopf
  donne le facteur de norme exact `8`, puis Fubini transporte l’annulation aux
  vraies sections SpinC, aux blocs bruts, à leurs spans et aux synthèses
  normalisées.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier, aucune
  orthogonalité ni complétude postulée.
- Limite : les trois axes de séparation (secteur, mode cercle, niveau
  sphérique) sont fermés. Leur assemblage hilbertien et la description exacte
  de son image fermée sont fermés par la gate suivante.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-GRADIENT-CASIMIR` — Orthogonalité exacte des deux signes

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/PREMIER-ORDRE`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D`.
- Résultat : les identités Clifford/tangentielles du germe Hopf donnent la
  paire pointwise exacte des gradients reconstruits. L’intégration par
  parties annule le terme ambient–angulaire; le terme de Dirichlet est
  exactement le Casimir `p(p+1)` fois la paire scalaire. Après Fubini sur le
  vrai domaine sphère × temps, la paire `L²` des gradients vaut donc
  `p(p+1)` fois la paire scalaire. Le produit des coefficients scalaires des
  branches `+` et `-` vaut son opposé, d’où l’orthogonalité exacte des deux
  familles brutes puis de leurs spans complets dans chaque bloc fixé.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni orthogonalité
  postulée.
- Limite : l’orthogonalité des paquets signés portant des labels
  secteur/mode/niveau distincts et leur isométrie jointe sont fermées par la
  gate suivante. L’exhaustion de toute la complétion géométrique est fermée
  par la gate Fourier--monopôle ultérieure.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-JOINT-ISOMETRY` — Isométrie hilbertienne jointe

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/SPECTRAL`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D`.
- Résultat : les blocs euclidiens normalisés, indexés simultanément par niveau
  sphérique, secteur racine et mode cercle, forment une famille orthogonale
  d’isométries dans la complétion `L²` géométrique indépendante. Leur somme
  hilbertienne `ℓ²` définit une isométrie linéaire canonique. Son image est
  exactement la fermeture du span de tous les blocs explicites. La densité de
  cette image est équivalente à sa surjectivité et fournit alors
  canoniquement l’équivalence unitaire globale.
- Hypothèses : seulement `period ≠ 0`; aucune complétude spectrale ni densité
  postulée.
- Limite : la surjectivité scalaire n’est pas démontrée. La gate suivante
  ferme toutefois toute l’orthogonalité et l’isométrie jointe de la famille
  signée complète, tour zéro comprise.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-GEOMETRIC-L2-SIGNED-JOINT-ISOMETRY` — Isométrie signée globale

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/SPECTRAL-SIGNÉ`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D`.
- Résultat : les paquets signés sont orthogonaux dès qu’un label
  niveau/secteur/mode diffère. La tour zéro est orthogonale à tous les blocs
  positifs signés. Tous ces blocs Parseval s’assemblent donc en une isométrie
  canonique sur leur somme hilbertienne `ℓ²`. Son image est exactement la
  fermeture de leur span, et une équivalence unitaire inconditionnelle entre
  les coefficients globaux et cette image spectrale fermée est construite.
  La densité dans toute la complétion géométrique est équivalente à la
  surjectivité et fournit alors l’unitaire ambiant.
- Hypothèses : seulement `period ≠ 0`; aucune complétude spectrale, densité
  ou orthogonalité postulée.
- Limite : la densité de la famille signée explicite dans la complétion de
  toutes les sections lisses est fermée par la gate suivante.
- Porte terminale : aucune ; réduit `DIRAC-GLOBAL-01` et
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-FOURIER-MONOPOLE-CORE-COMPLETENESS` — Complétude géométrique signée

- État : `DONE` (2026-07-28). Portée :
  `DIRAC/GÉOMÉTRIQUE/HILBERT-INTÉGRAL/SPECTRAL-SIGNÉ`.
- Gate :
  `P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D`.
- Résultat : les polynômes monopôle et les modes de Fourier temporels
  approchent uniformément les huit coefficients du repère de Hopf signé.
  Leur réalisation par de vraies sections lisses donne une erreur ponctuelle
  quadratique intégrable. Toute section lisse appartient donc à la fermeture
  de la synthèse signée. La densité du cœur lisse et la fermeture déjà prouvée
  de l’image rendent cette synthèse surjective et produisent l’équivalence
  linéaire isométrique globale avec la complétion géométrique `L²`.
- Hypothèses : seulement `period ≠ 0` et les structures géométriques déjà
  construites; aucune hypothèse de complétude spectrale.
- Limite : aucune pour la complétude géométrique du DIRAC SpinC. Les blocs
  non-SpinC de la Hessienne globale restent séparés.
- Porte terminale : ferme `DIRAC-GLOBAL-01` et retire le résidu de densité de
  `HESSIAN-GLOBAL-01`.

### `P9-SPINC-SIGNED-MODE-HESSIAN-UNITARY` — Unitaire géométrique du Hessien signé

- État : `DONE` (2026-07-29). Portée :
  `HESSIAN/DIRAC/SPINC/CŒUR-LISSE/MAXIMAL`.
- Gates :
  `P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D`,
  `P0EFTJanusProgramPGlobalHessianFrontier4D`.
- Résultat : les blocs Fourier--monopôle complets sont raffinés aux labels
  signés individuels du Hessien. Une permutation PT involutive corrige
  exactement la tour zéro lorsque l’orientation de la période l’exige. La
  famille obtenue est orthonormale et donne un unitaire sur toute la
  complétion géométrique. Chaque vecteur lisse porte la vraie valeur propre du
  Dirac de premier ordre. Sur toute combinaison finie, le véritable opérateur
  différentiel `2D + m²` entrelace exactement le multiplicateur diagonal du
  Hessien; sa réalisation maximale est auto-adjointe et Fredholm pour toute
  masse, avec noyau résonant fini. Son domaine maximal est tiré explicitement
  sur le `L²` géométrique, où l’opérateur non borné transporté est exactement
  conjugué au multiplicateur coefficient.
- Hypothèses : seulement `period ≠ 0`; aucun axiome métier ni contrat de
  complétude supplémentaire.
- Limite : cette fermeture concerne le modèle géométrique/spectral SpinC.
  L’action matière primitive et son accord same-action sur le cœur fini sont
  fermés par la gate suivante; le chart global et les autres blocs restent
  dans `HESSIAN-GLOBAL-01`.
- Porte terminale : retire le résidu géométrique/spectral SpinC.

### `P-HESSIAN-D10FREE-SPINC-BRST-LL` — Contenu physique corrigé

- État : `DONE` (2026-07-30). Portée :
  `HESSIAN/CONTENU-DE-CHAMPS/SECTORIEL`.
- Gates :
  `P0EFTJanusProgramPGlobalFieldSpace4D`,
  `P0EFTJanusProgramPGlobalAnalysisDomain4D`,
  `P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D`,
  `P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D`,
  `P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D`,
  `P0EFTJanusFullLLSameActionFredholmRestriction4D`.
- Résultat : le tangent, le domaine et la cible physiques sont D10-free;
  l’extension D10 est réservée au régulateur/déterminant. La matière
  Candidate-A est directement une paire sectorielle de sections SpinC
  primitives et son action graphe a pour vrai second Fréchet le Fredholm
  `2D+m²`, avec accord sur le cœur fini. Les BRST D9 abélien/difféomorphisme
  utilisent des types distincts `c/c̄/B`, donnent exactement `s²=0`, `sΨ`, un
  Hessien symétrique et les symboles FP existants. Le Fredholm LL same-action
  est exact sur la tranche maximale prouvée
  `llAuxMetric = llMeasure = 0`.
- Limite : aucune de ces gates ne prétend assembler le Hessien total. Lorenz
  et de Donder sont maintenant globaux dans les gates ultérieures; manquent
  leur intégration au chart global `C²`, les blocs métrique/normal/Maxwell
  mixte/bord et leurs multiplicités. La gate graphe ultérieure couvre le
  Hessien LL complet, mais pas encore sa coercivité/Fredholm.
- Porte terminale : réduit `HESSIAN-GLOBAL-01`, sans le fermer.

Mise à jour `L²` bulk abélien étendu — 1 août 2026 :

- les cinq graphes déjà assemblés ont maintenant un produit Hilbert réel
  imbriqué `WithLp 2`, continûment linéairement équivalent à l'ancien produit à
  norme max; le graphe matière est lui aussi transporté vers sa norme `L²`;
- le cœur lisse reste injectif et dense; l'action `C²` est exactement la même
  action transportée, avec première variation et seconde variation constante;
- son Hessien bloc apparié possède un représentant de Riesz borné
  auto-adjoint. Cela ne prouve ni l'auto-adjonction du FP scalaire isolé, ni le
  chart total, ni la somme de Fredholm globale.

### `P9-D10-CONTINUUM-HEAT-REGULATOR` — Régulateur thermique D10 tous niveaux

- État : `DONE` (2026-07-27). Portée : `ANALYTIQUE/SPECTRALE`.
- Gates : `P0EFTJanusProgramPD10ContinuumHeatRegulator4D`,
  `P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D`.
- Résultat : le mode D10 complet est réindexé exactement par les deux racines,
  tous les niveaux sphériques avec leur multiplicité et tous les modes du
  cercle. À tout temps strictement positif, le poids thermique et le terme
  chiral sont sommables. La permutation PT conserve le spectre carré, inverse
  la chiralité, annule la trace infinie et tout filet cofinal de coupures finies
  converge vers zéro. La restriction aux modes tronqués est exactement
  l’ancien régulateur D10 fini. Sur le véritable espace de Hilbert D10, le
  régulateur est aussi un opérateur compact, somme nucléaire en norme
  d’opérateur de projecteurs de rang un; ses troncatures spectrales finies
  convergent en norme.
- Hypothèses : aucune nouvelle hypothèse physique ni aucun axiome métier.
- Limite : cela ferme le secteur spectral D10, pas encore le régulateur commun
  des blocs non spectraux matière–métrique–Maxwell–ghost–bord ni son identité
  avec la Hessienne complète.
- Porte terminale : aucune ; réduit `REGULATOR-GLOBAL-01`.

### `P9-REGULATOR-PHYSICAL-LL-TEMPORAL-GHOST` — Ponts thermiques assemblés

- État : `DONE` (2026-07-30). Portée : `ANALYTIQUE/CONDITIONNELLE`.
- Gates : `P0EFTJanusProgramPD10AgreementHeatRegulatorBridge4D`,
  `P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D`,
  `P0EFTJanusMappingTorusTemporalGhostContinuumHeatRegulator4D`,
  `P0EFTJanusProgramPPhysicalLLTemporalGhostHeatRegulator4D`.
- Résultat : sous le contrat commun d’accord domaine/Hessienne, le régulateur
  D10 continuum se transporte à la variation complète, agit mode par mode
  comme `exp(-t Hessian)`, est contractant et préserve le domaine
  Fredholm/bord. Indépendamment, un même temps positif définit un opérateur
  borné sur l’ancienne somme étendue D9–matière–D10–LL et ghost temporel.
  Le sous-bloc ghost temporel
  spatialement constant possède maintenant son opérateur de chaleur continuum
  exact : spectre de la dérivée, compacité, décomposition nucléaire,
  cohomologie exacte du zéro-mode et annulation PT de la trace chirale, y
  compris à cutoff symétrique.
- Limite : le transport D10 reste conditionnel. Aucune compacité ni classe de
  trace n’est revendiquée pour la somme complète : la chaleur LL actuelle est
  compacte si et seulement si son espace d’énergie est de dimension finie; il
  manque aussi la croissance spectrale D9 et une réalisation LL elliptique à
  résolvante compacte/trace de chaleur.
  Les autres ghosts et blocs non spectraux, puis leur synthèse géométrique
  dense avec la Hessienne assemblée, restent ouverts.
- Porte terminale : aucune ; réduit `REGULATOR-GLOBAL-01` sans le fermer.

### `P-T01-AMBIENT-PINMINUS-LOCAL-SECTIONS-REDUCTION` — Fermeture du revêtement

- État : `DONE` (2026-07-25). Portée : `TOPOLOGIQUE`.
- Gates : `P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D`,
  `P0EFTJanusMappingTorusAmbientPinMinusCompactness4D`,
  `P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsClosure4D`,
  `P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsPropagation4D`,
  `P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D`,
  `P0EFTJanusMappingTorusAmbientPinMinusRealNormalRestrictionGauge4D`,
  `P0EFTJanusMappingTorusCanonicalLatitudeNormalPresentationComparison4D`.
- Résultat : Cartan–Dieudonné est borné à quatre réflexions, le groupe Pin
  concret est compact, le noyau de la projection est exactement `{±1}`, et la
  projection est un revêtement possédant les sections locales requises. Le
  cocycle Čech ambiant canonique est normalisé, inverse-cohérent, strictement
  cohérent sur les triples overlaps et définit le vrai bundle principal. Le
  normal réel possède également son cocycle Čech exact et cohérent. La
  zéro-cochaîne requise est maintenant construite explicitement par le vecteur
  de Clifford demi-angle normalisé `e+n`; elle entrelace tous les windings,
  réalise exactement la restriction et coïncide sur les overlaps sans choix
  de chemin. Sa continuité est prouvée pour tout champ normal horizontal,
  continu et non nul.
- Résultat complémentaire (2026-07-30) :
  `canonicalLatitudeNormalLift_contMDiff` et
  `canonicalLatitudeNormalCoordinate_contMDiffOn` donnent la régularité `C∞`
  intrinsèque, puis `canonicalLatitudeNormal_presentations_compare` transporte
  la représentation cover-produit vers une vraie trivialisation tangente du
  quotient et `canonicalLatitudeNormalCoordinate_eq_sectionPresentation`
  prouve l’égalité exacte des deux présentations au niveau normal zéro.
- Frontière exacte : ce pont ferme le sous-verrou de présentation `Pin⁻/T01`,
  pas le certificat terminal typé de fondations/pairings `T01`; ce n'est
  toujours pas une carte analytique autonome.
- Porte terminale : aucune ; réduction exacte d'un sous-verrou de `T01`.

### `P-LL-WEAK-JACOBI-SCOPE` — Hessien LL simultané et obstruction flux-only

- État : `DONE` (2026-07-25). Portée : `ANALYTIQUE/PARTIELLE`.
- Gates : `P0EFTJanusMappingTorusLLWeakJacobiGaugeComplex4D`,
  `P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D`,
  `P0EFTJanusMappingTorusLLGeneratingFrameVariation4D`,
  `P0EFTJanusMappingTorusLLGeneratingFrameFullHessian4D`,
  `P0EFTJanusMappingTorusLLGeneratingFrameElementaryFlows4D`.
- Résultat : le Hessien réel des trois slots typés (métrique auxiliaire, mesure,
  flux) donne un opérateur de Jacobi bilinéaire; une variation typée du repère,
  sa courbe exponentielle, son Hessien radial et le générateur diagonal à quatre
  slots sont construits. Le secteur radial possède maintenant une vraie courbe
  simultanée non gelée, son Hessien quatre slots avec termes croisés, sa
  symétrie, son Jacobi et son critère exact de noyau. Les taux exponentiels
  indépendants de chaque générateur et les cisaillements par un coefficient
  scalaire lisse donnent maintenant des courbes globales supplémentaires de
  vrais repères, avec vitesses exactes. Dans le secteur flux-only strictement
  positif, `J ∘ R = 0` équivaut à `R = 0`.
- Frontière exacte : le dépôt possède déjà la famille génératrice lisse, ses
  coefficients locaux et la reconstruction locale de tout tangent. Réaliser
  simultanément un tangent arbitraire exige seulement leur assemblage en une
  droite inverse lisse globale, puis un flot matriciel inversible; ce pont est
  rattaché à `HESSIAN-GLOBAL-01`, pas à une nouvelle carte LL.
  La direction de jauge générale n'est radiale que sous le critère affiché, et
  aucune dégénérescence injustifiée n'est affirmée.
- Porte terminale : aucune ; avance `HESSIAN-GLOBAL-01`.

### `P-FULL-ACTION-FRECHET-LINE-BRIDGE` — Pont Fréchet concret maximal

- État : `DONE` (2026-07-25). Portée : `ACTION/ANALYTIQUE-PARTIELLE`.
- Gates : `P0EFTJanusProgramPConcreteFullActionFrechetBridge4D`,
  `P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D`,
  `P0EFTJanusProgramPConcreteCandidateALineC2Closure4D`,
  `P0EFTJanusProgramPConcreteMatterLineC2Closure4D`,
  `P0EFTJanusProgramPConcreteMatterLineC2CriterionRealization4D`,
  `P0EFTJanusProgramPConcreteMatterLineC2CriterionCompletion4D`,
  `P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D`,
  `P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Closure4D`,
  `P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Realization4D`,
  `P0EFTJanusProgramPConcreteFullActionFrechetDiracAssembly4D`,
  `P0EFTJanusProgramPConcreteFullActionFrechetGeneralMeasureAssembly4D`.
- Résultat : Robin + LL + BV intégré instancient inconditionnellement le contrat
  Fréchet `C²` sur leur ligne commune; le pont neuf blocs est réduit exactement
  à six régularités `C²`. Candidate A est `C²` pour toute mesure finie; le slot
  matière est équivalent à la continuité de son Hessien sous les deux identités
  de dérivation exactes; EH `±` et Maxwell `±` sont `C²` pour une mesure de
  Dirac concrète et pour toute mesure finie sous leur critère de continuité
  jointe. Le bridge neuf blocs complet est construit sur mesure de Dirac, sous
  le seul critère matière affiché; il est aussi construit pour toute mesure
  finie sous les critères matière et Einstein–Maxwell exacts. Le critère matière
  est désormais construit depuis les contrats translatés, la continuité jointe
  et la densité diagonale de second ordre; le Hessien intégré et sa continuité
  sont alors démontrés.
- Limite : le contrat de base ne fournit pas la finitude de mesure, les cinq
  continuités conjointes ni la règle de chaîne diagonale. Surtout,
  `GlobalFixedFrameComponentContinuity` n'est pas une conséquence de la
  lissité intrinsèque : les quatre vecteurs modèles fixes ne sont pas des
  sections tangentes globales continues d'un atlas quotient arbitraire. Pour
  EH/Maxwell, la lissité séparée en chaque point ne fournit pas la continuité
  jointe paramètre–point. L'espace de champs intrinsèque, ses repères recollés,
  son produit `H¹`, sa trace et ses domaines fermés sont maintenant construits.
  Le transport vers l'action globale régulière est maintenant effectué.
  La variation complète et la Hessienne chartwise sont maintenant intégrées;
  leur identification au Fredholm gauge-fixé relève de
  `HESSIAN-GLOBAL-01`, pas d'un résidu technique autonome.
- Porte terminale : aucune ; avance `T03`–`T05`, `T11` et `T12`.

### `P-HESSIAN-EXISTING-GRAPH-BRICKS` — Réintégration des graphes fidèles

- État : `DONE` (2026-07-31). Portée :
  `HESSIAN/GAUGE-BRST/LL-ON-SHELL/NORMAL-JOINT`, sans fermeture globale.
- Gates déjà disponibles et désormais raccordées :
  `P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D`,
  `P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D`,
  `P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D`,
  `P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D`,
  `P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D`,
  `P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D`,
  `P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D`,
  `P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D`,
  `P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D`,
  `P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D`,
  `P0EFTJanusProgramPGlobalFullLLGraphRiesz4D`,
  `P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D`,
  `P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D`,
  `P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D`,
  `P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D`,
  `P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D`.
- Résultat : les potentiels intrinsèques des deux secteurs s'injectent
  linéairement dans le tangent physique minimal via les vrais repères
  Candidate-A. Le graphe Lorenz possède un cœur lisse dense injectif et un
  Riesz borné symétrique, de noyau exactement Lorenz, égal au Hessien BRST
  réduit on-shell. Il porte désormais une action quadratique `C∞` (donc
  `C²`) dont les première et seconde dérivées de Fréchet sont exactes; son
  cœur lisse s'injecte conjointement dans ce chart et dans le tangent minimal.
  Le graphe de Donder raffiné ajoute la caractéristique relevée du pairing
  lorentzien : son Hessien borné symétrique coïncide exactement avec le pairing
  intégré sur le cœur lisse, et son action quadratique est `C∞` avec second
  Fréchet constant. Les deux copies métriques et Lorenz sont assemblées dans
  un sous-chart physique métrique-plus-Abelien `C²`; son cœur commun s'injecte
  dans le tangent gauge-fixed typé en gardant le non-minimal nul. Le cœur LL complet
  `llAuxMetric × llMeasure × llField` possède lui aussi une injection dense,
  un Riesz symétrique et l'égalité exacte au Hessien same-action, termes
  croisés compris. Il porte maintenant une action quadratique `C∞`, de second
  Fréchet constant exactement égal à ce Hessien. Le sous-chart gauge, le
  graphe matière SpinC primitif et ce graphe LL sont désormais assemblés dans
  un produit physique bulk unique. Son action quadratique est `C∞`, égale
  exactement à la somme des trois actions de graphe, sa
  première dérivée est exacte et son second Fréchet constant est la somme
  bloc-diagonale exacte des trois formes same-action existantes. Son cœur
  jauge lisse × coefficients SpinC finis × LL lisse s'insère linéairement,
  injectivement et densément pour la vraie norme de graphe. À la métrique et
  à la masse physiques Candidate-A, une application linéaire injective
  enregistre conjointement le point graphe et ses slots exacts dans
  `GlobalPhysicalFieldTangent`.
  L'extension BRST abélienne off-shell réutilise une seule fois le potentiel
  et la caractéristique Lorenz, puis ajoute les coordonnées indépendantes
  `B/c̄/c` et le vrai FP `δ_g d c`. Son cœur lisse est injectif et dense; son
  Hessien borné symétrique, son Riesz et son action quadratique `C∞` coïncident
  exactement avec la polarisation du `sΨ` à la mesure lorentzienne canonique.
  Cette fermeture de caractéristiques ne prouve pas à elle seule la
  closabilité différentielle; la gate Green-core FP la fournit désormais pour
  la métrique intrinsèque, conditionnellement au datum Stokes scalaire. À la métrique Candidate-A,
  le même cœur s'injecte dans le graphe et dans les deux triplets abéliens de
  `GlobalGaugeFixedPhysicalFieldTangent`, avec triplet difféomorphisme nul.
  Dans le produit bulk étendu, cette brique remplace le facteur Lorenz sans
  dupliquer potentiel ni caractéristique. Les deux graphes de Donder, ce graphe
  abélien, la matière primitive et LL gardent un cœur lisse dense injectif,
  une action `C∞` (donc `C²`) et le second Fréchet constant égal à la somme
  bloc-diagonale exacte de leurs formes same-action, avec raccord typé injectif.
  Pour chaque métrique fournie, le vrai bloc BRST difféomorphe mono-métrique
  assemble `h/c/c̄/B`, le FP `c ↦ B_g(L_c g)`, `s² = 0` et la polarisation
  exacte de `sΨ`. Son cœur lisse est injectif et dense, son Riesz/Hessien est
  borné symétrique, son action est `C∞` et son raccord non minimal typé est
  injectif.
  Sur le lieu stationnaire LL, le champ LL est nul, les poids auxiliaires et
  projections croisées disparaissent et le Hessien se réduit au produit
  scalaire du champ LL. Le quotient par le noyau exact de sa projection est
  équivalent à `LLH1Space`; son Riesz quotient est l'identité, donc Fredholm
  d'indice zéro.
  La vraie section normale produit aussi une famille de collier
  deck-équivariante descendue gorge→bulk, égale à l'inclusion canonique en
  zéro, avec vitesse de coordonnée normale prescrite et accélération scalaire
  nulle. Le lift scalaire sur le cover et la coordonnée de graphe normale sont
  conjointement `C∞`; l'application physique descendue
  `(point, paramètre) ↦ normalGraph paramètre point` l'est aussi. Après
  transport le long du graphe nul, sa dérivée en zéro est exactement le lift
  normal orthogonal global de la classe différentielle correspondante.
- Limite : aucune identité de Green différentielle ni coercivité/range fermé
  LL off-shell n'est déduite; la conclusion Fredholm LL est limitée au quotient
  stationnaire à flux nul. La somme quadratique bulk n'est
  pas encore identifiée au pullback de l'action covariante non linéaire
  complète. Le produit physique bulk n'est
  pas le chart total : le raccord porte sur le cœur seulement et ne transforme
  aucun vecteur arbitraire de la complétion en champ lisse. Le chart analytique
  typé total, le raccord difféomorphe diagonal Candidate-A, les actions,
  Hessiens et complétions normal/bord, ainsi que les blocs Einstein--Maxwell
  en directions métriques générales, restent à assembler.
  Le bloc BRST mono-métrique ne fixait pas la projection des deux conditions
  de Donder vers l'unique triplet difféomorphe diagonal typé. Le pont d'adjoint
  cinétique la fixe maintenant aux poids Einstein `1/(2κ₊), 1/(2κ₋)`, construit
  la condition et le FP globaux, et prouve le critère d'ellipticité spatiale.
  Le no-go scalaire interdit toujours de prétendre préserver l'ancienne somme
  des deux carrés; le graphe off-shell doit employer la nouvelle forme croisée.
  Un chart nul avec coordonnée `Theta` indépendante et coefficient non nul
  non compensé doit aussi rester sur une strate régulière `Theta ≠ 0` : le
  facteur `Theta log |Theta|` n'est pas `C¹` en zéro. Les sous-charts
  contraints avec annulation prouvée ne sont pas exclus. Sur les strates
  régulières, le Hessien ponctuel same-action est désormais exactement
  `(u,v) ↦ Theta⁻¹ u v`, multiplié par le coefficient écran/gravité déjà
  déclaré; son intégration géométrique reste ouverte.
  Pour la normale, le pont dérivé vers le lift orthogonal est fermé; la famille
  d'action induite reste à construire. Aucun Hessien normal ni complétion n'est
  encore revendiqué.
- Porte terminale : réduit `HESSIAN-GLOBAL-01`, sans le fermer.

### Classement final des anciens résidus immédiats — 26 juillet 2026

Il ne reste aucune carte autonome dans cette ancienne liste :

- le spectre SpinC signé abstrait, la synthèse géométrique à support fini
  conjointement injective sur tous les niveaux positifs, secteurs, modes et
  multiplicités, et le transport unitaire du domaine maximal de coefficients
  sont fermés; la tour zéro est incluse dans la même synthèse canonique. Son
  véritable span lisse a désormais une analyse dense et une complétion
  spectrale unitaire. La complétude Fourier--monopôle prouve désormais
  l’égalité avec le produit géométrique intégral sur tout le cœur lisse et
  fournit l’unitaire ambiant;
- la normale intrinsèque et ses coordonnées locales sont `C∞`; leur
  comparaison explicite avec la représentation cover-produit est maintenant
  fermée comme contrôle de présentation `Pin⁻/T01`, distinct de la géométrie
  Candidate A et du certificat terminal `T01`;
- les générateurs LL, coefficients locaux, directions radiales/anisotropes et
  cisaillements sont construits; l'assemblage global d'un tangent arbitraire
  appartient à `HESSIAN-GLOBAL-01`;
- les critères et assemblages `C²` maximaux sont fermés; l'espace des vrais
  champs et l'action régulière assemblée sont maintenant fixés. L'Euler
  chartwise est fermé; Hessien et famille de Fredholm restent dans leurs
  blocs globaux dédiés.

## 6. Verrous globaux — ne pas distribuer comme petites cartes

Ces paquets absorbent tous les ponts restants. Aucun lemme intermédiaire ne
doit être annoncé comme fermeture globale.

Mise à jour `HESSIAN-GLOBAL-01` (2026-08-01) : la gate
`P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D`
réduit le raccord au vrai second
Fréchet est désormais réduit exactement à un seul résidu physique sur le cœur
diagonal. Pour tout pont de carte existant fourni,
`H_covariant_gauge-fixed = H_graphe + R_ancien`. La gate
`P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D` établit
maintenant `R_ancien = H_physique + défaut_même_action(matière--LL)`. La cible
correcte conserve donc `H_physique` et n'annule que ce défaut; annuler tout
`R_ancien` supprimerait la dynamique Einstein--Maxwell/bord. Aucun nouvel
axiome n'est ajouté par ce raccord.

La gate
`P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D`
ferme désormais le sous-raccord matière sur l'action covariante elle-même :
cœur fini à norme de graphe, neuf blocs `C²`, pullback exact
« spectateur constant + action SpinC » et vrai Hessien égal au pullback de
`2D+m²`. Elle ne construit pas l'habitant du pont diagonal total et ne change
donc pas l'état ouvert de `HESSIAN-GLOBAL-01` pour métrique/bord/domaines.

La gate
`P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D`
raccorde maintenant les normalisations indépendantes des générateurs nuls à
l'action covariante exacte : neuf blocs `C²`, pullback constant et vrai Hessien
nul. Elle ne couvre pas le déplacement normal ni la géométrie de bord générale.
Le même fichier prolonge désormais toute carte covariante par ce facteur : le
Hessien est le pullback par la première projection, donc les blocs purs et
mixtes de normalisation sont nuls. L'instance matière-plus-normalisation garde
exactement le Hessien `2D+m²`.

Registre autoritatif : [carte de fermeture
`HESSIAN-GLOBAL-01`](hessian_global_01_closure_map.md). Les listes historiques
de cette page ne créent aucune obligation supplémentaire.

Mise à jour `HESSIAN-GLOBAL-01` (2026-08-02) :
`P0EFTJanusProgramPGlobalLocalVariationalChart4D` ferme l’obstacle
d’interface. Une carte peut désormais porter ses données physiques seulement
sur un ouvert admissible `U` du modèle normé, avec `0 ∈ U`, et demander les
neuf propriétés `ContDiffWithinAt` dans `U`. L’ouverture donne le vrai Euler et
le Hessien de Fréchet ambiants sur tout l’espace tangent; le Hessien est
symétrique. Les cartes historiques sont retrouvées par `U = univ` avec action,
Euler et Hessien identiques. Le ticket devient `FRONTIER` : l'habitant
intrinsèque est encodé dans son coin fort et la sélection positive ferme sa
bijectivité Sylvester; restent la famille jointe et les blocs physiques à
identifier sans annuler leur dynamique.

`P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D`
raccorde désormais cette API au cœur lisse diagonal dense et injectif. Pour
tout point admissible, le Hessien covariant gauge-fixé est exactement le
graphe augmenté par les sept blocs physiques, plus le seul défaut same-action
matière--LL. L’accord équivaut à l’annulation de ce défaut, pas de la Hessienne
physique. Les blocs BRST, matière et LL sont réutilisés sans duplication;
`U = univ` redonne exactement l’ancien pont.
La racine ponctuelle générale possède maintenant son propre domaine de
perturbations ouvert centré en `0`, une branche `C²` sur tout le domaine et
l’identité carrée exacte, via
`P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D`. Cette gate vaut
autour de tout target raw à spectre réel positif scindé, sans réduction
diagonale/Minkowski. La même gate montre maintenant que toute racine continue
vérifiant l’identité carrée et la régularité de Sylvester point par point est
automatiquement `C²` lorsque la cible est `C²`; le recollement local est donc
fermé.
La couche uniforme `C⁰` est maintenant construite par
`P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D` : sur une base
compacte, les inverses de Sylvester ponctuels se recollent en un opérateur
borné sur les champs matriciels continus, donnant un ouvert centré en `0`, une
branche `C²` et le carré exact.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D` construit maintenant
la brique scalaire forte comme égaliseur fermé des applications existantes
`C⁰ → L²` et `H¹ → L²`. C’est un espace de Banach `C⁰ ∩ H¹` contenant le cœur
lisse exact, sans plongement de Sobolev ni nouvel axiome.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D` définit le
domaine analytique canonique comme fermeture de ce cœur lisse dans l’égaliseur.
Il est complet, s’y injecte et possède une image lisse dense par construction,
sans postuler une approximation simultanée.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D` ferme la
règle exacte du premier jet `(fg, f·dg + g·df)` pour le produit lisse déjà
présent et l’organise en application bilinéaire vers ce cœur.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D` ferme sa
borne en norme forte avec Hölder `L∞·L² → L²`, puis le prolonge canoniquement en
produit bilinéaire continu sur toute la fermeture complète, avec accord exact
sur les champs lisses et sans nouvel axiome.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D` assemble ce
produit sur les coefficients `4 × 4`, prouve l’accord exact avec les produits
lisse et continu, puis établit que le carré est `C∞` et que sa dérivée est le
Sylvester fort attendu.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D` réutilise
ensuite la famille inverse ponctuelle existante. Pour toute racine matricielle
lisse générale à Sylvester ponctuellement bijectif, ses coefficients inverses
sont lisses, donnent une équivalence bornée sur le cœur fort et produisent un
ouvert `0 ∈ U`, une branche `C²` et le carré exact, sans restriction diagonale
ni axiome supplémentaire.
  La taille fixe n'est plus un verrou. La nouvelle multiplication forte pour
  matrices finies arbitraires est associative et possède le calcul lisse
  carré/Sylvester exact; le relèvement linéaire fini transforme toute famille
  lisse ponctuellement bijective en équivalence bornée forte. Le pont de repère fini encode ensuite la racine
Candidate-A intrinsèque avec le projecteur lisse `P` de la famille génératrice
redondante. Les gates `...StrongFiniteFrameCorner4D` et
`...StrongFiniteFrameCornerAlgebra4D` construisent le coin fermé complet
`P M_N P`, y placent la racine et ferment son algèbre forte. La gate
`...StrongFiniteFrameCornerLocalRoot4D` donne enfin un certificat IFT Banach
réutilisable : sous bijectivité du Sylvester fort au centre, `U` est ouvert,
`0 ∈ U`, la branche est `C²` sur tout `U` et son carré est exact sur `U`. Aucun
repère global ni axiome physique n'est ajouté.
`P0EFTJanusProgramPGlobalStrongH1C0AnalysisDomain4D` l’étend au type fini
`GlobalBulkSobolevSlot` déjà présent : toutes les coordonnées bulk métriques,
jauge et fantômes forment un produit complet, compatible dans `L²`, avec
  relèvement exact du vrai tangent lisse. Les gates
  `...StrongFiniteFrameSylvester*` ferment aussi le transport manquant : la
  bijectivité intrinsèque ponctuelle donne la bijectivité forte du coin et la
  branche locale `C²` sur tout un ouvert. La portée est la strate régulière; le type
  `GlobalCandidateAGeometry` non qualifié admet encore des racines singulières.
  Le sous-type régulier explicite et le prédicat correspondant sur les cartes
  locales sont maintenant construits. La gate
  `P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D` prouve que
  la racine stockée, lorsqu’elle est exactement le sélecteur spectral positif
  physique existant, est intrinsèquement Sylvester-régulière et active la
  branche locale forte sans nouvel axiome.
  `P0EFTJanusProgramPGlobalCandidateALocalRootJointRegularity4D` ferme ensuite
  le passage fonctionnel : toute cible forte `C²` fournit un domaine paramètre
  ouvert, une racine sélectionnée `C²`, le carré exact et des coefficients
  conjointement continus en paramètre et point d'espace-temps.
  La couche d'ordre deux est désormais effective : le cœur scalaire C²
  valeur/premier jet/second jet est complet, son produit satisfait le Leibniz
  exact et il se projette continûment dans le cœur fort. Les matrices finies C²
  ont un produit associatif, un carré `C∞`, le Sylvester exact et une branche
  locale C² sur un ouvert; la gate jointe contrôle en plus tous les jets des
  coefficients en paramètre et espace-temps. Les gates
  `P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D`,
  `...CornerAlgebra4D` et `...SylvesterLocalRoot4D` transportent enfin la
  sélection intrinsèque dans le coin C² complet et activent sa branche locale
  par la régularité Sylvester déjà prouvée. Aucun nouvel axiome n'est utilisé.
  Restent la vraie application métrique générale vers ce cœur C² et les neuf
  blocs d'action.

Mise à jour supplémentaire `HESSIAN-GLOBAL-01` (2026-08-02) : le pont
`P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D` formule
maintenant le vrai Hessien local et son split directement sur le tangent
physique minimal D10-free; l’ancien pont étendu se factorise à D10 nul. Le
graphe LL complet possède son Riesz off-shell borné auto-adjoint et son radical
exact. Seuls la fermeture d’image et le Fredholm LL restent ouverts off shell;
sur la branche stationnaire, le quotient Fredholm d’indice zéro est déjà fermé.

Mise à jour P1 (2026-08-02) :
`P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D` ferme H05. Sa gate
terminale prouve l'appartenance du point physique à l'ouvert métrique général,
la dépendance `C²` de l'action et son égalité exacte avec
`intrinsicEinsteinHilbertAction`. La chaîne active commence désormais à P2.

| ID | Résultat global exigé | Dépendances principales |
|---|---|---|
| `GEO-GLOBAL-01` | **DONE (2026-07-26)** — Deux métriques Candidate A comme sections intrinsèques du même `T*⊗T*`, avec racine et densités identifiées aux modèles de coefficients. | `P0EFTJanusProgramPGlobalCandidateAGeometry4D` |
| `FIELD-GLOBAL-01` | **DONE (2026-07-30, contenu corrigé)** — Configuration commune pour métriques générales, deux secteurs de matière SpinC primitive, `U(1)^2`, ghosts/auxiliaires historiques, LL et bord. Le tangent physique exclut D10; un tangent étendu séparé le conserve pour régulateur/déterminant. | `P0EFTJanusProgramPGlobalFieldSpace4D` |
| `ANALYSIS-GLOBAL-01` | **DONE (2026-07-30, contenu corrigé)** — Sobolev intrinsèque, trace du throat et domaine physique fermé bulk/SpinC/LL; l’agrégat étendu ajoute explicitement D10. | `P0EFTJanusProgramPGlobalAnalysisDomain4D` |
| `BOUNDARY-GLOBAL-01` | **DONE (2026-07-26)** — EH+GHY, faces nulles/joints finis et LL sur la vraie gorge; flux scalaire conservé en général puis fermé sur le domaine PT/Dirichlet. | `P0EFTJanusProgramPGlobalBoundaryCompletion4D` |
| `KJ-GLOBAL-01` | **DONE (2026-07-26)** — `K_Gram`, `DK_Gram`, `R` et `B_Noether` sont intrinsèques; `K_SV` est la courbure de la vraie connexion de Levi-Civita sur l'atlas holonome total et `B_Bianchi` sa dérivée cyclique covariante. La connexion satisfait sa loi de transition et `B_Bianchi ∘ K_SV = 0` en tout point physique. Les opérateurs plats `Fin 4` sont séparés par le suffixe `_symbol`. | `P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D`, `P0EFTJanusProgramPGlobalCompatibilityOperators4D` |
| `KJ-GLOBAL-02` | **DONE (2026-07-26)** — Le complexe physique assemble le Bianchi covariant, le vrai différentiel de jauge `U(1)^2` dans le `L²` canonique, son noyau exact `H⁰ ≃ ℝ²`, quotient et complétion fermée, ainsi que la version appariée du package global avec noyau `GaugeLieAlgebra × GaugeLieAlgebra` et le domaine Dirichlet commun. Le complexe `ℤ⁴` reste explicitement un certificat de symbole auxiliaire. | `P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D`, `P0EFTJanusProgramPGlobalCompatibilityComplex4D` |
| `NATURAL-GLOBAL-01` | **DONE (2026-07-26)** — Catégorie Janus, jets holonomes descendus, vrais bundles `Pin⁻`/`PinC`, classificateur local fini fidèle et unicité exacte des coefficients dans la troncature EFT à six invariants. | `P0EFTJanusProgramPGlobalNaturalClassification4D` |
| `ACTION-GLOBAL-01` | **DONE (2026-07-30, matière migrée)** — Action Candidate A sur son domaine régulier commun : deux EH, interaction, matière SpinC primitive sectorielle `½ Re⟨ψ,(2D+m²)ψ⟩`, deux Maxwell, LL, GHY, faces nulles, contre-termes et joints. | `P0EFTJanusProgramPGlobalCovariantAction4D`, `P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D` |
| `EULER-GLOBAL-01` | **DONE (2026-07-26, portée chartwise)** — Les neuf blocs de l'action exacte sont identifiés, `C²` sur toute carte variationnelle régulière commune, et leur véritable dérivée de Fréchet définit l'Euler dans toute direction de cette carte. | `P0EFTJanusProgramPGlobalEulerLagrange4D` |
| `NOETHER-GLOBAL-01` | **DONE (2026-07-26, portée physique `U(1)²`)** — L'Euler annule tout générateur d'une symétrie terme par terme; indépendamment, l'orbite de jauge des deux Maxwell est constante pour toute paire de ghosts lisses et se combine au Bianchi courbe intrinsèque. | `P0EFTJanusProgramPGlobalNoether4D` |
| `HELMHOLTZ-GLOBAL-01` | **DONE (2026-07-26, portée chartwise)** — Le Jacobien du véritable Euler est symétrique; la primitive radiale normalisée reconstruit exactement la même action, et deux représentants de même Euler diffèrent d'une constante. | `P0EFTJanusProgramPGlobalHelmholtzReconstruction4D` |
| `VARCOH-GLOBAL-01` | **DONE (2026-07-26, portée fonctionnelle globale)** — Obstruction fonctionnelle exacte nulle, fonctionnelles variationnellement nulles constantes, noyau nul du classificateur naturel fini, ambiguïtés de contre-termes constantes et résidu physique de bord nul. | `P0EFTJanusProgramPGlobalVariationalCohomology4D` |
| `ADM-GLOBAL-01` | **FRONTIER (2026-07-27, portée FLRW réduite)** — La Legendre de l’action Candidate-A FLRW donne exactement `N₊C₊+N₋C₋`; les primaires sont ses dérivées de lapse, leur crochet canonique est la secondaire, la préservation la force, et un ouvert non vide garde le rang trois. Un témoin poussière positif fixe aussi le rapport des lapses. Il manque la réduction covariante avec shifts/dérivées spatiales, l’algèbre fonctionnelle, le rang global et l’exclusion BD. | `P0EFTJanusProgramPGlobalADMFrontier4D` |
| `STABILITY-GLOBAL-01` | **FRONTIER (2026-07-27, portée réduite)** — Le cône proportionnel sûr a une énergie non négative. Sur le témoin poussière, le noyau tangent contraint est exactement unidimensionnel; une courbe contrainte non triviale garde le Hamiltonien nul, donc la Hessienne ambiante négative n’est pas une instabilité contrainte mais le vide n’est pas strictement isolé. Il manque quotient ADM/BD, tous les modes, matière/bord, limite faible et PPN. | `P0EFTJanusProgramPGlobalStabilityFrontier4D`, `ADM-GLOBAL-01` |
| `DIRAC-GLOBAL-01` | **DONE (2026-07-28)** — Dirac D9 intrinsèque lisse/elliptique; tour de coefficients SpinC tous niveaux (zéro compris, deux racines) dense, auto-adjointe, Fredholm d’indice nul; accord D10 positif et domaine maximal unitairement égal à la tour zéro plus D10 positif. Pour tout `p`, la courbe nulle fournit exactement `2p+1` sections lisses complexes du véritable fibré quotient. Leur récurrence démontre directement le vrai `D²`. Chaque label signé complet possède une vraie eigensection lisse du Dirac de premier ordre, y compris la tour zéro corrigée selon l’orientation du period; les branches `±` sont disjointes et épuisent chaque bloc scalaire/gradient. Chaque branche possède une isométrie de Parseval géométrique à image complétée fermée et entrelace le vrai Dirac; le bloc deux signes possède la même réalisation pour `D²`. La séparation radiale prouve les finranks exacts `2p+1` par signe et `2(2p+1)` par bloc. Tous les blocs signés sont orthogonaux selon secteur/mode/niveau et s’assemblent avec la tour zéro dans une isométrie globale à image fermée. La complétude Fourier temporelle, l’approximation polynomiale monopôle et la reconstruction exacte du repère de Hopf signé prouvent que cette image contient le cœur lisse dense. Elle est donc toute la complétion géométrique et la synthèse fournit l’unitaire géométrique DIRAC global. | `P0EFTJanusProgramPGlobalDiracFrontier4D`, `P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D`, `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D`, `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D`, `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D`, `P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D`, `P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D` |
| `BRST-GLOBAL-01` | **FRONTIER RÉDUITE (2026-07-29)** — Le paquet commun champs/ghosts extérieurs, métrique–antifields et bord vérifie `s²=0`; `U(1)²`, scalaire, densité mesurée et antifield scalaire de gorge sont fermés. Les actions Cartan Maxwell et métrique globales sont maintenant lisses et bilinéaires; leurs données Cartan, représentations de Lie et crochets sont fermés. Elles forment le paquet tensoriel concret `canonicalTensorialCartanActionData`, dont les obstructions coadjointes BRST algébriques Maxwell/deux-métriques sont nulles et les pairings canoniques sont invariants; aucun dual tensoriel géométrique ou intégré n’est revendiqué. Le ghost bulk de translation temporelle et les trois ghosts bulk de rotation se restreignent exactement à leurs ghosts de gorge par la dérivée de l’inclusion, sans conclure de skew. Pour les rotations de gorge, le pullback tensoriel, l’isométrie intrinsèque, la naturalité ponctuelle du pairing relevé/deux-secteurs et l’invariance finie de son intégrale contre la mesure canonique sont fermés; la courbe scalaire intégrée correspondante a une dérivée nulle à angle zéro par constance. La chain rule publique pour tout `SmoothThroatField` à fibre fixe donne son `mvfderiv` le long du ghost, sans dériver le pullback tensoriel. Restent la différentiabilité tensorielle en angle, la chain rule du pairing et le pont générateur/action avant toute skew ou conclusion coadjointe. Pour le pairing métrique bulk, le vrai flot temporel, la mesure préservée, la naturalité par conjugaison/trace et la dérivée scalaire nulle de l’orbite du pairing sont fermés; restent le pont pointwise générateur/action et la différentiation à travers le pairing intégré avant toute skew. L’IPP canonique ferme aussi la skew des coefficients LL. Les dualiseurs lisses finis ferment séparation/injectivité métrique de gorge et de bulk. `finiteBV` est relié à sa vraie reparamétrisation nulle. Enfin, la nouvelle interface de flots complets non linéaires Candidate-A transforme l’invariance terme par terme des neuf blocs en invariance exacte de l’action et horizontalité Euler pour le générateur dépendant du champ. Restent les duals géométriques/intégrés et leur skew/coadjoint, les ponts flow/action concrets et le flot Candidate-A neuf-blocs à mesure fixe. | `P0EFTJanusMappingTorusGaugePotentialCartanFiber4D`, `P0EFTJanusMappingTorusGaugePotentialCartanFiberBridge4D`, `P0EFTJanusMappingTorusGaugePotentialCartanSmoothBundle4D`, `P0EFTJanusMappingTorusGaugePotentialCartanGlobalAction4D`, `P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D`, `P0EFTJanusProgramPMaxwellCartanCoadjointAntifieldBRST4D`, `P0EFTJanusMappingTorusMetricCartanFiberCore4D`, `P0EFTJanusMappingTorusMetricCartanFiber4D`, `P0EFTJanusMappingTorusMetricCartanGlobalAction4D`, `P0EFTJanusProgramPCanonicalTensorialCartanBRST4D`, `P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D`, `P0EFTJanusMappingTorusSpatialRotationAmbientLorentzIsometry4D`, `P0EFTJanusMappingTorusIntrinsicLorentzMetricSpatialRotationIsometry4D`, `P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D`, `P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D`, `P0EFTJanusProgramPGeneralMetricPositiveDualizer4D`, `P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D`, `P0EFTJanusProgramPGeneralMetricTimeTranslationPairingNaturality4D`, `P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D`, `P0EFTJanusProgramPD8RotationGhostThroatRestriction4D`, `P0EFTJanusProgramPThroatMetricRotationPullback4D`, `P0EFTJanusProgramPThroatMetricRotationPairingNaturality4D`, `P0EFTJanusProgramPGlobalBRSTFrontier4D` |
| `HESSIAN-GLOBAL-01` | **FRONTIER ANALYTIQUE (2026-08-02; P1 fermé)** — Les données physiques vivent sur un ouvert admissible `U`, `0 ∈ U`, et le Hessien ambiant agit sur tout le tangent. La sélection positive et la branche locale C² sont fermées. Les familles générales Maxwell et Einstein--Hilbert sont construites; H05/P1 prouve l'accord exact de l'action EH physique avec l'action intrinsèque. Le split minimal D10-free conserve les sept blocs physiques et n’isole que le défaut same-action matière--LL. Le quotient LL stationnaire est Fredholm d’indice zéro. Restent P2 (normal/bord), P3 (domaine commun, Green, adjoints, fermetures) et P4 (défaut matière--LL, multiplicités fidèles, somme Fredholm totale). D10 reste réservé au régulateur. | `P0EFTJanusProgramPGlobalLocalVariationalChart4D`, `P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D`, `P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D`, `P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D`, `P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D` |
| `REGULATOR-GLOBAL-01` | **DONE (2026-07-30, portée régulateur nucléaire de référence)** — À tout temps positif, un opérateur unique sur le produit Hilbert ambiant exact — slots bulk `L²` métrique/jauge/ghost/auxiliaire, coefficients SpinC signés des deux secteurs, D10 tous niveaux et flux LL `L²` — est inconditionnellement compact, injectif et muni d’une expansion rang-un absolument sommable. Le bulk conserve en plus son inclusion Dirichlet compacte, son Gram compact positif auto-adjoint et le lift adjoint à trace nulle. Les blocs SpinC et D10 gardent leurs chaleurs physiques exactes nucléaires. La chaleur D9 continuum exacte est nucléaire sous son hypothèse explicite de sommabilité, et chaque paquet fini l’est sans hypothèse. La chaleur exacte de la Hessienne LL reste compacte ssi son espace d’énergie est de dimension finie. Le régulateur global est un régulateur de référence dépendant d’une base : ni son accord avec la Hessienne globale, ni une convergence forte vers l’identité n’est affirmé; cet accord appartient à `HESSIAN-GLOBAL-01`. | `P0EFTJanusProgramPGlobalReferenceNuclearRegulator4D`, `P0EFTJanusProgramPGlobalBulkReferenceNuclearRegulator4D`, `P0EFTJanusProgramPGlobalBulkDirichletCompactRegulator4D`, `P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D`, `P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D`, `P0EFTJanusProgramPLL2SeparableReferenceNuclearRegulator4D`, `P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D`, `P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D` |
| `QUILLEN-GLOBAL-01` | **FRONTIER (2026-07-26)** — La vraie famille cercle possède ligne déterminante, métrique hermitienne, connexion plate compatible, recollement et holonomie unitaire. Il manque l’identification à la géométrie Quillen/Bismut–Freed de la famille Janus géométrique complète. | `P0EFTJanusProgramPGlobalQuillenFrontier4D` |
| `ANOMALY-GLOBAL-01` | **FRONTIER RÉDUITE (2026-07-27)** — Annulation additive PT, convergence du cutoff `Z4`, égalité des logarithmes renormalisés, annulation des phases mode par mode et inflow opposé. Le certificat inclut désormais la trace chirale D10 tous niveaux, absolument sommable, nulle par PT, avec convergence de tout filet de cutoffs finis. Il manque la classe locale/globale et sa trivialisation équivariante pour tout le contenu géométrique. | `P0EFTJanusProgramPGlobalAnomalyFrontier4D`, `P0EFTJanusProgramPD10ContinuumHeatRegulator4D` |
| `SCHEME-GLOBAL-01` | **BLOQUÉ-PHYSIQUE (no-go formel 2026-07-26)** — Des témoins distincts satisfont platitude et annulation PT; une ligne de Quillen fixée ne fixe pas l’action scalaire renormalisée. Les parties finies et la normalisation doivent venir d’une loi microscopique. | `P0EFTJanusProgramPGlobalSchemeFrontier4D`, `MICRO-GLOBAL-01` |
| `MICRO-GLOBAL-01` | **BLOQUÉ-PHYSIQUE (no-go formel 2026-07-27)** — Le parent bulk fourni se réduit exactement et satisfait Helmholtz/PT, mais deux parents admissibles donnent des mixages réduits différents. La sélection discrète de `α` et du sextique est exacte seulement après fourniture de `β`, du niveau, du verrou et de l’ancrage UV. Il manque donc la loi microscopique Janus sélectionnant le parent et ses parties finies. | `P0EFTJanusProgramPGlobalMicroFrontier4D`, `SCHEME-GLOBAL-01` |
| `VACUUM-GLOBAL-01` | **FRONTIER (2026-07-27; dépendance physique bloquante)** — L’interaction PT-plate proportionnelle a un minimum positif unique en `c=1` et une Hessienne réduite positive, mais les contraintes FLRW du vide y perdent leur rang et la branche poussière possède une direction contrainte isoénergétique. Le vide global exige encore l’action effective renormalisée, le quotient stable, la trivialisation d’anomalie et les parties finies microscopiques. | `P0EFTJanusProgramPGlobalVacuumFrontier4D`, `STABILITY/ANOMALY/SCHEME/MICRO-GLOBAL-01` |
| `SCALE-GLOBAL-01` | **BLOQUÉ-PHYSIQUE (no-go formel 2026-07-27)** — Géométrie, gap de Dirac, flux LL, action locale de chaleur et compatibilité des charges conservent une orbite commune de redimensionnement; les hypothèses actuelles ne sélectionnent donc aucune longueur positive unique. Il faut un ancrage microscopique dimensionné indépendant et un vide effectif stable sélectionné, sans injecter un rayon observé. | `P0EFTJanusProgramPGlobalScaleFrontier4D`, `MICRO-GLOBAL-01`, `VACUUM-GLOBAL-01` |

Portée exacte des fermetures et frontières globales :

- `GEO` travaille sur le domaine maximal honnête des paires munies d'une
  racine réelle lisse. Le constructeur conforme prouve que ce domaine est
  habité; aucune racine universelle incompatible avec l'obstruction spectrale
  n'est postulée.
- `FIELD` retire l'ancien tangent métrique diagonal en doublon et conserve une
  seule perturbation tensorielle générale; matière SpinC, projection D9,
  coordonnées D10 et trace de bord proviennent du même objet.
- `ANALYSIS` extrait les coefficients du vrai tenseur par la famille
  génératrice lisse intrinsèque, les complète dans le produit physique `H¹`,
  construit la trace continue et son noyau Dirichlet fermé, puis agrège les
  domaines SpinC, D10 et LL.
- `BOUNDARY` identifie la gorge canonique à la donnée non nulle
  gaussienne, relie son flux EH au même vecteur de Palatini que le bulk,
  assemble GHY/null/joints, et utilise le repère LL préservant la mesure. La
  formule scalaire universelle garde son flux orienté; son annulation est un
  théorème du secteur PT-fixe ou Dirichlet, jamais un axiome.
- `KJ-01/02` ne reposent sur aucun renommage du modèle de Fourier. Sur le vrai
  mapping-torus, la connexion de Levi-Civita, sa courbure et la dérivée de
  Bianchi incluent les termes de connexion/courbure; l'identité est couverte
  par l'atlas total. Le secteur linéaire de jauge possède son vrai modèle
  `L²`, son `H⁰`, son quotient et sa complétion fermée. Le modèle spectral
  `ℤ⁴` reste auxiliaire. Aucune exactitude globale de type Calabi
  `ker B = im K` pour une métrique courbe arbitraire n'est affirmée : cette
  question de linéarisation elliptique/Fredholm appartient à
  `HESSIAN-GLOBAL-01`, pas à la fermeture du complexe covariant.
- `NATURAL` est fermé à la portée annoncée : classification exacte des termes
  locaux dans la troncature EFT finie à six invariants. Elle classe les
  coefficients libres; elle ne les sélectionne pas physiquement.
- `ACTION` est fermée sur le domaine régulier explicitement typé. Le terme
  cinétique de matière est le vrai Dirac Levi-Civita doublé de la gorge
  canonique, pas un substitut scalaire.
- `EULER/HELMHOLTZ` travaillent sur toute carte normée commune dont les neuf
  blocs physiques exacts sont `C²`. Ils utilisent la vraie dérivée de
  Fréchet de l'action assemblée, prouvent la symétrie de son Jacobien et
  reconstruisent exactement l'action normalisée. Ils ne construisent pas
  encore un atlas normé couvrant chaque valeur brute de `GlobalFieldTangent`.
- `HESSIAN` ne dépend plus du contrat monolithique qui identifiait à tort tout
  tangent lisse au `ℓ²` D10. Le tangent, le domaine et la cible physiques sont
  désormais D10-free. L’ancien tangent étendu et son facteur D10 restent
  explicitement réservés au régulateur/déterminant et ne peuvent pas être
  réutilisés comme Hessienne d’action. Le produit Hilbert étendu
  bulk/SpinC/D10/LL et son cœur opérateur dense injectif sont construits à
  cette seule portée régulateur. La tour SpinC de **coefficients** tous niveaux
  et le bloc D10
  sont Fredholm; son domaine maximal est unitairement identifié à la tour
  zéro plus le domaine D10 positif, avec conjugaison exacte et énergie de
  graphe préservée. L’identité de Riesz LL est maintenant un facteur exact du
  même opérateur Fredholm, avec le repère canonique de l’action et l’accord
  démontré de son pairing de Hessienne.
  Pour toute symétrie physique `U(1)²` chartwise certifiée, la descente de la
  Hessienne vraie est exacte, symétrique et canonique. Une symétrie
  difféomorphe exacte fournie se combine désormais automatiquement et donne
  le sous-module total. Les résidus sont séparés : vrai pont tangent-carte,
  orthogonalité/complétude et analyse **géométrique** SpinC tous niveaux
  (les paquets finis et l’extension complétée sont fermés), invariance difféomorphe des neuf
  blocs et égalité au Fredholm elliptique global. Le no-go Hessien nul impose
  des hypothèses de couplage non dégénérées.
- `NOETHER` est inconditionnel pour les ghosts lisses appariés du secteur
  physique `U(1)²` et pour le Bianchi de Levi-Civita. Pour toute symétrie
  difféomorphe exacte des neuf blocs, l’identité d’Euler est automatique.
  Pour un générateur non linéaire différentiable, sa linéarisation est
  exactement `H(v,G)+E(DG·v)=0`; la dégénérescence Hessienne gauche/droite
  suit donc au point critique, y compris sur le cœur tangent global via tout
  bridge dense fourni. Le certificat associé juxtapose l’invariance de
  l’action et l’identité Euler/Noether issues de la symétrie affine fournie
  avec le carré nul et la stabilité du bord déjà indépendants dans le paquet
  BRST nonlinear; il n’identifie pas les deux différentielles. La construction
  de l’habitant géométrique neuf-blocs reste dans `BRST/HESSIAN-GLOBAL-01`.
- `BRST` combine désormais les représentations Cartan Maxwell et métrique
  concrètes dans un paquet tensoriel canonique et ferme les représentations
  coadjointes algébriques de Maxwell et de la paire de métriques, avec carré
  nul et pairings invariants. Le pairing tensoriel
  métrique intégré définit maintenant un morphisme linéaire canonique des
  antifields lisses vers ce dual algébrique. La famille tangentielle finie,
  son dualiseur covariant lisse et le support plein canonique prouvent
  maintenant son injectivité/non-dégénérescence **bulk**. Son entrelacement
  coadjoint reste exactement équivalent à l’identité intégrée
  `B(L_c α,h)+B(α,L_c h)=0`. La paire tensorielle de la gorge fixe est
  désormais un vrai module réel et son pairing intrinsèque intégré fournit
  aussi un morphisme linéaire vers le dual algébrique. Son injectivité est
  exactement réduite à la séparation par le pairing et est maintenant prouvée
  par le dualiseur positif lisse fini, sans définitude diagonale. Son
  équivariance reste réduite à la skew-adjonction intégrée pour toute
  représentation de gorge fournie. La réalisation
  inconditionnelle et ces critères sont
  désormais intégrés aux certificats nonlinear BRST et
  `GlobalBRSTFrontier`. Cette frontière globale agrège aussi le certificat
  nonlinear complet, le dual géométrique métrique de bulk et la fermeture
  coadjointe tensorielle pour la représentation Maxwell canonique et toute
  représentation Lie métrique fournie. Sur les tenseurs réels de gorge, la séparation bilinéaire et la
  skew-adjonction intégrée construisent directement le pont coadjoint
  géométrique fidèle via une porte globale. Un tenseur lorentzien symétrique
  non nul à endomorphisme relevé nilpotent et trace quadratique nulle exclut
  formellement la définitude diagonale comme voie générique. Le même modèle
  prouve toutefois la séparation bilinéaire de tous les tenseurs symétriques.
  Un certificat de dualiseur lisse positif globalise désormais
  automatiquement ce résultat par continuité et support plein : séparation
  intégrée et injectivité du dual en découlent; le pont coadjoint demande en
  plus une skew intégrée fournie. Le dualiseur est maintenant construit depuis
  l’inverse métrique lisse; il reste à prouver la skew-adjonction intégrée. La famille génératrice lisse finie existante
  fournit maintenant l’énergie explicite `Σᵢⱼ h(vᵢ,vⱼ)²`, positive et
  séparante. La somme covariante finie de rang un est maintenant définie et
  son identité de pairing avec cette énergie est prouvée abstraitement. La
  contraction fibrée existante prouve maintenant chaque coefficient et les
  deux énergies lisses; la continuité n’est donc plus une hypothèse.
  Les contractions métrique-repère sont désormais de vraies sections
  covecteur lisses, leurs produits extérieur et symétrisé sont de vrais
  tenseurs lisses et la multiplication scalaire lisse est construite. La
  somme finie pondérée symétrique est assemblée dans les deux secteurs
  intrinsèques. Son identité exacte de pairing pointwise est prouvée par un
  lemme intrinsèque de contraction de rang un, sans transport entre les
  wrappers `TangentSpace`.
  Les générateurs de pullback tensoriel et Maxwell sont désormais additifs
  sur les orbites différentiables et homogènes dans le champ; un contrat
  explicite de différentiabilité les bundle en applications linéaires. La métrique
  intrinsèque canonique a un générateur nul pour le sous-groupe complet de
  translation temporelle; cette fermeture métrique restreinte est agrégée
  par `GlobalBRSTFrontier`, sans être étendue artificiellement à tous les
  ghosts lisses.
  La contraction lisse tenseur–deux-vecteurs déjà disponible donne maintenant
  la réduction de Cartan métrique : comme pour Maxwell, le crochet est
  automatique dès que l’action lisse est construite. Son résidu est tensoriel
  dans les deux champs tests, fournit par `mkHom₂` un tenseur covariant
  symétrique fibre et se spécialise aux tenseurs lisses Janus. Toute évaluation
  sur deux ghosts lisses est un scalaire global lisse. L’assemblage fini donne
  maintenant l’action métrique globale lisse et bilinéaire, son
  `symmetricTensorCartanActionData`, sa représentation de Lie et son crochet
  exacts. Le résidu Cartan Maxwell
  est tensoriel, fournit un vrai covecteur fibre par `mkHom` et se spécialise
  aux potentiels D8. Sa régularité Hom-bundle uniforme est prouvée; l’action
  globale est lisse et bilinéaire, son `GaugePotentialCartanActionData`, sa
  représentation de Lie et son crochet sont fermés. Les obstructions BRST du
  champ et de l’antifield coadjoint algébrique ainsi que le pairing canonique
  d’évaluation sont fermés, sans construire de dual Maxwell géométrique ou
  intégré. Le ghost bulk de
  translation temporelle et les trois ghosts bulk de rotation se restreignent
  exactement à leurs ghosts de gorge par `mfderiv` de l’inclusion. Aucune skew
  tensorielle n’en découle seule. L’orbite de pullback des rotations existe,
  et la naturalité ponctuelle du pairing relevé et de sa version deux-secteurs
  est fermée. Son intégrale contre la mesure canonique est invariante sous
  chaque rotation finie, donc la courbe scalaire intégrée a une dérivée nulle
  à angle zéro par constance. Une chain rule publique dérive aussi tout
  `SmoothThroatField` à fibre fixe composé avec la rotation en son `mvfderiv`
  le long du ghost de rotation de gorge. Elle ne dérive pas le pullback
  tensoriel. Restent sa différentiabilité en angle, la chain rule du pairing
  et le pont générateur/action avant toute skew ou conclusion coadjointe;
  l’orbite tensorielle temporelle de gorge n’est pas encore bundlée.
  Chaque rotation de gorge possède maintenant un vrai difféomorphisme lisse
  et un pullback lisse des tenseurs symétriques, identité à angle nul. La
  rotation ambiante préserve exactement la forme de Minkowski et la rotation
  du cover est une isométrie exacte du tenseur Lorentzien intrinsèque. La
  naturalité ponctuelle du pairing quotient/gorge et son invariance intégrée
  finie sont fermées, ainsi que la dérivée nulle de la courbe scalaire
  intégrée. La chain rule générique à fibre fixe est publique, mais ne dérive
  pas le pullback tensoriel. Restent la différentiabilité tensorielle en
  angle, la chain rule du pairing et le pont générateur/action avant toute
  skew ou conclusion coadjointe.
  Pour le pairing métrique bulk, le vrai flot temporel, la fixité du fond
  intrinsèque, la mesure préservée et la dérivée scalaire nulle du pairing
  invariant sont formalisés. La naturalité est prouvée par conjugaison et
  invariance de la trace; restent le pont pointwise générateur/action et la
  différentiation à travers le pairing intégré avant toute skew.
  Candidate A possède aussi une interface correcte de flots complets non
  linéaires : l’invariance terme par terme implique l’invariance de l’action
  et l’horizontalité Euler du générateur dépendant du champ. La covariance
  avec mesure transportée implique maintenant exactement le contrat à mesure
  fixe sous préservation de la mesure; l’action scalaire générale instancie
  ce pont. Le changement de variables des cinq blocs mesurés Candidate-A
  (interaction, EH±, Maxwell±) est maintenant réduit à sept identités de
  pullback des champs densitaires fournies; pour l’interaction, la naturalité
  déterminant/racine/potentiel est réduite exactement au pullback musical,
  à la conjugaison de `rootAt` et au transport du repère régulier. La mesure
  canonique spécialise cette réduction au vrai flot temporel. Une orbite
  conforme concrète `ℝ → GlobalFieldConfiguration`, construite avec une
  échelle positive explicite et sa partenaire PT, possède maintenant ses lois
  zéro/add exactes; elle n’est pas relevée en données d’action ou en chart.
  Cela ne construit encore ni `GlobalCandidateAActionData`, ni chart, ni
  pullback du champ global complet. Le bloc GHY de la gorge canonique est
  identiquement nul, donc
  sa covariance est fermée; restent les covariances ambiantes
  SpinC-matière/LL/finite-BV, et l’interface abstraite autorise toujours le
  flot identité. L’API des données d’action passe encore par l’exigence
  historique de repère global `RegularGeneralLorentzMetric.frameEquiv`, alors
  que la brique statique de volume est désormais frame-free pour toute
  `SmoothGeneralLorentzMetric`. Restent la dépendance `C²`/Fréchet en métrique,
  Maxwell/l’interaction et le chart/core variationnel Candidate-A. La descente
  globale de la courbure scalaire est
  maintenant fermée : le
  troisième jet des vraies transitions
  holonomes et sa symétrie externe sont prouvés. Les composantes dans la base de
  la courbure-endomorphisme du gate de Bianchi sont identifiées exactement aux
  composantes de Riemann utilisées par Einstein--Hilbert. Une transition
  holonome fixe satisfait la loi complète de Levi--Civita/Christoffel comme
  `EventuallyEq`, grâce à l’égalité de germ de ses inverses fixe et ré-ancré.
  Cette loi est maintenant étendue aux vecteurs arbitraires, différentiée avec
  tous les termes connexion/Jacobienne, puis antisymétrisée. Les jets
  symétriques `D²` et `D³` s’annulent et donnent sans hypothèse
  `J (R₁(u,v)z) = R₂(Ju,Jv)(Jz)`, avec son corollaire sur
  l’endomorphisme de Riemann. Ricci est désormais sa trace sur les vecteurs
  arbitraires, sa matrice suit la congruence jacobienne, et la contraction par
  la métrique inverse prouve l’invariance du scalaire. L’atlas holonome total
  et les inverses locaux le recollent en `globalSmoothScalarCurvature`.
  Tout `RegularGeneralLorentzMetric` fournit donc un
  `RegularEinsteinHilbertMetric`. `frameFreeEinsteinHilbertAction` intègre
  maintenant le scalaire calculé contre toute mesure d’action finie non nulle.
  `P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D` construit, pour
  toute `SmoothGeneralLorentzMetric`, un ratio global positif lisse indépendant
  des cartes, la mesure finie non nulle `generalLorentzVolumeMeasure` et son
  interface `generalLorentzActionMeasure`; la métrique intrinsèque redonne
  exactement la mesure canonique. `P0EFTJanusMetricVolumeDensityHessian4D`
  prouve aussi la vraie seconde variation mixte ponctuelle de `sqrt |det g|`
  le long de courbes affines de matrices à signe de déterminant fixé :
  `sqrt |det g| * (1/4 tr(g⁻¹h) tr(g⁻¹k) -
  1/2 tr(g⁻¹h g⁻¹k))`, symétrique en `h,k`.
  `P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D` globalise
  cette formule, via `globalMetricVolumeRatio` et
  `generalMetricTensorPairingAt`, en une densité frame-free continue et
  intégrable dont l’intégrale est symétrique.
  `P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D` construit
  maintenant la vraie ligne conforme exponentielle positive
  `scale(t)=baseScale*exp(t*u)`. Son ratio relatif est exactement
  `rho=scale²`, avec dérivées `2*u*rho` et `4*u²*rho`; la seconde se décompose
  exactement en Hessien sur la vitesse plus première variation sur
  l’accélération, `2*u²*rho + 2*u²*rho`. Pour tout intégrande scalaire lisse
  fixé, l’action contre le volume variable est `C²`; la différentiation sous
  l’intégrale compacte de mesure finie est mutualisée dans
  `P0EFTJanusCompactParametricIntegralC2`. Ce résultat reste limité à cette
  ligne conforme à un paramètre : il ne construit ni atlas/topologie de
  sections ni dépendance `C²`/Fréchet métrique générale. Comme l’intégrande est
  fixé, ce gate seul ne constitue pas la variation générale de la courbure
  d’Einstein--Hilbert.
  `P0EFTJanusMappingTorusHomotheticEinsteinHilbertHessian4D` ferme maintenant
  cette variation sur la tranche des homothéties positives constantes de la
  métrique intrinsèque : Christoffel et Ricci sont invariants,
  `R(scale*g0)=scale⁻¹*R0`, tandis que le volume varie comme `scale²`. La vraie
  action Einstein--Hilbert est égale à son polynôme réduit en coordonnée
  affine, dont le Hessien est symétrique. Le long de sa courbe métrique
  exponentielle positive, l’action est `C∞` (donc `C²`) et sa dérivée seconde
  se décompose en Hessien sur la vitesse plus première variation sur
  l’accélération ; à `t=0`, elle
  vaut `u²/(2κ) * (Rtot - 8*Λ*Vol)`. Le facteur conforme spatialement
  variable est fermé séparément ci-dessous ; le Hessien Fréchet métrique
  général et l’opérateur de Jacobi neuf blocs ne sont pas construits.
  `P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D` globalise
  séparément, pour toute `SmoothGeneralLorentzMetric`, le pairing Maxwell de
  deux potentiels abéliens lisses arbitraires, puis sa densité diagonale et son
  action frame-free. Les lois `F₁=JᵀF₂J` et `g₁=Jᵀg₂J` donnent des champs
  globaux lisses et intégrables. En dimension quatre, `scale⁻²` annule le
  facteur de volume `scale²`; à potentiel fixé, l’action conforme est donc
  `C∞`, constante et son Hessien conforme symétrique est nul.
  `P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D` prouve ensuite
  l’invariance gauge exacte globale dans chacun des deux slots du pairing et
  pour l’action. Le Hessien tiré aux orbites gauge exactes est nul. L’ordre de
  dérivation gauge exacte puis variation de potentiel arbitraire certifie le
  noyau mixte nul; l’ordre log-conforme puis variation de potentiel arbitraire
  certifie aussi un bloc mixte nul.
  `P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D` ferme maintenant
  le Hessien physique à métrique fixée entre deux variations lisses arbitraires
  du potentiel sous forme bilinéaire symétrique intégrable. Les dérivées de
  ligne et mixtes coïncident avec ce Hessien, et les directions gauge exactes
  appartiennent à ses deux noyaux. Le bloc métrique
  arbitraire--potentiel, la dépendance Fréchet générale,
  et l’interaction/chart/core/Jacobi/Fredholm Candidate-A restent ouverts.
  `P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D`
  ferme maintenant le Lorenz différentiel lisse pour toute métrique générale
  fournie : potentiel relevé, divergence Levi-Civita, loi d’overlap,
  linéarité et vrai Faddeev--Popov `δ_g d`, égal au wave covariant dans chaque
  carte. La gate canonique précédente est exactement sa spécialisation
  intrinsèque et donne `δ(d c) = +□c`.
  `P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D` réutilise, sans
  nouvelle structure ni axiome, le datum Green--Stokes scalaire déjà isolé :
  le défaut FP devient exactement le courant orienté du cut-bulk et s’annule
  sur tout domaine Green-isotrope existant, avec spécialisation Dirichlet.
  Sous ce même datum, le Green-core physique de masse nulle est exactement
  chaque composante FP. La densité minimale par cutoffs déjà prouvée rend sa
  projection de graphe injective; le produit fini `Sector × Fin 2` possède un
  vrai cœur lisse apparié dense et une réalisation mono-valuée qui coïncide
  avec le FP existant sur ce cœur. La closabilité FP intrinsèque conditionnelle
  n’est donc plus un résidu.
  `P0EFTJanusProgramPGlobalAbelianFaddeevPopovLagrangianSelfAdjoint4D`
  spécialise aussi la triple frontière complétée déjà disponible : sous des
  entrées de triple, une condition lagrangienne et le paquet de clôture
  analytique existant, chaque composante réelle a un domaine dense et son
  domaine adjoint actuel égale son domaine de réalisation. L’inclusion appariée
  finie est dense/injective et coïncide avec le vrai FP sur son cœur lisse
  admis. Aucun habitant du paquet analytique n’est construit : ce résultat
  reste conditionnel. La route existante
  `...IntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D`
  est maintenant raccordée elle aussi : ses données PDE, son estimation de
  graphe et sa coercivité décalée suffisent déjà; Rellich est inconditionnel,
  le résolvant réel borné donne l’égalité des domaines adjoints, et la
  réalisation lisse admise est exactement le FP intrinsèque. La divergence
   locale y reconstruit aussi le datum Green--Stokes global avec exactement le
   même Green-core scalaire. Ces données ne
   sont pas habitées ici. L’audit des constructeurs confirme que les routes
   énergie/Gårding et décomposition positive redemandent exactement ces
   entrées. Dirichlet ferme le courant de bord, pas l’ellipticité ni la
   coercivité du wave lorentzien complet; le coefficient temporel strictement
   négatif déjà prouvé le sépare du régulateur elliptique `H¹` positif.
   Cette branche ne doit donc être habitée qu’après choix explicite d’une
   réalisation elliptique auxiliaire. Restent l’identité Stokes 4D
   inconditionnelle et l’identification au domaine du Hessien total, ainsi que
   l’adjoint compatible avec une métrique générale; le transport pondéré déjà
  construit règle le facteur deux, pas l’annulation tangentielle globale.
  `P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D` ferme la moitié trace du
  de Donder général sans choix de carte : `tr_g h`, `d(tr_g h)`, la correction
  `-1/2 d(tr_g h)` et son gradient sont des champs globaux lisses.
  `P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D`
  construit maintenant la vraie dérivée de Levi-Civita induite sur `Sym²` dans
  chaque présentation, avec lissité, symétrie, `∇g = 0` et loi d’overlap
  rang trois complète. Les gates de divergence la contractent directement
  dans les cartes, prouvent la loi covectorielle, puis recollent `div_g h`
  en une 1-forme globale lisse. Son assemblage avec la correction de trace
  ferme le de Donder complet et sa formule locale, sans nouveau postulat ni
  fibré rang trois artificiel.
  `P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderLinear4D` prouve maintenant
  son additivité et son homogénéité depuis ces briques locales et le bundle en
  application linéaire. La gate
  `P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D` relève les
  sorties, construit leur contraction lisse, prouve son intégrabilité pour la
  mesure générale existante et fournit une forme bilinéaire symétrique avec
  polarisation quadratique exacte. Elle ne revendique ni adjoint, ni
  réalisation `H¹`, ni insertion dans l’action Candidate-A.
  `P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D` réutilise le
  frame fini existant pour ajouter la caractéristique relevée, construire le
  graphe Hilbert raffiné et étendre exactement ce pairing lorentzien par un
  Hessien borné symétrique. La gate `...GraphPairingC2Chart4D` en fait une
  action quadratique `C∞` dont le second Fréchet constant redonne le pairing
  sur le cœur lisse. Enfin
  `P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D` assemble deux copies
  métriques avec Lorenz dans un sous-chart physique commun et injecte son cœur
  dans le tangent gauge-fixed typé avec non-minimal nul. Il ne revendique pas
  le chart total ni le Fredholm final.
  `P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D` installe aussi les neuf
  espèces globales distinctes `c/c̄/B` (deux triplets sectoriels
  `U(1)^2`-valués et un triplet tangent difféomorphe), leur différentiel non
  minimal carré nul, et l’extension
  injective de la configuration physique. Les wrappers et leurs produits
  portent désormais leurs vraies structures de modules réels, avec projections
  et inclusion physique linéaires. Le tangent gauge-fixed est le noyau de la
  projection vers les anciens coefficients ghost/auxiliaire : ils sont donc
  fixés et ne doublonnent plus les neuf champs typés. La règle physique
  abélienne globale
  `sA = -dc`, sa nilpotence, son vrai `sΨ` à mesure finie et son branchement
  sur les métriques, potentiels Maxwell et champs non minimaux Candidate-A
  sont fermés. Le sous-chart physique branche désormais les perturbations
  métriques de Donder avec Lorenz; la règle difféomorphe complète `sg` et les
  directions non minimales du chart total restent ouvertes.
  `P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D`
  construit toutefois le vrai opérateur FP mono-métrique
  `c ↦ B_g(L_c g)` depuis l'action de Cartan existante. Candidate A en fournit
  deux copies canoniques mais un seul triplet non minimal difféomorphe : le
  choix d'une somme, différence ou pondération des deux conditions n'est fixé
  nulle part et n'est donc pas ajouté artificiellement.
  `P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D` ferme désormais
  le second-ordre directionnel exact des slots `llAuxMetric × llMeasure`
  directement depuis `globalCandidateALLAction`. La symétrie est prouvée;
  `P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D` construit en plus une
  complétion Hilbert de graphe, l’inclusion lisse dense injective et le
  représentant de Riesz borné qui redonne ce Hessien exact sur le cœur.
  Toutes les directions `llMeasure` pures restent toutefois dans son noyau.
  Leur radical fermé, le quotient Hilbert action-faithful et l’opérateur
  descendu sont maintenant explicites. Son injectivité équivaut exactement à
  l’égalité « radical mesure = noyau pondéré total », qui peut échouer lorsque
  les poids d’énergie LL s’annulent; une coercivité reste ensuite nécessaire
  pour l’image fermée. Aucun Fredholm n’est donc ajouté artificiellement.
  `P0EFTJanusProgramPGlobalGHYSameActionHessian4D` ferme séparément le contrôle
  GHY canonique fixe : sous l'hypothèse explicite que la famille sélectionne
  cette branche, l’action exacte et ses deux dérivées de Fréchet sont nulles.
  Le datum mobile reste dans le même sommant Robin et n'est pas annulé. Le bloc
  faces nulles/contre-termes/joints possède aussi son vrai Hessien nul le long
  de toute mise à l’échelle des normalisations de générateurs, par la
  transgression exacte face--joint existante. Ses variations géométriques et
  normales générales restent ouvertes.
  Aucun théorème formel
  d’inhabitabilité du type historique n’est revendiqué.
  Côté Hessien, sous flot difféomorphe non linéaire fourni, différentiabilité
  de tous ses générateurs et criticité, leur span ponctuel est maintenant un
  noyau bilatère exact. La Hessienne descend par ce quotient puis par le
  quotient combiné avec `U(1)²`. Cela ne construit ni le flot neuf-blocs, ni
  le chart, ni le pont tangent global → chart.
  Le pairing Maxwell global construit sur la courbure est gauge-dégénéré et
  n’est pas utilisé comme dual des potentiels; les résultats ci-dessus portent
  seulement sur les orbites gauge exactes et les directions métriques
  log-conformes.
- `VARCOH` ferme la cohomologie **fonctionnelle globale** sur ces cartes et
  le noyau de la troncature naturelle finie. Il ne prétend pas construire le
  bicomplexe variationnel horizontal local complet des densités de jets.
- `ADM` ferme toute la chaîne réellement dérivée dans la réduction FLRW :
  Legendre, primaires, crochet secondaire, préservation et rang local ouvert.
  Le compte `7` degrés de liberté reste la cible arithmétique conditionnelle;
  aucun shift ni crochet fonctionnel de champs n’est caché dans ce certificat.
- `STABILITY` sépare formellement la Hessienne ambiante de la variation
  contrainte. La courbe poussière exacte donne des configurations distinctes
  de même énergie : elle interdit une lecture de minimum strict isolé dans ce
  secteur, sans prouver une instabilité globale.
- `VACUUM` rassemble le minimum proportionnel 1D, le no-go de rang du vide
  FLRW, la direction contrainte sourcée et la liberté de schéma. Ces résultats
  sont compatibles mais ne sélectionnent pas un vide physique global.
- `MICRO` rassemble la réduction exacte du parent disponible, sa réciprocité
  de Helmholtz et la sélection discrète conditionnelle. Le contre-exemple à
  deux parents prouve que les hypothèses actuelles ne sélectionnent ni
  l'action réduite ni ses parties finies.
- `SCALE` combine les no-go géométrique, spectral, chaleur et charge : toutes
  les lois disponibles sont covariantes sous une même dilatation. Une longueur
  absolue exige donc une donnée dimensionnée indépendante, puis un vide stable.
- `DIRAC` et `REGULATOR` sont `DONE` à leurs portées déclarées; ce dernier
  fournit un régulateur nucléaire de référence sans l’identifier à la
  Hessienne. `BRST/QUILLEN/ANOMALY` conservent des certificats de frontier
  intégrés et sans nouvel axiome. `HESSIAN` est désormais une `FRONTIER` :
  l’interface locale sur domaine ouvert est fermée, mais son habitant métrique
  général et l’accord avec la cible Fredholm restent à construire. Le pont chaleur–Hessienne
  ne peut reprendre qu’après choix d’une action et d’un opérateur compatibles.
- `SCHEME` est plus qu’un TODO technique : le no-go construit deux libertés
  de schéma effectives. Sans donnée microscopique supplémentaire,
  `SCHEME-GLOBAL-01` est impossible à déduire des hypothèses actuelles.

Ces distinctions expliquent pourquoi les portes terminales plus fortes
`T03`–`T06` restent décochées ci-dessous : elles exigent encore l'atlas
physique brut, le système local par composantes et le bicomplexe local, pas
seulement leur fermeture fonctionnelle chartwise.

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
contrat `ProgramStatus`. L'audit complet a été revérifié vert le 2026-07-26.
Aucune porte
terminale n'est fermée.

Mise à jour : `P0EFTJanusMappingTorusGlobalSmoothScalarWave4D` ferme le
paquetage global lisse, la linéarité réelle et l'intégrabilité de l'onde
scalaire canonique. `P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D`
ajoute le produit global lisse et la règle de Leibniz du gradient local.
Le jet-produit covariant symétrique et sa contraction d'onde exacte sont aussi
fermés algébriquement. Son identification à la dérivée seconde effective du
produit global est maintenant prouvée. L'appariement global
lisse des gradients et la règle ponctuelle globale de l'onde sont fermés.
Les lois conformes de courbure et le Hessien EH spatial sont fermés. Le cœur
Einstein--Maxwell conforme restreint assemble désormais ce Hessien et le bloc
potentiel Maxwell; son bloc croisé conforme--potentiel est identifié au vrai
Hessien mixte same-action existant et vaut zéro. Le mélange dans des directions
métriques arbitraires attend toujours une carte concrète de l'espace des
métriques.
`P0EFTJanusMappingTorusSpatialConformalMetricJet4D` ferme maintenant les lois
locales du coefficient, de la matrice et de la dérivée première de la métrique
conforme positive existante. L'inverse, Christoffel, Riemann, Ricci et la
contraction scalaire sont fermés.
### Hessien conforme spatial — fermé

- courbe exponentielle et densités d'ordres `0`, `1`, `2` ;
- dérivation deux fois sous l'intégrale compacte ;
- Hessien bilinéaire symétrique ;
- égalité exacte avec la dérivée seconde diagonale en zéro ;
- inverse de la métrique conforme explicite.

`P0EFTJanusMappingTorusSpatialConformalEinsteinMaxwellCoreHessian4D` ajoute la
forme bilinéaire symétrique sur le produit des directions conformes spatiales
et des directions de potentiel abélien. Son bloc croisé est exactement
`conformalPotentialFrameFreeMaxwellMixedHessian`, nul par le théorème
same-action à deux paramètres déjà disponible. Aucune direction métrique
lorentzienne arbitraire n'est ajoutée.

Fermeture géométrique : la loi de Christoffel contractée, sa dérivée,
Riemann, Ricci, la séparation Palatini/quadratique et leur contraction
scalaire prouvent maintenant la formule conforme standard depuis la
construction coordonnée brute. La spécialisation exponentielle locale et
globale donne
`R(g_t) = exp(-2tu) (R(g₀) - 6t □u - 6t² ⟨du,du⟩)`.
Le ratio de volume `exp(4tu)` identifie ensuite la vraie action
Einstein--Hilbert frame-free à la courbe différentiée ci-dessus ; sa seconde
variation diagonale en zéro est donc exactement le Hessien symétrique certifié.

### Pont d'adjoint cinétique diagonal — fermé (2026-08-01)

- les poids sont ceux de l'action Einstein--Hilbert existante :
  `w₊ = 1/(2κ₊)` et `w₋ = 1/(2κ₋)` ;
- l'adjoint 4D du générateur diagonal pour le pairing de DeWitt pondéré est
  exactement `w₊F₊ + w₋F₋`, avec unicité des deux poids ;
- la condition globale lisse et son FP sont construits depuis les deux briques
  mono-métriques existantes ;
- le symbole spatial vaut `(w₊+w₋)|ξ|²`; l'annulation des poids l'annule, leur
  non-annulation donne le noyau trivial à covecteur non nul ;
- limite : les blocs normal/bord, l'identification à l'action covariante
  non linéaire et les fermetures de domaines restent hors de ce pont.

### Graphe BRST diagonal et insertion bulk — fermés (2026-08-01)

- le cœur partagé contient deux perturbations métriques et un seul triplet
  difféomorphe ; son BRST est nilpotent et sa condition est exactement le
  poids cinétique dérivé ci-dessus ;
- son image lisse est injective et dense dans le graphe off-shell complété ;
  le Hessien borné symétrique, le représentant de Riesz et l'action `C²`
  coïncident exactement avec la polarisation de `sΨ` ;
- ce graphe remplace les deux blocs de Donder dans le produit bulk existant,
  à côté du graphe abélien apparié, de la matière SpinC primitive et du graphe
  LL complet ; l'action a pour seconde dérivée exacte le Hessien assemblé ;
- le produit imbriqué `WithLp 2` de ces quatre facteurs est un Hilbert réel
  complet, continûment équivalent au chart précédent ; le même cœur reste
  dense/injectif et le Hessien exact possède un Riesz borné auto-adjoint ;
- le même cœur possède un raccord linéaire injectif vers les slots typés
  existants, sans seconde copie Lorenz ni second triplet difféomorphe ;
- `HESSIAN-GLOBAL-01` reste ouvert uniquement au-delà de cette insertion :
  identification à l'action covariante complète, chart métrique d'ordre
  supérieur, blocs normal/bord et Einstein--Maxwell métrique général,
  domaines/adjoints, portée fermée et radical fini LL off-shell, puis somme
  Fredholm fidèle finale. Le cœur typé est déjà fidèle; la cible spectrale
  historique `ι × Fin 8` ne l'est pas comme contenu total.

### Réductions fortes Einstein--Maxwell et LL — fermées (2026-08-02)

- l'intégrale sur toute mesure finie est une application linéaire continue du
  cœur scalaire fort; des lifts forts `C²` du volume/courbure ou du
  volume/pairing suffisent donc aux vraies lignes Einstein--Hilbert/Maxwell ;
- le cœur C² ferme désormais produit, racine et jets spatiaux d'ordre deux;
  reste à construire la vraie application métrique générale vers ce cœur pour
  le volume, la courbure scalaire et le pairing Maxwell ;
- tout opérateur borné auto-adjoint à portée fermée et noyau fini a conoyau
  fini; appliqué au Riesz LL complet, ceci réduit le Fredholm off-shell aux
  deux seules estimées portée fermée/radical fini ;
- les no-go Hessien nul interdisent de déduire le Fredholm de la seule
  régularité `C²`; une strate elliptique non dégénérée et son domaine de bord
  doivent être construits explicitement, sans les cacher dans un nouvel axiome.

### Bloc bord par reparamétrisation finie — fermé (2026-08-01)

- les paramètres de normalisation des faces nulles sont indépendants dans le
  vrai Hilbert fini `EuclideanSpace ℝ NullFace` ;
- la transgression face--joint existante prouve que l'action exacte
  `GHY + faces nulles + contre-termes + joints` y est constante ;
- sa première et sa seconde Fréchet exactes sont nulles, et son Riesz nul est
  borné auto-adjoint ;
- limite : les déformations normales et la géométrie de bord générale restent
  ouvertes.

### Raccord terminal H14--D11 au frame basepoint — fermé (2026-08-21)

- la façade terminale construit désormais la famille de vrais noyaux, la
  factorisation naturelle sectorielle, le frame unitaire en norme opérateur et
  la trace nucléaire nulle depuis un seul frame admissible `0 → a` ;
- aucune famille d'isomorphismes pairwise `(a,b)` ni donnée `zeroTrace`
  indépendante ne reste en entrée ;
- restent honnêtement externes : représentation/refinement/pullback, cinq lois
  de norme sectorielles du frame basepoint, sa régularité en norme opérateur et
  le paquet spectral selected-trace complet ;
- le paquet spectral exige encore les différences actual/reference, les
  frontières filtrées, les moyennes de slices et leurs identités de
  semi-groupes. Les frontends Bochner fixes ne prouvent pas encore ce pont ; le
  décompte terminal demeure donc `0/14`.
