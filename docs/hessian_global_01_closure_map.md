# HESSIAN-GLOBAL-01 — carte de fermeture autoritative

Cette page est l'unique registre de fermeture de `HESSIAN-GLOBAL-01`.
Les autres documents peuvent expliquer l'historique, mais ne doivent pas
maintenir une seconde liste des résidus.

## Portée terminale

- La famille d'action et son Hessien de Fréchet sont définis sur un ouvert
  admissible du tangent métrique général et restent `C²` hors-shell.
- La réalisation Fredholm terminale est évaluée sur la strate stationnaire
  elliptique avec un domaine de bord commun. La stationnarité n'est pas un
  nouvel axiome : c'est la portée du Hessien physique utilisé pour le
  déterminant et la stabilité.
- Le tangent physique est D10-free. D10 reste réservé au régulateur et au
  déterminant de référence.
- Aucun ansatz conforme, diagonal ou à mesure de Dirac ne peut fermer une
  obligation générale.

## Registre

| ID | Obligation | Statut | Déclaration canonique |
|---|---|---|---|
| H00 | Carte locale sur un ouvert, Euler et Hessien ambiants, symétrie | `DONE` | `global_candidateA_local_hessian_gate`, dans `P0EFTJanusProgramPGlobalLocalVariationalChart4D` |
| H01 | Racine physique sélectionnée intrinsèquement Sylvester-régulière | `DONE` | `GlobalCandidateAPositiveSelectedRootCertificate4D.intrinsicRegular`, dans `P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D` |
| H02 | Régularité jointe paramètre–point et carré exact de la branche locale | `DONE` | `c2LocalRootPullbackBranch_contDiffOn`, `c2LocalRootPullbackBranch_square`, `c2LocalRootPullbackBranch_jointContinuous`, dans `P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootJointRegularity4D` |
| H03 | Domaine métrique général réel, volume `C²`, cœur lisse fidèle et dense | `DONE` | `regular_general_metric_c2_chart_gate`, dans `P0EFTJanusProgramPRegularGeneralMetricC2Chart4D` |
| H04 | Maxwell métrique générale : `dA`, inverse variée, densité et intégrale `C²`, accord au point de base | `DONE` | `regular_general_metric_c2_maxwell_gate`, dans `P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D` |
| H05 | Einstein–Hilbert métrique générale : courbure/densité spatiale `C⁰`, dépendance paramétrique `C²`, accord avec l'action intrinsèque | `DONE/P1` | `regular_general_metric_c2_einstein_hilbert_gate`, dans `P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D` |
| H06 | Matière SpinC primitive : même action et Hessien Fredholm | `DONE` | `globalCandidateAMatterFiniteGraph_sameActionHessian` et `primitiveSpinCGeometricSignedMassRealOperator_fredholm` |
| H07 | Neuf champs non minimaux typés, sans D10 ni duplication | `DONE` | `globalTypedNonminimalBRST_square_zero`, `globalMinimalPhysicalTangentInclusion_injective`, dans `P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D` |
| H08 | Graphes BRST diagonal/Abelian et cœur total typé fidèle | `DONE` | `diagonalExtendedBulkGraphTypedCoreLinearMap_injective`, dans `P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D` |
| H09 | LL complet same-action ; quotient stationnaire Fredholm d'indice zéro | `DONE/ON-SHELL` | `globalCandidateAFullLLFieldQuotientRieszOperator_fredholm_criterion_of_stationary`, `globalCandidateAFullLLFieldQuotientRieszIndex_zero_of_stationary` |
| H10 | Déplacement normal et géométrie générale de bord : famille induite, second Fréchet et accord same-action | `OPEN/P2` (fondation holonome, cœur conjoint, métrique/inverse induites, connexion et accord physique à la base compilés ; normalisation unitaire, carré causal, seconde forme symétrique, trace fidèle, densité induite, intégrande, action deux-feuilles et second Fréchet symétrique compilés sur un ouvert GHY contenant zéro ; reste uniquement l'identification de germe avec l'unique action mobile Candidate-A déjà reliée au ledger) | responsable unique : `P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D` ; helpers analytiques : `P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D`, `P0EFTJanusProgramPThroatFiniteFrameReconstruction4D`, `P0EFTJanusBoundedFiberJetSubstitutionC2`, `P0EFTJanusBoundedFiberJet2SubstitutionC2`, `P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D` |
| H11 | Mesure et domaine communs : Green, adjoints, closabilité et réalisation fermée du Hessien **augmenté** | `WAIT H10/H13, P3` (le graphe BRST–SpinC–LL existant est fermé ; il faut réaliser sur ce même domaine les sept blocs physiques retenus) | responsable unique : `P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D` |
| H12 | Multiplicités typées fidèles, somme Fredholm totale et indice | `WAIT H11, P4` (les multiplicités et la sous-somme SpinC×LL sont compilées ; le Riesz actuel ne porte que le graphe BRST–SpinC–LL et n'est donc pas encore l'opérateur total) | responsable unique : `P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D` |
| H13 | Résidu matière–LL nul sur la même action et identification du vrai Hessien covariant au Hessien augmenté, sans supprimer les sept blocs physiques | `WAIT H10, P4` | critère existant `diagonalExtendedBulkMinimalPhysicalLocalGaugeFixed_eq_augmented_iff`, dans `P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D` |
| H14 | Certificat terminal et passage du ticket à `DONE` | `WAIT H10/H13/H11/H12` | futur `P0EFTJanusProgramPGlobalHessianClosure4D` ; il ne doit contenir aucune nouvelle hypothèse physique |

## Les quatre paquets autorisés par la carte

### P1 — Einstein–Hilbert métrique générale

État : `DONE` (2026-08-02). La gate terminale prouve `0 ∈ U`, la dépendance
`C²` de l'action sur l'ouvert métrique général et l'égalité exacte au point de
base avec `intrinsicEinsteinHilbertAction`. Le pont passe par les courbures
Riemann/Ricci/scalaires intrinsèques déjà disponibles ; aucun ansatz conforme
ni nouvel axiome n'est introduit.

Réutiliser le cœur métrique `C²`, l'inverse et le volume existants. La
courbure scalaire d'une métrique `C²` est une fonction spatiale `C⁰`; seule sa
dépendance au paramètre doit être `C²`. Il est interdit de la relever dans un
cœur spatial `C²`, ce qui imposerait artificiellement une métrique `C⁴`.

### P2 — Déplacement normal et bord général

État : fondation géométrique assemblée et compilée (2026-08-02). Le fichier
responsable réutilise `normalGraph_joint_contMDiff` et le théorème paramétré
`ContMDiffAt.mfderiv`. Le pullback réel de toute métrique lorentzienne
ambiante est désormais une famille lisse jointe paramètre–point
(`normalGraphInducedMetricValue_joint_contMDiff`), symétrique, exactement
égale en zéro à la trace générale existante. Le lieu non nul joint est ouvert;
la compacité de la gorge donne l'ouverture uniforme du domaine paramétrique
`U`. Sur `U`, l'inverse intrinsèque et ses deux identités d'inversion sont
construits. La transversalité de base prouve `0 ∈ U`; la gate compilée est
`normal_boundary_induced_metric_local_family_gate`. Aucune géométrie de bord
libre n'est ajoutée. Le même fichier construit aussi l'endomorphisme relatif
frame-free `g_ref⁻¹ g_t`, son déterminant intrinsèque, la densité
`sqrt |det(g_ref⁻¹ g_t)|`, sa stricte positivité sur `U` et sa continuité
jointe point–paramètre. L'argument local est relié au déterminant intrinsèque
par conjugaison ; aucune frame globale n'est choisie.
Cette densité pondère désormais la mesure canonique de gorge dans
`normalGraphInducedVolumeMeasure`. La mesure obtenue est finie, non nulle sur
`U`, et son intégrale est exactement réécrite contre la mesure de référence.
Pour la métrique intrinsèque à `t = 0`, l'endomorphisme relatif est l'identité,
la densité vaut `1` et la mesure est exactement la mesure canonique existante.
Le quotient de l'espace tangent ambiant par l'image du différentiel du graphe
est maintenant construit sans frame globale et sa dimension `1` est dérivée.
Le projecteur orthogonal métrique descend injectivement à ce quotient; toute
classe non nulle donne une normale non nulle, non isotrope, puis une normale
unitaire de carré causal `±1`. Son expression en coordonnées est `C∞` sur le
lieu non nul et
`normalGraphMetricNormalProjectorCoordinates_eq_inCoordinates` prouve qu'elle
est exactement la carte du projecteur intrinsèque. Enfin,
`exists_eventually_nonzero_normalGraphLocalMetricNormalCoordinates` fournit
autour de chaque point admissible une normale métrique locale lisse et non
nulle, sans choisir de coorientation globale du fibré normal éventuellement
tordu.

La courbure extrinsèque est maintenant dérivée du même graphe, de la même
métrique ambiante et de la véritable connexion de Levi–Civita dans l'atlas
holonome existant. Sa matrice symétrique est raccordée sans changement de
formule à `NonNullBoundaryPointData`; la symétrisation conserve exactement la
trace GHY. `normalGraphHolonomicGHYDensity_neg_normal_orientation` prouve que
le changement simultané de normale et de signe d'orientation laisse la
densité inchangée.

Le recollement de la géométrie d'ordre un est également compilé. Le vrai
Jacobien de transition transporte la différentielle du graphe
(`normalGraphHolonomicFamilyDerivativeCoordinates_transition`), la métrique
induite est indépendante de la carte, et le projecteur normal, son carré puis
la normale unitaire se transportent exactement dans la seconde carte. Ces
résultats réutilisent les transitions holonomes existantes et ne choisissent
ni nouvelle frame ni nouvelle normale physique. Le terme de Levi–Civita a
ensuite été recollé avec la dérivée du vrai Jacobien variable : les deux
corrections hessiennes de transition s'annulent exactement dans
`normalGraphHolonomicTransportedMetricUnitNormalCovariantDerivative_transition`.
La contraction métrique du Weingarten brut est donc indépendante de la carte
pour le même germe normal transporté
(`normalGraphHolonomicRawExtrinsicCurvatureCoordinates_chart_independent_transport`).

La coorientation physique n'est plus un résidu. La carte tubulaire canonique
existante est réutilisée sur son vrai ouvert normal : son différentiel est
injectif sur toute la bande admissible, donc sa verticale canonique est
transverse au graphe mobile. Elle descend sur le double d'orientation en une
classe quotient globale non nulle (`normalGraphCanonicalNormalClass_ne_zero`).
La normalisation métrique intrinsèque donne alors un champ unitaire partout
non nul et orthogonal au graphe. Sa loi de deck impaire est prouvée dans
`normalGraphCanonicalMetricUnitNormalLift_deck`, et sa régularité globale
`C∞` dans `normalGraphCanonicalMetricUnitNormalLift_contMDiff`. Ces résultats
réutilisent le projecteur normal et les trivialisations déjà disponibles ;
aucune normale, frame ou hypothèse physique supplémentaire n'est fournie.

Le raccord avec le germe Weingarten lisse historique est maintenant
explicite. Dans toute carte holonome, la normale canonique est orthogonale au
même différentiel du graphe, son projecteur métrique la fixe et son carré a
valeur absolue `1`. Le théorème
`normalGraphCanonicalHolonomicLocalUnitNormalCoordinates_eq` identifie donc
exactement la normale locale normalisée à la normale globale au point
d'ancrage. La courbure Weingarten correspondante conserve sa régularité
jointe `C∞` par
`normalGraphCanonicalHolonomicWeingartenExtrinsicCurvature_contMDiffAt`.
Cette orthogonalité est maintenant établie sur un vrai voisinage de carte
source avec l'inverse métrique intrinsèque préexistante :
`normalGraphHolonomicInducedMetricInverseCoordinates_eventually_rightInverse`
et
`normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_eventually_orthogonal`.
Sa différentiation donne le pont exact
`normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_eq_weingarten`.
La forme de Gauss descendue dans le ledger et le germe Weingarten lisse ne
sont donc pas deux représentations concurrentes de la courbure extrinsèque.

Le transfert vers la valeur chart-free est désormais formalisé sans donner
une structure de variété aux matrices. Les coefficients de l'inverse et de la
seconde forme sont traités séparément, puis contractés par sommes finies dans
`normalGraphHolonomicLocalMeanCurvatureFamily_contMDiffAt`. Le théorème
`normalGraphCanonicalHolonomicWeingartenMatrix_base_eq_gauss` identifie les
matrices, et
`normalGraphCanonicalHolonomicLocalMeanCurvatureFamily_base_eq_gauss`
identifie exactement la valeur du représentant lisse à la contraction globale
indépendante de carte au point d'ancrage. Cette étape réutilise la topologie
existante et n'introduit ni atlas matriciel ni troisième courbure.

La régularité jointe de la coorientation physique n'est plus une obligation
ouverte. La descente paramétrée générique déjà présente,
`mappingTorusInvariantMapProd_contMDiff`, donne
`normalGraphCanonicalLatitudeLift_joint_contMDiff`. Dans la même
trivialisation tangente, le projecteur métrique, son carré causal et sa
normalisation sont composés sans nouveau choix ; le résultat
`normalGraphCanonicalMetricUnitNormalJointCoordinates_contMDiffAt` est `C∞`
en point de bord et paramètre. Son accord au point de base avec la normale
physique antérieure est
`normalGraphCanonicalMetricUnitNormalJointCoordinates_base_eq`. Le passage
par l'inverse d'une unique carte holonome fixe préserve cette régularité dans
`normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_contMDiffAt`.
Les théorèmes `_base_formula`,
`normalGraphCanonicalMetricUnitNormalJointCoordinates_base_reconstructs` et
`normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_base_eq`
prouvent que ce représentant joint est exactement, à l'ancre, la normale
physique holonome déjà utilisée dans Gauss–Weingarten, transport dépendant
compris. L'identité n'est désormais plus limitée à l'ancre :
`normalGraphCanonicalMetricUnitNormalJointCoordinates_eq_intrinsic` identifie
point par point le représentant joint à la normale canonique physique, et
`normalGraphCanonicalJointCoordinateAdmissible_eventually` prouve que son
domaine non nul et les trois trivialisations requises contiennent un vrai
voisinage. Après passage à la carte fixe,
`normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic`
donne exactement la dérivée de l'inverse holonome appliquée à cette même
normale physique. Il ne s'agit donc pas d'une nouvelle coorientation locale.

La projection du double d'orientation disposait déjà du théorème
`orientationDoubleToThroat_isLocalDiffeomorph`. Son `localInverse` est
désormais exposé par `normalGraphOrientationLocalSection`, avec passage par le
point de base, régularité et recomposition locale prouvés. La normale jointe
est ainsi tirée vers le domaine exact `EffectiveThroat × ℝ` sans section
globale supplémentaire. Sa dérivée spatiale, la forme de Weingarten
symétrisée et sa contraction avec l'inverse induit compilent dans
`normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates`,
`normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates`
et `normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily`; ce dernier
est jointement `C∞` au point de base. Le différentiel de la carte et celui de
son inverse fixe sont maintenant reliés sur un vrai voisinage par
`normalGraphHolonomicLocalInverseDerivative_eventually_rightInverse`. Il en
résulte l'orthogonalité locale exacte de cette même normale physique dans
`normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventually_orthogonal`.
Après passage par l'unique carte source canonique, la dérivation
Gauss–Weingarten donne l'égalité brute, matricielle puis contractée avec la
valeur Gauss chart-free dans les théorèmes
`normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss`,
`normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix_base_eq_gauss`
et
`normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_base_eq_gauss`.
Le transfert au point d'ancrage est donc fermé. L'unicité locale des choix
réancrés est aussi compilée :
`normalGraphOrientationLocalSection_eventuallyEq_reanchored` pour la section
d'orientation et
`normalGraphHolonomicLocalInverse_eventuallyEq_reanchored` pour l'inverse de
la carte ambiante. Le germe de coordonnées du graphe et le représentant de la
normale se réancrent eux aussi dans
`normalGraphHolonomicCoordinateGerm_eventuallyEq_reanchored` et
`normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventuallyEq_reanchored`.
La covariance source est désormais complète : les transitions tangentielle
et cotangentielle préservent l'appariement, puis les lois
`_natural_of_eventuallyEq` transportent la différentielle du graphe, la
dérivée normale et la forme de Weingarten brute puis symétrique. L'adaptateur
bilinéaire continu est prouvé égal à la matrice historique par
`normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_toMatrix`;
il n'introduit donc aucune seconde courbure.
`normalGraphThroatContractedTrace_natural` donne enfin l'invariance de la
trace et
`normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eventually_eq_reanchored`
l'égalité sur un voisinage admissible. Composé avec
`normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_base_eq_gauss`
à chaque ancre, ce résultat ferme l'accord point par point avec la courbure
moyenne de Gauss chart-free.

Le jet d'ordre deux du graphe est désormais écrit dans la carte source
canonique installée par Mathlib. Sa loi de transition exacte exhibe le défaut
`D²T`; ce terme s'annule avec le terme inhomogène de Christoffel dans
`normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt_transition`.
La contraction avec la normale globale donne alors la seconde forme
fondamentale de Gauss. Ses versions brute, symétrique et matricielle sont
indépendantes de toute carte holonome ambiante dans les théorèmes
`normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_chart_independent`,
`normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_chart_independent`
et
`normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_chart_independent`.
Il n'y a ni nouvelle coorientation ni seconde représentation du bord.

La complétion `L²` antiperiodique existante a été auditée et n'offre pas
l'évaluation ponctuelle nécessaire. Sans introduire de déplacement scalaire
indépendant, `NormalBoundaryC2JetCore` est donc défini comme la fermeture
uniforme des vrais jets d'ordre deux des sections normales existantes. Le
plongement lisse y est injectif et dense, l'espace est complet, l'évaluation
est continue et la loi impaire du deck subsiste par densité. Le graphe
`normalBoundaryC2Graph` est défini sur ce cœur entier ; il est globalement et
jointement continu en déplacement–paramètre–point, et
`normalBoundaryC2Graph_smooth` prouve son accord exact avec le graphe lisse
initial. Il ne s'agit donc ni d'une troisième représentation ni d'un cas
scalaire restreint.

Les trois composantes du même jet complété sont maintenant toutes exposées
par des applications linéaires continues. En plus de la valeur,
`normalBoundaryC2JetCoreFirstAt` et `normalBoundaryC2JetCoreSecondAt` évaluent
les dérivées tangentielles première et seconde ; leurs théorèmes `_smooth`
prouvent l'accord définitionnel avec les vrais jets des déplacements lisses.
Le futur intégrand GHY complété peut donc être construit algébriquement sur ce
même cœur, sans prétendre qu'un élément de sa fermeture est lui-même lisse.

La contraction globale `g⁻¹K` est maintenant
`normalGraphCanonicalGaussMeanCurvature`; son caractère impair sous deck est
compilé. Le produit avec le signe d'orientation et la densité frame-free de la
mesure induite donne `normalGraphCanonicalInducedGaussGHYIntegrand`, invariant
sous le renversement simultané. Les deux relèvements canoniques existants
donnent des intégrandes identiques et l'action mobile
`normalGraphCanonicalTwoSheetGaussGHYAction`; le théorème
`normalGraphCanonicalTwoSheetGaussGHYAction_eq_two_mul_first` contrôle
exactement la multiplicité deux. La projection du premier relèvement vers
`canonicalLatitudeThroatMap` est définitionnelle : la densité relative
insérée est donc bien celle de `normalGraphInducedVolumeMeasure`, sans second
déterminant ni double comptage.

Le pont vers la brique historique est désormais explicite et compilé. La
géométrie mobile remplit directement `NonNullFaceDatum`; son `weight` est le
facteur de Radon–Nikodym entre la densité coordonnée du ledger et la mesure
canonique déjà utilisée. Le théorème
`normalGraphCanonicalGaussNonNullFaceDatum_curve_zero_eq_integrand` identifie
point par point la valeur en zéro de l'exacte courbe GHY existante à
l'intégrande mobile. Après intégration sur les deux relèvements,
`normalGraphCanonicalTwoSheetGaussGHYLedgerAction_eq` prouve l'égalité exacte
des actions. Il n'existe donc plus deux formules GHY concurrentes.

La promotion dans l'action centrale est maintenant compilée.
`GlobalCandidateANonNullBoundaryDatum` n'accepte que deux provenances : le
ledger fini fixe historique ou le graphe normal mobile construit ici.
`globalCandidateAGHYAction` évalue cette provenance unique ; aucune valeur
scalaire GHY libre n'est stockée. Le constructeur mobile est exactement
`normalGraphCanonicalTwoSheetGaussGHYAction`, et
`globalCandidateANonNullBoundaryAction_normalGraph_eq_ledger` le réidentifie
au ledger installé. Les transformations de données déjà présentes conservent
le même datum. L'ancien théorème d'annulation exige désormais explicitement
la branche fixe, et la covariance générale porte le vrai bloc Robin au lieu
de le supprimer.

La perte de dérivée est désormais traitée sans axiome physique. Le helper
`P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D` construit le
cœur métrique de bord `C³`, avec inclusion lisse exacte des métriques générales,
image dense et injective, projection continue vers le cœur bulk `C²` et trace
d'ordre trois. Le gate compilé est
`regular_general_metric_boundary_c3_core_gate`. Le fichier responsable assemble
ce cœur avec le cœur normal `C²` dans un espace de Banach conjoint ; injectivité,
densité et complétude sont enregistrées par
`normal_boundary_functional_core_gate`. Tous les blocs bulk continuent donc de
voir exactement la projection `C²` existante.

Les évaluations nécessaires sur le même graphe complété sont compilées.
`candidateANormalBoundaryRelativeMetricEntryAtGraph`,
`candidateANormalBoundaryRelativeMetricFirstEntryAtGraph`,
`candidateANormalBoundaryRelativeMetricSecondEntryAtGraph` et
`candidateANormalBoundaryRelativeMetricThirdJetAtGraph` exposent les jets
métriques d'ordres zéro à trois et sont jointement continus en métrique,
déplacement, paramètre et point de bord. Leurs théorèmes `_smooth` se réduisent
aux évaluations lisses déjà certifiées par le helper `C³`, sans dupliquer les
matrices physiques.

L'audit du repère a aussi éliminé une fausse piste. Le dualiseur positif de
gorge déjà présent sépare les covecteurs, mais ne fournit pas à lui seul leur
reconstruction continue. La brique 4D
`P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D` contenait en
revanche l'algèbre exacte à spécialiser. Le helper compilé
`P0EFTJanusProgramPThroatFiniteFrameReconstruction4D` construit, avec la seule
métrique intrinsèque non dégénérée déjà prouvée, l'opérateur du repère fini
redondant, son inverse lisse et les coefficients lisses qui reconstruisent
exactement toute section tangente. Il ne choisit aucune base globale et
n'ajoute aucune donnée géométrique.

Ce même helper contient maintenant l'algèbre globale nécessaire au GHY. Les
applications canoniques d'analyse et de synthèse vérifient exactement
`synthesis ∘ analysis = id`. L'encodage d'un endomorphisme respecte donc la
composition malgré la redondance. Son relèvement `I - P + M(A)` agit comme
l'identité sur le complément du projecteur et vérifie, sans choix de base
globale, `det(I - P + M(A)) = det(A)` et `trace(M(A)) = trace(A)`. La preuve du
déterminant réutilise l'identité de Weinstein–Aronszajn de Mathlib ; la gate
publique est `intrinsic_throat_finite_frame_matrix_algebra_gate`. Cette brique
permettra d'inverser la métrique induite et de contracter la seconde forme
fondamentale dans un champ matriciel global, sans nouvelle géométrie.

Cette reconstruction est consommée par
`normalBoundaryC2JetCoreDifferentialAt` : les lectures de première dérivée du
cœur normal deviennent un covecteur tangent intrinsèque. Le théorème
`normalBoundaryC2JetCoreDifferentialAt_smooth` prouve qu'il s'agit exactement
du différentiel de variété du déplacement scalaire issu de la vraie section
normale sur le cœur dense, et non d'un nouveau champ indépendant.

Le dernier obstacle analytique générique de l'évaluation sur un graphe mobile
est également compilé dans `P0EFTJanusBoundedFiberJetSubstitutionC2`. Ce helper
ne contient aucune donnée géométrique : il évalue un champ borné muni de ses
trois dérivées fibrées compatibles sur un graphe continu borné. Les restes de
Taylor uniformes donnent les premier et second Fréchet exacts, la continuité du
second et `boundedFiberJet3Evaluation_contDiff_two`; la gate publique est
`bounded_fiber_jet_substitution_c2_gate`. Il s'agit de la brique analytique
manquante, pas d'une troisième représentation de l'action.

Son instanciation sur le déplacement normal est maintenant compilée dans
`P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D`.
L'opérateur ponctuel `arctan` est `C²` sur les graphes continus bornés ; le
graphe de latitude obtenu depuis le cœur normal complété est donc `C²` et
`normalBoundaryLatitudeFiberPoint_graph` l'identifie exactement au
`normalBoundaryC2Graph` déjà utilisé par l'action. La sélection locale de la
structure normée canonique du sous-espace supprime seulement un diamant
d'instances Lean ; elle ne change ni le cœur, ni sa topologie, ni la physique.

Le même helper réutilise désormais `finiteSmoothTangentFrame` et le dualiseur
métrique déjà prouvé dans
`P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D`. L'inverse du
dualiseur est exposé comme endomorphisme de fibré lisse, puis le véritable
relèvement tangent de latitude est décomposé en coefficients `C∞`. Ces
coefficients et leurs deux premières dérivées de latitude descendent
exactement par l'invariance du double d'orientation. Leurs versions en
coordonnée brute sont bornées par restriction à l'intervalle
compact canonique `[-π/2, π/2]` atteint par `arctan`, via
`boundedArctanCompactPullbackCLM`. Il n'y a donc ni hypothèse de périodicité,
ni prolongement arbitraire, ni nouveau choix de repère.

La contraction des jets métriques `C³` est maintenant compilée. Les quatre
composantes de latitude coïncident sur le cœur lisse dense avec les dérivées
géométriques d'ordre zéro à trois. Le jet brut obtenu après `arctan` appartient
à `boundedFiberJet3Submodule`; `boundedFiberJet3Submodule_isClosed` et la
densité de `smoothToRegularGeneralMetricBoundaryC3Core` étendent cette
compatibilité à toute la complétion. L'application linéaire continue résultante
est `normalBoundaryRelativeMetricRawJet3CLM`.

La gate générique est donc réellement instanciée :
`candidateANormalBoundaryRelativeMetricFiberEvaluation_contDiff_two` donne la
régularité `C²` sur le cœur métrique-normal complété, et
`candidateANormalBoundaryRelativeMetricFiberEvaluation_apply` l'identifie
exactement à `candidateANormalBoundaryRelativeMetricEntryAtGraph` sur le graphe
physique déjà utilisé. Le certificat public est
`candidate_a_normal_boundary_relative_metric_fiber_c2_gate`.

La dérivée spatiale première requise par la connexion de Levi–Civita ne peut
pas être envoyée dans ce même jet d'ordre trois : cela demanderait à tort une
métrique `C⁴`. Le compagnon analytique
`P0EFTJanusBoundedFiberJet2SubstitutionC2` prouve directement la substitution
`C²` d'un jet valeur–première–seconde dont le composant supérieur est
uniformément continu. Cette continuité vient ici du pullback de la bande
compacte par `arctan`; elle n'est pas une hypothèse physique. Les identités de
dérivation sont étendues du cœur lisse à la complétion par la fermeture de
`jet2DerivativeSubmodule`. L'instanciation physique
`candidate_a_normal_boundary_relative_metric_spatial_first_fiber_c2_gate`
identifie alors, pour chaque générateur spatial déjà présent, l'évaluation
`C²` exacte à `candidateANormalBoundaryRelativeMetricFirstEntryAtGraph`. Le
GHY dispose donc de la métrique mobile et de ses premières dérivées avec la
régularité optimale `C³`, sans dérivée d'ordre quatre.

Ces gates scalaires sont maintenant assemblées, sans nouvelle représentation,
dans le champ matriciel borné
`candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation` et dans ses
matrices de premières dérivées spatiales. Toutes ces applications sont `C²`.
Le déterminant de l'endomorphisme relatif ambiant est le vrai polynôme de
Leibniz dans cette algèbre de champs ; il est `C²` et son évaluation ponctuelle
est exactement le déterminant de la matrice physique déjà stockée. Le
certificat commun est `candidate_a_normal_boundary_metric_matrix_fiber_c2_gate`.

L'inversion ne crée pas une nouvelle représentation. L'évaluation sur le
graphe est prouvée multiplicative et transporte les deux identités de
`generalMetricRelativeC2InverseMatrix`. Elle montre que la matrice évaluée est
une unité exactement sur la préimage du domaine métrique déjà existant. Son
inverse est ensuite écrit par la formule standard déterminant–adjugée :
l'adjugée est polynomiale, et l'inversion du déterminant est `C²` dans
l'algèbre de Banach des champs bornés. Le résultat est `C²` sur cet ouvert et
est égal au témoin C2 antérieur ; le certificat est
`candidate_a_normal_boundary_inverse_metric_matrix_fiber_c2_gate`. Aucun
axiome de non-dégénérescence ni domaine supplémentaire n'est introduit.

Les coefficients lisses fixes déjà présents dans le collier, le repère et la
géométrie de base utilisent désormais exactement le même mécanisme. Le jet
brut `normalBoundarySmoothFieldRawJet3` est construit depuis leurs trois
dérivées de latitude existantes, et
`candidate_a_normal_boundary_smooth_field_fiber_c2_gate` prouve leur
évaluation `C²` exacte sur `normalBoundaryC2Graph`. Ce n'est ni un nouveau
champ dynamique, ni une nouvelle représentation : cette gate sert seulement
à assembler les coefficients fixes avec la métrique mobile déjà complétée.

La métrique relative n'est plus laissée comme substitut de la métrique
physique. `candidateANormalBoundaryActualMetricMatrixFiberEvaluation` la
compose avec la matrice lisse de la métrique de fond déjà présente et réalise
exactement la carte installée `g₀ (1 + g₀⁻¹h)`. Son inverse utilise l'ordre
installé `(1 + g₀⁻¹h)⁻¹ g₀⁻¹` sur le même ouvert métrique. Le certificat
`candidate_a_normal_boundary_actual_metric_matrix_fiber_c2_gate` donne la
régularité `C²` des deux matrices ; aucune troisième représentation ni nouvel
axiome de non-dégénérescence n'est ajouté.

La différentielle du graphe est maintenant assemblée dans ce même repère.
Elle réutilise les dérivées spatiales stockées du cœur normal, les lifts
horizontal et vertical du collier, et l'unique facteur de chaîne
`1 / (1 + r²)` de `arctan`. La contraction finie
`T_i^a g_ab T_j^b` définit la matrice induite complétée et est `C²`; la gate
publique est `candidate_a_normal_boundary_induced_metric_fiber_c2_gate`.

L'inversion induite réutilise maintenant l'algèbre fidèle du repère fini
redondant. L'endomorphisme relatif à la métrique intrinsèque est prolongé
par la formule canonique `I-P+M(A)` sur le complément de reconstruction. Son
domaine est l'ouvert où son déterminant est une unité. Comme pour la métrique ambiante,
l'inverse est la formule déterminant–adjugée déjà utilisée, donc `C²`, avec
identités inverse gauche et droite. La gate publique est
`candidate_a_normal_boundary_induced_metric_inverse_fiber_c2_gate`. Aucun
axiome de non-dégénérescence ni nouvelle représentation n'est ajouté.

L'identification physique de ce prolongement est maintenant fermée. Le pont
réutilise la composition fidèle du repère redondant et prouve que le lift à
zéro est exactement `intrinsicThroatFiniteFrameLiftAt` de l'endomorphisme
relatif de la trace lorentzienne générale. Son déterminant est donc le
déterminant intrinsèque déjà non nul par `HasNoTangentialRadical`. La
compacité transforme la non-annulation ponctuelle en unité de l'algèbre des
fonctions continues bornées. Les certificats publics sont
`zero_mem_candidateANormalBoundaryInducedMetricDomain` et
`candidate_a_normal_boundary_induced_metric_physical_base_gate`. Aucun nouvel
axiome de non-dégénérescence n'est ajouté.

La connexion nécessaire à la seconde forme est maintenant raccordée sans
nouvelle représentation. La dérivée spatiale des coefficients du tangent de
graphe utilise les lifts horizontal/vertical et le deux-jet normal déjà
stockés. La dérivée de la métrique réelle est identifiée à
`regularGeneralMetricC0MetricFirstDerivative`; les coefficients de Koszul et
de Christoffel obtenus sont ensuite identifiés exactement à
`regularGeneralMetricC0KoszulLower` et
`regularGeneralMetricC0Christoffel` sur l'ouvert métrique existant. Le
certificat public
`candidate_a_normal_boundary_graph_connection_fiber_c2_gate` regroupe la
régularité `C²` et cet accord exact avec la même carte métrique.

La normalisation et l'action complétées sont maintenant compilées. La racine
locale déjà construite dans l'algèbre des champs bornés normalise le carré de
la normale sans nouveau choix de coorientation ; le carré unitaire obtenu est
exactement le signe causal de la base. La seconde forme symétrique est le
simple redimensionnement de la forme de Gauss existante. Sa contraction
réutilise le dual de référence, l'inverse induit fidèle et la trace du repère
redondant. Le déterminant induit, normalisé à `1` à la base, réutilise la même
carte de racine pour produire la densité de volume `C²`. L'ouvert commun est
`candidateANormalBoundaryGHYDomain`, ouvert et contenant zéro par la seule
transversalité déjà installée. L'intégrande et l'action deux-feuilles sont
`C²`; `candidate_a_normal_boundary_ghy_second_frechet_gate` expose leur vrai
second Fréchet et sa symétrie. L'intégration passe par la mesure de première
feuille, poussée depuis `canonicalLatitudeBaseMeasure`; le facteur deux est le
facteur déjà prouvé pour les deux feuilles.

Reste pour `H10` : identifier sur un germe de variations lisses cette action
complétée avec `normalGraphCanonicalTwoSheetGaussGHYAction`, donc avec
`globalCandidateANonNullBoundaryAction` via le pont ledger déjà compilé. Cette
égalité de germe identifiera automatiquement le second Fréchet au bloc normal
de la même action Candidate-A.
Le raccord lisse de la métrique ambiante est maintenant exact : la matrice
complétée reconstruit `g₀ + h`, puis le tenseur de toute métrique lorentzienne
admissible fournie avec cette égalité. Le lift canonique de latitude est aussi
identifié au lift utilisé par la substitution pour tout le graphe lisse, et non
plus seulement au paramètre zéro. Les lifts horizontal et vertical sont les
vraies dérivées partielles du même collier joint, et les coefficients du repère
fini reconstruisent exactement le tangent du graphe. Enfin,
`candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_normalGraph`
identifie la métrique induite complétée au tenseur de toute métrique lisse
admissible appliqué aux vrais tangents, tandis que
`candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_historical`
la réidentifie à `normalGraphInducedMetricValue` après le seul pullback par la
double orientation. Le raccord de la métrique induite générale est donc fermé,
et pas seulement sa spécialisation en zéro. Le dual intrinsèque et le lift
fidèle déjà présents transportent ensuite cette égalité jusqu'à
`candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_apply` :
le déterminant complété est exactement celui de l'endomorphisme historique
tiré sur la double orientation. L'isométrie intrinsèque de cette présentation
de période doublée avec la gorge historique est désormais prouvée par
`intrinsicSmoothNondegenerateThroatMetric_orientationDouble_natural`.
Elle conjugue exactement les deux endomorphismes relatifs dans
`normalBoundarySmoothGraphRelativeEndomorphism_intertwines`; l'invariance du
déterminant par conjugaison donne
`candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_eq_historical`.
La branche locale sélectionnée vaut `1` à la base et reste ponctuellement
positive sur un vrai voisinage uniforme
(`candidateANormalBoundaryInducedRelativeVolumeRoot_eventually_pos`). Ainsi
`candidateANormalBoundaryInducedVolumeDensity_smooth_eq_historical` identifie
la densité complétée à `normalGraphRelativeVolumeDensity` sur ce germe, sans
nouvel axiome ni choix de signe. Le contrôle analogue de la normale est
également fermé :
`candidateANormalBoundaryMetricNormalRelativeRoot_eventually_pos` conserve la
branche positive sur un voisinage uniforme et
`candidateANormalBoundaryMetricNormalMagnitude_eq_sqrt_abs` l'identifie à la
racine carrée usuelle de la valeur absolue du carré normal. Enfin,
`candidateANormalBoundaryVertical_smooth_reconstructs` reconstruit le vecteur
vertical canonique directement à partir du lift global déjà présent, sans
nouvelle présentation de couverture. La projection tangentielle générale est
maintenant identifiée au projecteur historique par
`candidateANormalBoundaryTangentialProjectionVector_smooth_eq_historical` et
sa reconstruction ambiante par
`candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_historical`.
Les contractions finies donnent ensuite exactement la normale métrique et son
carré historiques (`candidateANormalBoundaryMetricNormalVector_smooth_eq_historical`,
`candidateANormalBoundaryMetricNormalSquare_smooth_eq_historical`). Enfin,
l'inverse de la magnitude sélectionnée puis la synthèse du vecteur unitaire
sont identifiés à la normalisation intrinsèque existante par
`candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_eq_historical`
et `candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical`.
Restent pour `H10` la géométrie de Gauss, l'intégrande et l'action sur le même
germe admissible. Les branches
historiques de reparamétrisation nulle restent des contrôles, pas un substitut
au bord général.

Checkpoint d'arrêt propre (2026-08-04) : l'audit n'a pas créé une nouvelle
géométrie. Dans le banc de preuve non importé
La premiÃ¨re sous-brique est maintenant promue dans le module de production :
`candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient`, sa
rÃ©gularitÃ© `ContMDiff` et sa reconstruction dans le repÃ¨re sont compilÃ©es.
Le transport de dÃ©rivÃ©e par la section locale est aussi maintenant promu sous
`candidateANormalBoundarySmoothCoefficient_localSection_mfderiv`.
Le raccord de germe complet reste validÃ© dans le banc de preuve non importÃ©
`ScratchHessianHistorical.lean`,
`historicalCandidateANormalBoundaryMetricUnitNormalField_eventuallyEq`
réutilise les germes de section d'orientation et de carte holonome existants
pour identifier, sur un voisinage, la normale reconstruite dans le repère
régulier à la normale locale historique. Le théorème compilé
`historicalCandidateANormalBoundaryMetricUnitNormalField_mfderiv` transporte
alors exactement cette égalité à la dérivée spatiale. Ce checkpoint ne compte
pas encore comme fermeture de production : aucun fichier de `JanusFormal`
n'importe un module `Scratch*`. La prochaine et seule sous-obligation de Gauss
est l'expansion de cette dérivée dans le repère régulier, puis son appariement
avec les briques Christoffel et tangent déjà compilées. Aucune ébauche de cette
étape suivante n'est conservée dans le checkpoint.
À cet arrêt, l'audit `scripts/audit_janus_program_p.py` passe et la compilation
directe de `P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.lean`
réussit ; les avertissements restants sont des avertissements de linter, pas
des erreurs Lean.

Audit de l'action existante : `GlobalBoundaryVariationData.nonNullFaces`
reconstruit toujours le contrôle fixe avec `canonicalThroatNonNullFaceDatum`,
mais ce ledger n'est plus imposé par `globalCandidateAGHYAction`. Le champ
`GlobalCandidateAActionData.nonNullBoundary` sélectionne maintenant la source
géométrique fixe ou mobile. Déclarer la branche fixe constante comme « bord
général » ne ferme donc plus artificiellement H10.

### P3 — Domaine analytique commun

État : socle assemblé et compilé (2026-08-02). Le fichier responsable prouve
le certificat D10-free du domaine physique, la densité et l'injectivité du
cœur lisse diagonal, l'auto-adjonction et le graphe fermé du représentant de
Riesz same-action, puis réexporte les certificats Fredholm SpinC et LL
stationnaire. Il réduit aussi exactement la closabilité FP abélienne au datum
de Green scalaire déjà nommé. L'interface
`ExistingRectangularHilbertGraph.DenseFormalAdjointCore` transforme une vraie
identité de Green sur cœur dense en injectivité de la projection du graphe,
et ses adaptateurs utilisent directement les complétions de Donder et Lorenz
déjà présentes : aucune troisième représentation n'est créée.
Le cas FP est en outre raccordé à l'endpoint analytique minimal déjà
existant par
`globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_closable_of_graphMinimalAnalytic`
et
`globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_selfAdjoint_of_graphMinimalAnalytic` :
quand ce certificat scalaire est disponible, on obtient la closabilité, puis
l'égalité du domaine adjoint et l'identification exacte sur le cœur lisse,
sans second datum de Green.
Les inclusions des paquets tests scalaires finis de de Donder et Lorenz sont
maintenant définies sur les complétions existantes, et leur image dense est
prouvée par la densité lisse scalaire déjà disponible et `DenseRange.piMap`.

L'audit de dépendances corrige ici un ordre auparavant circulaire. Le Riesz L²
déjà construit représente exactement le graphe BRST–SpinC–LL, mais pas les
sept blocs physiques de l'action. Il ne faut donc pas demander à P3 de prouver
la portée fermée et le noyau fini de ce seul opérateur de jauge : les directions
physiques transverses ne sont contrôlées qu'après augmentation par H13.

Reste pour `H11`, après H13 : prolonger la forme augmentée sur la même
complétion fidèle, puis prouver sa fermeture, son domaine adjoint et les
estimées Fredholm bloc par bloc. Pour l'identification différentielle FP la
chaîne existante réduit bien l'obligation à l'identité Green hors-shell, pour
tous champs lisses `field/test`, entre la divergence locale produit et
`-2 * cutBulkCanonicalDivergenceMeasure ... Set.univ`. Les fichiers
`...EulerTangentialFiberCancellation4D` et `...EulerLocalToCutBulkBridge4D`
restent des interfaces `Data`, pas des preuves. La spécialisation Dirichlet
on-shell de `...ProgramPBoundaryTangentGreenStokes4D` est un vrai théorème,
mais elle est trop étroite pour établir la closabilité sur un cœur dense.
Aucune nouvelle complétion physique concurrente n'est introduite.

### P4 — Somme Fredholm fidèle

État : socle assemblé et compilé (2026-08-02). Le fichier responsable
identifie exactement les neuf espèces non minimales comme deux triplets
abéliens sectoriels plus un triplet difféomorphe, conserve l'injection du
cœur typé, et réexporte les vrais blocs same-action SpinC/LL ainsi que leurs
certificats Fredholm disponibles. Le modèle historique `Fin 9` n'est pas
substitué aux champs lisses. La famille scalaire à deux paramètres
`globalCandidateAMatterLLCommonTwoParameterAction` insère maintenant les
directions SpinC et LL dans les deux sommants inchangés de l'action
Candidate-A. Le théorème
`globalCandidateAMatterLLCommonTwoParameterAction_mixed_deriv_eq_zero`
prouve directement que sa dérivée mixte matière–LL est nulle ; ce résultat
n'est plus un champ supposé du pont local générique.

La stabilité Fredholm par produit de deux opérateurs partiellement définis est
maintenant prouvée dans `linearPMapProd_fredholm`. Pour la sous-somme physique
déjà fermée, `globalCandidateAMatterLLFredholmOperator` assemble le véritable
opérateur SpinC avec la complétion LL positive ;
`globalCandidateAMatterLLFredholmOperator_fredholm` prouve son critère
Fredholm. Le quotient du graphe LL complet est exactement équivalent à cette
complétion sur la strate de flux nul, et
`globalCandidateAMatterLL_actualLL_eq_identity_of_stationary` réexporte
l'identification de son Riesz à l'identité directement depuis la stationnarité.

La réalisation du **graphe** fidèle n'est plus à construire :
`globalCandidateAFaithfulSameActionRieszOperator` réutilise exactement le
produit L² diagonal déjà présent, avec un triplet difféomorphe, deux triplets
abéliens, SpinC et LL. Son cœur lisse reste injectif conjointement dans ce
graphe et dans le tangent corrigé à neuf champs. Le théorème
`globalCandidateAFaithfulSameActionRieszOperator_pairing` l'identifie au
Hessien du graphe same-action existant. Il ne contient pas encore les sept
blocs physiques conservés par H13. Comme ce Riesz est auto-adjoint,
`globalCandidateAFaithfulSameActionRieszOperator_fredholm_of_closedRange_finiteKernel`
fournit une réduction abstraite « portée fermée + noyau fini » pour ce graphe,
et
`globalCandidateAFaithfulSameActionRieszOperator_index_zero_of_closedRange_finiteKernel`
force alors son indice à zéro. Ce n'est pas encore l'indice du Hessien physique
augmenté. Aucun calcul sur `Fin 9` n'intervient.

Ordre corrigé : P4 relie d'abord le coefficient mixte concret au champ de
comparaison du pont local, ce qui ferme H13 sur le cœur sans annuler les sept
blocs physiques. P3 réalise ensuite cette forme **augmentée** sur le domaine
commun. P4 assemble enfin ses vrais blocs Fredholm et prouve l'indice de la
somme totale. Ni `Fin 9` ni D10 ne peuvent remplacer ces preuves.

## Critère mécanique de fermeture

Le ticket passe à `DONE` seulement si :

1. H00–H10 sont `DONE` dans ce registre ;
2. H13 est prouvé par égalité, pas fourni comme champ de structure ;
3. H11 puis H12 sont `DONE` pour la forme augmentée, pas pour le seul graphe ;
4. `P0EFTJanusProgramPGlobalHessianClosure4D` compile depuis la façade ;
5. l'audit vérifie les déclarations terminales de P1–P4 et H14 ;
6. les documentations de statut renvoient ici sans liste contradictoire.

## Checkpoint 2026-08-05

Le transport autonome du produit matriciel est compilÃ© dans
`candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_mul`, avec
`normalBoundaryRealMatrixMul` pour lever toute ambiguÃ¯tÃ© de multiplication.

Le morphisme d'Ã©valuation dispose maintenant du lemme pointwise compilÃ©
`candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_apply`.

L'Ã©valuation de la courbure moyenne commute maintenant avec la trace
matricielle via
`candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply`.

La forme de Gauss unitÃ© symÃ©trisÃ©e est maintenant raccordÃ©e au vecteur
historique par `candidateANormalBoundaryMetricUnitGauss_smooth_eq_vector`.

Le pont de domaine demandÃ© est maintenant fermÃ© :
`normalGraphNonNullAt_of_candidate_GHY_mem` dÃ©duit `NormalGraphNonNullAt`
de l'appartenance du relÃ¨vement lisse au domaine GHY Candidate-A.

L'instance tangentielle finie est maintenant installÃ©e localement et
`normalGraphRelativeEndomorphism_injective_of_det_ne_zero` convertit le
dÃ©terminant historique non nul en injectivitÃ© de l'endomorphisme relatif.

Le raccord lisse du domaine au dÃ©terminant historique est compilÃ© dans
`normalGraphRelativeDeterminant_ne_zero_of_candidate_mem`.

Le transfert algÃ©brique `det â‰  0 â†’ Function.Injective matrix.mulVec` est
maintenant compilÃ© dans
`normalBoundaryRealMatrix_mulVec_injective_of_det_ne_zero`.

Le domaine inverse-mÃ©trique fournit maintenant explicitement la non-annulation
pointwise du dÃ©terminant via
`candidateANormalBoundaryInducedRelativeLiftDeterminant_ne_zero_of_mem`.

Le cas de base du domaine canonique est maintenant transportÃ© par
`candidateANormalBoundaryCanonicalTransport_zero_nonNull`, via le lemme
existant `zero_mem_normalGraphNonNullDomain`.

Le transport minimal `candidateANormalBoundaryCanonicalTransport` est maintenant
construit : il projette le champ `metric.metric` dÃ©jÃ  contenu dans l'interface
regular et transporte le dÃ©placement et le paramÃ¨tre. Il n'ajoute aucun choix.

La rÃƒÂ¨gle de rÃƒÂ©ÃƒÂ©criture `candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_apply`
est ajoutÃƒÂ©e ; elle expose explicitement la multiplicitÃƒÂ© deux dÃƒÂ©jÃƒÂ validÃƒÂ©e.

Interface ajoutÃ©e : `candidateANormalBoundaryGraphTangentCoordinates_historical_apply`
permet de rÃ©Ã©crire directement la somme du repÃ¨re rÃ©gulier.

La deuxiÃ¨me brique locale est maintenant promue dans la cible de production :
`candidateANormalBoundaryGraphTangentCoordinates_historical` reconstruit le
tangent du graphe en coordonnÃ©es holonomes, et
`candidateANormalBoundaryGraphTangentCoordinates_historical_eq_source` le
relie au premier dÃ©rivÃ© holonome existant. La cible compile ; H10 reste ouvert
pour les dÃ©veloppements de Christoffel/Gauss et les paquets analytiques.

### Checkpoint trace GHY lisse (2026-08-05)

L'API de frontiere du module de substitution expose maintenant publiquement
`OrientationBoundary`, la multiplication matricielle reelle et deux wrappers
sur `CutThroatBoundary`. Le module leger
`P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYSmoothTraceBridge4D`
compile et prouve
`candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply_mul` :
la courbure moyenne Candidate-A est la trace du produit des deux matrices
evaluees. Aucun axiome physique n'est ajoute. H10 reste ouvert pour identifier
ce produit avec la courbure historique, puis remonter aux integrandes, actions
et Hessiennes.
