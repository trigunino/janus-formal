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
