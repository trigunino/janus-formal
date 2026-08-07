# HESSIAN-GLOBAL-01 — frontière analytique constructive réduite

Date du lot : **7 août 2026**.

Ce document décrit la route constructive H10–H14 de la branche
`agent/hessian-spinc-maximal-domain`. Les modules ont été écrits selon la
décision du projet de poursuivre l’implémentation sans attendre la validation
Lean complète. Aucun résultat nouveau de ce lot ne doit être présenté comme
certifié par le noyau avant le passage du workflow focalisé.

## Résultat structurel

Le certificat terminal reste :

```lean
global_candidateA_hessian_closure_gate
```

La façade publique est :

```text
P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D
```

La route actuellement privilégiée est :

```lean
global_candidateA_hessian_preferred_analytic_closure_gate
```

Elle consomme trois paquets naturels :

```text
famille Candidate-A à six blocs C² + Robin fourni par H10
sept extensions bilinéaires continues des blocs physiques
inverse sur les compléments finis du noyau et du conoyau
```

Elle reconstruit automatiquement les anciens paquets `family`,
`physicalBound`, `parametrix`, puis le certificat H14.

## SpinC : fermeture géométrique implémentée

La partie SpinC n’est plus une entrée analytique du terminal. La chaîne
Clifford–connexion–repère invariant–IPP–courant de Green construit la
réalisation maximale same-action pour toute masse réelle. La façade privilégiée
reste :

```lean
primitive_spinC_smooth_graph_of_geometric_green
```

Les anciennes voies par décroissance Fourier, témoin de domaine maximal,
symétrie fournie ou densité de cœur restent seulement des adaptateurs.

## H10 : chaîne de germe désormais algébrique

Les nouveaux modules sont :

```text
P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryComponentwiseTerminalClosure4D
```

Ils prouvent la chaîne suivante sans nouvelle hypothèse d’action ou de
Hessien :

```text
égalité de T, ∂T et Γ
  → égalité de ∇T = ∂T + ΓTT
  → égalité de n · g · ∇T
  → égalité de K
  → égalité de tr(g_ind⁻¹ K)
  → égalité de orientation × densité × courbure moyenne
  → égalité ponctuelle des intégrandes
  → égalité des intégrales à deux feuilles
  → égalité des premiers et seconds Fréchet sur le germe.
```

Le gate générique terminal est :

```lean
candidate_a_normal_boundary_componentwise_terminal_closure_gate
```

### Résidu physique exact de H10

Il reste à instancier ce gate avec les coefficients Candidate-A déjà construits
et à fournir, sur **un même ouvert admissible**, les égalités composante par
composante :

1. tangent du graphe dans le repère régulier ;
2. dérivée spatiale du tangent ;
3. coefficients de Christoffel ;
4. normale métrique unitaire ;
5. métrique ambiante ;
6. inverse de la métrique induite ;
7. signe de coorientation ;
8. densité induite.

Les contractions finies, la courbure moyenne, l’intégrande, l’action et le
Hessien ne sont plus des obligations séparées.

## Paquet A : famille locale, Robin supprimé des hypothèses

Le module :

```text
P0EFTJanusProgramPGlobalCandidateANormalBoundaryRobinC2Transfer4D
```

prouve qu’une égalité d’action sur un ouvert transporte automatiquement la
régularité `C²` et le second Fréchet du bloc complété vers le bloc Robin
historique.

Le paquet préféré est donc :

```lean
ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
```

Il ne demande des preuves `C²` que pour six blocs :

```text
Candidate-A central
Einstein–Hilbert +
Einstein–Hilbert −
Maxwell +
Maxwell −
BV fini
```

Le septième bloc, Robin/GHY, est construit depuis H10. Matière et LL sont déjà
reconstruits depuis leurs actions quadratiques sur les graphes fermés. Le gate
H13 correspondant est :

```lean
global_candidateA_h13_minimalPhysical_h10RobinFamily_gate
```

## Paquet B : H11 depuis sept extensions continues

Le paquet intermédiaire par estimations séparées reste :

```lean
GlobalCandidateASevenPhysicalBlockCoreBounds4D
```

La voie préférée est maintenant :

```lean
GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
```

Pour chaque bloc, elle stocke :

- une forme bilinéaire continue sur l’unique espace de Hilbert commun ;
- son accord exact avec le vrai bloc du Hessien sur le cœur lisse dense.

L’estimation

```text
‖B_j(x,y)‖ ≤ ‖B_j‖ ‖ιx‖ ‖ιy‖
```

est déduite deux fois de l’inégalité de norme d’opérateur. La constante commune
est ensuite la somme finie des sept normes. Aucun choix séparé de constante ou
de forme agrégée n’est nécessaire.

Gate :

```lean
global_candidateA_h11_common_augmented_domain_gate_of_continuousExtensions
```

### Résidu physique exact de H11

Construire les sept extensions continues et prouver leur accord dense. Les
estimations de produit et leur sommation sont désormais formelles.

## Paquet C : H12 depuis les compléments finis

La route par inverse généralisé :

```lean
GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D
```

est maintenant elle-même produite par :

```lean
GlobalCandidateAFaithfulAugmentedComplementInverse4D
```

Les données naturelles sont :

```text
QH = I - Pker
HQ = I - Pcoker
Pcoker H = 0
range(Pker) finie
range(Pcoker) finie
stationnarité LL
```

La gate prouve alors :

```text
HQH = H
I - QH = Pker
I - HQ = Pcoker
```

puis construit le paramétrix à défaut fini, l’image fermée, le noyau et le
conoyau finis, la propriété Fredholm et l’indice zéro.

Gate :

```lean
global_candidateA_h12_faithful_augmented_fredholm_gate_of_complement
```

### Résidu physique exact de H12

Construire l’inverse borné sur le complément elliptique et les deux projections
finies. Les défauts et les conclusions Fredholm ne sont plus fournis à la main.

## Route terminale préférée

Les modules d’assemblage sont :

```text
P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D
P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D
P0EFTJanusProgramPGlobalHessianH10RobinComplementClosure4D
```

La chaîne est :

```text
composantes géométriques H10
  → même germe GHY et Robin C²
  → famille locale à six blocs C²
  → mismatch matière–LL nul (H13)
  → sept extensions continues
  → domaine commun augmenté (H11)
  → inverse sur compléments finis
  → Fredholm, indice zéro (H12)
  → certificat H14.
```

Aucune étape H15 n’est prévue.

## État de confiance

- **SpinC structurel :** fermé dans l’implémentation, non recertifié dans ce lot.
- **H10 formel :** contractions, intégration et calcul de germes fermés ;
  instanciation géométrique exacte encore à raccorder.
- **Famille :** Robin, matière et LL retirés des hypothèses indépendantes.
- **H11 :** bornes retirées des hypothèses dès que les extensions existent.
- **H12 :** paramétrix retiré des hypothèses dès que l’inverse sur complément
  existe.
- **Validation Lean des nouveaux modules :** non garantie.
- **Ticket terminal :** ne doit être marqué `DONE` qu’après instanciation des
  données physiques et compilation de la façade et de l’audit.
