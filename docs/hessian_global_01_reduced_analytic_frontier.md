# HESSIAN-GLOBAL-01 — frontière analytique réduite

Date du lot : **7 août 2026**.

Ce document décrit l’état d’implémentation de la route constructive H10–H14.
Les nouveaux modules ont été écrits conformément à la décision du projet de
poursuivre sans attendre une validation Lean complète ; les déclarations
ci-dessous ne doivent donc pas être présentées comme certifiées par le noyau
tant que le workflow ciblé n’a pas réussi.

## Résultat structurel

Le certificat terminal reste :

```lean
global_candidateA_hessian_closure_gate
```

La route constructive privilégiée est maintenant :

```lean
global_candidateA_hessian_diracGreen_bounded_closure_gate
```

et la façade publique :

```text
P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D
```

Le paquet d’entrée terminal n’a plus que trois champs analytiques :

```lean
family
physicalBound
parametrix
```

Il ne stocke plus aucun témoin SpinC.

## SpinC : fermeture géométrique implémentée

La partie SpinC n’est plus un paquet analytique ouvert. Les modules suivants
construisent la chaîne complète :

```text
P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D
P0EFTJanusProgramPPrimitiveSpinCConnectionHermitian4D
P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameDecomposition4D
P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameCoordinateDerivatives4D
P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameIPP4D
P0EFTJanusProgramPPrimitiveSpinCCliffordSection4D
P0EFTJanusProgramPPrimitiveSpinCDiracGreenCurrent4D
P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D
```

### 1. Signes Clifford

Les trois générateurs Clifford explicites sont prouvés anti-hermitiens pour le
pairing positif réellement intégré :

```text
⟨γᵢψ,φ⟩ = -⟨ψ,γᵢφ⟩.
```

Cette identité est transportée des coordonnées demi-spinorielles au vrai fibré
D9 doublé.

### 2. Connexion primitive hermitienne

La dérivée plate satisfait le Leibniz hermitien. Les corrections restantes
s’annulent dans la dérivée du pairing :

- la correction Levi–Civita est une combinaison réelle de `γᵢγⱼ` avec
  `i ≠ j` ;
- le potentiel monopôle et la connexion du repère normal sont des multiples
  réels de l’action infinitésimale `U(1)`.

Le certificat public est :

```lean
ProgramPPrimitiveSpinCConnectionHermitianCertificate4D
```

### 3. Même géométrie pour le repère Dirac et les flots invariants

Le repère orthonormal radial utilisé par le Dirac est décomposé exactement en
translation temporelle et rotations de la sphère :

```text
eᵢ = nᵢ T + Σₐ (n × eᵢ)ₐ Rₐ.
```

Les quatre générateurs `T, R₀, R₁, R₂` préservent la mesure canonique de gorge.
Les dérivées des coefficients donnent :

```text
T(nᵢ) + Σₐ Rₐ((n × eᵢ)ₐ) = -2 nᵢ.
```

Il en résulte une vraie intégration par parties, sans contrat de Stokes :

```text
∫ eᵢ(f) = 2 ∫ nᵢ f.
```

### 4. Courant global et identité de Green

Le courant

```text
Jᵢ(ψ,φ) = ⟨γᵢψ,φ⟩
```

est construit comme champ scalaire complexe global sur le vrai fibré
primitif. Le résidu ponctuel de l’opérateur implémenté est :

```text
⟨ψ,Dφ⟩ - ⟨Dψ,φ⟩
  = -Σᵢ eᵢ Jᵢ + 2 ⟨γ(n)ψ,φ⟩.
```

L’intégration par parties transforme le premier terme en
`-2 ∫⟨γ(n)ψ,φ⟩`, qui annule exactement la correction Levi–Civita. Le théorème
terminal SpinC est :

```lean
d9PrimitiveSpinCGeometricDirac_pairing_symm
```

Il construit sans entrée supplémentaire :

```lean
ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D
```

puis, pour tout `m² ∈ ℝ` :

- la symétrie de `2D + m²` ;
- la relation multiplicateur des coefficients signés ;
- l’appartenance de toute section lisse au domaine maximal ;
- l’accord de l’opérateur maximal avec l’expression différentielle ;
- le vecteur Fourier pondéré ;
- Parseval ;
- l’accord same-action ;
- la réalisation exacte du graphe matière.

La façade SpinC privilégiée est :

```lean
primitive_spinC_smooth_graph_of_geometric_green
```

Les anciennes routes par décroissance Fourier, domaine maximal fourni,
symétrie fournie ou densité de cœur restent disponibles uniquement comme
adaptateurs.

## Les trois paquets analytiques encore ouverts

### A. Famille locale Candidate-A

```lean
ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
```

Le chart est fixé au vrai :

```lean
GlobalMinimalPhysicalFieldTangent
```

Il est D10-free. Le paquet doit fournir l’ouvert admissible, la famille
Candidate-A `C²`, les identités d’action matière/LL et les deux bornes de norme
de graphe correspondantes.

### B. Borne commune des sept blocs physiques

```lean
GlobalCandidateASevenPhysicalCoreBound4D
```

Il reste une seule estimation bilinéaire sur le cœur diagonal dense :

```text
‖Bphys(x,y)‖ ≤ C ‖ι(x)‖ ‖ι(y)‖.
```

`P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D` étend alors
canoniquement la forme avec `LinearMap.extendOfNorm`, prouve l’accord dense et
construit H11 sur l’unique complétion existante.

### C. Paramétrix augmenté à défaut fini

```lean
GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
```

Il porte :

```text
QH = I - K,
HQ = I - C,
CH = 0,
range(K) et range(C) de dimension finie,
stationnarité LL.
```

Les gates en déduisent :

```text
range(H) = ker(C),
```

puis l’image fermée, le noyau fini, le cokernel fini, le caractère Fredholm et
l’indice zéro.

## Chaîne terminale actuelle

```text
famille locale Candidate-A
  → chart minimal H13
  → mismatch matière–LL = 0
  → borne des sept blocs
  → extension H11
  → paramétrix H12
  → Fredholm + indice zéro
  → certificat H14.
```

La partie SpinC est injectée automatiquement avant H13 par le théorème de Green
géométrique. Aucune étape H15 n’est prévue.

## État de confiance

- **SpinC structurel :** fermé dans l’implémentation.
- **Frontière résiduelle :** trois paquets analytiques.
- **Validation Lean des nouveaux modules :** non garantie à ce stade.
- **Ticket terminal :** ne doit être marqué `DONE` qu’après construction de
  `family`, `physicalBound`, `parametrix` et compilation de la façade.
