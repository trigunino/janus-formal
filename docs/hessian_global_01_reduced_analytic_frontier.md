# HESSIAN-GLOBAL-01 — frontière analytique constructive réduite

Date du lot : **8 août 2026**.

Ce document décrit la route constructive H10–H14 de la branche
`agent/hessian-spinc-maximal-domain`. L’implémentation a été poursuivie sans
attendre une validation Lean complète ; les nouvelles déclarations ne doivent
donc pas être présentées comme certifiées par le noyau avant le passage des
workflows focalisés.

## Résultat structurel

Le certificat terminal demeure :

```lean
global_candidateA_hessian_closure_gate
```

La façade constructive publique est :

```text
P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D
```

et son point d’entrée préféré :

```lean
global_candidateA_hessian_terminal_constructive_closure_gate
```

La frontière terminale comporte exactement trois paquets analytiques :

```text
famille Candidate-A à six blocs C²
extensions continues canoniques des sept Hessiennes physiques
shift fini auto-adjoint avec ‖x‖ ≤ C ‖(H + P)x‖
```

H10 et SpinC ne sont plus des entrées de cette façade.

## SpinC : fermeture géométrique implémentée

La chaîne Clifford–connexion–repère invariant–IPP–courant de Green construit la
réalisation maximale same-action pour toute masse réelle. La façade privilégiée
reste :

```lean
primitive_spinC_smooth_graph_of_geometric_green
```

Les anciennes voies par décroissance Fourier, domaine maximal fourni, symétrie
fournie ou densité de cœur restent uniquement des adaptateurs.

## H10 : fermé par l’unique action mobile Candidate-A

Le terminal concret est :

```lean
global_candidateA_h10_closure_gate
```

Il assemble les résultats déjà présents :

- l’action GHY complétée à deux feuilles est `C²` sur le vrai domaine ouvert ;
- son second Fréchet est symétrique ;
- toute présentation lisse admissible coïncide sur un vrai germe avec l’unique
  source mobile de `globalCandidateAGHYAction` ;
- la source lisse factorise par le cœur métrique-normal complété et ne dépend
  pas du représentant choisi.

Le paquet final est :

```lean
GlobalCandidateAH10ClosureCertificate4D
```

Il ne demande aucune nouvelle action, normale, métrique ou donnée de bord. La
transversalité déjà utilisée pour entrer dans le domaine GHY est sa seule
prémisse géométrique.

Les modules génériques de calcul de germe composante par composante restent
utiles pour auditer l’origine de l’égalité, mais leurs huit identités
`EventuallyEq` ne sont plus exposées comme un quatrième paquet terminal.

## Paquet A : famille locale à six blocs `C²`

Le paquet terminal H13 est :

```lean
ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
```

Il conserve seulement les régularités indépendantes :

```text
Candidate-A central
Einstein–Hilbert +
Einstein–Hilbert −
Maxwell +
Maxwell −
BV fini
```

Les trois autres secteurs sont reconstruits :

```text
Robin/GHY ← H10
matière   ← action quadratique du graphe SpinC
LL        ← action quadratique du graphe LL complet
```

Le mismatch matière–LL est annulé sur la même action sans retirer les sept
blocs physiques.

## Paquet B : extensions canoniques des sept Hessiennes physiques

Le paquet H11 préféré est :

```lean
GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
```

Les formes du cœur sont fixées comme les véritables seconds Fréchet des sept
blocs de l’action locale. Chaque bloc fournit uniquement son prolongement
bilinéaire continu, son accord sur le cœur dense et sa symétrie.

Les estimations sont alors automatiques :

```text
‖B_j(x,y)‖ ≤ ‖B_j‖ ‖ιx‖ ‖ιy‖,
C_total = Σ_j ‖B_j‖.
```

Le prolongement de la somme sur l’unique espace de Hilbert commun, son Riesz,
la fermeture du graphe, l’auto-adjonction et l’accord avec le Hessien augmenté
sont reconstruits par les gates H11.

Le résidu analytique de H11 est exactement : **construire les sept
prolongements continus canoniques et prouver leur accord sur le cœur dense**.

## Paquet C : shift fini auto-adjoint contrôlé par une borne globale

Le paquet PDE-facing est :

```lean
GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
```

Il contient :

```text
un projecteur de défaut fini P,
la coercivité de H hors de P,
l’auto-adjonction de H + P,
une constante C et la borne ‖x‖ ≤ C ‖(H + P)x‖,
la stationnarité LL.
```

La borne est transformée en certificat anti-Lipschitz. Pour un opérateur borné
auto-adjoint, l’injectivité implique alors la densité de l’image via

```text
ker(H + P)ᗮ = closure(range((H + P)†)).
```

Le critère Banach anti-Lipschitz donne ensuite la bijectivité. La suite est
construite automatiquement :

```text
surjectivité de H + P
→ inverse borné de H + P
→ QH = HQ = I - P
→ HQH = H
→ défauts gauche/droite finis
→ image fermée, noyau et conoyau finis
→ Fredholm, indice zéro.
```

La surjectivité, l’inverse, le paramétrix et les défauts ne sont donc plus des
prémisses indépendantes.

## Route terminale à trois entrées

Le gate préféré est :

```lean
global_candidateA_hessian_h10Robin_lowerBound_closure_gate
```

Chaîne complète :

```text
H10 géométrique déjà fermé
  → Robin C² et Hessien Robin authentique
  → famille locale à six blocs C²
  → mismatch matière–LL nul (H13)
  → sept extensions continues canoniques
  → domaine commun augmenté (H11)
  → shift fini auto-adjoint avec borne globale
  → inverse, paramétrix et Fredholm (H12)
  → certificat H14.
```

Aucune étape H15 n’est prévue.

## Résidu mathématique exact

Hors corrections Lean, la fermeture demande maintenant :

1. construire la famille locale Candidate-A concrète et ses six preuves `C²` ;
2. construire les sept prolongements continus canoniques sur le domaine commun ;
3. choisir le projecteur fini des modes d’obstruction et démontrer la borne
   elliptique globale
   \[
   \|x\| \le C\,\|(H+P)x\|.
   \]

Tous les autres témoins de H10–H14 sont reconstruits par les gates.

## État de confiance

- **SpinC structurel :** fermé dans l’implémentation, non recertifié dans ce lot.
- **H10 structurel :** fermé par le gate concret, sans entrée terminale.
- **H13 :** réduit à six régularités locales indépendantes.
- **H11 :** réduit à sept prolongements canoniques continus.
- **H12 :** réduit à une obstruction finie et une borne elliptique globale.
- **Validation Lean :** non garantie à ce stade.
- **PR :** reste en brouillon tant que les workflows Lean ne sont pas verts.
