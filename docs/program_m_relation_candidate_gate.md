# MF-GATE-002 — De la relation brute au rapport d'ordre

## But

MF-GATE-002 relie la base faible `MF-A0` au rapport `MF-GATE-001` sans
supposer que la relation primitive est déjà un ordre. La direction des flèches
est conservée comme donnée mathématique ; elle n'est pas interprétée comme un
temps ou une causalité physique.

## Construction

Pour une matrice booléenne carrée `R`, l'outil :

1. calcule la fermeture réflexive-transitive `R*` ;
2. regroupe les objets mutuellement accessibles ;
3. construit l'ordre quotient entre ces fibres ;
4. applique les diagnostics aveugles de `MF-GATE-001` à ce quotient.

Cette construction correspond au squelette formalisé dans
`JanusFormal.Foundations.ProgramMCausalSkeleton`. Le rapport conserve les
empreintes de la relation, de sa fermeture et du quotient, ainsi que les
tailles des fibres et les nombres de paires ajoutées ou effacées.

## Perte d'information démontrée

L'audit figé compare la relation de couverture d'un ordre de Poisson à 256
objets avec une relation à 257 objets où un objet est remplacé par un cycle de
deux objets. Les empreintes primitives sont différentes, mais les quotients et
tous les diagnostics aval sont identiques.

Cela prouve qu'un résultat aval ne peut pas établir l'absence de cycles, la
multiplicité interne des fibres, ni les arêtes primitives ayant engendré
l'accessibilité. Une reconstruction sans perte doit employer le squelette
décoré `MF-DEC-001` ou conserver l'entrée originale.

## Utilisation

```text
python scripts/evaluate_program_m_relation_candidate.py \
  --relation candidate.npy --output report.json

python scripts/evaluate_program_m_relation_candidate.py \
  --examples --output outputs/program_m/mf_gate_002_examples.json
```

Les formats d'entrée sont les mêmes que pour `MF-GATE-001`. Le statut final est
celui du quotient ordonné.

## Limites

MF-GATE-002 ne dérive ni causalité physique, ni topologie de continuum, ni
dimension, ni métrique, ni gorge. Il ne teste pas les lois nombre-volume et
chaîne-temps ou l'unicité géométrique. Program P ne doit pas être appelé à ce
stade.
