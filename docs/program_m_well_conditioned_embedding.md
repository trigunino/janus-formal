# MF-MAN-003 — Cible causale, volumétrique et temporelle

## Construction

`CausalVolumeTimeTarget` fixe, avant le test d'un candidat :

- un ordre sur les points de la cible ;
- ses régions et leur volume ;
- une fonction de temps propre ;
- un identifiant de provenance non vide.

`WellConditionedEmbeddingSpecification` demande ensuite :

- un plongement préservant et reflétant l'ordre ;
- une loi nombre-volume avec densité et tolérance ;
- une fenêtre d'échelles admissibles ;
- une loi reliant temps propre et nombre maximal de pas dans une chaîne.

La longueur de chaîne est calculée intrinsèquement avec `Set.chainHeight` de
Mathlib sur l'intervalle fermé `{z | x ≤ z ∧ z ≤ y}`, puis `1` est soustrait
pour compter les pas. Un intervalle dégénéré a ainsi une durée discrète nulle.
Cette valeur n'est pas fournie par le candidat et Lean prouve qu'elle est
inchangée par tout isomorphisme d'ordre.

## Pourquoi c'est plus fort

MF-MAN-002 fabriquait le volume après avoir vu l'ordre discret. Ici les lois
utilisent exclusivement le volume et le temps de la cible passée en paramètre.
Le registre de provenance doit garantir que cette cible a été définie
indépendamment. Un identifiant ne peut pas, à lui seul, formaliser l'ordre
historique dans lequel un chercheur a inventé ses définitions.

## Base bibliographique

La correspondance ordre–causalité et nombre–volume est standard dans la
[revue de Surya](https://link.springer.com/article/10.1007/s41114-019-0023-1).
Le contrôle supplémentaire longueur de chaîne–temps propre suit l'architecture
des plongements « well-conditioned » proposée par
[Madsen (2026)](https://arxiv.org/abs/2607.05840). Ce préprint récent est une
source externe : ses théorèmes d'unicité approximative ne sont pas reproduits
ici.

## Limites

La cible n'est pas encore une variété lorentzienne : aucune structure lisse,
métrique de signature lorentzienne, hyperbolicité globale ou mesure induite
n'est formalisée. Aucune cible concrète n'est certifiée et aucune unicité
géométrique n'est prouvée. MF-MAN-003 est donc **I/T**, pas une émergence de
géométrie. Il ne suppose ni Janus ni une gorge.
