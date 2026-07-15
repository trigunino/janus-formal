# Audit de la piste quantique bimétrique

## Résultat

Dans le modèle exploratoire construit ici, aucune signature quantique propre à
Janus n’a été établie.

## Vérifications

- `time_dependent_signature.py` : un (r(t)) modifie la trajectoire, mais un
  Hamiltonien standard dépendant du temps peut reproduire cet effet.
- `separation_gravity_signature.py` : la distance et le potentiel externe
  modifient un couplage phénoménologique, donc restent réparamétrables.
- `standard_comparison.py` : à couplage effectif égal, les prédictions Janus
  et standard sont identiques.
- `decoherence_phase_signature.py` : le déphasage et la perte de pureté sont
  identiques à ceux d’un canal de déphasage standard au même taux.
- Les tests précédents vérifient unitérarité, symétrie d’échange, borne CHSH,
  stabilité locale et non-signalisation.

## Conclusion limitée mais robuste

La bimétrie peut servir de mécanisme de paramétrisation pour un couplage,
mais elle ne produit pas encore de prédiction mesurable non dégénérée avec la
mécanique quantique standard.

Pour dépasser ce résultat négatif, il faudrait une dérivation covariante
complète qui impose une relation nouvelle entre métriques et observables,
plutôt qu’un couplage ou un taux introduit à la main.
