# MF-ADV-008 — Niveaux infinis décorés

## Construction

MF-ADV-007 échouait à cause de grandes classes de jumeaux exacts. MF-ADV-008
conserve ses niveaux ordonnés, mais remplace chaque antichaîne de niveau par un
ordre biparti aléatoire de hauteur deux :

- chaque objet reçoit iid un côté bas ou haut;
- chaque paire bas-haut du même niveau reçoit indépendamment une relation avec
  probabilité `p=1/5`;
- les niveaux différents restent totalement ordonnés.

Les relations internes ne peuvent pas former de chaîne de trois, donc la
transitivité globale est conservée. La loi reste échangeable, projective et
ergodique. Les voisinages aléatoires rendent les jumeaux exacts macroscopiques
exponentiellement improbables. Les ordres bipartis aléatoires de hauteur deux
sont une famille classique; voir
[Biró–Hamburger–Kierstead–Pór–Trotter–Wang](https://arxiv.org/abs/2003.07935).

## Moments recalculés

Les nouvelles masses satisfont

```text
S₂ = Σqᵢ² = 5/9,    S₃ = Σqᵢ³ = 20/51.
```

Avec `p=1/5`, les limites deviennent exactement

```text
paires  = 1 - (1-p/2)S₂ = 1/2
triples = 1 - 3S₂ + 2S₃ + (3p/2)(S₂-S₃) = 1/6.
```

Lean vérifie ces identités rationnelles et prouve qu'une réalisation arbitraire
de la microstructure est réflexive, antisymétrique et transitive dans
`JanusFormal/Foundations/ProgramMDecoratedLayerAdversary.lean`.

## Résultat

Les quatre gates existants ont été gelés. Sur les tailles inédites 432, 864,
1728 et 3456 :

- `58/64` trajectoires passent tout;
- hauteurs moyennes : `23.7, 32.5, 43.5, 57.4`;
- rapport moyen de hauteur : `2.45`;
- fraction jumelle moyenne : `0.0123 → 0.00171`;
- rapport moyen de fraction jumelle : `0.144`.

MF-MAN-019 est donc cassé sans réintroduire de jumeaux macroscopiques.

## Limite révélée

Les quatre diagnostics ne voient pas l'organisation hiérarchique en blocs :
entre deux niveaux, toutes les relations sont présentes, tandis qu'à l'intérieur
elles suivent une règle bipartie. Le prochain audit doit réutiliser les profils
d'intervalles de MF-LOC-001 à plusieurs échelles, plutôt qu'ajouter un détecteur
spécifique à cette construction.

Le script est `scripts/audit_program_m_decorated_layer_adversary.py`; la sortie
est `outputs/program_m/mf_adv_008_decorated_layer_adversary.json`.

