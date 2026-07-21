# MF-ADV-007 — Niveaux infinis et hauteur en racine carrée

## Construction

Chaque objet reçoit iid un niveau dans un ensemble dénombrable ordonné. Quatre
niveaux ont une masse explicite; la masse restante suit une loi de Zipf
d'exposant 2. Deux objets de niveaux différents sont ordonnés par leur niveau;
ceux d'un même niveau forment une antichaîne.

La loi est échangeable, projective et ergodique. Pour la queue Zipf normalisée,
les sommes des carrés et cubes valent respectivement `2/5` et `8/35`. Les masses
ont été résolues afin que la distribution complète vérifie

```text
Σ qᵢ² = 1/2,    Σ qᵢ³ = 1/3.
```

Elle reproduit donc les limites `1/2` et `1/6` de MF-ENS-002. Le nombre de
niveaux occupés dans ce schéma d'occupation à queue puissance croît comme
`√n`, et constitue exactement la hauteur de l'ordre. Ce comportement appartient
à la théorie des partitions échangeables et schémas d'occupation; voir
[Schweinsberg](https://arxiv.org/abs/0911.1793) et les schémas de Karlin discutés
par [Alsmeyer–Iksanov–Marynych](https://arxiv.org/abs/1601.04274).

## Résultat

Sans modifier les gates MF-ENS-002 et MF-MAN-018, sur les nouvelles tailles
336, 672, 1344 et 2688 :

- `54/64` trajectoires passent le gate combiné;
- hauteurs moyennes : `15.3, 20.8, 27.6, 35.8`;
- rapport moyen extrême : `2.38`, au-dessus du seuil gelé `2`.

Le gate à trois diagnostics est donc cassé par une loi non minkowskienne : ses
grandes classes de niveau restent des antichaînes répétées.

Lean formalise les conséquences exactes des équations de moments, l'exigence de
hauteur non bornée et la non-injectivité de cette signature grossière dans
`JanusFormal/Foundations/ProgramMInfiniteLayerNoGo.lean`. Comme pour MF-ADV-006,
l'existence positive des constantes numériques est vérifiée à précision machine
mais pas encore certifiée algébriquement dans Lean.

## Ce que cela révèle

L'ancien diagnostic MF-MAN-016 détecte déjà la faiblesse évidente de ce modèle :
une fraction macroscopique d'objets possède exactement le même passé et le même
futur. Le bon successeur n'est donc pas un nouveau filtre ad hoc, mais le relevé
de MF-MAN-016 au niveau ensemble : la plus grande classe de jumeaux relationnels
doit devenir négligeable quand `n` augmente.

Le script est `scripts/audit_program_m_infinite_layer_adversary.py`; la sortie
est `outputs/program_m/mf_adv_007_infinite_layer_adversary.json`.

