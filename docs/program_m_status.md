# Program M — Statut courant

**Statut au 19 juillet 2026 : fondations consolidées, intégration géométrique
avec Program P en attente.**

Program M n'est ni abandonné ni déclaré physiquement complet. Sa phase
fondationnelle a produit une interface mathématique testée ; la prochaine
expérience utile exige que les interfaces géométriques de P soient stabilisées.

## Architecture retenue

```text
M0  relations primitives
    → configurations, transformations, composition et collage
    → préordre libre et distance orientée minimale

M1  valeurs dans un espace capable de signes
    → zéro, valeurs non négatives et valeurs signées sont des cas admissibles

M2  mesure uniforme optionnelle
    → mesure de comptage, à une échelle près

M3  extension involutive optionnelle
    → involution choisie + charge impaire + interfaces équivariantes

    → adaptateur algébrique signé vers Program P
```

## Décision sur le signe

La base n'est plus décrite comme « non signée ». Le **langage de coefficients**
peut être un groupe additif signé, par exemple `ℝ`, ce qui englobe :

- la charge nulle ;
- le sous-cas non négatif ;
- les charges positives et négatives.

Cela rend le langage plus général sans imposer deux secteurs. Ce qui reste une
hypothèse supplémentaire est :

- choisir une involution non triviale ;
- imposer `q(σx)=-q(x)` ;
- exclure `q=0` pour utiliser l'adaptateur binaire de P ;
- fixer la magnitude et son interprétation physique.

Autrement dit, **le signe est autorisé dans la base ; la structure Janus du
signe n'est pas supposée dans la base**.

## Ce que M fournit déjà

- un groupoïde de configurations relationnelles ;
- des fonctionnelles scalaires invariantes admissibles, sans action préférée ;
- composition, interfaces, collage et descente ;
- préordre et distance orientée libre ;
- critère exact d'unicité des données portées par les paires ;
- mesure de comptage sous uniformité explicite ;
- extension signée composable et recollable ;
- adaptateur conditionnel vers les secteurs `JanusCharge` de P.

## Ce que M ne fournit pas

- une métrique lorentzienne ou une dimension unique ;
- une sélection universelle de l'involution, des poids ou de la magnitude ;
- une interprétation en masse inertielle ou gravitationnelle ;
- une gorge, un mapping torus ou un PT géométrique ;
- une dynamique, un médiateur, une action ou des prédictions.

## Condition de reprise

Lorsque P sera prêt, le prochain test sera comparatif : brancher le même
adaptateur M sur une géométrie sans gorge puis sur la géométrie à gorge. Cela
déterminera si la gorge est sélectionnée par des contraintes supplémentaires
ou reste une entrée indépendante.

Le checkpoint scientifique détaillé est
[`program_m_archive.md`](program_m_archive.md) et la traçabilité complète est
dans [`program_m_provenance_register.md`](program_m_provenance_register.md).
