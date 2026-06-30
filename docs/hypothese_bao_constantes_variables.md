# Hypothese BAO Et Constantes Variables

Position : Janus est pris comme axiome de travail.

Le test DESI BAO direct echoue avec une regle standard unique. L'inversion du probleme montre cependant une empreinte simple : les corrections effectives `D_M` et `D_H` ressemblent a une loi de puissance proche de :

```text
scale_eff(z) proportional (1 + z)^(-1/2) = sqrt(a)
```

ou `a = 1 / (1 + z)`.

## Lien Avec Le Papier 2026

Dans le texte auteur 2026 sur l'alternative a l'inflation par constantes variables, l'extraction PDF indique notamment :

- conservation de l'invariance de Lorentz ;
- conservation de la constante de structure fine ;
- toutes les longueurs caracteristiques varient comme `a` ;
- tous les temps caracteristiques varient comme `a^(3/2)` ;
- une loi de jauge implique un exposant `1/2` pour les vitesses ou quantites associees.

L'extraction automatique perd certains symboles, donc ces points doivent etre reverifies sur le PDF original avant d'etre cites comme equations definitives.

## Interpretation De Travail

DESI BAO mesure des ratios `D_M/r_d`, `D_H/r_d`, `D_V/r_d`. Dans Lambda-CDM, `r_d` est traite comme une regle standard comobile issue de la physique du plasma primordial.

Sous Janus vrai, le regime a constantes variables peut modifier :

- la longueur physique du ruler sonore ;
- sa conversion en coordonnees comobiles ;
- la difference entre propagation radiale et transverse ;
- la relation entre redshift observe et perte d'energie photonique.

L'empreinte `sqrt(a)` devient donc une piste : elle pourrait indiquer que le BAO conserve une trace du regime de jauge primordial.

## Ce Qui Reste A Prouver

1. Deriver `D_M/r_d` et `D_H/r_d` depuis les equations Janus, sans importer les definitions Lambda-CDM.
2. Expliquer pourquoi les corrections radiale et transverse sont proches mais pas identiques.
3. Montrer que la correction `sqrt(a)` ou sa generalisation apparait avant l'ajustement DESI.
4. Tester la prediction sur donnees non utilisees : eBOSS, WiggleZ, DESI DR1/DR2 sous selections separees.

## Regle Anti-Fit Artificiel

Les corrections inferees depuis DESI servent seulement a identifier une empreinte. Elles ne sont pas des preuves.

Une carte BAO est admissible seulement si sa forme est fixee avant le test observationnel par une source Janus verifiee. Dans ce cadre, on accepte au maximum une normalisation globale `H0*r_d`, parce que cette echelle n'est pas encore fixee dans le prototype.

Le test no-fit actuel est `scripts/score_bao_c8_source_gauge_no_fit.py`. Il fixe `q0=-0.087` depuis M18 et les exposants depuis la logique de jauge X2026 Eq. 40. Resultat : les lois source directes ne suffisent pas encore. Donc l'anisotropie vue par C7 reste une cible de derivation, pas une loi physique etablie.

## Statut

Prometteur comme empreinte, insuffisant comme preuve.

Le script associe est `scripts/infer_janus_bao_ruler.py`, avec rapport genere dans `outputs/reports/janus_bao_ruler_inference.md`.
