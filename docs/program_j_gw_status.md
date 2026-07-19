# J-GW — état initial

## Verdict

## Raccordement technique a P

- `GW-BP01` ferme : fonctionnelle Candidate A integree sur la base D8 mesuree.
- `GW-BP02` ferme : invariance PT de cette fonctionnelle.
- `GW-BP03` ferme (passe 2) : racine diagonale globale, fermeture spectrale cote moins et controle des faces singulieres.
- `GW-BP04` ferme (passe 3) : echange PT involutif sur les champs lisses des deux secteurs du quotient D8.
- `GW-BP05` ferme (passe 4) : pullback PT lisse et involutif des tenseurs covariants symetriques generaux sur D8.
- `GW-BP06` ferme (passe 5) : certificat inconditionnel de covariance du stress scalaire et d'echange des deux secteurs.
- Reprise P : seconde variation tensorielle complete, fond FLRW physique et couplage a la matiere visible. `GW-P01/GW-P03/GW-P07/GW-P08` restent ouverts.

`GW01-Minkowski-TT` est fermé au niveau **T/C**. L'interface algébrique
`GW01-FLRW` est construite, mais sa promotion physique reste ouverte.

Le symbole d'Einstein linéarisé déjà dérivé dans P donne, sur une polarisation
TT explicite,

```text
omega_diag^2 = k^2.
```

Le Hessien d'interaction relatif et les deux poids cinétiques positifs donnent

```text
omega_rel^2 = k^2 + m_rel (1/M_plus^2 + 1/M_minus^2).
```

Pour `M_plus^2>0`, `M_minus^2>0` et `m_rel>0`, la fréquence relative au carré
est strictement positive : le modèle réduit n'a pas de tachyon TT sur le fond
de Minkowski.

## Ce qui est réellement établi

- **T** cône de lumière du mode diagonal TT depuis le symbole d'Einstein;
- **T/C** diagonalisation pondérée du mode relatif;
- **T/C** positivité de sa fréquence au carré;
- **N** ces résultats Minkowski ne ferment pas automatiquement le cas FLRW.

## Prochaine gate

`GW01-FLRW` doit dériver, depuis l'action bimétrique déclarée :

1. les coefficients cinétiques dépendant du temps;
2. la matrice de masse tensorielle sur le fond proportionnel;
3. le terme de friction de chaque métrique;
4. la projection exacte de la matière visible et du détecteur;
5. la limite Minkowski et la limite GR.

Tant que ces cinq objets manquent, aucune contrainte issue d'un catalogue GW
et aucune distance de sirène standard ne constitue une prédiction Janus.

## Registre de reprise lorsque P sera complet

La structure Lean `PCompletionInputs` conserve les huit obligations exactes :

| ID | Entrée exigée de P | Utilisation J-GW |
| --- | --- | --- |
| `GW-P01` | action renormalisée complète | point de départ de la variation |
| `GW-P02` | fond FLRW solution des équations | coefficients évalués hors-shell interdits |
| `GW-P03` | seconde variation sur ce fond | action tensorielle quadratique |
| `GW-P04` | élimination lapse/shift | réduction physique des contraintes |
| `GW-P05` | normalisation cinétique tensorielle | fantômes et amplitude canonique |
| `GW-P06` | matrice de masse tensorielle | mode relatif et oscillations |
| `GW-P07` | métrique couplée à la matière visible | source astrophysique |
| `GW-P08` | réponse du détecteur | forme d'onde observée |

Point de reprise : construire une valeur de `PCompletionInputs`, puis remplacer
l'interface conditionnelle par la seconde variation dérivée. Le théorème
`missing_complete_p_action_blocks_physical_gw01` empêche formellement de
déclarer `GW01-FLRW` fermé avant `GW-P01`.

## GW02 — stabilité et causalité

La partie réduite Minkowski est maintenant fermée à niveau **T/C** :

- `m_rel² >= 0` exclut une fréquence tensorielle tachyonique;
- pour `m_rel² > 0`, la vitesse de groupe au carré
  `v_g²=k²/(k²+m_rel²)` appartient à `[0,1)`;
- le mode diagonal sans masse a exactement `v_g²=1` pour `k != 0`;
- le déficit au cône lumineux vaut exactement `m_rel²/(k²+m_rel²)`;
- une borne de Higuchi positive implique conditionnellement
  `m_eff² > 2 H²`.

La fermeture physique FLRW reste suspendue à :

| ID | Entrée exigée | Reprise |
| --- | --- | --- |
| `GW-P09` | masse tensorielle effective dérivée de P | injecter dans Higuchi |
| `GW-P10` | histoire physique `H(t)` dérivée de P | tester toute la trajectoire |
| `GW-P11` | marge uniforme de Higuchi | exclure la surface de couplage fort |

Le théorème `missing_p_background_blocks_physical_gw02` interdit la fermeture
physique de GW02 sans `GW-P10`.

## GW03 — oscillations et propagation

La couche générique est fermée à niveau **T/X** : rotation orthogonale des deux
modes, conservation de norme, probabilité bornée, limites sans mélange et sans
déphasage, retard massif Minkowski et intégrateur de phase sur un fond FLRW
fourni en entrée.

Le solveur `src/janus_lab/gw_propagation.py` n'ajuste aucune donnée. Il attend
`H(z)`, la masse et le mélange comme entrées externes.

| ID | Entrée P manquante | Reprise |
| --- | --- | --- |
| `GW-P12` | angle/projection de mélange physique | remplacer l'entrée libre |
| `GW-P13` | histoire de phase issue de la matrice de masse | alimenter le solveur |

## GW04 — source et détecteur

L'interface linéaire `source -> modes -> propagation -> détecteur` et sa limite
GR sont formalisées. Sa fermeture physique attend toujours `GW-P07/P08`, plus
la normalisation absolue de la forme d'onde (`GW-P14`).

## Audit observationnel générique

L'audit exécutable enregistre, sans fit :

- la borne GWTC-3 à 90 % `m_g <= 1.27e-23 eV/c²`;
- la fenêtre GW170817 `-7e-16 < 1-c_T < 3e-15`;
- les liens vers les sources primaires;
- un verdict séparé masse/vitesse pour une valeur candidate.

Ce verdict n'est pas encore un test de Janus : les valeurs candidates ne
seront physiques qu'après fermeture de `GW-P09` et `GW-P07/P08`.

## Cibles

```text
JanusFormal.Branches.JanusGravitationalWaves
JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWMinkowskiTensorGate
JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWFLRWTensorInterface
JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWStabilityCausalityGate
JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWOscillationGate
JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWSourceDetectorInterface
```
