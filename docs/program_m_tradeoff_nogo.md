# MF-MAN-011 — No-go de scalarisation volume/temps

## Problème

MF-MAN-010 produit deux géométries non dominées : l'une minimise l'erreur de
volume, l'autre l'erreur de temps. Une somme pondérée pourrait artificiellement
désigner un gagnant, mais elle ajoute une préférence absente de la relation.

La somme pondérée est une méthode classique d'optimisation multiobjectif ; ses
poids servent précisément à parcourir différents compromis de Pareto
([Kim et de Weck, 2005](https://doi.org/10.1007/S00158-004-0465-1)).

## Théorème formel

Pour le premier témoin exact de MF-MAN-010, les pertes sont :

| Candidat | Volume | Temps |
| --- | ---: | ---: |
| préféré par le volume | `119/32` | `22` |
| préféré par le temps | `37/9` | `43/4` |

Avec

```text
L_w = w L_volume + (1-w) L_temps,
```

Lean prouve que le candidat préféré par le volume gagne exactement lorsque

```text
3240/3353 < w.
```

Ce seuil n'est pas intrinsèque. Pour `w=99/100`, le candidat volume gagne avec
les valeurs ci-dessus. Si l'erreur temporelle est seulement exprimée dans une
unité multipliée par 100, Lean prouve que le candidat temps gagne. La relation,
les plongements et leur ordre de Pareto n'ont pourtant pas changé.

## Conclusion

Une scalarisation ne résout pas l'ambiguïté : elle la déplace dans le choix du
poids et des unités. Program M doit donc conserver le front de Pareto jusqu'à
ce qu'une normalisation soit dérivée d'une loi indépendante, préenregistrée ou
justifiée physiquement.

Ce no-go ne dit pas qu'aucune préférence physique ne pourra exister. Il dit
qu'elle n'est pas contenue dans les axiomes actuels et ne peut pas être ajoutée
silencieusement.

## Vérification

```text
lake build JanusFormal.Foundations.ProgramMTradeoffNoGo
```
