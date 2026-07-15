# J-CO — état initial

## CO01 — audit de la source plugstar

Source vérifiée visuellement : Petit et D'Agostini, *Alternatives to Black
Holes: Gravastars and Plugstars*, DOI `10.4236/jmp.2025.1610072`, pages
1481-1483 pour les équations principales.

## Registre des équations

| Objet | Équations | Verdict |
| --- | --- | --- |
| Schwarzschild intérieur à densité constante | (1)-(9), (11) | formule standard réutilisable après contrôle des conventions |
| pression radiative centrale | (10) | hypothèse locale, pas équation d'état globale |
| seuil de pression centrale | (12)-(14) | compactness `Rs/R=8/9`, vérifiée |
| « vitesse de la lumière » | (15)-(16) | expression de vitesse coordonnée; interprétation physique variable non dérivée |
| inversion masse/énergie | texte après (17) | conjecture, aucune loi dynamique fournie |
| redshift critique | (18)-(20) | calcul algébrique donnant le ratio 3, vérifié |

## Verdict scientifique

**T/X** : le noyau algébrique constant-density et le ratio cité sont
reproductibles.

**N** : cela ne constitue pas encore une plugstar. La source ne fournit ni
tenseur énergie-impulsion négatif, ni loi de conversion, ni jonction bimétrique,
ni analyse de stabilité radiale, ni transfert radiatif produisant une image
EHT. Elle qualifie elle-même le modèle de brouillon sans vision physique
cohérente.

`CO02` ne doit donc pas intégrer arbitrairement une « masse inversée ». Son
point d'entrée légitime est :

```text
équations statiques explicites des deux métriques
  + équations d'état des deux secteurs
  + loi de conversion ou courant conservé
  + conditions centre/interface/infini
```

## Registre de reprise

| ID | Atome manquant | Bloque |
| --- | --- | --- |
| `CO-P01` | équations statiques issues de l'action P/B | CO02 |
| `CO-P02` | tenseurs matière signés cohérents avec Bianchi | CO02 |
| `CO-P03` | loi dynamique de conversion de masse | définition plugstar |
| `CO-P04` | jonctions entre cœur, enveloppe et extérieur | CO02/CO03 |
| `CO-P05` | équation d'état causale | CO02/CO03 |
| `CO-P06` | modèle d'émission/transfert radiatif | CO04/CO06 |

## Cibles

```text
JanusFormal.Branches.JanusCompactObjects
JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCO01PlugstarSourceAudit
scripts/audit_plugstar_source_equations.py
```

## Blocs indépendants de P réalisés

### CO02-GR

Une référence en unités `G=c=1` fournit :

- solution intérieure analytique à densité constante;
- pression centrale et divergence de Buchdahl;
- intégrateur TOV RK4 pour une équation d'état fournie;
- contrôles de domaine et limite de surface.

Cette référence ne contient aucun secteur négatif et ne prétend pas être une
plugstar.

### CO03-GR

Un diagnostic de branche `dM/d rho_c > 0` est disponible pour repérer le
premier point tournant d'une séquence d'équilibre. Il s'agit d'un diagnostic,
pas encore du problème complet de Sturm-Liouville des pulsations radiales.

### CO04-Schwarzschild

Le module calcule redshift de surface, sphère de photons `r=3M`, paramètre
d'impact critique `3 sqrt(3) M`, orbites circulaires, déflexion faible et délai
de Shapiro dominant. Ces résultats décrivent un extérieur Schwarzschild et ne
distinguent pas à eux seuls trou noir, étoile ultracompacte ou plugstar.

### Audit redshift/EHT

Verdict **N** : le rapport des extrema d'une barre de couleur d'une image à une
fréquence d'observation donnée n'est pas un rapport de longueurs d'onde. Une
inférence spectrale exige l'identification d'une même raie ou un modèle de
transfert radiatif fréquentiel calibré. L'EHT publie des visibilités et des
produits reconstruits; les comparaisons physiques utilisent notamment GRMHD,
ray tracing et données synthétiques.

Chaîne minimale désormais enregistrée :

```text
métrique + plasma -> transfert radiatif covariant -> I_nu
-> visibilités complexes synthétiques -> même reconstruction -> statistique
```

### Interface bimétrique future

`BimetricStaticCandidate` stocke déjà les deux lapses, métriques radiales,
densités, pressions anisotropes, courant de conversion et rayon d'interface.
`BimetricStaticLaws` exige équations d'Euler, Bianchi total, loi de conversion,
régularité, jonction, asymptotique et causalité. P/B devra remplir ces champs;
aucune valeur n'est inventée maintenant.

## CO04 — ray tracing de référence

Le traceur numérique intègre l'équation orbitale nulle équatoriale

```text
u'' + u = 3 M u^2,  u=1/r,
```

et classe chaque rayon comme `escaped`, `captured` ou `surface`. Il permet de
comparer un horizon à une surface matérielle déclarée `R>2M`, sans modèle
d'émission. Il reproduit la séparation par la sphère de photons et conserve
explicitement les trajectoires pour une future synthèse d'image.

Limite : une carte de rayons n'est pas une image EHT; il manque encore
émissivité, absorption et convolution/interférométrie.

## CO05 — pulsars et binaires GR

La référence calcule maintenant :

- avance relativiste du périastre;
- délai de Shapiro binaire;
- décroissance de période de Peters-Mathews;
- amplification excentrique;
- fréquence ISCO Schwarzschild.

Ces objets définissent le zéro GR auquel une future correction Janus devra être
soustraite. Aucune donnée de pulsar n'est ajustée à ce stade.

Reprises supplémentaires :

| ID | Atome manquant | Bloque |
| --- | --- | --- |
| `CO-P07` | métrique extérieure Janus dérivée | correction ray tracing/timing |
| `CO-P08` | loi de rayonnement binaire Janus | correction de `Pdot` |
| `CO-P09` | couplage de la matière visible aux métriques | Shapiro/périastre observables |
