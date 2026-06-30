# Premier Resultat Expansion

Date : 7 juin 2026.

Ce document consigne le premier resultat numerique obtenu avec les donnees publiques telechargees par Janus Lab. Il est volontairement direct : l'objectif final reste de chercher ou Janus peut battre les modeles standards, mais le chemin doit accepter les tests defavorables.

## Donnees Branchees

- DESI DR2 BAO via les fichiers Cobaya officiels `desi_bao_dr2`.
- Pantheon+SH0ES via `Pantheon+SHOES.dat`.
- Pantheon+ est utilise ici avec erreurs diagonales seulement ; ce n'est pas encore une analyse de precision.

## Ce Qui A Ete Corrige

1. La solution Janus utilise `a(u) proportional cosh^2(u)`, pas `cosh(2u)`.
2. La relation supernovae Janus publiee en 2018 a ete ajoutee :
   `m = 5 log10[z + z^2(1-q0)/(1+q0 z + sqrt(1+2 q0 z))] + cst`.
3. Le BAO Janus n'est plus force dans une distance plate ; le code utilise la relation ouverte `r = sinh(2(u0-u_e))` issue du papier 2018.

## Resultats Actuels

Rapport genere : `outputs/reports/baseline_expansion_scores.md`.

### Supernovae Pantheon+ diagonales

- Le meilleur Janus sur une grille fine donne environ `q0 = -0.0354`.
- Chi2 diagonal : environ `777.47`.
- Dans la grille grossiere du rapport, Janus `q0=-0.030` donne `chi2 = 777.58`.
- Les meilleurs Lambda-CDM/CPL de cette passe sont autour de `chi2 = 745`.

Interpretation : Janus n'est pas catastrophique sur les supernovae seules, mais il ne bat pas Lambda-CDM/CPL sur Pantheon+ diagonal dans cette premiere implementation. Le `q0` prefere par Pantheon+ est aussi moins negatif que la valeur `q0 = -0.087 +/- 0.015` revendiquee en 2018 sur 740 supernovae.

### DESI DR2 BAO

- Lambda-CDM `Omega_m=0.300` : `chi2 ~= 10.39` pour 13 points.
- CPL `w0=-0.8, wa=-0.5` : `chi2 ~= 7.99`, mais avec plus de parametres.
- Meilleur Janus teste : `q0=-0.030`, `chi2 ~= 909`.
- Meme avec `q0` tres proche de zero, le diagnostic rapide reste mauvais : `q0=-0.001` donne `chi2 ~= 577`.

Interpretation : la traduction BAO actuelle de Janus est tres defavorable face a DESI DR2. C'est le point dur principal.

## Hypotheses A Verifier

1. **Mauvaise observable BAO pour Janus**
   DESI publie des distances BAO interpretees avec un standard ruler `r_d`. Si le regime Janus a constantes variables modifie la physique du son primordial ou la definition effective de `r_d`, notre comparaison BAO est incomplete.

2. **Relation distance-redshift incomplete**
   La relation supernovae 2018 est specifique aux magnitudes. Les BAO demandent une derivation dediee de `D_M`, `D_H` et `D_V` dans le cadre Janus complet.

3. **Tension reelle avec DESI DR2**
   Si les deux points precedents ne sauvent pas la prediction, DESI DR2 devient un obstacle majeur pour la loi d'expansion Janus simple.

4. **Donnees SN modernes**
   La valeur `q0=-0.087` etait ajustee sur un ancien echantillon de 740 supernovae. Pantheon+ contient 1701 entrees et peut deplacer fortement le fit.

## Prochaines Actions

1. Reproduire exactement le papier SN 2018 sur son jeu de donnees original.
2. Refaire Pantheon+ avec covariance complete, puis comparer `q0`.
3. Deriver proprement les observables BAO Janus depuis les equations, sans supposer que `r_d` est identique a Lambda-CDM.
4. Ajouter un notebook/script de residus par redshift pour voir quels points DESI cassent Janus.
5. Chercher une prediction discriminante ou Janus est fort : grandes structures, vides/repellers, courbes de rotation, formation precoce JWST, ou objets compacts.

## Mise A Jour Axiomatique

En prenant Janus comme axiome de travail, le script `scripts/infer_janus_bao_ruler.py` inverse le probleme BAO :

- correction globale unique : insuffisante ;
- correction redshift unique : amelioration, mais encore mauvaise ;
- correction lineaire separee `D_M` / `D_H` / `D_V` : amelioration forte ;
- dans cette famille phenomenologique, la grille prefere `q0 ~= -0.087`, la valeur mise en avant par le papier supernovae 2018.

Lecture provisoire : si Janus est vrai, DESI BAO semble demander une **regle BAO effective anisotrope**. La direction transverse et la direction radiale ne se corrigent pas exactement de la meme maniere. C'est une piste theorique forte a relier au regime de constantes variables, mais ce n'est pas encore une prediction derivee.
