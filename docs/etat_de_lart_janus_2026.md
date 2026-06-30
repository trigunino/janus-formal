# Etat De L'Art Janus 2026

Date de reference : 7 juin 2026.

Ce document sert de point de depart. Il ne tranche pas la validite du modele Janus ; il classe les sources recentes, les revendications testables et les donnees observationnelles utiles.

## 1. Socle Janus Recent

### Articles publies avec DOI

1. **Petit, Margnat & Zejli, 2024 - modele cosmologique bimetrique**
   - Source : European Physical Journal C, 84, 1226.
   - DOI : https://doi.org/10.1140/epjc/s10052-024-13569-w
   - Role dans le projet : socle geometrique et equations de champ couplees.
   - A extraire : conventions de signe, metriques, tenseurs d'interaction, conditions de Bianchi, limite cosmologique homogene/isotrope.

2. **Petit & Zejli, 2025 - groupe symplectique Janus**
   - Source : Reviews in Mathematical Physics, 37(1), 2450054.
   - DOI : https://doi.org/10.1142/S0129055X24500545
   - Role dans le projet : base mathematique pour les symetries, inversion masse/energie, dualite matiere-antimatiere.
   - A extraire : definitions de groupe, action coadjointe, interpretation des torsors.

3. **Petit, D'Agostini & Monnet, 2025 - dynamique galactique**
   - Source : Astrophysics and Space Science, 370:121.
   - DOI : https://doi.org/10.1007/s10509-025-04511-x
   - Role dans le projet : piste de test "matiere noire" via Vlasov-Poisson et courbes de rotation.
   - A extraire : forme de la fonction de distribution, predictions de courbes de rotation, parametres ajustables.

4. **Petit & D'Agostini, 2025 - plugstars**
   - Source : Journal of Modern Physics, 16(10), 1479-1490.
   - DOI : https://doi.org/10.4236/jmp.2025.1610072
   - Role dans le projet : piste de test "trous noirs / objets compacts".
   - A extraire : prediction du rapport de temperatures de brillance proche de 3, lien avec M87* et Sgr A*.

5. **Petit & D'Agostini, 2026 - critique du modele trou noir, partie I**
   - Source : Journal of Modern Physics, 17(2), 199-239.
   - DOI : https://doi.org/10.4236/jmp.2026.172014
   - Role dans le projet : argument geometrique contre l'interpretation standard des trous noirs.
   - A extraire : predictions observationnelles explicites, pas seulement critiques historiques.

### Textes 2026 a traiter comme preprints / documents auteur

1. **Expansion Janus et DESI**
   - Source : https://www.jp-petit.org/papers/cosmo/2026-Expansion-exact-solution-2014-.pdf
   - Revendication centrale : la solution exacte Janus donnerait une acceleration plus forte dans le passe, en accord avec les indices DESI DR2.
   - Equations utiles reperees :
     - `a(u) = alpha * cosh^2(u)` ou notation equivalente selon la mise en page du PDF.
     - `t(u) = alpha / 2 * (1 + sinh(2u) / 2 + u)`
   - A faire : verifier la derivation complete, la normalisation, et la comparaison numerique aux donnees DESI/SNe. La lecture OCR peut confondre `cosh^2(u)` avec `cosh(2u)` ; le code utilise la forme compatible avec l'integrale temporelle.

### Relation supernovae publiee en 2018

- Source : D'Agostini & Petit, *Constraints on Janus Cosmological model from recent observations of supernovae type Ia*, Astrophysics and Space Science 363:139, 2018.
- PDF auteur : https://www.jp-petit.org/papers/cosmo/2018-AstroPhysSpaceSci.pdf
- Relation utilisee pour le banc d'essai SN :
  - `m_bol = 5 log10[z + z^2(1-q0)/(1+q0 z + sqrt(1+2 q0 z))] + cst`
  - domaine : `q0 < 0` et `1 + 2 q0 z > 0`
- La publication revendique un meilleur ajustement autour de `q0 = -0.087 +/- 0.015` sur 740 supernovae.

2. **Alternative a l'inflation par constantes variables**
   - Source : https://www.jp-petit.org/papers/cosmo/2026-Alternative-to-Inflation-Variable-Constants-Regime.pdf
   - Revendication centrale : homogeneite primordiale sans inflation, via regime de constantes variables conservant invariance de Lorentz et constante de structure fine.
   - A faire : identifier des observables CMB concretes ; sinon garder hors du premier prototype.

3. **Autres textes 2026**
   - Incoherence mathematique/geometrique du trou noir, partie II.
   - "The Real World as a part of a Complex Reality".
   - A traiter plus tard, sauf si une prediction observationnelle nette en sort.

## 2. Observations Pertinentes En 2026

### DESI

- DESI DR2, publie en 2025, constitue la base observationnelle la plus pertinente pour l'expansion recente.
- Guide officiel : https://www.desi.lbl.gov/2025/03/19/desi-dr2-results-march-19-guide/
- Communique 2026 : DESI a termine son releve planifie de cinq ans le 15 avril 2026, avec les premiers resultats complets attendus en 2027.
- Source : https://www.desi.lbl.gov/2026/04/15/desi-reaches-mapping-milestone-surpassing-expectations/

Conclusion : au 7 juin 2026, il faut utiliser DESI DR2 pour le code, pas encore un "DESI 5 ans cosmologie" qui n'est pas publie.

### Tension de Hubble

- Planck 2018 sous Lambda-CDM : `H0 ~= 67.4 km/s/Mpc`.
- SH0ES 2022 : `H0 ~= 73.04 km/s/Mpc`.
- Role : test de compatibilite globale, pas seulement ajustement local.

### Supernovae Ia

- Pantheon+ et jeux associes SH0ES : distances luminosite.
- Source de donnees : https://zenodo.org/records/16365279
- Role : contraindre `d_L(z)` et le module de distance.

### CMB

- Planck reste un test tres dur pour tout modele alternatif.
- Point crucial : un modele peut ameliorer une tension recente mais echouer sur les pics acoustiques CMB.
- Pour le premier prototype : utiliser seulement des contraintes compressees ; le calcul complet CMB viendra plus tard.

### Galaxies et grandes structures

- SPARC : courbes de rotation de galaxies.
- DES / KiDS / HSC : tension `S8`, lentillage faible.
- JWST : formation precoce de galaxies.
- Ces axes sont importants, mais moins simples que DESI/SNe pour un premier banc d'essai.

### Objets compacts

- EHT M87* et Sgr A* : tests plugstar / trou noir.
- Prochaine fenetre utile : nouvelles images EHT attendues autour de 2027 selon les annonces relayees par J.-P. Petit ; a verifier avec sources EHT officielles avant usage.

## 3. Hypotheses Janus A Tester

1. **Expansion cosmique**
   - Prediction revendiquee : acceleration plus forte dans le passe, tendant a diminuer.
   - Donnees : DESI DR2 BAO + Pantheon+/DES-SN5YR/Union3.
   - Concurrents : Lambda-CDM, CPL `w0-wa`, quintessence simple.

2. **Matiere noire**
   - Prediction revendiquee : masses negatives remplacent les fonctions attribuees a la matiere noire.
   - Donnees : courbes de rotation, lentillage, amas, Bullet Cluster, CMB.
   - Risque : expliquer les rotations ne suffit pas ; le lentillage et le CMB sont indispensables.

3. **Inflation**
   - Prediction revendiquee : homogeneite primordiale sans inflation.
   - Donnees : CMB, spectre primordial, modes tensoriels, nucleosynthese.
   - Priorite : basse pour le prototype, haute pour validation finale.

4. **Trous noirs**
   - Prediction revendiquee : objets supermassifs de type plugstar, rapport de temperature de brillance proche de 3.
   - Donnees : EHT, dynamique stellaire proche Sgr A*, ondes gravitationnelles LIGO/Virgo/KAGRA.
   - Risque : domaine tres conflictuel ; besoin de predictions chiffrables.

## 4. Strategie De Non-Redondance

Pour ne pas refaire ce qui existe deja :

1. extraire toutes les equations et predictions numeriques deja publiees ;
2. reproduire les figures et resultats de reference ;
3. comparer aux donnees publiques plus recentes ;
4. seulement ensuite proposer une extension ou un modele numerique nouveau.

La premiere cible raisonnable est donc : **reproduire et tester la loi d'expansion Janus face a DESI DR2 + supernovae**.
