# Audit exploratoire : energies negatives quantiques et secteur Janus

Statut : note exploratoire, non promue au registre des formules verifiees.

Date : 2026-07-15.

## Question et verdict court

La theorie quantique des champs (TQC) autorise des densites d'energie
renormalisees localement negatives, mais elle ne fournit pas, a elle seule, une
matiere macroscopique stable de masse gravitationnelle negative. Les frequences
negatives, antiparticules, normes negatives de jauge et masses effectives
negatives ne sont pas le secteur negatif de Janus.

Une connexion Janus reste concevable seulement sous une hypothese supplementaire :
chaque feuillet aurait un Hamiltonien positif relativement a sa propre orientation
temporelle, tandis que le signe oppose apparaitrait dans la projection/couplage
gravitationnel entre feuillets. Cette construction n'est pas derivee des axiomes
J1-J4 actuels. En particulier, ceux-ci ne donnent ni action quantique a deux
feuillets, ni vide, ni prescription de renormalisation de
`<T_munu>_ren`.

## 1. Donnees Janus effectivement disponibles

Les axiomes J1-J4 et les equations M15 affirment :

\[
\rho_+>0,\qquad \rho_-<0,
\]

\[
G^{(+)}_{\mu\nu}=\chi\left(T^{(+)}_{\mu\nu}
+Q_{-+}T^{(-)}_{\mu\nu}\right),\qquad
Q_{-+}=\sqrt{\frac{-g_-}{-g_+}},
\]

\[
G^{(-)}_{\mu\nu}=-\chi\left(Q_{+-}T^{(+)}_{\mu\nu}
+T^{(-)}_{\mu\nu}\right).
\]

Le registre confirme ces formules comme affirmations des sources M15/M30, pas
comme validations observationnelles. Il ne contient aucune formule reliant
`T_-` a un tenseur quantique renormalise, a l'effet Casimir ou aux solutions
negatives de Dirac. Le TODO confirme que la voie PT/CPT manque encore du contenu
de champ sur les deux feuillets, d'une prescription de vide et d'une energie
d'etat renormalisee.

## 2. Taxonomie : ce que « negatif » signifie

| Objet | Sens exact | Etat physique stable ? | Equivalent a Janus ? |
|---|---|---:|---:|
| Frequence KG/Dirac negative | Mode `exp(+i omega t)`, branche `p0=-E_p` | Oui apres quantification | Non |
| Antiparticule | Creation par l'operateur de la branche conjuguee, energie `+E_p` | Oui | Non |
| `<T00>_ren < 0` | Energie locale inferieure a celle du vide de reference | Oui, mais localement et sous fortes bornes | Connexion possible, non demontree |
| Casimir | Difference d'energie renormalisee entre conditions aux limites | Oui pour le dispositif complet | Pas un second secteur |
| Etat comprime/subvacuum | Quadrature ou observable normalement ordonnee sous le niveau du vide | Oui, transitoire | Analogie seulement |
| Masse effective negative | Courbure negative d'une bande/dispersion | Oui dans un milieu pilote | Non : masse inertielle microscopique et gravitation restent positives |
| Ghost cinetique | Mauvais signe du terme cinetique; Hamiltonien typiquement non borne | Generalement non | Danger, pas explication |
| Norme negative de jauge | Etat auxiliaire de quantification covariante | Elimine du sous-espace physique | Non |
| Secteur Janus negatif | `rho_-<0`, seconde metrique et seconde famille geodesique | Postule | Objet a expliquer |

Pour un champ de Dirac libre, le reordonnement normal donne schematiquement

\[
H=\int d^3p\,E_{\mathbf p}
\left(a^\dagger a+b^\dagger b\right),\qquad E_{\mathbf p}>0.
\]

La branche negative devient donc l'antiparticule d'energie positive; elle ne
produit pas `rho_-<0`. C'est egalement compatible avec ALPHA-g, qui observe une
acceleration de l'antihydrogene dirigee vers la Terre [1].

## 3. Audit minimal de stabilite

### 3.1 Modele a energie signee et couplage direct

Le modele jouet le plus direct est

\[
H_0=\frac12(p_+^2+\omega_+^2q_+^2)
-\frac12(p_-^2+\omega_-^2q_-^2),
\qquad H_{\rm int}=\lambda q_+^2q_-^2.
\]

`H0` n'est borne ni inferieurement ni superieurement. Si `lambda != 0`, la
conservation de l'energie autorise des excitations `+E` et `-E` de somme nulle,
avec une phase disponible sans plafond. La version TQC permet alors

\[
|0\rangle\longrightarrow
|\mathbf p_+,\ldots\rangle+|\mathbf p_-,\ldots\rangle,
\qquad \sum E_+ +\sum E_-=0,
\]

et conduit generiquement a une desintegration du vide. Les modeles phantom
illustrent cette contrainte et requierent un cutoff tres bas pour rester
phenomenologiquement tolerables [2]. Des systemes mecaniques ghost particuliers
peuvent avoir des trajectoires bornees, mais cela ne constitue pas encore une
TQC locale, unitaire et gravitationnelle stable [3].

### 3.2 Trois regimes

1. **Decouplage exact.** Pour `lambda=0` et des secteurs superselectionnes,
   aucune paire ne peut etre produite. Le spectre global reste non borne et le
   decouplage exact doit etre protege par une symetrie.
2. **Couplage direct.** Un vertex commun rend normalement possible la production
   `+/-`; ce regime echoue sans mecanisme supplementaire demonstrant un vide
   stable et une matrice S unitaire.
3. **Couplage gravitationnel seulement.** Il n'est pas equivalent a un
   decouplage : les perturbations metriques communes ou couplees peuvent servir
   d'intermediaire. Il faut diagonaliser l'action quadratique complete et verifier
   signes cinetiques, gradients, poles et residus, pas seulement les equations
   lineaires de densite.

### 3.3 Sortie potentiellement coherente

Une voie conditionnelle consiste a imposer

\[
H_+\ge 0\quad\text{dans le futur }t_+,
\qquad H_-\ge 0\quad\text{dans le futur }t_-,
\qquad t_-=-t_+,
\]

et a faire provenir le signe relatif d'une projection PT/CPT des sources, non
d'un ghost cinetique. Cela ressemble a l'univers CPT-symetrique, ou CPT choisit
un vide, mais ce modele ne produit pas de masse gravitationnelle negative [4].
Pour Janus, il manque encore l'action, le produit scalaire physique, le generateur
global et la preuve d'absence de vertices permettant la production illimitee.

## 4. Energie quantique negative et gravitation

### 4.1 Ce que la TQC permet

Pour deux plaques ideales separees de `a`, la contribution electromagnetique
Casimir standard est

\[
\frac{E_C}{A}=-\frac{\pi^2\hbar c}{720a^3},\qquad
\rho_C=-\frac{\pi^2\hbar c}{720a^4},\qquad
P_C=-\frac{\pi^2\hbar c}{240a^4}.
\]

Il s'agit d'une difference renormalisee. Le dispositif total inclut plaques,
contraintes et energie de liaison; une densite locale negative n'implique donc
pas automatiquement une masse totale negative.

Les inegalites quantiques bornent les moyennes temporelles. Pour un champ
scalaire libre sans masse en espace de Minkowski 4D et une fonction reelle
lisse `g` (unites `hbar=c=1`), une borne de Fewster-Eveson est

\[
\int dt\,g(t)^2\,\langle T_{00}(t)\rangle_{\rm ren}
\ge -\frac{1}{16\pi^2}\int dt\,|g''(t)|^2.
\]

La constante et la forme changent avec le champ et l'echantillonnage [5,6].
Ces bornes interdisent de rendre arbitrairement intense et
durable une impulsion negative. La QNEC impose en outre une borne nulle locale
reliee a la variation seconde de l'entropie d'intrication [7].

### 4.2 Ce que Janus predit actuellement pour une cavite

Une cavite ordinaire appartient au secteur positif. Sa variation de source est
donc `delta T_+`, et les equations actuelles donnent directement

\[
\delta G_+=\chi\,\delta T_+.
\]

Elles ne produisent aucun coefficient Janus distinct pour une cavite Casimir
ordinaire. Dans la limite faible standard, l'hypothese d'equivalence donne

\[
\Delta F_z=\frac{g\,\Delta E_C}{c^2}.
\]

On peut parametrer une anomalie par

\[
\Delta F_z=(1+\varepsilon_{\rm vac})
\frac{g\,\Delta E_C}{c^2},
\]

mais **`epsilon_vac` n'est pas derivable des axiomes actuels**. Une cavite du
secteur negatif entrerait dans l'equation positive via `Q_-+ delta T_-`, mais ni
sa preparation, ni son observable, ni son raccord au Casimir ordinaire ne sont
definis. Fixer `epsilon_vac` serait donc un ajustement interdit, pas une
prediction.

## 5. Confrontation experimentale

| Experience | Observable | Etat/resultat | Signal Janus actuellement calculable ? |
|---|---|---|---:|
| ARCHIMEDES | Variation de poids lors de la modulation d'energie de cavites supraconductrices | Construction terminee en 2025; mise en cryogenie annoncee pour fin 2026, pas encore de mesure publiee du poids du vide [8,9] | Non, faute de `epsilon_vac` derive |
| Lumiere comprimee | Variance homodyne sous le bruit du vide | Gain interferometrique de 10 dB mesure; ce n'est pas une mesure gravitationnelle directe de `T00` [10] | Non |
| Masse effective negative atomique | Reponse dynamique/dispersion d'un gaz pilote | Oscillateur collectif effectif de masse negative realise [11] | Simulateur de stabilite seulement |
| ALPHA-g | Distribution verticale d'annihilation de l'antihydrogene | `a_g=(0.75 +/- 0.13 +/- 0.16)g`, dirige vers la Terre [1] | Exclut l'identification simple antimatiere=`rho_-` |

ARCHIMEDES est le test le plus proche de la question « l'energie renormalisee
gravite-t-elle ? », mais un resultat standard ne validerait pas un second
secteur. Un ecart exigerait d'abord l'elimination des effets thermiques,
electromagnetiques et mecaniques avant toute interpretation Janus.

## 6. Conclusions classees

### Deja exclu ou conceptuellement invalide

- Identifier les solutions Dirac/Klein-Gordon negatives a une matiere Janus.
- Identifier antimatiere et masse gravitationnelle negative.
- Utiliser une masse effective negative comme preuve de `T00<0` gravitant.
- Utiliser des normes negatives de jauge comme etats physiques.
- Introduire un ghost local directement couple sans traiter la desintegration
  du vide et l'unitarite.

### Mathematiquement possible, non demontre

- Deux Hamiltoniens positifs, chacun defini par le futur propre de son feuillet,
  avec signe relatif issu d'une projection PT/CPT.
- Densites quantiques locales negatives dans chaque feuillet, soumises aux QEI.
- Couplage uniquement gravitationnel stable, sous reserve d'une action complete
  dont la matrice cinetique, les gradients et les residus sont sains.

### Prediction falsifiable disponible

Aucune nouvelle prediction numerique Janus n'est derivable des axiomes actuels.
La premiere prediction falsifiable exige de deriver, sans ajustement, au moins
l'un des objets suivants :

1. `epsilon_vac` pour une cavite ordinaire;
2. un rapport de chute libre propre a un etat/objet du secteur negatif;
3. un taux fini de transition entre secteurs;
4. un spectre de modes a deux feuillets montrant simultanement absence de ghost,
   absence d'instabilite de gradient et Hamiltoniens physiques positifs.

Le prochain calcul utile est donc l'action quadratique quantifiee des deux
feuillets. Une nouvelle etude Casimir sans cette action ne peut pas distinguer
Janus de la relativite generale semi-classique.

## References

1. ALPHA Collaboration, [Observation of the effect of gravity on the motion of antimatter](https://www.nature.com/articles/s41586-023-06527-1), Nature 621 (2023).
2. J. M. Cline, [Phantom Fluid Cosmology -or- Ghosts for Gordon](https://arxiv.org/abs/2401.02958) (2024).
3. C. Deffayet et al., [Global and local stability for ghosts coupled to positive energy degrees of freedom](https://arxiv.org/abs/2305.09631), JCAP 11 (2023) 031.
4. L. Boyle, K. Finn, N. Turok, [CPT-Symmetric Universe](https://arxiv.org/abs/1803.08928), Phys. Rev. Lett. 121 (2018) 251301.
5. L. H. Ford, [Negative Energy Densities in Quantum Field Theory](https://arxiv.org/abs/0911.3597), Int. J. Mod. Phys. A 25 (2010).
6. C. J. Fewster, S. P. Eveson, [Bounds on negative energy densities in flat spacetime](https://arxiv.org/abs/gr-qc/9805024), Phys. Rev. D 58 (1998) 084010.
7. S. Balakrishnan et al., [A General Proof of the Quantum Null Energy Condition](https://arxiv.org/abs/1706.09432), JHEP 09 (2019) 020.
8. E. Calloni et al., [The Archimedes experiment](https://arxiv.org/abs/1511.00609), Nucl. Instrum. Meth. A 824 (2016).
9. Einstein Telescope Italia, [ARCHIMEDES construction completed at Sos Enattos](https://www.einstein-telescope.it/en/2025/03/28/archimedes-construction-completed-at-sos-enattos/) (2025), et [presentation Moriond 2025](https://moriond.in2p3.fr/2025/Gravitation/transparencies/2-tuesday/2-afternoon/05_alloca.pdf).
10. J. Heinze et al., [10 dB Quantum-Enhanced Michelson Interferometer with Balanced Homodyne Detection](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.129.031101), Phys. Rev. Lett. 129 (2022) 031101.
11. J. Kohler et al., [Negative-Mass Instability of the Spin and Motion of an Atomic Gas Driven by Optical Cavity Backaction](https://arxiv.org/abs/1709.04531), Phys. Rev. Lett. 120 (2018) 013601.
