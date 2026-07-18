# Programme B — GHY non-null du throat canonique

Le normal canonique fourni par P vérifie `n²=+1`; le throat relève donc du
secteur non-null. La densité locale appropriée est
\[
\mathcal L_{GHY}=M^2\epsilon\sqrt{|\det h|}\,
\mathrm{tr}(h^{-1}K).
\]
P possède déjà sa variation locale exacte et la cancellation de Dirichlet
`delta(EH)+delta(GHY)=0` pour chaque secteur.

Pour des mesures induites PT-identifiées, écrivons
`epsilon_minus=p_epsilon epsilon_plus` et `K_minus=p_K K_plus`. Le rapport de
la somme appariée à la densité plus est
\[
1+{M_-^2\over M_+^2}p_\epsilon p_K.
\]
Une inversion simultanée de l'orientation et de la courbure donne
`p_epsilon*p_K=+1` : GHY est alors PT-pair et les deux contributions
s'ajoutent. L'annulation inter-feuillets n'est donc pas générique. La fermeture
variationnelle correcte est sectorielle, par `EH_±+GHY_±`.

Reste à construire, depuis le collar canonique de P, le tenseur concret
`K_ab`, son déterminant induit et l'intégrale globale. Les interfaces locales
existent déjà; leur instanciation géométrique est le prochain pont P→B.

Un raccourci rigoureux est désormais isolé : si PT fixe la géométrie induite
du throat et si la covariance de la connexion transporte le renversement du
normal en `K_ab -> -K_ab`, alors au point fixe `K_ab=-K_ab`, donc `K_ab=0`.
Le throat serait totalement géodésique et sa densité GHY de fond serait nulle.
P prouve déjà le point fixe métrique et le renversement du normal, mais pas
encore leur prolongement à la connexion/courbure extrinsèque; cette dernière
flèche ne doit donc pas être supposée.

## Mise à jour : atlas normal lisse de P

P construit maintenant des représentants locaux lisses et non nuls du normal
canonique, avec recollement par le cocycle réel `s_ij=±1`. Il n'est donc plus
nécessaire de choisir un normal global, choix interdit par la ligne normale
non orientable. Sur un chevauchement,
\[
n_j=s_{ij}n_i,\qquad K_j=s_{ij}K_i,\qquad
\epsilon_j=s_{ij}\epsilon_i.
\]
Par conséquent `epsilon_j K_j=epsilon_i K_i`; la densité GHY est un scalaire
global dès que la covariance de la connexion établit la loi de recollement de
`K`. Le problème restant n'est plus la régularité du normal, mais uniquement
la construction de cette connexion/courbure extrinsèque sur l'atlas canonique.

## Loi extrinsèque locale désormais fermée

Dans chaque carte normale de Gauss fournie par P, la connexion de Levi-Civita
donne exactement
\[
B_{ab}={\sigma\over2}\partial_nh_{ab},\qquad K=h^{ab}B_{ab}.
\]
Lean prouve maintenant que `sigma -> -sigma` entraîne `B -> -B` et `K -> -K`.
Avec le cocycle local constant du normal, la loi de recollement requise est
donc établie dès que les cartes canoniques de latitude sont identifiées aux
cartes de Gauss.

Le verrou est réduit à une égalité géométrique précise : construire le collar
de Gauss de la métrique canonique et montrer que son normal coïncide avec le
normal de latitude. Aucune liberté de signe supplémentaire ne subsiste.

## Calcul du fond équatorial

Dans les coordonnées de latitude du fond intrinsèque utilisé par P, la partie
tangentielle sphérique du produit s'écrit
\[
h(n)=\cos^2(n)h_{S^2}-dt^2.
\]
Ainsi `partial_n h(0)=0`. La formule gaussienne donne `B_ab=0`, `K=0` et une
densité GHY de fond nulle. Le calcul est exact et testé. Il reste à identifier
formellement dans Lean ce collar avec la métrique descendue du quotient; avant
ce bridge, ce résultat n'est pas revendiqué comme théorème global du throat.
