# Programme B — témoin poussière de P et borne de Higuchi

Dans la réduction hamiltonienne de P,
\[
\dot a=N{\partial C\over\partial p}=-N{p\over6M^2a},
\qquad H={\dot a\over Na}=-{p\over6M^2a^2}.
\]
Le témoin poussière exact de P a `a_±=p_±=M_±²=1`, donc
`H_±=-1/6`. La borne de Higuchi dépend ici de la magnitude commune.

Pour `beta1=beta3=1`, `beta2=0`, `K_±=1`, la formule complète de B donne
\[
\Delta_{bi}=2H^4(m^2-H^2).
\]
Le témoin est donc strictement sain si `m²>1/36`. Sous la normalisation
conditionnelle `m²=1`,
\[
\Delta_{bi}={35\over23328}>0.
\]

Ceci décide la stabilité instantanée de ce point réduit, pas celle d'une
histoire cosmologique. Il reste surtout à dériver le facteur exact reliant
`interactionScale` dans P au `m²` canonique de la perturbation hélicité-zéro
dans B; la valeur `m²=1` ne doit pas être utilisée avant ce bridge.

## Voisinage stable certifié

Pour deux magnitudes de Hubble positives, l'inégalité
`(H_+²+H_-²)² >= 4 H_+² H_-²` donne
\[
\Delta_{bi}\geq 2H_+^2H_-^2(m^2-H_+H_-).
\]
Ainsi `H_+H_-<m²` est une condition suffisante stricte. En particulier, sous
la normalisation conditionnelle `m²=1`, tout rectangle
\[
|H_+-1/6|\leq\epsilon,\qquad |H_--1/6|\leq\epsilon,
\quad 0\leq\epsilon<1/6
\]
est entièrement dans le cône sain. La restriction `epsilon<1/6` conserve les
deux magnitudes strictement positives; elle est volontairement conservative.
