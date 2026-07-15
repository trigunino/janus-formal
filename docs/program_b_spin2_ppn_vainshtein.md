# Programme B — projecteur spin-2, PPN et Vainshtein

Pour une source conservée, les amplitudes d'échange sont

- massless : `T_mn T^mn - T²/2`;
- Fierz–Pauli massif : `T_mn T^mn - T²/3`.

Le pôle massif contribue donc avec les facteurs `4/3` au potentiel newtonien
`Phi` et `2/3` au potentiel spatial `Psi`. Pour une amplitude Yukawa relative
`alpha` et `y=exp(-m r)` :

`G_eff/G0 = 1 + (4/3) alpha y`,

`gamma = Psi/Phi = (3+2 alpha y)/(3+4 alpha y)`.

Les amplitudes sont `alpha=K_minus/K_plus` dans `++`,
`alpha=K_plus/K_minus` dans `--`, et `alpha=-1` dans le canal croisé.

## Verdict linéaire

Pour des cinétiques égales et `m r << 1`, `gamma=5/7`, très loin de GR. La
limite `m -> 0` est discontinue : c'est l'effet vDVZ. La mesure Cassini donne
`gamma-1=(2.1 +/- 2.3) 10^-5`; une Yukawa non écrantée d'amplitude d'ordre un
est donc exclue à l'échelle solaire.

Résultat nouveau important : l'annulation courte distance trouvée avec le
noyau scalaire ne survit pas au projecteur spin-2 complet. Dans le canal
croisé, `Phi/Phi0=-1/3` et `Psi/Psi0=1/3` pour `m r << 1`.

## Étape non linéaire requise

Candidate A doit fonctionner dans le régime de Vainshtein,

`r_V=(r_s/m²)^(1/3)`,

avec les expériences locales à `r << r_V`. Le rayon seul ne prouve pas
l'écrantage. Dans la réduction hélicité-0 de type cubique, l'équation

`u+c u²=(r_V/r)^3`

a pour branche saine `c>0` et pour facteur d'écrantage par rapport à la
solution linéaire

`S_V=2/[1+sqrt(1+4 c (r_V/r)^3)]`.

Ainsi `S_V` tend vers zéro comme `(r/r_V)^(3/2)/sqrt(c)` et permet
`gamma -> 1` profondément dans le rayon de Vainshtein. Il reste à dériver le
coefficient absolu `c(beta_n,K_plus,K_minus)` de Candidate A et à vérifier l'absence
d'instabilité de gradient sur la branche PT : le profil actuel est donc une
réduction universelle, pas encore la solution non linéaire complète du modèle.

L'expansion `Lambda_3` fixe déjà les combinaisons de forme
`alpha1=beta1+2 beta2+beta3` et `alpha2=beta2+beta3`. Sur le cône PT,
`alpha2/alpha1=1/2>0`; le terme cubique nécessaire à Vainshtein est donc
présent et non dégénéré.

Mise à jour canonique : le calcul dans
`program_b_canonical_vainshtein_coefficient.md` ferme le coefficient autonome.
Sur la branche PT, `C2=(beta1+beta2)^2(1+K_plus/K_minus)/2` et
`C3=(beta1+beta2)^2`. Seule la charge scalaire de matière manque encore pour
fixer numériquement `r_V`.
