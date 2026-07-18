# Programme B — flux de bord PT et intégrabilité

Le critère covariant local d'intégrabilité d'une charge est l'annulation du
flux symplectique

`Omega_boundary(delta1,delta2)=delta1 delta2 H-delta2 delta1 H`.

Si PT inverse l'orientation et rend ce flux impair, les contributions des deux
feuillets s'annulent. La charge Hamiltonienne totale appariée est alors
localement intégrable sur le sous-espace PT.

La fonctionnelle de joint appariée est maintenant explicitée :
\[
I_C=2\epsilon\int_C\left(K_+\sqrt{\sigma_+}\eta_+
+K_-\sqrt{\sigma_-}\eta_-\right).
\]
Elle s'annule si les densités pondérées sont PT-opposées. Pour un joint nul,
les redéfinitions opposées des normales produisent un résidu
`(K_+sqrt(sigma_+)-K_-sqrt(sigma_-)) log(alpha)`. L'indépendance de
normalisation exige donc l'égalité des aires pondérées, ou un contre-terme de
joint fixé.

La fonctionnelle et son obstruction sont fermées algébriquement. P/E reste
nécessaire pour décider si la géométrie physique satisfait l'égalité des aires
pondérées et pour choisir globalement les normales nulles; l'intégrabilité
globale n'est donc pas encore affirmée.

## Mise à jour depuis le Programme P

Pour le throat canonique effectivement construit par P, le normal de latitude
descendu est orthogonal au throat et son carré métrique vaut exactement `+1`.
Il est donc spacelike, non nul. Le problème de redéfinition multiplicative des
normales nulles ne concerne pas cette jonction canonique : B doit y employer la
fonctionnelle de joint non-null. Le cas nul reste pertinent seulement pour une
autre strate ou une autre géométrie de jonction.

Attention : cela ne signifie pas que les deux termes GHY s'annulent entre
feuillets. Si PT renverse simultanément l'orientation et `K_ab`, leur produit
est pair et les densités GHY s'ajoutent. La cancellation démontrée par P est
`delta(EH_±)+delta(GHY_±)=0` dans chaque secteur; voir
`program_b_nonnull_ghy_pt_bridge.md`.
