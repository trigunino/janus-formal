# Programme B — propagateurs statiques et correction de Yukawa

Pour l'opérateur quadratique réduit

`O(q²) = q² diag(K_plus,K_minus) + mu [[1,-1],[-1,1]]`,

l'inverse exact possède un pôle massless et un pôle massif :

`G(q²) = R0/q² + Rm/(q²+m²)`, avec

`m² = mu (K_plus+K_minus)/(K_plus K_minus)`.

Les résidus sont

`R0 = [[1,1],[1,1]]/(K_plus+K_minus)`,

`Rm = [[K_minus/K_plus,-1],[-1,K_plus/K_minus]]/(K_plus+K_minus)`.

Le noyau statique est donc

`G(r) = [R0 + Rm exp(-m r)]/(4 pi r)`,

et, pour deux vecteurs de sources `J1,J2`,

`V(r) = -J1^T [R0 + Rm exp(-m r)] J2/(4 pi r)`.

La correction Yukawa relative dans le canal `++` vaut `K_minus/K_plus`.
Dans le canal croisé, elle vaut `-1` : le terme massif annule le terme
massless à courte distance. Exactement,
`R0+Rm=diag(1/K_plus,1/K_minus)`.

Ce résultat fixe les pôles et les coefficients du noyau statique conservé.
Il ne contient pas encore le projecteur spin-2 complet, le facteur vDVZ/PPN,
ni l'écrantage non linéaire de Vainshtein.
