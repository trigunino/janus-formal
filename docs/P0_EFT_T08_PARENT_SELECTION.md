# T08 — reconstruction du parent et contraintes de sélection

Point de départ du 2026-09-19, après examen des notes jointes de ChatGPT :
**T08 reste ouvert**. Vingt-quatre modules établissent maintenant des résultats sur
les parents quadratiques, la reconstruction hilbertienne et les vrais domaines
non bornés à résolvante réelle fournie, puis sur les libertés laissées par le
recollement, les domaines de Robin et les invariants T02/BRST existants. Ils ne
dérivent pas un parent physique Janus. Le chantier T12 est
indépendant et n'est pas modifié.

## Résultats formalisés

Dans `P0EFTJanusParentBulkBoundaryShearEquivalence.lean`, le changement
`x ↦ x + u n + v t` est construit avec son inverse, à bord fixé, puis appliqué
à l'action parent. La classification est exacte dans cette catégorie :

\[
P_1\sim P_2\quad\Longleftrightarrow\quad
a_1=a_2\ \text{et}\ K_1=K_2.
\]

Ici `a` est le coefficient bulk non nul et `K` le potentiel réduit de Schur.
Cette catégorie autorise uniquement ces cisaillements, pas les changements
d'échelle du bulk ni toutes les équivalences physiques possibles.
`boundary_shear_equivalent_iff` et `boundary_shear_equivalence` établissent
la classification et la relation d'équivalence.

En particulier, `shifted_completion_action` prouve, pour toute cible réduite :

\[
S_{\mathrm{shift}}(x,n,t)=S_{\mathrm{ref}}(x+n,n,t).
\]

Le contre-exemple existant de non-identifiabilité des **coefficients** reste
correct ; il ne constitue pas un contre-exemple à l'unicité modulo ces
changements de variables. Une source marquée modifie le problème : la preuve
`shear_with_fixed_bulk_source` exhibe le terme supplémentaire
`J (u n + v t)` si l'on garde le couplage source `-J x` fixe.
Les vraies traces géométriques et les sources physiques restent à définir.

Dans `P0EFTJanusParentBulkSpectralResponseSeparation.lean`, deux parents ont
un couplage normal non nul égal à `1`, des coefficients bulk `1` et `2`, et
le même potentiel réduit `k(n²+t²)/2`. Leurs réponses normales sont :

\[
K_1(z)=k+1-\frac1{1-z},\qquad
K_2(z)=k+\frac12-\frac1{2-z}.
\]

Les preuves donnent `K₁(0)=K₂(0)=k` mais `K₁(-1)-K₂(-1)=1/3`.
Ces points évitent les pôles. Pour `k>0`, les deux actions parent sont
strictement positives hors de l'origine, par complétion du carré.
L'ambiguïté statique subsiste donc sans couplage bulk invisible ni instabilité.
La réponse complète est plus informative que sa seule valeur statique.

La comparaison fixe le terme spectral `-z x²/2`, donc la normalisation bulk.
Un cisaillement transporte aussi ce terme et crée des couplages dépendant de
`z` : l'équivalence statique du premier module n'implique pas l'égalité de
familles spectrales dont on maintient ce marquage fixe. La fonction rationnelle
Lean est totale ; son interprétation comme réponse exclut les pôles.

## Extension : quelles données physiques préserver ?

`P0EFTJanusMarkedParentEquivalence.lean` étend les cisaillements aux changements
linéaires bulk inversibles `x ↦ r(x+un+vt)`, avec `r≠0`, à bord fixé.
Pour deux coefficients bulk **positifs**, l'égalité du potentiel réduit est
nécessaire et suffisante pour cette équivalence. Les deux parents couplés du
contre-exemple spectral sont donc eux aussi équivalents après oubli de la
normalisation spectrale.

En revanche, préserver `x²` pour toutes les données bulk et bord impose
`r=±1`, `u=v=0`. Préserver le couplage à une source indépendante `-Jx` impose
`r=1`, `u=v=0`. Le même couple est prouvé **inéquivalent** lorsque le terme
spectral normalisé est conservé. Cette distinction est démontrée sur les
transformations, et non déclarée par un statut physique.

## Reconstruction positive, sans fournir les coefficients bulk

`P0EFTJanusScalarSpectralReconstruction.lean` reconstruit le parent complet à
deux secteurs, modulo un signe bulk commun, depuis **six valeurs de réponse** :
trois normales en `z=0,-1,-2`, deux mixtes en `z=0,-1`, une trace en `z=0`.
Hypothèses : coefficient bulk positif, couplage normal non nul et normalisation
spectrale fixe. Les six coefficients et l'action complète sont identifiés ;
les trois seules valeurs normales ne reconstruisent que le plan `trace=0`.
Le théorème principal est `six_samples_reconstruct_parent_up_to_bulk_sign`.

`P0EFTJanusCyclicMomentReconstruction.lean` réalise le théorème proposé dans les
notes, en dimension éventuellement infinie. Pour des opérateurs **bornés
auto-adjoints** sur des espaces de Hilbert réels complets, avec familles de
couplage cycliques, l'égalité de tous les moments

\[
\langle B_1q,A_1^nB_1r\rangle=\langle B_2q,A_2^nB_2r\rangle
\quad(n\ge0)
\]

construit une **unique** équivalence linéaire isométrique `U` telle que
`U B₁=B₂` et `U A₁=A₂ U`. La réciproque est également prouvée.
`gramEquivalence` construit l'application sur les combinaisons finies puis la
prolonge par densité : l'existence de `U` n'est pas une hypothèse.
`cyclic_equivalence_iff_moments` donne la classification exacte dans cette classe.

Limites de ce premier théorème : le terme direct de bord `C` n'est pas contenu
dans les moments ; les secteurs invisibles sont exclus par cyclicité.
Les extensions suivantes lèvent ces deux limites pour la reconstruction de
la partie observable à partir de la réponse complète. Le dernier prolongement
ci-dessous traite les domaines non bornés à résolvante réelle fournie ; la
localité physique et l'origine des données de réponse restent ouvertes.

## Raccord complet : réponse réelle, partie observable et action

`P0EFTJanusResolventMomentIdentification.lean` développe la véritable réponse
`G(t;q,r)=⟨Bq,(I-tA)⁻¹Br⟩` en série de Neumann sur le disque de rayon
`‖A‖⁻¹` (rayon infini si `A=0`). Ses coefficients sont exactement les moments.
L'égalité des germes en zéro est **équivalente** à l'égalité de tous les moments.
La reconstruction ne suppose donc plus ces derniers fournis séparément.

`P0EFTJanusObservableBulkReduction.lean` construit
`V=fermeture(span{AⁿBq})`, le plus petit sous-espace fermé invariant contenant
le couplage. La restriction `A|V` est bornée auto-adjointe, cyclique par
construction et conserve tous les moments. Le complément orthogonal est
invariant et exactement caractérisé par l'annulation de tous les signaux au
bord. L'équivalence des parties observables est unique, **sans supposer les
réalisations initiales cycliques**.

`P0EFTJanusFullSchurResponseReconstruction.lean` relie algébriquement
`K(z)=C+B*(zI-A)⁻¹B` à `C+tG(t)` pour `t=1/z≠0` ; les grands paramètres sont
prouvés hors du spectre. L'égalité de ces réponses dans un voisinage ponctué
de `t=0` détermine `C` par continuité, puis tous les moments. Le théorème
`full_schur_germ_reconstructs_visible_parent` identifie le terme direct et
l'action complète sur la partie observable, par une unique isométrie qui
transporte `B` et entrelace `A`. Le cas cyclique reconstruit tout le parent.

La restriction conserve aussi le germe réel de réponse. L'énergie invisible
n'est pas supprimée : pour `y∈V` et `z∈V⊥`, une preuve séparée donne
`S(y+z,q)=S_visible(y,q)+⟨z,Az⟩/2`. Le bord ne détermine pas ce dernier terme.
Ces énoncés utilisent des marquages `B` et pairings `C` généraux ; la classe
physique linéaire continue, à `C` bilinéaire symétrique, en est un cas particulier.

`P0EFTJanusTwoModeLocalReconstruction.lean` traite ensuite une classe locale
finie explicitement choisie : `A=[[a,b],[b,c]]`, couplée par `B=g e₀`.
Avec `b,g>0`, les quatre premiers moments matriciels `BᵀAⁿB` déterminent
`a,b,c,g`. Le déterminant de Krylov vaut `b g²>0`. Si `b=0`, tous les moments
ignorent `c`, ce qui exhibe exactement la perte d'un mode invisible.
Cette classe de chaînes orientées est fournie, pas dérivée des données Janus.

## Extension aux opérateurs non bornés et au domaine lagrangien existant

`P0EFTJanusUnboundedResolventDomainReconstruction.lean` utilise un véritable
`LinearPMap` avec son domaine. Le paquet `ResolventAt A μ` contient une
application bornée `R` et les **deux identités inverses** pour `μI-A`.
Le domaine est alors exactement `range R`. Une isométrie entrelaçant deux
résolvantes au même `μ` construit une équivalence des domaines et transporte
l'action des opérateurs non bornés. La symétrie de `A` donne l'autoadjonction
de `R`. La formule `R(I-tR)⁻¹` est démontrée comme vraie résolvante à `μ-t`,
sur le même domaine, lorsque `I-tR` est inversible ; cette condition vaut
dans un voisinage de zéro.

`P0EFTJanusLocalResolventResponseReconstruction.lean` développe la réponse
locale `C+⟨Bq,R(I-tR)⁻¹Br⟩`. Son terme constant masque le premier moment de
`R` ; les coefficients non constants donnent seulement les moments d'ordre
au moins deux. `P0EFTJanusShiftedCyclicReconstruction.lean` prouve que cela
suffit : pour `R` injectif auto-adjoint, `B` cyclique implique `RB` cyclique,
sans supposer un inverse borné de `R` ni un gap. L'isométrie reconstruite
depuis `RB` retrouve `B` par injectivité, puis tous les moments et `C`.
La reconstruction des moments et de la partie observable reste valable sans
cyclicité du parent initial.

`local_response_reconstructs_unbounded_parent` assemble ces flèches : un germe
local exact, pour tous les canaux de bord, reconstruit `C`, le couplage,
l'opérateur et son vrai domaine à unique isométrie près dans la classe cyclique.
Hypothèses explicites : même paramètre réel régulier, vraies résolvantes bornées
fournies et symétrie des opérateurs. Aucune hypothèse de bornitude de `A`.

`P0EFTJanusBoundaryTripleResolventSelectionBridge4D.lean` instancie ce raccord
avec le domaine lagrangien, l'inclusion, l'opérateur et les identités inverses
du triplet de bord complété existant. Le signe est changé explicitement entre
ses conventions `(A-μI)⁻¹` et `(μI-A)⁻¹`. Le théorème
`measured_local_response_selects_lagrangian_realization` déduit de la réponse
mesurée l'équivalence du **domaine lagrangien original** avec le domaine cible
et l'entrelacement des opérateurs ; aucune isométrie n'est fournie en entrée.

Limites : l'existence de ce paquet physique et sa réponse indépendante restent
à établir pour le parent Janus recherché. Il faut des données exactes dans un
voisinage spectral, pas un nombre fini de mesures bruitées. Les secteurs
invisibles et la préservation de la localité géométrique ne sont pas fixés par
ce théorème. L'unicité inverse ne constitue toujours pas la sélection de T08.

## Parent local : réduction exacte et approximation distinguées

`P0EFTJanusLocalAuxiliaryReduction.lean` construit le modèle de symbole local
`(m²+s)x²/2+b x q+C(s)q²/2`, avec `m²>0`, `s≥0` et `C` polynomial.
Son élimination stationnaire donne exactement `K(s)=C(s)-b²/(m²+s)`.
Pour `b≠0`, **aucun polynôme** ne coïncide avec `K` sur tout `s≥0`.
La preuve utilise une identité polynomiale forcée par l'intervalle infini,
évaluée ensuite au pôle négatif ; elle ne traite pas ce pôle comme physique.

L'approximation locale `K₁(s)=C(s)-b²/m²+b²s/(m²)²` possède le reste exact
`K₁-K=b²s²/((m²)²(m²+s))`. Sur `0≤s≤εm²`, `ε≥0`, la borne est
`|K-K₁|≤(b²/m²)ε²`. Il s'agit d'une preuve sur les symboles constants, sans
affirmation d'existence PDE ou d'identification à la gorge Janus.

## Contraintes de sélection : trois libertés explicitement vérifiées

`P0EFTJanusT08LocalGluingSelectionFreedom.lean` considère les segments locaux
`S(x,y)=a(x²+y²)/2-bxy`, avec `a>b>0` et `d=a²-b²`. L'élimination du point
commun donne exactement
`a'=(a₁a₂+d)/(a₁+a₂)`, `b'=b₁b₂/(a₁+a₂)`. Elle conserve `d` et est associative.
Chaque `d>0` admet un segment élémentaire `a=√(d+1), b=1` : la positivité et
le recollement ne sélectionnent donc pas ce paramètre dans cette classe.
Les exemples `(a,b)=(2,1)` et `(3,1)` ne sont pas proportionnels comme actions.
Sur une chaîne fermée à trois sommets, leur différence vaut `x²+y²+z²` :
elle persiste sans bord externe. La symétrie démontrée est le changement
simultané de signe, ainsi que l'échange des extrémités ; ce n'est pas une
preuve du PT physique Janus. Les traces sont fixées. Ce modèle fini n'instancie
ni la géométrie ni le contenu de champs du parent physique recherché.

`P0EFTJanusT08RobinSelectionFreedom4D.lean` utilise le système de Green et
les domaines complétés/fermés existants, sous leurs hypothèses de Green et de
borne de trace. À traces valeur/normale fixées, le
graphe de Robin détermine son opérateur. La surjectivité de la trace complétée
permet de retrouver le sous-espace de bord depuis le domaine ; sous
closabilité, cette distinction subsiste sur le vrai domaine fermé.
Pour un espace de traces non trivial, tous les coefficients réels `κ` donnent
des domaines distincts, fermés et maximaux pour l'adjoint de bord. Cette
compatibilité ne choisit donc pas `κ`. Une observation marquée non nulle
`(v,n)` dans le graphe le détermine par `κ=⟨v,n⟩/‖v‖²`.
La maximalité de bord ne remplace pas l'hypothèse séparée de régularité
nécessaire à l'auto-adjonction effective de l'opérateur.

`P0EFTJanusT08InvariantDeformationFreedom4D.lean` construit une famille
injective `λχ` dans le vrai carrier T02 de fonctionnelles invariantes de degré
au plus quatre. Ici `χ` est la **valeur du champ scalaire LL-measure**, pas
une densité composite ni une constante. Les transitions d'atlas la préservent.
Le raccord existant aux jets spatiaux T06 transporte exactement cette
fonctionnelle. Le BRST abélien à fantôme scalaire, qui agit sur les slots de
jauge, l'annule pour tout `λ`, y compris sous le décalage fini associé.
L'opérateur d'Euler T06, évalué sur une variation unitaire de `χ`, vaut `λ` :
les coefficients distincts restent distincts après identification des
expressions d'Euler. Il ne s'agit donc pas seulement de représentants
différents d'une densité d'Euler nulle.
Ce résultat ne prouve ni invariance sous les difféomorphismes non linéaires,
ni invariance BV complète, ni existence d'un vide pour l'action déformée.
Les trois constructions sont des diagnostics séparés, pas un unique parent
Janus satisfaisant simultanément toutes les contraintes physiques.

## Potentiels centrés : minimum scalaire et Hessienne fixés

`P0EFTJanusT08ValuePotentialEuler4D.lean` calcule l'opérateur d'Euler spatial
T06 pour tout potentiel différentiable dépendant seulement de la valeur du
champ : les termes de dérivées totales disparaissent, et l'expression d'Euler
est la dérivée ordinaire du potentiel. Pour `λ(Lφ-v)^n`, elle vaut
`λ n (Lφ-v)^(n-1) Lδφ`. Cette formule est dérivée du véritable opérateur T06,
pas définie comme un nouvel opérateur simplifié.

`P0EFTJanusT08StableMassDeformation4D.lean` inscrit `λ(χ-v)²` dans le carrier
invariant T02, avec référence `v` arbitraire, éventuellement non nulle. Le
raccord T06 est exact et le BRST abélien installé préserve ce potentiel.
Pour `λ>0`, les minima de ce potentiel scalaire et les jets stationnaires
sont exactement ceux avec `χ=v`. Son Euler vaut `2λ(χ-v)δχ` et distingue
les coefficients. La positivité et un minimum scalaire prescrit laissent
donc encore une échelle libre ; ce résultat seul ne résout pas l'ambiguïté T09.

`P0EFTJanusT08QuarticDeformationFreedom4D.lean` construit `λ(χ-v)⁴` dans
la même classe T02 par développement polynomial explicite. Cette déformation
est préservée par le BRST abélien et sa valeur, sa première dérivée de Fréchet
et sa deuxième dérivée sont nulles à **tout jet vérifiant `χ=v`**.
Le témoin avec terme quadratique fixé est `Pλ=(χ-v)²+λ(χ-v)⁴`, lui aussi
construit dans T02 et préservé par le BRST abélien. Pour `λ≥0`, il est positif
ou nul et atteint zéro à `χ=v`. Sa Hessienne à cette référence est toujours
`2 δχ₁ δχ₂`. L'égalité `Pλ=c Pμ` sur les jets impose `c=1` et `λ=μ` :
la liberté quartique n'est donc plus une simple normalisation globale.
L'Euler T06 de la déformation quartique vaut `4λ(χ-v)³δχ` et distingue `λ`.

Hors référence, le coefficient scalaire de la Hessienne vaut
`2+12λ(χ-v)²` : la famille globale de Hessiennes peut distinguer les couplages.
Une seule valeur indépendante `R=Pλ` à déplacement `δ=χ-v≠0` suffit également :
`λ=(R-δ²)/δ⁴`. Ce sélecteur conditionnel explicite quelle donnée supplémentaire
est nécessaire dans cette famille ; il ne produit pas cette donnée physique.

Portée : les références sont des jets prescrits, pas des solutions Janus
construites. Il s'agit de potentiels et de Hessiennes locales, pas encore de
l'action intégrée ni de son opérateur de fluctuations réalisé. L'égalité des
Hessiennes à cette référence ne prétend pas leur égalité sur tous les champs,
et ne démontre pas la préservation de toutes les hypothèses T12. Les coordonnées
sont marquées ; distinguer les expressions d'Euler ne classifie pas les
équivalences par changements non linéaires de champs ou transformations BV.

## Changements de champ : ce que fixe réellement le terme cinétique

`P0EFTJanusT08PotentialFlattening.lean` construit
`fλ(x)=x√(1+λx²)` pour `λ≥0`. C'est une bijection strictement croissante, avec
`fλ(x)²=x²+λx⁴`. Le potentiel quartique isolé peut donc être aplati par ce
changement de variable. Sa dérivée vaut `(1+2λx²)/√(1+λx²)` : elle vaut `1`
à l'origine, mais son carré dépasse `1` si `λ>0` et `x≠0`. Le même changement
transforme alors le coefficient cinétique hors référence. L'identité du
potentiel ne suffit donc pas à comparer les densités complètes.

`P0EFTJanusT08KineticPointTransformationRigidity.lean` part d'un véritable
changement ponctuel `f`, de sa dérivée continue `g` et de la condition locale
`g²=1`. La continuité et les valeurs intermédiaires imposent un signe global ;
le théorème des accroissements finis donne `f(x)-v=g(v)(x-v)` si `f(v)=v`.
Seules l'identité et la réflexion autour de `v` subsistent. Aucune isométrie
globale n'est supposée pour obtenir ce résultat.

`P0EFTJanusT08KineticMarkedQuarticClassification.lean` classe ensuite les densités
`Lλ(q,w)=w²/2+(q-v)²+λ(q-v)⁴` dans une catégorie explicite. L'égalité admise est
`Lμ(f(q),f′(q)w)=Lλ(q,w)+b(q)w+C`, pour tous `q,w`, avec `f` de classe C1 et
`f(v)=v`. Les vitesses `0,1,-1` imposent `(f′)²=1` et `b=0` ; la référence
fixée impose `C=0`. Si `b` est la dérivée d'un courant de bord, ce courant est
constant. Le résultat de rigidité donne alors **équivalence si et seulement
si `λ=μ`**. Le potentiel est raccordé exactement à la fonctionnelle T02
précédente ; le terme cinétique scalaire est une donnée supplémentaire fournie.

Cette classification fixe aussi **l'échelle absolue de l'action**. En effet,
une identité séparée prouve
`Lμ(v+r(q-v),rw)=r² L(μr²)(q,w)`. Ainsi les coefficients positifs `1` et `1/4`
sont distincts à échelle fixée, mais reliés par `r=2` si l'on autorise aussi
un facteur global `4`. Le choix de cette échelle reste une question T09.
La classification ne couvre ni changements de variable indépendante, ni
transformations dépendant des dérivées, ni mélange des champs Janus, ni
quotient BV complet. Elle ne dérive pas le terme cinétique physique.

`P0EFTJanusT08ScaledQuarticClassification.lean` complète ce quotient : avec un
facteur global positif `a` autorisé, la comparaison impose exactement
`λ=aμ`. Réciproquement, le changement `q↦v+√a(q-v)` réalise cette équivalence.
Les courants de bord dépendant du champ et la constante additive ne changent
pas ce résultat. Il y a donc trois classes selon le signe du coefficient et,
dans la famille non négative, exactement **deux classes : `λ=0` et `λ>0`**.
Ce résultat porte sur la catégorie scalaire déclarée, pas sur tout le parent
Janus ni sur les transformations mélangeant ses champs.

## Raccord au secteur LL : mesure et potentiel

`P0EFTJanusT08CompositeMeasureScalarBridge` construit le raccord local
`χ=Φ(J)/ρ`, où `ρ≠0` est une densité de volume orientée fournie. Il prouve
l'invariance du rapport sous changement linéaire de coordonnées et
`δχ=(δΦ·ρ−Φ·δρ)/ρ²`. À volume fixé et jet inversible, les variations
matricielles réalisent toute variation scalaire ponctuelle ; au jet nul,
leur image tangentielle est nulle. Ceci ne construit pas des champs
auxiliaires globaux dont ces matrices seraient les Jacobiennes.

Pour un potentiel différentiable, le même module dérive la densité
`Φ·F+ρU(χ)` à énergie de flux `F` fixée :
`δL=(F+U′(χ))δΦ+(U(χ)−χU′(χ))δρ`.
Ce calcul distingue les variations indépendantes et composites ; il
n'identifie pas leurs équations globales ni leurs conditions de bord.

`P0EFTJanusT08GlobalLLPotentialVariation4D` déforme ensuite **l'action LL
globale existante**, sur son throat compact, par `U(χ)=λ(χ−v)^n`.
L'intégration est construite comme application linéaire continue pour toute
mesure de Borel finie ; la dérivation sous l'intégrale est donc démontrée.
La variation simultanée de `llMeasure` et `llField` donne
`Eχ=‖llField‖²+λn(χ−v)^(n−1)` et conserve `Efield=2χ·llField` pour cette
action sans cinétique différentiel. À `χ≠0`, `λ≠0`, `n≥2`, les deux
équations ponctuelles équivalent à `llField=0` et `χ=v`.
Cela n'est ni un lemme fondamental pour une mesure arbitraire, ni l'équation
du secteur LL complet avec son cinétique. Le théorème intégré porte sur
les potentiels puissances ; un potentiel C1 général reste à traiter.

### Champs auxiliaires globaux et raccord différentiel

`P0EFTJanusT08GlobalCompositeAuxiliaryVariation4D` définit trois véritables
champs scalaires lisses sur le throat. Leurs jets sont leurs dérivées
de variété, évaluées sur un triplet tangent fourni. La courbe globale
`φ+tψ` induit exactement `Jφ+tJψ` : la variation de la densité composite
et celle de `ΦF+ρU(Φ/ρ)` sont ainsi démontrées pour des variations de champs,
et non des matrices indépendantes. Le rapport est invariant sous changement
inversible du triplet tangent et transformation correspondante de `ρ`.
Une dilatation globale induit `δΦ=3Φ` ; les translations constantes des
auxiliaires préservent exactement la mesure.

Ce module ne fournit ni une base tangente globale, ni une mesure composite
partout non dégénérée, ni la réalisation de tout `δχ` prescrit. L'obstruction
globale ci-dessous exclut même la non-dégénérescence partout pour ces auxiliaires
réels ; aucune équivalence des deux problèmes variationnels n'est postulée. L'intégration
de la variation composite et son intégration par parties restent à établir.

`P0EFTJanusT08DifferentialLLPotentialVariation4D` ajoute les mêmes potentiels
puissances à **l'action différentielle existante**. Il sépare exactement
l'intégrale cinétique de l'action algébrique déformée et dérive les trois
variations indépendantes :

- mesure : `Eχ=‖llField‖²+U′(χ)` ;
- flux : le pairing faible existant, avec poids `1+‖llAuxMetric‖²`, est conservé ;
- métrique auxiliaire : le pairing avec l'énergie des dérivées du flux est conservé.

La stationnarité en flux est équivalente à l'équation faible différentielle
existante. La conclusion algébrique `llField=0` ne s'y transfère donc pas.
Ce raccord n'ajoute ni source physique, ni contraction lorentzienne intrinsèque,
ni opérateur fort de divergence ou flux de bord. Le cadre différentiel utilisé
reste celui du modèle positif à générateurs tangents fourni dans le dépôt.

### Obstruction compacte aux auxiliaires réels globaux

`P0EFTJanusT08CompactCompositeMeasureObstruction4D` prouve sur le throat
compact sans bord, avec un point de base fourni, que tout scalaire réel lisse
possède un point critique. La preuve passe par un maximum global et le
théorème de Fermat dans les véritables cartes du throat, dont le modèle est
sans bord. Appliquée au premier des trois auxiliaires, elle annule une
colonne du jet : **la mesure composite s'annule quelque part, quel que soit
le triplet tangent utilisé en ce point**.

Conséquence formelle : aucun triplet de scalaires réels globaux ne réalise
un `χ` partout non nul par `χ=det J/ρ`. En particulier, une référence constante
non nulle du modèle indépendant ne peut pas être identifiée ainsi à une
configuration composite globale régulière. Il ne s'agit plus d'un simple
lemme de réalisation manquant. Cela n'exclut pas les configurations
dégénérées, les auxiliaires définis par cartes avec recollement, ni des
auxiliaires à cible non réelle ; ces dernières possibilités restent à
construire et leur choix physique à justifier. Le résultat ne dit pas que
la variation du déterminant s'annule à tous les jets singuliers.

### Équations de Piola pondérées et constante locale

`P0EFTJanusT08CompositePiolaCoefficient4D` réutilise la véritable identité
différentielle de Piola T06 dans l'espace de coordonnées du throat. Pour une
application auxiliaire C2 régulière avec dérivée inverse locale et
différentiabilité des flux de cofacteurs fournies,
les vecteurs de cofacteurs `A_v=det(Dφ)·(Dφ)⁻¹v` sont de divergence nulle.
Le produit par un coefficient différentiable `q` donne
`div(q A_v)=det(Dφ)·dq((Dφ)⁻¹v)`.

Les trois équations dans les directions de la base auxiliaire équivalent
exactement à `dq=0`. Sur un ouvert connexe elles imposent `q=C`, sans fixer
`C`. L'application auxiliaire identité fournit un exemple régulier explicite
avec `q=1`. Une identité ponctuelle de produit sépare aussi le terme
`q·dψ(A_v)` en une divergence et le terme `−ψ·div(q A_v)`.

Le candidat physique est `q=‖llField‖²+U′(χ)`, identifié dans la variation
locale antérieure. Le raccord au pairing de cofacteurs est désormais prouvé
ci-dessous. L'intégration et le lemme fondamental sont désormais raccordés
pour des tests à support compact dans l'espace de coordonnées, comme indiqué
plus bas. Le résultat de Piola
ne suppose ni ne prouve encore l'équivalence à la stationnarité de l'action
composite intégrée. Il établit la classification différentielle locale du
système de Piola pondéré ; il ne sélectionne pas un parent indépendant.

### Raccord de la variation du déterminant au pairing de Piola

`P0EFTJanusT08CompositeDeterminantPiolaBridge4D` identifie le jet LL
coordonnée–auxiliaire à la transposée de la matrice de dérivée dans la base
T06. Son déterminant est celui de l'opérateur de dérivée. L'identité
polynomiale `δdet(J;JM)=det(J)·tr(M)` est démontrée même aux jets singuliers.
Avec la loi de dérivée inverse locale, elle donne ensuite exactement
`δΦ=Σ_a dψ_a(A_a)` pour les vecteurs de cofacteurs de Piola existants.

La courbe de vrais champs locaux `φ+tψ` induit effectivement les jets
affines utilisés. Pour `ρ≠0`, volume et énergie de flux fixés, la dérivée
de `ΦF+ρU(Φ/ρ)` est donc `(F+U′(χ))Σ_a dψ_a(A_a)`.
Le module prouve aussi, pour un coefficient différentiable `q`,
`qδΦ=Σ_a div(ψ_a q A_a)−Σ_a ψ_a div(q A_a)`.
Les divergences restent présentes : aucun terme de bord n'est supprimé.

Ce raccord ferme la lacune **locale** entre variation composite et calcul
de Piola. Le raccord intégré à support compact est donné ci-dessous ; les
bords généraux et le recollement restent à construire. Aucun choix de `C`
ni de parent physique n'est ajouté.

### Stokes à support compact et séparation des variations

**Validation finale de l'extension intégrée en attente du build T12 ; voir
le détail en fin de document.** Les résultats ci-dessous décrivent le code
écrit, sans anticiper la réussite de cette dernière compilation.

`P0EFTJanusT08CompositeCompactSupportStokes4D` travaille avec la véritable
mesure de Haar additive sur l'espace de coordonnées T06 du throat. Pour un
champ lisse `B` et un test lisse à support compact `ψ`, il démontre
`∫ψ div B=−∫dψ(B)`, avec toutes les intégrabilités nécessaires. Aucune
décroissance du champ `B` n'est imposée. Le lemme fondamental fait ensuite
passer de l'annulation des pairings contre tous ces tests à `div B=0`
**partout**, grâce à la continuité du résidu et au support plein de Haar.

Appliqué aux champs `B_a=q A_a`, le résultat donne l'identité intégrée réelle
`∫qδΦ=−Σ_a∫ψ_a div(q A_a)`. Les tests scalaires dans chaque direction de la
base sont réalisés par les véritables variations vectorielles `ψ e_a`.
L'annulation de cette première variation intégrée pour toute variation
auxiliaire lisse à support compact équivaut donc aux trois résidus nuls.
Sous les hypothèses de régularité et d'inverse de Piola, elle équivaut à
`dq=0`, laissant la constante déjà décrite sur les composantes connexes.

Portée exacte : les champs sont ici lisses sur l'espace euclidien de
coordonnées et les variations y sont à support compact. La non-dégénérescence
globale sur le throat compact n'est pas postulée. Il reste à construire une
action locale finie (sur domaine borné, ou relative à une référence), à prouver
que sa dérivée est l'intégrale de la variation locale pour le potentiel
retenu, puis à transporter et recoller ce calcul sur les cartes. L'intégrale
de la variation ne doit pas être confondue avec une dérivée d'une action
sur tout l'espace dont la densité de fond pourrait être non intégrable.

## Suite prioritaire : rejoindre le véritable secteur LL

1. **Relier les représentations du champ de mesure.**
   `MappingTorusSmoothGlobalFieldConfiguration4D` traite `llMeasure=χ` comme
   scalaire lisse indépendant. `LLBraneCompositeMeasureVariation` et
   `LLBraneCompositeMeasureFrechet` réalisent séparément la densité signée
   `Φ=det J` sur jets affines. Le rapport et les jets de champs globaux sont
   maintenant construits. La réalisation partout non dégénérée par trois
   scalaires réels globaux est exclue. Construire une réalisation locale
   recollée ou une autre cible auxiliaire, ou traiter explicitement les zéros,
   puis établir le raccord à l'intégration et les variations admissibles.
   Le choix physique de cette relation n'est
   pas une conséquence de leur existence séparée.
2. **Calculer l'effet réel des déformations LL.**
   `MappingTorusGlobalLLWorldvolume4D` contient la densité `χ‖llField‖²` et
   `MappingTorusGlobalLLVariation4D` dérive `Eχ=‖llField‖²`. Le cas puissance
   et son raccord au cinétique sont maintenant dérivés sur le vrai throat.
   Étendre à `U` général et construire l'action composite locale finie.
   Stokes et le lemme fondamental sont établis à support compact ; justifier
   maintenant la dérivée sous l'intégrale et le transport aux cartes.
   Distinguer soigneusement la
   condition indépendante `Eχ=0` de l'équation composite attendue
   `div(Eχ·cof Dφ)=0` : une constante d'intégration peut survivre localement.
   Réutiliser
   `ProgramPT05LLLocalDensityRelativeBridge4D` et `FullLLVariationalAPI4D`.
   Exiger la conservation des équations de l'action déjà sélectionnée serait
   circulaire si leur nécessité n'est pas justifiée indépendamment.
3. **Identifier les véritables données cinétiques et sources marquées.**
   Dans `MappingTorusDifferentialLLWeakEquation4D`, le cinétique agit sur
   **llField**, avec poids `1+‖llAuxMetric‖²`, et non sur **llMeasure**.
   Les modèles canoniques scalaires ci-dessus ne doivent pas lui être
   substitués. Extraire symboles, pairings, traces, sources et échelle
   observable, puis définir les équivalences physiques qui les transportent.
4. **Raccorder les symétries existantes à LL/T02/T06.**
   Assembler l'algèbre extérieure des fantômes, la covariance des densités
   mesurées et le BV métrique disponibles ci-dessous avec les vrais champs
   et dérivées LL. Prouver la variation de l'action déformée modulo courants,
   puis classifier les déformations admissibles et leurs obstructions.
   Livrable attendu : liste justifiée des couplages survivants, pas seulement
   invariance sous le BRST abélien actuel.
5. **Dériver un parent depuis une entrée indépendante.**
   Construire `S₀` avec origine documentée des termes, coefficients, sources
   et conditions de bord. Calculer sa variation bulk–bord et sa réduction,
   exacte ou avec erreur contrôlée. Comparer ensuite le résultat à Candidate A,
   sans utiliser cette cible pour fixer les données d'entrée. Les théorèmes
   de reconstruction T08 s'appliqueront si une véritable réponse indépendante
   et le paquet de résolvante régulier sont fournis ; ils ne les sélectionnent
   pas. Garder distinctes la normalisation T09 et les parties finies T10.

Appuis existants vérifiés pour cette dernière branche :
`ProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D` donne les
coordonnées invariantes de degré au plus quatre sur J² ;
`ProgramPT06NullLagrangiansBoundaryTermsTerminalCertificate4D` fournit le
quotient local par les densités nulles et courants relatifs ;
`ProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D` construit un complexe
jet scalaire BRST non trivial. Ces noms portent le préfixe `P0EFTJanus`.
Le troisième complexe reste abélien. D'autres briques existent déjà :
`MappingTorusExteriorDiffeomorphismGhostBRST4D` porte une véritable algèbre
extérieure et le secteur fantôme des difféomorphismes ;
`MappingTorusMeasuredDensityBRST4D` traite coefficient et mesure transportée ;
`MappingTorusGeneralLorentzMetricBVIntegratedMaster4D` intègre un BV métrique
ultralocal. Tous portent aussi le préfixe `P0EFTJanus`. Leur raccord au secteur
LL différentiel complet et à ses bords reste à construire. Il manque surtout
un `S₀` physique indépendant et le complexe couplé `s₀={S₀,-}` nécessaire au
calcul des déformations admissibles. Une base de densités et l'équation
maîtresse d'une Candidate A déjà fournie ne sélectionnent pas ses coefficients.

Les pistes bibliographiques des notes (BV–BFV, bimétrique, Weyl, action
spectrale, UV) restent des pistes à instruire ; aucun de leurs résultats n'est
importé comme hypothèse physique dans ce premier lot. T09, T10, T11 et le
calcul quantique des déterminants ne sont pas résolus par ces résultats.

## Validation ciblée

```powershell
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkBoundaryShearEquivalence JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkSpectralResponseSeparation
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMarkedParentEquivalence JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusScalarSpectralReconstruction JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCyclicMomentReconstruction JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLocalAuxiliaryReduction
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullSchurResponseReconstruction JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusTwoModeLocalReconstruction
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundaryTripleResolventSelectionBridge4D
python scripts/audit_janus_program_p.py
python -m pytest -q tests/test_janus_program_p.py
```

Les trente-deux modules sont importés par la façade Program P et enregistrés dans
l'audit d'intégrité. Aucune fermeture terminale n'est ajoutée.

Validation du premier prolongement (2026-09-19) : six modules compilés, dont les quatre
extensions (build du lot scalaire/local réussi, `8565/8565` jobs ; build du
module de moments réussi, `8558/8558`, dépendances comprises). Audit réussi
(`6/14` terminaux), `93` tests Program P réussis, `git diff --check` réussi.
Import conjoint des quatre extensions vérifié. Les six théorèmes principaux
audités par `#print axioms` ne dépendent que de `propext`, `Classical.choice`
et `Quot.sound` ; aucun axiome physique ajouté ni `sorry`.
La façade entière n'a pas été recompilée pendant le chantier T12 concurrent.

Validation du raccord résolvante/observable (2026-09-19) : build ciblé des
quatre nouveaux modules réussi (`8562/8562` jobs, dépendances comprises),
audit d'intégrité et `93` tests réussis ; contrôle du diff réussi.
Import conjoint vérifié ; les cinq principaux théorèmes du lot ne dépendent
que des trois axiomes logiques standards cités ci-dessus.

Validation de l'extension non bornée (2026-09-19) : quatre nouveaux modules
compilés, build ciblé du bridge et de ses dépendances réussi (`8929/8929`),
audit d'intégrité réussi (`6/14` terminaux), `93` tests réussis. Les avertissements
rejoués par Lake proviennent des dépendances existantes, pas des nouveaux modules.

Validation des contraintes de sélection (2026-09-19) : les trois modules
`P0EFTJanusT08LocalGluingSelectionFreedom`, `P0EFTJanusT08RobinSelectionFreedom4D`
et `P0EFTJanusT08InvariantDeformationFreedom4D` compilent sans avertissement.
Compilations ciblées sérialisées avec `lake env lean --memory=4096 --threads=1`,
sans relancer le build global T12 concurrent. Import conjoint réussi et neuf
théorèmes principaux contrôlés par `#print axioms` : seulement `propext`,
`Classical.choice`, `Quot.sound`. Audit d'intégrité réussi (`6/14` terminaux),
`93` tests Program P réussis et `git diff --check` réussi. Aucun `sorry` ni
axiome physique ajouté. Ce lot précise les contraintes insuffisantes ; il
ne ferme pas T08.

Validation des potentiels centrés (2026-09-19) : les trois modules
`P0EFTJanusT08ValuePotentialEuler4D`, `P0EFTJanusT08StableMassDeformation4D`
et `P0EFTJanusT08QuarticDeformationFreedom4D` compilent sans avertissement,
avec import conjoint réussi. Compilations ciblées à un thread, plafond 4 Go,
sans relancer la façade complète pendant le chantier T12. Les douze théorèmes
principaux contrôlés par `#print axioms` n'utilisent que les trois axiomes
logiques standards. Audit d'intégrité réussi (`6/14` terminaux), `93` tests
Program P réussis et contrôle du diff réussi. Aucun `sorry` ni axiome physique
ajouté. La liberté quartique à données locales fixées est établie ; la
sélection physique de T08 reste ouverte.

Validation des changements de champ (2026-09-19) : les trois modules
`P0EFTJanusT08PotentialFlattening`, `P0EFTJanusT08KineticPointTransformationRigidity`
et `P0EFTJanusT08KineticMarkedQuarticClassification` compilent sans avertissement
(un thread, plafond 4 Go). Import conjoint réussi ; les onze théorèmes
principaux vérifiés par `#print axioms` n'utilisent que `propext`,
`Classical.choice`, `Quot.sound`. Audit d'intégrité réussi (`6/14` terminaux),
`93` tests Program P réussis et contrôle du diff réussi. Aucun `sorry` ni
axiome physique ajouté ; aucune recompilation de la façade globale.

Validation du quotient avec échelle libre (2026-09-19) : extension de
`P0EFTJanusT08KineticPointTransformationRigidity` et nouveau module
`P0EFTJanusT08ScaledQuarticClassification` compilés sans avertissement ; import
et six contrôles `#print axioms` réussis (seulement les axiomes logiques
standards). Audit réussi (`6/14` terminaux), `93` tests Program P et contrôle
du diff réussis. La revue du vrai secteur LL précise désormais la priorité
physique dans la feuille de route ci-dessus. T08 reste ouvert.

Validation du raccord mesure/action LL (2026-09-19) : les deux modules
`P0EFTJanusT08CompositeMeasureScalarBridge` et
`P0EFTJanusT08GlobalLLPotentialVariation4D` compilent sans avertissement
(un thread, plafond 4 Go), ainsi que leur import conjoint. Sept théorèmes
contrôlés par `#print axioms` ne dépendent que de `propext`,
`Classical.choice`, `Quot.sound`. Audit réussi (`6/14` terminaux), `93` tests
Program P réussis et contrôle du diff réussi. Aucun `sorry` ni axiome
physique ajouté ; façade globale non recompilée pendant le chantier T12.

Validation des champs auxiliaires globaux et du raccord différentiel
(2026-09-20) : `P0EFTJanusT08GlobalCompositeAuxiliaryVariation4D` et
`P0EFTJanusT08DifferentialLLPotentialVariation4D` compilent sans avertissement
(un thread, plafond 4 Go). Import conjoint réussi ; huit théorèmes contrôlés
par `#print axioms` n'utilisent que les trois axiomes logiques standards.
Audit réussi (`6/14` terminaux), `93` tests réussis et contrôle du diff réussi.
Aucun `sorry` ni axiome physique ajouté. Les sources T12 ne sont pas modifiées
par ce lot ; aucune recompilation de la façade complète.

Validation de l'obstruction compacte (2026-09-20) : le nouveau module
`P0EFTJanusT08CompactCompositeMeasureObstruction4D` compile sans avertissement
(un thread, plafond 4 Go). Import conjoint avec le raccord différentiel réussi.
Ses quatre théorèmes n'utilisent que `propext`, `Classical.choice`, `Quot.sound`
d'après `#print axioms`. Audit réussi (`6/14` terminaux), `93` tests réussis,
contrôle du diff réussi. Aucun axiome physique ajouté ; sources T12 inchangées
par ce lot. Cette obstruction ne constitue pas une fermeture de T08.

Validation des équations locales de Piola pondérées (2026-09-20) :
`P0EFTJanusT08CompositePiolaCoefficient4D` compile sans avertissement,
avec un thread et plafond de 4 Go, y compris le cas explicite `q=1` sur
l'application auxiliaire identité. Audit réussi (`6/14` terminaux), `93` tests
Program P réussis et contrôle du diff réussi. Le nouveau fichier ne contient
ni `sorry`, ni `admit`, ni déclaration d'axiome. Aucun contrôle supplémentaire
par `#print axioms` ni rebuild de la façade entière dans ce lot. Les sources
T12 n'ont pas été modifiées par ce travail.

Validation du raccord déterminant–Piola (2026-09-20) : le nouveau module
`P0EFTJanusT08CompositeDeterminantPiolaBridge4D` compile sans avertissement,
à un thread et plafond de 4 Go. Sept contrôles `#print axioms`, incluant trois
théorèmes du module de Piola précédent, ne donnent que `propext`,
`Classical.choice`, `Quot.sound`. Audit réussi (`6/14` terminaux), `93` tests
Program P réussis, contrôle du diff réussi. Les vérifications finales ont
réussi après la régénération de dépendances par le chantier concurrent ;
aucune source T12 modifiée par ce lot et aucune recompilation de la façade
entière. T08 reste ouvert au niveau intégré et à la sélection physique.

État de validation du lot Stokes compact (2026-09-20) : les théorèmes de
Stokes scalaire et de séparation des tests ont compilé dans une première
version du nouveau module. L'extension à la première variation composite
intégrée et son équivalence à `dq=0` est écrite, mais sa **compilation finale
reste à confirmer**. Les relances ont été arrêtées au chargement des imports
par des `.olean` successivement absents pendant le build T12 concurrent.
Une commande attend la fin de ce build avant de recompiler le module puis
le contrôle `.b/T08CompactSupportStokesCheck.lean` (cinq `#print axioms`).
Ces contrôles finaux ne sont donc pas encore déclarés réussis. Audit Python
réussi (`6/14` terminaux), `93` tests réussis et contrôle du diff réussi.
Aucune source T12 modifiée. Ne pas compter cette extension intégrée comme
entièrement validée tant que la compilation finale n'a pas été confirmée.
