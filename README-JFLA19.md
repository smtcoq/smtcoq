# README for the submission to the [JFLA conference 2019](https://dpt-info.u-strasbg.fr/~magaud/JFLA2019)

This README is related to the submission of an article to the [JFLA conference 2019](https://dpt-info.u-strasbg.fr/~magaud/JFLA2019). It is intentionaly written in French.


## Installation

Il faut utiliser l'installation à partir des sources décrite dans [ce fichier](https://github.com/smtcoq/smtcoq/blob/master/INSTALL.md).

Une nouvelle release, ainsi que la mise à jour du paquet opam, sont prévues courant novembre.


## Utilisation

Le fichier [examples/Example.v](https://github.com/smtcoq/smtcoq/blob/master/examples/Example.v) donne un aperçu des possibilités offertes par SMTCoq. La fin du fichier présente des exemples sur les éléments présentés dans la soumission.


## Description des éléments présentés dans la soumission
### Ajout de lemmes quantifiés

La fin du fichier [examples/Example.v](https://github.com/smtcoq/smtcoq/blob/master/examples/Example.v) (lignes 154 à fin) présente différentes utilisations décrites en introduction et dans la section 3.5.

Côté Coq:

- L'extension du vérificateur (§ 3.3) est définie dans le fichier [src/Trace.v](https://github.com/smtcoq/smtcoq/blob/master/src/Trace.v). Notamment, la nouvelle règle `ForallInst` apparaît à la ligne 344. Son fonctionnement est donné dans le fichier [src/spl/Assumptions.v](https://github.com/smtcoq/smtcoq/blob/master/src/spl/Assumptions.v).

- Le cas d'application à la tactique `verit` (§ 3.4.3) est définie dans le fichier [src/SMTCoq.v](https://github.com/smtcoq/smtcoq/blob/master/src/SMTCoq.v), avec la définition de la tactique `vauto` permettant la preuve automatique des instanciations.

Côté OCaml:

- L'extension du vérificateur (§ 3.3) est définie dans le fichier [src/trace/smtCertif.ml](https://github.com/smtcoq/smtcoq/blob/master/src/trace/smtCertif.ml). Notamment, la nouvelle règle `ForallInst` apparaît à la ligne 113. Son trairement est donné dans le fichier [src/trace/smtTrace.ml](https://github.com/smtcoq/smtcoq/blob/master/src/trace/smtTrace.ml), ligne 423.

- Le préprocesseur pour la règle forall_inst de veriT (§ 3.4.2 et 3.4.3) est défini dans le fichier [src/verit/veritSyntax.ml](https://github.com/smtcoq/smtcoq/blob/master/src/verit/veritSyntax.ml), lignes 213 et suivantes.


### Traductions entre représentations des données

Le fichier [examples/Example.v](https://github.com/smtcoq/smtcoq/blob/master/examples/Example.v) (lignes 71 à 150) présente différentes utilisations décrites dans la section 4.

L'implantation de ces tactiques est donnée par le fichier documenté [src/Conversion_tactics.v](https://github.com/smtcoq/smtcoq/blob/master/src/Conversion_tactics.v).
