Ces fichiers sont là pour vérifier que tout fonctionne avant le TP.

Si vous avez un problème, demandez-nous.

Pour vérifier que tout marche, vous devriez pouvoir taper les commandes
suivantes dans votre terminal en étant dans ce dossier :
```
make # (compile le code OCaml)
make run # (lance le code)
make clean # (nettoie des fichiers auxiliaires)
```

# Linux :

Il faudra sûrement `dune` (et d'autres trucs plus logiques).
Pour l'installer, il suffit de taper :
```
sudo apt update
sudo apt install ocaml-dune make ocaml
```

# Windows :

### Idée numéro 1:
Taper 'fonctionalités' dans la barre de recherche et lancer "Ajouter des
fonctionalités Windows". Chercher et cocher "Sous-système Windows pour
Linux" (et rédemarrer). Aller sur le Microsoft Store et chercher Ubuntu
20.04 (ou une autre version). Ensuite ouvrer un terminal (en tapant
"Ubuntu" dans l'onglet de recherche en bas à gauche par exemple) et se
rapporter au cas précédent.

*Note :* Taper `explorer.exe .` dans le terminal linux pour ouvrir les
gestionnaires de fichiers à un endroit que le terminal peut voir.

*Note 2 :* si vous avez des `Permission denied` en tapant `make`, essayez
`sudo make` (c'est moche)

### Idée numéro 2:
Installer `Cygwin`. Pour choisir les packages à installer, trier les par
categories. Prendre toute la catégorie `OCaml`. Dans la catégorie `Devel`,
prendre `gcc-core`, `make`, `ocaml-dune`.

Vous pouvez ensuite ouvrir une invite de commande `cygwin`. Taper `cygpath -w ~`
pour savoir où sont stocker les fichiers pour y accéder via Windows.

### Idée numéro 3:
Utiliser l'installateur Diskuv OCaml pour Windows.
