if [ "$HOSTNAME" = "s-1vcpu-1gb-lon1-01" ]; then
	cd /home/hugo/cours-l3/
	# python3 tools/autocompress.py
else
	cd /Users/hugos29/Documents/ecole/ens1/
	# ipython tools/autocompile.py

  cp profon/pieuvre/docs/presentation.pdf profon/pieuvre-presentation.pdf
  cp profon/pieuvre/docs/report.pdf profon/pieuvre-report.pdf
fi

if [ "$HOSTNAME" = "s-1vcpu-1gb-lon1-01" ]; then
  cp all-l3.pdf ../web/public/data/ens1/all.pdf

  # ==========
  # SEMESTRE 2
  # ==========

  cp algo2/main.pdf ../web/public/data/ens1/algo2.pdf
  cp algo2/td.pdf ../web/public/data/ens1/algo2-td.pdf
  cp algo2/dm1/main.pdf ../web/public/data/ens1/algo2-dm1.pdf
  cp algo2/dm2.pdf ../web/public/data/ens1/algo2-dm2.pdf

  cp log/main.pdf ../web/public/data/ens1/logique.pdf
  cp log/chap00.pdf ../web/public/data/ens1/logique-chap00.pdf
  cp log/chap01.pdf ../web/public/data/ens1/logique-chap01.pdf
  cp log/chap02.pdf ../web/public/data/ens1/logique-chap02.pdf
  cp log/chap03.pdf ../web/public/data/ens1/logique-chap03.pdf
  cp log/chap04.pdf ../web/public/data/ens1/logique-chap04.pdf
  cp log/chap05.pdf ../web/public/data/ens1/logique-chap05.pdf

  cp log/dm1.pdf ../web/public/data/ens1/logique-dm1.pdf
  cp log/dm2.pdf ../web/public/data/ens1/logique-dm2.pdf
  cp log/td.pdf ../web/public/data/ens1/logique-td.pdf
  cp log/revisions-a4.pdf ../web/public/data/ens1/logique-revisions-a4.pdf
  cp log/revisions-long.pdf ../web/public/data/ens1/logique-revisions-long.pdf

  # cp stage/rapport/main.pdf ../web/public/data/ens1/stage-report.pdf
  # cp stage/presentation/main.pdf ../web/public/data/ens1/stage-presentation.pdf

  cp proba/td.pdf ../web/public/data/ens1/proba-td.pdf
  cp proba/dm1.pdf ../web/public/data/ens1/proba-dm1.pdf
  cp proba/revisions.pdf ../web/public/data/ens1/proba-revisions.pdf

  cp profon/main.pdf ../web/public/data/ens1/profon.pdf
  cp profon/small-docs/trad.pdf ../web/public/data/ens1/profon-traduction-cps.pdf
  cp profon/small-docs/opti.pdf ../web/public/data/ens1/profon-optimisation-cps.pdf
  cp profon/td.pdf ../web/public/data/ens1/profon-td.pdf
  cp profon/cic.pdf ../web/public/data/ens1/profon-cic.pdf
  cp profon/chap00.pdf ../web/public/data/ens1/profon-chap00.pdf
  cp profon/chap01.pdf ../web/public/data/ens1/profon-chap01.pdf
  cp profon/chap02.pdf ../web/public/data/ens1/profon-chap02.pdf
  cp profon/chap03.pdf ../web/public/data/ens1/profon-chap03.pdf
  cp profon/chap04.pdf ../web/public/data/ens1/profon-chap04.pdf
  cp profon/chap05.pdf ../web/public/data/ens1/profon-chap05.pdf
  cp profon/pieuvre-presentation.pdf ../web/public/data/ens1/profon-presentation.pdf
  cp profon/pieuvre-report.pdf ../web/public/data/ens1/profon-report.pdf

  # ==========
  # SEMESTRE 1
  # ==========

  cp algo1/main.pdf ../web/public/data/ens1/algo1.pdf

  cp thprog/main.pdf ../web/public/data/ens1/thprog.pdf

  cp thprog/chap00/chap00.pdf ../web/public/data/ens1/thprog-chap00.pdf
  cp thprog/chap01/chap01.pdf ../web/public/data/ens1/thprog-chap01.pdf
  cp thprog/chap02/chap02.pdf ../web/public/data/ens1/thprog-chap02.pdf
  cp thprog/chap03/chap03.pdf ../web/public/data/ens1/thprog-chap03.pdf
  cp thprog/chap04/chap04.pdf ../web/public/data/ens1/thprog-chap04.pdf
  cp thprog/chap05/chap05.pdf ../web/public/data/ens1/thprog-chap05.pdf
  cp thprog/chap06/chap06.pdf ../web/public/data/ens1/thprog-chap06.pdf
  cp thprog/chap07/chap07.pdf ../web/public/data/ens1/thprog-chap07.pdf
  cp thprog/chap08/chap08.pdf ../web/public/data/ens1/thprog-chap08.pdf
  cp thprog/chap09/chap09.pdf ../web/public/data/ens1/thprog-chap09.pdf
  cp thprog/chap10/chap10.pdf ../web/public/data/ens1/thprog-chap10.pdf

  cp integration/main.pdf ../web/public/data/ens1/integ.pdf
  cp integration/dm2/main.pdf ../web/public/data/ens1/integ-dm2.pdf

  cp category-theory/dm1/main.pdf ../web/public/data/ens1/categ-dm1.pdf
  cp category-theory/dm2/main.pdf ../web/public/data/ens1/categ-dm2.pdf
  cp category-theory/dm3/main.pdf ../web/public/data/ens1/categ-dm3.pdf

  cp fdi/dm1/main.pdf ../web/public/data/ens1/fdi-dm1.pdf
  cp fdi/dm2/main.pdf ../web/public/data/ens1/fdi-dm2.pdf
  cp fdi/dm3/main.pdf ../web/public/data/ens1/fdi-dm3.pdf
  cp fdi/dm4/main.pdf ../web/public/data/ens1/fdi-dm4.pdf
  cp fdi/dm5/main.pdf ../web/public/data/ens1/fdi-dm5.pdf

  cp algebre1/dm1/main.pdf ../web/public/data/ens1/algebre1-dm1.pdf
  cp algebre1/dm2/main.pdf ../web/public/data/ens1/algebre1-dm2.pdf
  cp algebre1/td/main.pdf ../web/public/data/ens1/algebre1-td.pdf
  cp algebre1/td/td01.pdf ../web/public/data/ens1/algebre1-td1.pdf
  cp algebre1/td/td02.pdf ../web/public/data/ens1/algebre1-td2.pdf
  cp algebre1/td/td03.pdf ../web/public/data/ens1/algebre1-td3.pdf
  cp algebre1/td/td04.pdf ../web/public/data/ens1/algebre1-td4.pdf
  cp algebre1/td/td05.pdf ../web/public/data/ens1/algebre1-td5.pdf
  cp algebre1/td/td06.pdf ../web/public/data/ens1/algebre1-td6.pdf
  cp algebre1/td/td07.pdf ../web/public/data/ens1/algebre1-td7.pdf
  cp algebre1/td/td08.pdf ../web/public/data/ens1/algebre1-td8.pdf
  cp algebre1/td/td09.pdf ../web/public/data/ens1/algebre1-td9.pdf
  cp algebre1/td/td10.pdf ../web/public/data/ens1/algebre1-td10.pdf
  cp algebre1/td/td11.pdf ../web/public/data/ens1/algebre1-td11.pdf
  cp algebre1/td/td12.pdf ../web/public/data/ens1/algebre1-td12.pdf
fi
