index.html: index.rst template.txt
	rst2html.py index.rst index.html --math-output=MathJax --template=template.txt --stylesheet=stylesheets/normalize.css,stylesheets/pygment_trac.css,stylesheets/style.css --no-toc-backlinks --section-numbering

.PHONY: clean
clean:
	-rm index.html
