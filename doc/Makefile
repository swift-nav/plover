index.html: index.rst template.txt
	rst2html.py index.rst index.html --math-output=MathJax --template=template.txt --stylesheet=stylesheets/normalize.css,stylesheets/pygment_trac.css,stylesheets/style.css --no-toc-backlinks --section-numbering

.PHONY: clean
clean:
	-rm index.html

CURR_BRANCH := $(shell git rev-parse --abbrev-ref HEAD)
GIT_TOP := $(shell git rev-parse --show-toplevel)
TMP_DOC_DIR := $(shell mktemp -d /tmp/gh_pages.XXXXXX)

.PHONY: publish gh-pages
gh-pages: index.html
	-git branch -D gh-pages
	cd $(GIT_TOP)
	cp -r $(GIT_TOP)/doc/* $(TMP_DOC_DIR)/
	git checkout --orphan gh-pages
	cp -r $(TMP_DOC_DIR)/* $(GIT_TOP)/
	git add $(shell ls $(TMP_DOC_DIR))
	git commit -m "auto published"
	git checkout $(CURR_BRANCH)

publish: gh-pages
	git push origin gh-pages --force
