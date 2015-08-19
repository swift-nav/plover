PAGES := index.html reference.html guide.html tutorials.html

index.html: index.rst template.txt
	rst2html.py $< $@ --math-output=MathJax --template=template.txt --stylesheet=stylesheets/normalize.css,stylesheets/pygment_trac.css,stylesheets/style.css --no-toc-backlinks --section-numbering

%.html: %.rst template.txt
	rst2html.py $< $@ --math-output=MathJax --template=template.txt --stylesheet=stylesheets/normalize.css,stylesheets/pygment_trac.css,stylesheets/style.css,stylesheets/nonindex.css --no-toc-backlinks --section-numbering

.PHONY: clean
clean:
	-rm -f $(PAGES)

.PHONY: pages
pages: $(PAGES)

CURR_BRANCH := $(shell git rev-parse --abbrev-ref HEAD)
GIT_TOP := $(shell git rev-parse --show-toplevel)
TMP_DOC_DIR := $(shell mktemp -d /tmp/gh_pages.XXXXXX)

.PHONY: publish gh-pages
gh-pages: $(PAGES)
	@echo This will cause some noise
	git stash
	-git branch -D gh-pages
	cp -r $(GIT_TOP)/doc/* $(TMP_DOC_DIR)/
	cd $(GIT_TOP) && git checkout --orphan gh-pages
	cd $(GIT_TOP) && git rm --cached -rf . && (mkdir $(GIT_TOP)/doc || true)
	cd $(GIT_TOP) && git commit --allow-empty -m "re-init"
	cd $(GIT_TOP) && cp -r $(TMP_DOC_DIR)/* $(GIT_TOP)/
	@echo Adding: `ls $(TMP_DOC_DIR)`
	cd $(GIT_TOP) && git add `ls $(TMP_DOC_DIR)`
	cd $(GIT_TOP) && git commit -m "auto published"
	cd $(GIT_TOP) && git checkout -f $(CURR_BRANCH)
	-git stash pop
	@echo
	@echo Success
	@echo Use \'make publish\' to submit to github.

publish: gh-pages
	@echo Publishing...
	git push origin gh-pages --force
	@echo Published.
