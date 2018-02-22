# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = sphinx-build
SPHINXPROJ    = RedPRL
SOURCEDIR     = src
BUILDDIR      = build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) $(SPHINXOPTS) $(O) -M help "$(SOURCEDIR)" "$(BUILDDIR)"

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) $(SPHINXOPTS) $(O) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)"
