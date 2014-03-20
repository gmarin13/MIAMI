
include miami.config
MIAMI_TARGET ?= $(MIAMI_HOME)

all:
	cd src && $(MAKE) $@ MIAMI_KIT=1
ifneq ($(MIAMI_TARGET),$(MIAMI_HOME))
	@echo "Installing out of tree"
	mkdir -p $(MIAMI_TARGET)
	@echo "Copying documentation"
	@cp -r doc README LICENSE ACKNOWLEDGEMENTS $(MIAMI_TARGET)
	@echo "Copying utilities"
	@cp -r Scripts share ExtractSourceFiles $(MIAMI_TARGET)
	@echo "Copying Viewer"
	@cp -r Viewer $(MIAMI_TARGET)
else
	@echo "Installing in place"
endif

clean cleanall info:
	cd src && $(MAKE) $@ MIAMI_KIT=1
