# ``The contents of this file are subject to the Erlang Public License,
# Version 1.1, (the "License"); you may not use this file except in
# compliance with the License. You should have received a copy of the
# Erlang Public License along with this software. If not, it can be
# retrieved via the world wide web at http://www.erlang.org/.
# 
# Software distributed under the License is distributed on an "AS IS"
# basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
# the License for the specific language governing rights and limitations
# under the License.
# 
# The Initial Developer of the Original Code is Ericsson Utvecklings AB.
# Portions created by Ericsson are Copyright 1999, Ericsson Utvecklings
# AB. All Rights Reserved.''
# 
#     $Id$
#
include $(ERL_TOP)/make/target.mk
include $(ERL_TOP)/make/$(TARGET)/otp.mk

# ----------------------------------------------------
# Application version
# ----------------------------------------------------
include ../../vsn.mk
VSN=$(KERNEL_VSN)
APPLICATION=kernel

# ----------------------------------------------------
# Release directory specification
# ----------------------------------------------------
RELSYSDIR = $(RELEASE_PATH)/lib/$(APPLICATION)-$(VSN)

# ----------------------------------------------------
# Target Specs
# ----------------------------------------------------
XML_APPLICATION_FILES = ref_man.xml
XML_REF3_FILES = application.xml \
	auth.xml \
	code.xml \
	disk_log.xml \
	erl_boot_server.xml \
	erl_ddll.xml \
	erl_prim_loader_stub.xml \
	erlang_stub.xml \
	error_handler.xml \
	error_logger.xml \
	file.xml \
	gen_tcp.xml \
	gen_udp.xml \
	gen_sctp.xml \
	global.xml \
	global_group.xml \
	heart.xml \
	inet.xml \
	inet_res.xml \
	init_stub.xml \
	net_adm.xml \
	net_kernel.xml \
	os.xml \
	packages.xml \
	pg2.xml \
	rpc.xml \
	seq_trace.xml \
	wrap_log_reader.xml \
	user.xml \
	zlib_stub.xml

XML_REF4_FILES = app.xml config.xml

XML_REF6_FILES = kernel_app.xml

XML_PART_FILES = part_notes.xml part_notes_history.xml
XML_CHAPTER_FILES = notes.xml notes_history.xml

BOOK_FILES = book.xml

XML_FILES = \
	$(BOOK_FILES) $(XML_CHAPTER_FILES) \
	$(XML_PART_FILES) $(XML_REF3_FILES) $(XML_REF4_FILES) \
	 $(XML_REF6_FILES) $(XML_APPLICATION_FILES)

# ----------------------------------------------------

HTML_FILES = $(XML_APPLICATION_FILES:%.xml=$(HTMLDIR)/%.html) \
	$(XML_PART_FILES:%.xml=$(HTMLDIR)/%.html)

INFO_FILE = ../../info

MAN3_FILES = $(XML_REF3_FILES:%.xml=$(MAN3DIR)/%.3)
MAN4_FILES = $(XML_REF4_FILES:%.xml=$(MAN4DIR)/%.4)
MAN6_FILES = $(XML_REF6_FILES:%_app.xml=$(MAN6DIR)/%.6)

HTML_REF_MAN_FILE = $(HTMLDIR)/index.html

TOP_PDF_FILE = $(PDFDIR)/$(APPLICATION)-$(VSN).pdf


# ----------------------------------------------------
# FLAGS 
# ----------------------------------------------------
XML_FLAGS += 

# ----------------------------------------------------
# Targets
# ----------------------------------------------------
$(HTMLDIR)/%.gif: %.gif
	$(INSTALL_DATA) $< $@

docs: pdf html man

$(TOP_PDF_FILE): $(XML_FILES)

pdf: $(TOP_PDF_FILE)

html: gifs $(HTML_REF_MAN_FILE)

man: $(MAN3_FILES) $(MAN4_FILES) $(MAN6_FILES)

gifs: $(GIF_FILES:%=$(HTMLDIR)/%)
debug opt: 

clean clean_docs:
	rm -rf $(HTMLDIR)/*
	rm -f $(MAN3DIR)/*
	rm -f $(MAN4DIR)/*
	rm -f $(MAN6DIR)/*
	rm -f $(TOP_PDF_FILE) $(TOP_PDF_FILE:%.pdf=%.fo)
	rm -f errs core *~ 

# ----------------------------------------------------
# Release Target
# ---------------------------------------------------- 
include $(ERL_TOP)/make/otp_release_targets.mk

release_docs_spec: docs
	$(INSTALL_DIR) $(RELSYSDIR)/doc/pdf
	$(INSTALL_DATA) $(TOP_PDF_FILE) $(RELSYSDIR)/doc/pdf
	$(INSTALL_DIR) $(RELSYSDIR)/doc/html
	$(INSTALL_DATA) $(HTMLDIR)/* \
		$(RELSYSDIR)/doc/html
	$(INSTALL_DATA) $(INFO_FILE) $(RELSYSDIR)
	$(INSTALL_DIR) $(RELEASE_PATH)/man/man3
	$(INSTALL_DATA) $(MAN3DIR)/* $(RELEASE_PATH)/man/man3
	$(INSTALL_DIR) $(RELEASE_PATH)/man/man4
	$(INSTALL_DATA) $(MAN4_FILES) $(RELEASE_PATH)/man/man4
	$(INSTALL_DIR) $(RELEASE_PATH)/man/man6
	$(INSTALL_DATA) $(MAN6_FILES) $(RELEASE_PATH)/man/man6

release_spec:

