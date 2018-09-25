ROOTDIR=$(CURDIR)/..
TRACEFORMATDIR=$(ROOTDIR)/src/cpp/pb
MLDIR=$(ROOTDIR)/src/ocaml/piqi

# I don't think we need to compile all piqi files actually, only frame.piqi
PIQIFILE=frame.piqi
OTHERPIQIFILES=$(filter-out $(PIQIFILE), $(wildcard *.piqi))
PROTOFILES=$(addsuffix .proto, $(PIQIFILES))
MLFILES=$(addsuffix _piqi.ml, $(basename $(PIQIFILE)))
MLEXTFILES=$(addsuffix _piqi_ext.ml, $(basename $(PIQIFILE)))
PROTOCFILES=$(addsuffix .piqi.pb.cc, $(basename $(PIQIFILE)))
PROTOHFILES=$(addsuffix .piqi.pb.h, $(basename $(PIQIFILE)))

PIQI=piqi
PIQIC=piqic
PROTOC=$(ROOTDIR)/protobuf/src/protoc

PIQIFLAGS = --pp

# Install direclty, otherwise depending components fail to build, because
# BAP builds everything in one go.
all: install

# Empty target to be compatible with the BAP build system
tags:

$(PIQIFILE) : $(OTHERPIQIFILES)
	touch $@

%.piqi.proto : %.piqi
	$(PIQI) to-proto $<

%.piqi.pb.cc %.piqi.pb.hh : %.piqi.proto
	$(PROTOC) $< --cpp_out=.

#%_piqi.ml : %.piqi
#	piqic ocaml $(PIQIFLAGS) $<

%_piqi.ml %_piqi_ext.ml : %.piqi
	$(PIQIC) ocaml-ext $(PIQIFLAGS) $<

clean:
	rm -f $(PROTOFILES) $(MLFILES) $(MLEXTFILES) $(PROTOCFILES) $(PROTOHFILES)

.PHONY: install-pb install-piqi install
install-pb: $(PROTOCFILES) $(PROTOHFILES)
	mkdir -p $(TRACEFORMATDIR)
	cp $^ $(TRACEFORMATDIR)

install-piqi: $(MLFILES) $(MLEXTFILES)
	mkdir -p $(MLDIR)
	cp $^ $(MLDIR)

install: install-pb install-piqi
