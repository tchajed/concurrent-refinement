SOURCE := PFun.v Prog.v Automation.v Threads.v

VO_FILES := $(SOURCE:.v=.vo)

all: $(VO_FILES)

Prog.vo: PFun.vo

Threads.vo: Prog.vo Automation.vo

%.vo: %.v
	coqc $<
