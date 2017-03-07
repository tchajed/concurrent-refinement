SOURCE := Prog.v Threads.v

VO_FILES := $(SOURCE:.v=.vo)

all: $(VO_FILES)


%.vo: %.v
	coqc $<
