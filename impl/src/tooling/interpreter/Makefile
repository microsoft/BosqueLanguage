CCFLAGS = -g -BSQ_DEBUG_BUILD -std=c++17
LINKERFLAG = -lm

SOURCE_H = $(wildcard *.h) $(wildcard assembly/*.h) $(wildcard core/*.h) $(wildcard runtime/*.h)
SOURCE_CPP = $(wildcard *.cpp) $(wildcard assembly/*.cpp)$(wildcard core/*.cpp) $(wildcard runtime/*.cpp)
OUTPUTDIR = output

INCLUDE_WIN = --include-directory="C:\Program Files\boost_1_76_0" --library-directory="C:\Program Files\boost_1_76_0\stage\lib"
INCLUDE_POSIX = 

empty:
	@echo "Must specify a target"

icpp: $(SOURCE_H) $(SOURCE_CPP) $(OUTPUTDIR)
	@echo "Building icpp"
	clang++ $(CCFLAGS) $(INCLUDE_POSIX) -o $(BINS)/icpp $(SOURCE_CPP)

icpp.exe: $(SOURCE_H) $(SOURCE_CPP) $(OUTPUTDIR)
	@echo "Building icpp.exe"
	clang.exe $(CCFLAGS) $(INCLUDE_WIN) -o $(BINS)\icpp.exe $(SOURCE_CPP)

$(OUTPUTDIR):
    mkdir $(OUTPUTDIR)

clean:
    @echo "Cleaning up..."
    rm  $(OUTPUTDIR)/*
