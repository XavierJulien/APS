#!/usr/bin/env bash
export PATH=$PATH:~/Master/APS
toProlog $1 | swipl -s Typage/typeChecker.pl -g main_stdin
