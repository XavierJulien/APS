#!/usr/bin/env bash
toProlog $1 | swipl -s Typage/typeChecker.pl -g main_stdin
