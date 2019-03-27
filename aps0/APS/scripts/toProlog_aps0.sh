#! /bin/bash

for i in `ls ../Samples/aps0/*.aps`
do
	echo $i " -> "
	../toProlog $i
	echo -e
done
