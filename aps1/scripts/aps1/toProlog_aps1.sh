#! /bin/bash

for i in `ls ../../Samples/aps1/*.aps`
do
	echo $i " -> "
	../../toProlog $i
	echo -e
done
