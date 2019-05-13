#! /bin/bash

for i in `ls ../../Samples/aps2/*.aps`
do
	echo $i " -> "
	../../toProlog $i
	echo -e
done
