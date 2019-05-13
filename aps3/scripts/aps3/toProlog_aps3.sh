#! /bin/bash

for i in `ls ../../Samples/aps3/*.aps`
do
	echo $i " -> "
	../../toProlog $i
	echo -e
done
