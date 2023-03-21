
for i in {0..50}
do
	cat file${i}.txt | ./advent2016 > file$((i+1)).txt
	echo "written to step $((i + 1))"
done
