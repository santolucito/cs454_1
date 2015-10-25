
for file in "benchMarks"/*
do
  echo "running $file"
  scala -cp classes VCGen "$file"
  echo
done
