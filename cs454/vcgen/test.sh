
for file in "imp"/*
do
  echo "running $file"
  scala -cp classes VCGen "$file"
  echo
done
