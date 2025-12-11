if [ "$#" -ne 3 ]; then
  echo "modify-proof.sh <input(inlined).ml> <output.ml> <proof json dump dir>"
  exit 1
fi
input=$1
input_no_linedir=${input%.ml}.nolinedir.ml
input_mli=${input_no_linedir%.ml}.mli
input_bin=${input_no_linedir%.ml}.marshalled.bin
output=$2
echo "==================== tactic logger: modify-proof.sh =================="
echo "  - input: $input"
echo "  - output: $output"
echo "======================================================================"
dumpdir=$3

export TACLOGGER_DIR=${HOLLIGHT_DIR}/TacticTrace

basedir=${TACLOGGER_DIR}

# Remove the line number directives first.
python3 ${TACLOGGER_DIR}/remove-linenum-dirs.py $input $input_no_linedir

${basedir}/get-ast.sh $input_no_linedir
# get-ast.sh creates input_bin
${basedir}/tracer modify $input $input_bin $input_mli ${basedir}/hol_lib_inlined.mli ${output}.org

head -2 ${output}.org > $output
echo "(* --- exportTrace.ml --- *)" >> $output
cat ${basedir}/exportTrace.ml >> $output
echo "(* --- kernel_wrapper.ml --- *)" >> $output
cat ${basedir}/kernel_wrapper.ml >> $output
echo "" >> $output
tail -n +3 ${output}.org >> $output
echo "exptrace_dump \"${dumpdir}\";;" >>$output

rm $input_bin $input_no_linedir
