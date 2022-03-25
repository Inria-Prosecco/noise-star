# Small utility for substitution in files
SED=$(which gsed &>/dev/null && echo gsed || echo sed)

# Map the algo names to the F* identifiers
aead_algs=("ChaChaPoly" "AESGCM")
hash_algs=("SHA256" "SHA512" "BLAKE2s" "BLAKE2b")

declare -A algos
algos["ChaChaPoly"]="CHACHA20_POLY1305"
algos["AESGCM"]="AES256_GCM"
algos["SHA256"]="SHA2_256"
algos["SHA512"]="SHA2_512"
algos["BLAKE2s"]="Hash.Blake2S"
algos["BLAKE2b"]="Hash.Blake2B"

# The list of patterns
patterns=( \
  "NN" "KN" "NK" "KK" "NX" "KX" "XN" "IN" "XK" "IK" "XX" \
  "IX" "N" "K" "X" "NNpsk0" "NNpsk2" "NKpsk0" "NKpsk2" "NXpsk2" \
  "XNpsk3" "XKpsk3" "XXpsk3" "KNpsk0" "KNpsk2" "KKpsk0" "KKpsk2" \
  "KXpsk2" "INpsk1" "INpsk2" "IKpsk1" "IKpsk2" "IXpsk2" "Npsk0" \
  "Kpsk0" "Xpsk1" "NK1" "NX1" "X1N" "X1K" "XK1" "X1K1" "X1X" "XX1" \
  "X1X1" "K1N" "K1K" "KK1" "K1K1" "K1X" "KX1" "K1X1" "I1N" "I1K" \
  "IK1" "I1K1" "I1X" "IX1" "I1X1")

dh_alg="25519"
dh_tm="DH_Curve25519"
ref_aead_alg="ChaChaPoly"
ref_aead_tm="${algos["$ref_aead_alg"]}"
ref_hash_alg="BLAKE2s"
ref_hash_tm="${algos["$ref_hash_alg"]}"
header=$'(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_api_instances.sh], DO NOT EDIT DIRECTLY ****)\n'
common_file_ref="instances/Impl.Noise.API.Instances.Common_25519_ChaChaPoly_BLAKE2s.fst"

# Cleanup options
cleanup=false
if [[ "$1" == "-clean" || "$2" == "-clean" ]]; then
    cleanup=true
fi;

# Subset: for testing, we generate only a subset of the files
if [[ "$1" == "-subset" || "$2" == "-subset" ]]; then
    patterns=("NN" "IKpsk2")
    aead_algs=("AESGCM")
    hash_algs=("SHA512")
fi;

# Ref: generate only the Makefile rule for the reference - TODO: remove this
if [[ "$1" == "-ref" || "$2" == "-ref" ]]; then
    patterns=("IKpsk2")
    aead_algs=("ChaChaPoly")
    hash_algs=("BLAKE2s")
fi;

# Generate the configuration files for all the cipher suites
for aead_alg in "${aead_algs[@]}"; do
    for hash_alg in "${hash_algs[@]}"; do
        # Ignore the reference
        if [[ $aead_alg == "ChaChaPoly" && $hash_alg == "BLAKE2s" ]]; then
           continue
        fi;

        # Retrieve the F* terms (are needed to substitute inside the files)
        aead_tm="${algos["$aead_alg"]}"
        hash_tm="${algos["$hash_alg"]}"

        # Copy the files
        fst="instances/Impl.Noise.API.Instances.Common_${dh_alg}_${aead_alg}_${hash_alg}.fst"
        echo $fst
        
        # Cleanup
        rm -f $fst

        # If -cleanup: only remove the files
        if $cleanup; then
            continue
        fi;
        touch $fst

        # Add the header
        echo $header >> $fst

        # Add the body
        cat $common_file_ref >> $fst

        # Replace the names (in the dependencies for ex.) with the proper ones
        sed -i "s/${ref_aead_alg}/${aead_alg}/g" $fst
        sed -i "s/${ref_hash_alg}/${hash_alg}/g" $fst

        # Replace the algorithms with the proper ones
        sed -i "s/${ref_aead_tm}/${aead_tm}/g" $fst
        sed -i "s/${ref_hash_tm}/${hash_tm}/g" $fst
        
        # TODO: add rules in Makefile.instances
    done;
done

# Initialize the Makefile.instances file
rm -f Makefile.instances
touch Makefile.instances
all_instances_rule="all-api-instances:"

ref_pattern="IKpsk2"
instance_file_ref="instances/Impl.Noise.API.Instances.IKpsk2_25519_ChaChaPoly_BLAKE2s"

echo_libnoise_api_rule () {
echo "
${pattern_subfolder_full}/libnoiseapi.a: ${pattern_subfolder_full}/Makefile.basic
	\$(MAKE) -C \$(dir \$@) -f \$(notdir \$<)" >> Makefile.instances
}

update_all_instances_rule () {
  all_instances_rule="
${all_instances_rule} \\
    ${pattern_subfolder_full}/libnoiseapi.a"
}

# Generate the Makefile rules
generate_rules () {
  # Add the proper rules in the Makefile.instances
  # Update the 'all-api-instances' rule (we add it at the very end)
  update_all_instances_rule
  # Generate the rule for libnoiseapi.a
  echo_libnoise_api_rule
  # Add the rule for the Makefile
  echo "${pattern_subfolder_full}/Makefile.basic: PATTERN_NAME=${pat}" >> Makefile.instances
  echo "${pattern_subfolder_full}/Makefile.basic: CIPHERSUITE_NAME=${cipher_suite_base_name}" >> Makefile.instances
}

# Generate the files for all the patterns, specialized for all the cipher suites
for pat in "${patterns[@]}"; do
    for aead_alg in "${aead_algs[@]}"; do
        for hash_alg in "${hash_algs[@]}"; do
            # We generate the Makefile rules and the target folders for all
            # the files, but ignore the reference when copying the .fst and .fsti
            cipher_suite_base_name=${dh_alg}_${aead_alg}_${hash_alg}
            base_name="${pat}_${cipher_suite_base_name}"
            base_file="instances/Impl.Noise.API.Instances.${base_name}"

            pattern_folder="dist/api-${pat}"
            pattern_subfolder="${base_name}"
            pattern_subfolder_full="${pattern_folder}/${pattern_subfolder}"

            fst="${base_file}.fst"
            fsti="${base_file}.fsti"

            # Create the necessary folders
            mkdir -p $pattern_subfolder_full

            # Generate the .fst and .fsti files
            # Ignore the reference
            if [[ $pat == "IKpsk2" && $aead_alg == "ChaChaPoly" && $hash_alg == "BLAKE2s" ]]; then
                # Always generate the Makefile rules for the reference (the
                # reference files are always present)
                generate_rules
                continue
            fi;

            ## Cleanup
            rm -f $fst $fsti
            # If -cleanup: only remove the files
            if $cleanup; then
                continue
            fi;

            # Generate the Makefile rules
            generate_rules

            touch $fst && touch $fsti

            ## Create the new files with the generic header
            header=$'(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_api_instances.sh], DO NOT EDIT DIRECTLY ****)\n'
            echo $header >> $fst
            echo $header >> $fsti

            ## Add the body - we use the IKpsk2 file as model
            cat instances/Impl.Noise.API.Instances.IKpsk2_25519_ChaChaPoly_BLAKE2s.fst >> $fst
            cat instances/Impl.Noise.API.Instances.IKpsk2_25519_ChaChaPoly_BLAKE2s.fsti >> $fsti

            # Replace the names (in the dependencies for ex.) with the proper ones
            $SED -i "s/IKpsk2/$pat/g" $fst
            $SED -i "s/IKpsk2/$pat/g" $fsti

            $SED -i "s/${ref_aead_alg}/${aead_alg}/g" $fst
            $SED -i "s/${ref_hash_alg}/${hash_alg}/g" $fst
            $SED -i "s/${ref_aead_alg}/${aead_alg}/g" $fsti
            $SED -i "s/${ref_hash_alg}/${hash_alg}/g" $fsti

            # Replace the algorithms with the proper ones
            $SED -i "s/${ref_aead_tm}/${aead_tm}/g" $fst
            $SED -i "s/${ref_hash_tm}/${hash_tm}/g" $fst
            $SED -i "s/${ref_aead_tm}/${aead_tm}/g" $fsti
            $SED -i "s/${ref_hash_tm}/${hash_tm}/g" $fsti
        done;
    done;
done

echo "$all_instances_rule" >> Makefile.instances
