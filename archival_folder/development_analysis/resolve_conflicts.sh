#!/bin/bash
# Resolve merge conflicts by keeping our enhanced versions

# For each file with conflicts
for file in Papers/P2_BidualGap/documentation/paper-final.tex \
            Papers/P3_2CatFramework/latex/Paper3A_Publication.tex \
            Papers/P3_2CatFramework/latex/Paper3B_Publication.tex \
            Papers/P4_SpectralGeometry/Paper4_QuantumSpectra.tex; do
    
    if [ -f "$file" ]; then
        echo "Resolving conflicts in $file"
        
        # Create a temporary file
        temp_file="${file}.tmp"
        
        # Process the file line by line
        in_conflict=0
        keep_ours=0
        
        while IFS= read -r line; do
            if [[ "$line" == "<<<<<<< HEAD" ]]; then
                in_conflict=1
                keep_ours=1
                continue
            elif [[ "$line" == "=======" ]]; then
                if [ $in_conflict -eq 1 ]; then
                    keep_ours=0
                    continue
                fi
            elif [[ "$line" == ">>>>>>> origin/main" ]]; then
                in_conflict=0
                keep_ours=0
                continue
            fi
            
            # Write line if not in theirs section
            if [ $in_conflict -eq 0 ] || [ $keep_ours -eq 1 ]; then
                echo "$line" >> "$temp_file"
            fi
        done < "$file"
        
        # Replace original with resolved
        mv "$temp_file" "$file"
        echo "Resolved $file"
    fi
done

echo "All conflicts resolved"
