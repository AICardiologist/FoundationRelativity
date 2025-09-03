# .latexmkrc - Configuration for latexmk
# This enables consistent PDF generation across all Paper 3 documents

# Use pdflatex by default
$pdf_mode = 1;

# Output directory (optional - uncomment to use)
# $out_dir = 'build';

# Custom dependency for shared macros
add_cus_dep('tex', 'pdf', 0, 'run_pdflatex');

sub run_pdflatex {
    system("pdflatex -interaction=nonstopmode $_[0]");
}

# Ensure paper3-macros.tex is tracked as a dependency
@default_files = ('Paper3_Main.tex', 'Paper3A_Publication.tex', 
                  'Paper3B_Publication.tex', 'Paper3_Lean_Formalization.tex');

# Custom clean extensions
$clean_ext = 'synctex.gz run.xml';

# Viewer settings (platform-specific)
if ($^O eq 'darwin') {
    $pdf_previewer = 'open -a Preview';
} elsif ($^O eq 'linux') {
    $pdf_previewer = 'evince';
} else {
    $pdf_previewer = 'start';  # Windows
}