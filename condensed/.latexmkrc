add_cus_dep('lagda','tex',0,'lagda2tex');

sub lagda2tex {
    my $base = shift @_;
    return system('agda', '--latex', '--latex-dir=..', "$base.lagda");
}

$pdflatex = 'pdflatex -shell-escape';