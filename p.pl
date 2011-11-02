use Modern::Perl;
use Paradox ;
my $d = new Paradox "biolife.db" ;
print "Header:\n" ;
print join ("|",@{$d->{field_type}}),"\n" ;
print join ("|",@{$d->{field_length}}),"\n" ;
print join ("|",@{$d->{field_name}}),"\n" ;
print "Data:\n" ;
while (my @record_data = $d->fetch ()) {
 print join ("|",@record_data),"\n" ;
}

