# Reading DB-files from Paradox with Perl
#
# Copyright (C) 2000-2001 Sergey A. Eremenko (cae@donpac.ru) and
#     Alexander E. Chizhov (alex@donpac.ru)
# English translation copyright (C) 2001 Edward Stankevich (edward@donpac.ru)
#
# Created for JSC Rostovtelecom specially
# Licensed by GPL
# $Id: Paradox.pm v1.0.21 $
#
# 1.0.0 - first release
# 1.0.1 - view of 'short' as 0x0000 fixed, its empty now
# - made as module
# - additional checking for fields sizes
# 1.0.2 - view of 'money' and 'number' as 0x0000000000000000 fixed,
#   its empty now
# 1.0.3 - 'get_record_as_hash' added
# 1.0.4 - 'open', 'close', 'reopen' added for multiple reading
#   of the same file
# - small bug of calling 'new' without name was fixed at one
# 1.0.5 - very unpleasant bug of inaccurate copying from localtime.c
#   was fixed. There was infinite looping at bounds date of
#   years, such as 01-01-1999. Thats why those who using this
#   thing are STRONGLY RECOMMENDED to upgrade for 1.0.5.
# 1.0.6 - the bug of impossibility of reading last record, if last
#   data block consists of this record alone, fixed.
# 1.0.7 - header data integrity checking added
# - Paradox 3,4,5,7 checking added
# - 'long' type processing added
# - 'autoincrement' type processing added
# - 'logical' type processing added
# - 'time' type processing added
# - 'alt2koi' coding hase been modified
# - 'win1251' russian coding operation added
# - sort order and codepage are checking now. Also text coding
#   process in russian case only.
# - 'timestamp' type processing added
# 1.0.8 - bug of reading field name having spaces fixed,
#   thanks to Christopher R. Redinger
# 1.0.9 - bug of reading field name ending by zero fixed.
# 1.0.10 - read files with block lenght equal 16384 and 32768
# 1.0.15 - using Encode for decoding, encoding between codepages
# - 'alt2koi' and 'win1251' deleted
# 1.0.20 - 'memo' type processing added
# 1.0.21 - some cosmetical fixes
package Paradox;

# Object variables
# handle  - file handle
# dummy - next reading data
#
# DB-file header
# record_length   - record length
# header_length   - header length
# block_length    - 1 data block length
# all_records   - number of records
# all_used_blocks - number of real used data blocks
# first_data_block  - first data block
# all_fields    - number of fields
# sort_order    - sort order
# version   - Paradox version
# code_page   - DOS codepage
# @field_type   - array of field types
# @field_length   - array of field lengths
# @field_name   - array of field names
#
# Reading file data
# is_last_block   - is it last block?
# current_used_block  - number of current used block
# current_block   - number of current block
# next_block    - number of next block
# need_read_block - is need to read next data block?
# end_of_base   - is it end of base?
# last_record_offset  - last record offset in data block
# current_record_offset - current record offset in data block

require 5.004;
use Fcntl qw (:flock);
use IO::File;
use Encode;
use strict;
our $file_name;

#determinating length of M field
sub memo_length {
    my ($string) = @_;
    $string = unpack( 'L', substr( $string, -6, 4 ) );
    return $string;
}

#determinating offset of Blob Block
sub mb_offset {
    my $string = shift;
    $string = unpack( 'L', substr( $string, -10, 4 ) );
    return $string & 0xFFFFFF00;
}

#determinating index of Blob record
sub mb_index {
    my $string = shift;
    $string = unpack( 'C', substr( $string, -10, 1 ) );
    return $string;
}

#determinating mod number of Blob record
sub mod_number {
    my $string = shift;
    $string = unpack( 'S', substr( $string, -2, 2 ) );
    return $string;
}

#open read M record from MB
sub read_MEMO_from_MB {
    my $f_table   = shift;
    my $memo      = shift;
    my $mb_offset = &mb_offset($memo);
    my $mb_index  = &mb_index($memo);
    my @files_mb  = glob("*.[Mm][Bb]");
    my $mb;

    foreach my $f_memo (@files_mb) {
        if ( substr( $f_table, 0, -3 ) eq substr( $f_memo, 0, -3 ) ) {
            $mb = $f_memo;
            last;
        }
    }

    open( MB, $mb ) or die "Can't open file $mb \n";
    binmode(MB);
    my $entry_offset = 12 + $mb_offset + ( 5 * $mb_index );

    seek( MB, $entry_offset, 0 );
    read( MB, my $memo_entry, 5 );
    my $data_offset_in_block = unpack( "C", substr( $memo_entry, 0x0, 1 ) );

    my $data_lenght_in_block = unpack( "C", substr( $memo_entry, 0x1, 1 ) );

    my $modification_number = unpack( "S", substr( $memo_entry, 0x2, 2 ) );

    my $data_lenght_modulo_16 = unpack( "C", substr( $memo_entry, 0x4, 1 ) );

    seek( MB, $mb_offset + $data_offset_in_block * 16, 0 );
    read( MB,
        my $memo_field,
        --$data_lenght_in_block * 16 + $data_lenght_modulo_16
    );

    #print "$memo_field \n";
    close(MB);
    return $memo_field;
}

# $header_length have to be read at this moment !
sub read_next_header_data {
    my $self = shift;
    my ($length) = @_;

    die "instance method called on class" unless ref $self;
    if ( !defined($length) ) {
        return;
    }
    sysread( $self->{handle}, $self->{dummy}, $length )
      || die "Cannot read header in read_next_header_data: $!\n";
    if ( sysseek( $self->{handle}, 0, 1 ) > $self->{header_length} ) {
        die "Bad format! Header is too small\n";
    }
}

# convert Paradox definition of two-byte integer into "normal human"

sub paradox_short_to_scalar {
    my ($num) = @_;
    my ($short);
    my ( $high, $low );

    if ( !defined($num) ) {
        return undef;
    }
    ($short) = unpack( 'n', $num );
    if ( $short == 0 ) {
        return "";
    }
    elsif ( ( $short & 0x8000 ) > 0 ) {
        return $short & 0x7fff;
    }
    else {
        return -( $short ^ 0x7fff ) - 1;
    }
}

# convert Paradox definition of four-byte integer into "normal human"

sub paradox_long_to_scalar {
    my ($num) = @_;
    my ($long);

    if ( !defined($num) ) {
        return undef;
    }
    ($long) = unpack( 'N', $num );
    if ( $long == 0 ) {
        return "";
    }
    elsif ( ( $long & 0x80000000 ) > 0 ) {
        return $long & 0x7fffffff;
    }
    else {
        return -( $long ^ 0x7fffffff ) - 1;
    }
}

# convert Paradox definition of boolean into "normal human"

sub paradox_logic_to_scalar {
    my ($num) = @_;
    my ($logical);

    if ( !defined($num) ) {
        return undef;
    }
    ($logical) = unpack( 'C', $num );
    if ( 0 == $logical ) {
        return "";
    }
    elsif ( 0x81 == $logical ) {
        return "true";
    }
    elsif ( 0x80 == $logical ) {
        return "false";
    }
    return "INVAL-BOOL";
}

# convert Paradox definition of time into "normal human"

sub paradox_time_to_scalar {
    my ($num) = @_;
    my ($long);

    if ( !defined($num) ) {
        return undef;
    }
    $long = &paradox_long_to_scalar($num);
    if ( "" eq $long ) {
        return "";
    }
    if ( $long < 0 ) {
        return "INVAL-TIME";
    }
    return &msec_to_time($long);
}

# convert microseconds into time

sub msec_to_time {

    # to being divided without remainder
    use integer;

    my ($hour) = @_;
    my ( $min, $sec, $msec );

    if ( !defined($hour) ) {
        return undef;
    }
    $msec = $hour % 1000;
    $hour /= 1000;
    $sec = $hour % 60;
    $hour /= 60;
    $min = $hour % 60;
    $hour /= 60;
    no integer;
    return sprintf "%02d:%02d:%02d.%d", $hour, $min, $sec, $msec;
}

# convert Paradox definition of floating point into "normal human"
# WARNING! I've checked it only at Intel platform!
# I could write some universal, but I'm lazy :-)

sub paradox_number_to_scalar {
    my ($num) = @_;
    my ($result);
    my (@num_array);

    undef $result;
    if ( defined($num) ) {
        @num_array = unpack( 'CCCCCCCC', $num );
        if (   $num_array[0] == 0
            && $num_array[1] == 0
            && $num_array[2] == 0
            && $num_array[3] == 0
            && $num_array[4] == 0
            && $num_array[5] == 0
            && $num_array[6] == 0
            && $num_array[7] == 0 )
        {
            return "";
        }

        # high bit in first byte is set
        if ( ( $num_array[0] & 0x80 ) > 0 ) {
            $num_array[0] &= 0x7f;
        }
        elsif ( ( $num_array[0] == 0 ) && ( ( $num_array[1] & 0xf0 ) < 0x10 ) )
        {
        }
        else {
            foreach (@num_array) {
                $_ ^= 0xff;
            }
        }
        @num_array = reverse @num_array;
        $result = unpack( 'd', pack( 'CCCCCCCC', @num_array ) );
    }
    return $result;
}

# convert Paradox definition of date to "normal human"

sub paradox_date_to_scalar {
    my ($num) = @_;
    my ($long);

    if ( !defined($num) ) {
        return undef;
    }
    $long = unpack( 'N', $num );
    if ( ( $long & 0x80000000 ) > 0 ) {
        return &days_to_date( $long & 0x7fffffff );
    }
    elsif ( $long == 0 ) {
        return "";
    }
    else {
        return "INVAL-DATE";
    }
}

# convert Paradox definition of date and time to "normal human"

sub paradox_timestamp_to_scalar {

    # to work with more than LongInt numbers
    use Math::BigInt;

    my ($num) = @_;
    my ( $date, $time );
    my ( $a,    $b );

    if ( !defined($num) ) {
        return undef;
    }
    $date = &paradox_number_to_scalar($num);
    if ( "" eq $date ) {
        return "";
    }
    if ( $date < 0 ) {
        return "INVAL-TIMESTAMP";
    }
    $a = Math::BigInt->new($date);
    $b = Math::BigInt->new("86400000");
    ( $date, $time ) = $a->bdiv($b);
    return &days_to_date($date) . " " . &msec_to_time($time);
}

# I don't lay claim to algorythm, it was simply been copied from localtime.c
# Portions (C) 1996 Arthur David Olson (arthur_david_olson@nih.gov).

my (@year_lengths) = ( 365, 366 );
my (@mon_lengths) = (
    [ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ],
    [ 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ]
);

# is it a leap year?

sub isleap {
    my ($y) = @_;

    if ( !defined($y) ) {
        return undef;
    }
    return ( $y % 4 ) == 0 && ( ( $y % 100 ) != 0 || ( $y % 400 ) == 0 );
}

sub days_to_date {

    # to being divided without remainder
    use integer;

    my ($days) = @_;
    my ( $year,  $mon,  $day );
    my ( $yleap, $newy, $ref );

    if ( !defined($days) ) {
        return undef;
    }

  # as long as this is amount of days from 1st january (1st january of 1st year
  # is 1), you have to subtract one day to have an amount of days from beginning
    $days--;

    # Paradox keep the date beginning from 1st year A.D.
    $year = 1;
    while ( $days < 0 || $days >= $year_lengths[ $yleap = isleap($year) ] ) {
        $newy = $year + $days / 365;
        if ( $days < 0 ) {
            $newy--;
        }
        $days -=
          ( $newy - $year ) * 365 +
          ( ( $newy - 1 ) / 4 - ( $newy - 1 ) / 100 + ( $newy - 1 ) / 400 ) -
          ( ( $year - 1 ) / 4 - ( $year - 1 ) / 100 + ( $year - 1 ) / 400 );
        $year = $newy;
    }
    $ref = $mon_lengths[$yleap];
    for ( $mon = 0 ; $days >= $ref->[$mon] ; $mon++ ) {
        $days -= $ref->[$mon];
    }

    # months from nil, need to be increased by 1
    $mon++;

    # same situation
    $days++;
    no integer;
    return sprintf "%02d-%02d-%04d", $days, $mon, $year;
}

# main file is F

sub PX_read_header {
    my $self = shift;
    my ( $i, $char, $string );

    die "instance method called on class" unless ref $self;
    sysseek( $self->{handle}, 0, 0 )
      || die "Cannot make seek in PX_read_header: $!\n";

    # 00 word
    sysread( $self->{handle}, $self->{dummy}, 2 )
      || die "Cannot read header in PX_read_header: $!\n";
    $self->{record_length} = unpack( 'v', $self->{dummy} );

    # 02 word
    sysread( $self->{handle}, $self->{dummy}, 2 )
      || die "Cannot read header in PX_read_header: $!\n";
    $self->{header_length} = unpack( 'v', $self->{dummy} );

    # 04 byte
    $self->read_next_header_data(1);
    $i = unpack( 'C', $self->{dummy} );
    ( 0 == $i || 2 == $i )
      || die "Unknown DB-file type!\n";

    # 05 byte
    $self->read_next_header_data(1);
    $i = unpack( 'C', $self->{dummy} );
    ( $i >= 1 && $i <= 4 || $i == 16 || $i == 32 )
      || die "Unknown DB-file block size!\n";
    $self->{block_length} = $i * 1024;

    # 06 long
    $self->read_next_header_data(4);
    $self->{all_records} = unpack( 'V', $self->{dummy} );

    # 0A word
    $self->read_next_header_data(2);
    $self->{all_used_blocks} = unpack( 'v', $self->{dummy} );

    # 0C word
    $self->read_next_header_data(2);

    # 0E word
    $self->read_next_header_data(2);
    $self->{first_data_block} = unpack( 'v', $self->{dummy} );

    # 10 word ........
    $self->read_next_header_data(0x11);

    # 21 word
    $self->read_next_header_data(2);
    $self->{all_fields} = unpack( 'v', $self->{dummy} );

    # 23 word long
    $self->read_next_header_data(6);

    # 29 byte
    $self->read_next_header_data(1);
    $self->{sort_order} = unpack( 'C', $self->{dummy} );

    # 2A byte ........
    $self->read_next_header_data(0x0f);

    # 39 byte
    $self->read_next_header_data(1);
    $i = unpack( 'C', $self->{dummy} );
    ( $i >= 3 && $i <= 12 )
      || die "Unknown DB-file version!\n";
    $self->{version} = $i;
    $self->read_next_header_data(0x1e);
    if ( $self->{version} > 4 ) {

        # 58 word ........
        $self->read_next_header_data(18);

        # 6A word
        $self->read_next_header_data(2);
        $self->{code_page} = unpack( 'v', $self->{dummy} );
        $self->read_next_header_data(12);
    }
    else {

        # Paradox 3 has not such header
        if ( 0xc0 == $self->{sort_order} ) {
            $self->{code_page} = 866;
        }
        elsif ( 0x4c == $self->{sort_order} ) {
            $self->{code_page} = 1251;
        }
    }

    # 58 (Paradox3) or 78 (any) array
    undef @{ $self->{field_type} };
    undef @{ $self->{field_length} };
    undef @{ $self->{field_name} };
    for ( $i = 0 ; $i < $self->{all_fields} ; $i++ ) {
        $self->read_next_header_data(1);
        push( @{ $self->{field_type} }, unpack( 'C', $self->{dummy} ) );
        $self->read_next_header_data(1);
        push( @{ $self->{field_length} }, unpack( 'C', $self->{dummy} ) );
    }

    # ignore all until field names
    $self->read_next_header_data( 4 * $self->{all_fields} + 4 );
    if ( $self->{version} > 11 ) {
        $self->read_next_header_data(0x105);
    }
    else {
        $self->read_next_header_data(0x4f);
    }
    for ( $i = 0 ; $i < $self->{all_fields} ; $i++ ) {
        $string = "";
        do {
            sysread( $self->{handle}, $char, 1 )
              || die "Cannot read header in PX_read_header: $!\n";
            if ( sysseek( $self->{handle}, 0, 1 ) > $self->{header_length} ) {
                die "Bad format! Header is too small\n";
            }
            $char = unpack( 'Z', $char );
            if ( ord($char) ) {
                $string .= $char;
            }
        } while ( ord($char) );
        if ( 0xc0 == $self->{sort_order} && 866 == $self->{code_page} ) {

            #push (@{$self->{field_name}},alt2koi($string));
            push( @{ $self->{field_name} }, decode( 'cp866', $string ) );
        }
        elsif ( 0x4c == $self->{sort_order}
            && ( 1252 == $self->{code_page} || 1251 == $self->{code_page} ) )
        {

            #push (@{$self->{field_name}},win2koi($string));
            push( @{ $self->{field_name} }, $string );

        }
        else {
            push( @{ $self->{field_name} }, $string );
        }
    }
}

# return next block number and last record offset in block
# and specify file position for reading of first record

sub PX_read_data_block {
    my $self = shift;
    my ($dummy);

    die "instance method called on class" unless ref $self;
    sysseek(
        $self->{handle},
        $self->{block_length} * ( $self->{current_block} - 1 ) +
          $self->{header_length},
        0
    );
    sysread( $self->{handle}, $dummy, 2 )
      || die "Cannot read data block N", $self->{current_block}, ": $!\n";
    $self->{next_block} = unpack( 'v', $dummy );
    sysread( $self->{handle}, $dummy, 2 )
      || die "Cannot read data block N", $self->{current_block}, ": $!\n";
    sysread( $self->{handle}, $dummy, 2 )
      || die "Cannot read data block N", $self->{current_block}, ": $!\n";
    $self->{last_record_offset} = unpack( 'v', $dummy );
    $self->{current_used_block}++;
}

# new object creating

sub new {
    my $class = shift;
    my $new = bless {}, $class;
    $new->{handle} = IO::File->new();
    $file_name = $_[0];
    return $new->open(@_);

}

# open file and initialize all object variables

sub open {
    my $self = shift;

    die "instance method called on class" unless ref $self;
    if ( !defined( $_[0] ) ) {
        return undef;
    }
    if ( not sysopen( $self->{handle}, $_[0], O_RDONLY ) ) {
        warn "Cannot open file \'", $_[0], "\': $!\n";
        return undef;
    }
    if ( not flock( $self->{handle}, LOCK_SH ) ) {
        warn "Cannot lock file \'", $_[0], "\': $!\n";
        return undef;
    }
    return $self->reopen();
}

# close file

sub close {
    my $self = shift;

    die "instance method called on class" unless ref $self;
    flock( $self->{handle}, LOCK_UN );
    close( $self->{handle} );
}

# unlock and close file

sub DESTROY {
    my $self = shift;

    $self->close();
}

# re-open file being already opened (properly simply return to BOF)

sub reopen {
    my $self = shift;

    die "instance method called on class" unless ref $self;
    $self->PX_read_header();
    $self->{is_last_block}      = 0;
    $self->{next_block}         = $self->{first_data_block};
    $self->{current_used_block} = 0;
    $self->{end_of_base}        = 0;
    $self->{need_read_block}    = 1;
    return $self;
}

# read next record while block is being read
# read record and return its data in array or undef
# BCD, Binary and all BLOBs NOT SUPPORTED!

sub PX_read_record {
    my $self = shift;
    my (@result);
    my ( $a, $i, $dummy );

    die "instance method called on class" unless ref $self;
    if ( $self->{current_record_offset} < $self->{last_record_offset} ) {
        $self->{need_read_block} = 0;
    }
    else {
        $self->{need_read_block} = 1;
    }
    if ( $self->{current_record_offset} > $self->{last_record_offset} ) {
        return;
    }

    sysseek(
        $self->{handle},
        $self->{block_length} * ( $self->{current_block} - 1 ) +
          $self->{header_length} + 6 +
          $self->{current_record_offset},
        0
    ) || die "Cannot make seek to record: $!\n";

    $self->{current_record_offset} += $self->{record_length};
    undef @result;
    for ( $i = 0 ; $i < $self->{all_fields} ; $i++ ) {

        # BCD type has a fixed length
        if ( ${ $self->{field_type} }[$i] == 0x17 ) {
            sysread( $self->{handle}, $dummy, 17 )
              || die "Cannot read record: $!\n";
        }
        else {
            sysread( $self->{handle}, $dummy, ${ $self->{field_length} }[$i] )
              || die "Cannot read record: $!\n";
        }
        if ( ${ $self->{field_type} }[$i] == 1 ) {

            # Field A
            $a = unpack( 'Z' . ${ $self->{field_length} }[$i], $dummy );
            if ( 0xc0 == $self->{sort_order} && 866 == $self->{code_page} ) {
                push( @result, encode( 'cp1251', decode( 'cp866', ($a) ) ) );
            }
            elsif ( 0x4c == $self->{sort_order}
                && ( 1252 == $self->{code_page} || 1251 == $self->{code_page} )
              )
            {
                push( @result, $a );    #?
            }
            else {
                push( @result, $a );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 2 ) {

            # Field D
            if ( ${ $self->{field_length} }[$i] == 4 ) {
                push( @result, &paradox_date_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 3 ) {

            # Field S
            if ( ${ $self->{field_length} }[$i] == 2 ) {
                push( @result, &paradox_short_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 4 ) {

            # Field I
            if ( ${ $self->{field_length} }[$i] == 4 ) {
                push( @result, &paradox_long_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 5 ) {

            # Field $
            if ( ${ $self->{field_length} }[$i] == 8 ) {
                push( @result, &paradox_number_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 6 ) {

            # Field N
            if ( ${ $self->{field_length} }[$i] == 8 ) {
                push( @result, &paradox_number_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 9 ) {

            # Field L
            if ( ${ $self->{field_length} }[$i] == 1 ) {
                push( @result, &paradox_logic_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 0x14 ) {

            # Field T
            if ( ${ $self->{field_length} }[$i] == 4 ) {
                push( @result, &paradox_time_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 0x15 ) {

            # Field @
            if ( ${ $self->{field_length} }[$i] == 8 ) {
                push( @result, &paradox_timestamp_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 0x16 ) {

            # Field +
            if ( ${ $self->{field_length} }[$i] == 4 ) {
                push( @result, &paradox_long_to_scalar($dummy) );
            }
            else {
                push( @result, "-*%& UNSUPPORTED &%*-" );
            }
        }
        elsif ( ${ $self->{field_type} }[$i] == 0x17 ) {

            # Field #
            push( @result, "-*%& UNSUPPORTED &%*-" );
        }
        elsif ( ${ $self->{field_type} }[$i] == 0xC ) {

            # Field M
            if ( &mb_offset($dummy) ) {
                push( @result, &read_MEMO_from_MB( $file_name, $dummy ) );
            }
            else {
                push( @result, substr( $dummy, 0, &memo_length($dummy) ) );

            }

            if ( 0xc0 == $self->{sort_order} && 866 == $self->{code_page} ) {
                push( @result,
                    encode( 'cp1251', decode( 'cp866', pop(@result) ) ) );

            }

        }

        else {
            push( @result, "-*%& UNSUPPORTED &%*-" );
        }
    }
    return @result;
}

# read next record

sub fetch {
    my $self = shift;

    die "instance method called on class" unless ref $self;
    if ( $self->{end_of_base} ) {
        return;
    }
    if ( $self->{need_read_block} ) {
        for (
            ;
            !$self->{is_last_block}
            && $self->{current_used_block} <= $self->{all_used_blocks} ;
          )
        {
            $self->{current_block} = $self->{next_block};
            $self->PX_read_data_block();
            if ( $self->{next_block} == 0 ) {
                $self->{is_last_block} = 1;
            }
            if (   $self->{last_record_offset} < 0
                || $self->{last_record_offset} >
                $self->{block_length} - $self->{record_length} )
            {
                next;
            }
            $self->{current_record_offset} = 0;
            return $self->PX_read_record();
        }
        $self->{end_of_base} = 1;
        return;
    }
    return $self->PX_read_record();
}

# read next record as hash ("field name" => "value")

sub get_record_as_hash {
    my $self   = shift;
    my $result = {};
    my @record_data;

    if ( not( @record_data = $self->fetch(@_) ) ) {
        return;
    }
    @{$result}{ @{ $self->{field_name} } } = @record_data;
    return %$result;
}

1;

# Usage:
#
#use Paradox ;
#
#$d = new Paradox "path/to/file.db" ;
#print "Header:\n" ;
#print join ("|",@{$d->{field_type}}),"\n" ;
#print join ("|",@{$d->{field_length}}),"\n" ;
#print join ("|",@{$d->{field_name}}),"\n" ;
#print "Data:\n" ;
#while (@record_data = $d->fetch ()) {
# print join ("|",@record_data),"\n" ;
#}
