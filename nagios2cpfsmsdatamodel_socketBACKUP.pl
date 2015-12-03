#!/usr/bin/perl --


use strict;
use Time::Local;
use vars qw($socket $smart_update);
use IO::Socket;
use Time::HiRes;
#use CollageQuery;
use Data::Dumper;

# Settings
my $debug             = 1;    # Set 0 for minimal, 1 for summary, 2 for basic, 3 for debug level, 4 for ridiculous level.
my $smart_update      = 0;    # If set to 1, then send only state changes and heartbeats.
my $heartbeat_mode    = 0;    # Do not change this setting -- it is controlled by smart_update.
my $send_sync_warning = 1;    # Send a console message when Nagios and SMSDataModel are out of sync. 0 = no warning, 1 = warning.

my $nagios_version = 3;
my $statusfile     = '/usr/local/ffm/nagios/var/status.dat';
my $logfile        = '/usr/local/ffm/nagios/var/nagios2cpfsmsdatamodel_socket.log';


my $remote_port = 4913;

# Wait time in seconds between checks of the nagios status.log file.
#my $loop_wait_time = 15;
my $loop_wait_time = 60;

# Whether to send pending to ok transition events or just skip them
my $send_events_for_pending_to_ok = 0;

# Time between full updates in seconds.  This is the longest you want to wait for updates to the LastCheckTime in SMSDataModel.
# Set this to a longer time on busy systems.  Suggested 90 second minimum, 300 second maximum.  The longer the time, the larger
# the bundles of updates.  Setting this too long could result in a "bumpy" performance curve, as the system processes large
# bundles.  Old advice:  If you set this near the maximum, you might also want to also increase the xml_bundle_max_size below.
my $full_update_time = 120;

my $thisnagios            = "localhost";    # `hostname`;
my $xml_bundle_size       = 5;              # this is NOT the minimum size
my $xml_bundle_max_size   = 50;            # but this is the maximum size. Suggest this be Minimum 50, Maximum 5000.
my $sync_timeout_seconds  = 5;
my $message_counter       = 1;
my $default_max_event_bundle_size = 50;
my $max_event_bundle_size = $default_max_event_bundle_size;
#my $syncwait              = 20;             # This is a multiplier of loop_wait_time to wait on updates while smsstack processes the sync.
					    # You may need to increase this if you see deadlocks after commit in the framework.log file.
my $syncwait              = 20;             # This is a multiplier of loop_wait_time to wait on updates while smsstack processes the sync.
					    # You may need to increase this if you see deadlocks after commit in the framework.log file.

# Init variables
my $last_statusfile_mtime = 0;
my $element_ref           = {};
my $global_nagios	  = {};
my $collage_status_ref    = {};
my $collage_heartbeat_ref = {};
my $device_ref            = {};
my $host_ref              = {};
my $service_ref           = {};
my $loop_count            = 0;
my $remote_host           = $thisnagios;
#my $remote_host           = "129.221.25.121";    # `hostname`;
my $total_wait            = 0;
my @xml_messages          = ();
my @event_messages        = ();
my $n_hostcount           = 0;
my $n_servicecount        = 0;
my $last_n_hostcount      = 0;
my $last_n_servicecount   = 0;
my $f_hostcount           = 0;
my $f_servicecount        = 0;
my $last_f_hostcount      = 0;
my $last_f_servicecount   = 0;
my $enable_feeding        = 1;
my $syncwaitcount         = 0;
my $logtime               = '';

# Pre-extend the event_messages array for later efficiency, then truncate back to an empty state.
$#event_messages = $max_event_bundle_size;
@event_messages = ();

freeze_logtime();

# if argument passed, just run once to synchronize state between Nagios and SMSDataModel
my $sync_at_start = shift || 0;

$SIG{"PIPE"} = \&sig_pipe_handler;    # handle broken pipe error

my %HostStatus = ( 0 => "UP", 1 => "DOWN", 2 => "UNREACHABLE" );
my %ServiceStatus = ( 0 => "OK", 1 => "WARNING", 2 => "CRITICAL", 3 => "UNKNOWN" );

my %CheckType = ( 0 => "ACTIVE", 1 => "PASSIVE" );

my %StateType = ( 0 => "SOFT", 1 => "HARD" );

chomp $thisnagios;
my %hostipaddress = ();

if ( !open( LOG, '>>', $logfile ) ) {
    print "Can't open logfile '$logfile'.\n";
}
LOG->autoflush(1);

=head not required for 1.0
if ( my $socket = IO::Socket::INET->new( PeerAddr => $remote_host, PeerPort => $remote_port, Proto => "tcp", Type => SOCK_STREAM ) ) {
    print $socket
"<GENERICLOG consolidation='SYSTEM' ApplicationType='SYSTEM' MonitorServerName='localhost' Device='127.0.0.1' Severity='OK' MonitorStatus='OK' TextMessage='SMSDataModel-Nagios status check process started.' />";
    close($socket);
}
else {
    freeze_logtime();
    print LOG "${logtime}Listener services not available. Retrying in 10 seconds.\n";
    sleep 10;
    exit(0);
}

sub load_cached_addresses() {

    # Get hosts->IPaddress from Monarch
    my ( $Database_Name, $Database_Host, $Database_User, $Database_Password ) = CollageQuery::readGroundworkDBConfig("monarch");
    my $dbh = DBI->connect( "DBI:mysql:$Database_Name:$Database_Host", $Database_User, $Database_Password )
      or die "Can't connect to database $Database_Name. Error:" . $DBI::errstr;

    my $query = "select name,address from hosts; ";
    my $sth   = $dbh->prepare($query);
    $sth->execute() or die $sth->errstr;
    my @serviceprofile_ids = ();
    while ( my $row = $sth->fetchrow_hashref() ) {
	$hostipaddress{ $$row{name} } = $$row{address};
    }
    $sth->finish();
    $dbh->disconnect();
    return;
}
sub getInitialState {
    ## Check each host and service status in SMSDataModel, and populate collage_status_ref
    ## with current state. Do this at startup to avoid huge initial message loads.
    my $collage_status_ref = shift;
    my $smsstack         = CollageQuery->new();
    my $element_ref        = get_status( $statusfile, $nagios_version );
    if ( $debug > 3 ) {
	freeze_logtime();
	print LOG $logtime . Data::Dumper->Dump( [ \%{$element_ref} ], [qw(\%element_ref)] );
    }
    my $fn_hosts         = $smsstack->getHosts();
    my $fn_host_services = $smsstack->getHostServices();
    if ( ref($fn_hosts) eq 'HASH' ) {
	foreach my $host ( keys %{$fn_hosts} ) {
	    my $fn_host = $fn_hosts->{$host};
	    my $cs_host = \%{ $collage_status_ref->{Host}->{$host} };
	    my $el_host = $element_ref->{Host}->{$host};
	    if ( $debug > 1 ) {
		print LOG Data::Dumper->Dump( [ $fn_host ], [qw($fn_host)] );
		print LOG "Nagios last check time: $el_host->{LastCheckTime}\n";
	  	print LOG "Nagios next check time: $el_host->{NextCheckTime}\n";
	    }

	    # Look for hosts that have never been checked -- don't bother sending results if so.
	    if ( $el_host->{LastCheckTime} eq '0' && ( !defined $fn_host->{LastCheckTime} ) ) {
		$cs_host->{LastCheckTime} = "0";    # This will show up as no change of state
	    }
	    else {
		$cs_host->{LastCheckTime} = $fn_host->{LastCheckTime};    # Might be a change, might not
	    }
	    # Do the same for NexCheckTime in case it was never fed (like for passive checks)
            if ( $el_host->{NextCheckTime} eq '0' && ( !defined $fn_host->{NextCheckTime} ) ) {
                $cs_host->{NextCheckTime} = "0";    # This will show up as no change of state
            }
            else {
                $cs_host->{NextCheckTime} = $fn_host->{NextCheckTime};    # Might be a change, might not
            }
	    $cs_host->{Comments}                  = $fn_host->{Comments};
	    $cs_host->{CurrentAttempt}            = $fn_host->{CurrentAttempt};
	    $cs_host->{CurrentNotificationNumber} = $fn_host->{CurrentNotificationNumber};
	    $cs_host->{ExecutionTime}             = $fn_host->{ExecutionTime};
	    $cs_host->{Latency}                   = $fn_host->{Latency};
	    $cs_host->{MaxAttempts}               = $fn_host->{MaxAttempts};
	    $cs_host->{MonitorStatus}             = $fn_host->{MonitorStatus};
	    $cs_host->{NextCheckTime}             = $fn_host->{NextCheckTime};
	    $cs_host->{ScheduledDowntimeDepth}    = $fn_host->{ScheduledDowntimeDepth};
	    $cs_host->{StateType}                 = $fn_host->{StateType};
	    $cs_host->{isAcknowledged}            = $fn_host->{isAcknowledged};
	    $cs_host->{isChecksEnabled}           = $fn_host->{isChecksEnabled};
	    $cs_host->{isEventHandlersEnabled}    = $fn_host->{isEventHandlersEnabled};
	    $cs_host->{isFlapDetectionEnabled}    = $fn_host->{isFlapDetectionEnabled};
#	    $cs_host->{isHostFlapping}            = $fn_host->{isHostFlapping};
	    $cs_host->{isNotificationsEnabled}    = $fn_host->{isNotificationsEnabled};
#	    $cs_host->{isObsessOverHost}          = $fn_host->{isObsessOverHost};
	    $cs_host->{isPassiveChecksEnabled}    = $fn_host->{isPassiveChecksEnabled};
	    $cs_host->{LastPluginOutput}          = $fn_host->{LastPluginOutput};
	    $cs_host->{PercentStateChange}        = $fn_host->{PercentStateChange}; 
	    $cs_host->{LastStateChange}        = $fn_host->{LastStateChange};
	    # Look for fancy MonitorStatus values and translate to the simple ones Nagios knows
            if ( $fn_host->{MonitorStatus} =~ /DOWN/ ) {
                $cs_host->{MonitorStatus} = 'DOWN';    # 
            }
	    # FIX FUTURE: We ignore isObsessOverHost for now, as is is not needed in smsstack (yet)
	    # Similarly we ignore isHostFlapping.
	    # isObsessOverHost           (property)
	    # The isObsessOverHost flag is perhaps problematic.  The obsess_over_host flag can be set in Nagios
	    # for an individual host, but such settings can be globally overridden by the obsess_over_hosts flag
	    # at the Nagios level.  So we need to over-ride the host setting with the global if it's off... 
#	    if ( $global_nagios->{obsess_over_hosts} == 0 ) {
#                 $cs_host->{isObsessOverHost} = 0;
#            }
	    # Separately, this property is not set in smsstack: GWMON-7678 filed to address this.
	    # Take out the following assignment when that issue is resolved:
#	    if ( !defined $cs_host->{isObsessOverHost} ) {
#                $cs_host->{isObsessOverHost} = $el_host->{isObsessOverHost};
#            }
	    ####

	    if ( !defined $cs_host->{Comments} ) {
		$cs_host->{Comments} = ' ';
	    }
	    if ( ref($fn_host_services) eq 'HASH' ) {
		foreach my $service ( keys %{ $fn_host_services->{$host} } ) {
		    my $fn_svc = $fn_host_services->{$host}->{$service};
		    my $cs_svc  = \%{ $cs_host->{Service}->{$service} };
		    my $el_svc  = $el_host->{Service}->{$service};
		    if ( $debug > 2 ) {
			print LOG Data::Dumper->Dump( [ $fn_svc ], [qw($fn_svc)] );
		    }
		    my $f_state = $fn_svc->{MonitorStatus};
		    my $n_state = $el_svc->{MonitorStatus};

		    # $fn_svc->{LastCheckTime}; This does not exist -- must use the Check Time from the current status log ...
		    $cs_svc->{LastCheckTime} = $el_svc->{LastCheckTime};

		    if ( !defined $cs_svc->{Comments} ) {
			$cs_svc->{Comments} = ' ';
		    }
		    $cs_svc->{MonitorStatus} 	      = $fn_svc->{MonitorStatus};
		    $cs_svc->{CurrentAttempt}         = $fn_svc->{CurrentAttempt};
		    $cs_svc->{MaxAttempts}            = $fn_svc->{MaxAttempts};
		    $cs_svc->{NextCheckTime}          = $fn_svc->{NextCheckTime};
		    $cs_svc->{ScheduledDowntimeDepth} = $fn_svc->{ScheduledDowntimeDepth};
		    $cs_svc->{isAcceptPassiveChecks}  = $fn_svc->{isAcceptPassiveChecks};
		    $cs_svc->{isChecksEnabled}        = $fn_svc->{isChecksEnabled};
		    $cs_svc->{isEventHandlersEnabled} = $fn_svc->{isEventHandlersEnabled};
		    $cs_svc->{isFlapDetectionEnabled} = $fn_svc->{isFlapDetectionEnabled};
		    $cs_svc->{isNotificationsEnabled} = $fn_svc->{isNotificationsEnabled};
#		    $cs_svc->{isObsessOverService}    = $fn_svc->{isObsessOverService};
		    $cs_svc->{isProblemAcknowledged}  = $fn_svc->{isProblemAcknowledged};
#		    $cs_svc->{isServiceFlapping}      = $fn_svc->{isServiceFlapping};
		    $cs_svc->{LastPluginOutput}	      = $fn_svc->{LastPluginOutput};
	   	    $cs_svc->{PercentStateChange}     = $fn_svc->{PercentStateChange}; 
		    $cs_svc->{Latency}		      = $fn_svc->{Latency};
		    $cs_svc->{ExecutionTime}          = $fn_svc->{ExecutionTime};
		    $cs_svc->{LastStateChange}        = $fn_svc->{LastStateChange};
		    # Look for fancy MonitorStatus values and translate to the simple ones Nagios knows
                    if ( $fn_svc->{MonitorStatus} =~ /CRITICAL/ ) {
                        $cs_svc->{MonitorStatus} = 'CRITICAL';    # 
                    } elsif ( $fn_svc->{MonitorStatus} =~ /WARNING/ ) {
			    $cs_svc->{MonitorStatus} = 'WARNING';    #
		    }
		}
	    }
	}
    }
    return $collage_status_ref;
}
=cut
my $init_start_time = Time::HiRes::time();
freeze_logtime();
print LOG "${logtime}loading cached addresses ...\n";
#load_cached_addresses;
freeze_logtime();
print LOG "${logtime}loading global nagios parameters ...\n";
$global_nagios = get_globals( $statusfile );
freeze_logtime();
print LOG "${logtime}loading initial state ...\n";
#getInitialState($collage_status_ref);
$collage_heartbeat_ref = $collage_status_ref;

if ($debug) {
    my $init_time = sprintf "%0.4F", ( Time::HiRes::time() - $init_start_time );
    freeze_logtime();
    print               "Startup init time=$init_time seconds.\n";
    print LOG "${logtime}Startup init time=$init_time seconds.\n";
}

freeze_logtime();
print LOG "${logtime}starting main loop ...\n";

if ( $debug > 3 ) {
    freeze_logtime();
    print LOG $logtime . Data::Dumper->Dump( [ \%{$collage_status_ref} ], [qw(\%{collage_status_ref})] );
}

$total_wait      = 0;
$n_hostcount     = 0;
$n_servicecount  = 0;

my $next_sync_timeout = time + $sync_timeout_seconds;    # for xml batching

my $looping_start_time = Time::HiRes::time();
while (1) {
    my $start_time = Time::HiRes::time();
    if ( $debug > 0 ) {
	freeze_logtime();
	print LOG "${logtime}Starting cycle.\n";
    }

    $total_wait += $loop_wait_time;

    # Don't bother with this loop iteration if the input data hasn't changed since last time.
    my $statusfile_mtime = (stat($statusfile))[9];
    if ( !defined $statusfile_mtime ) {
	freeze_logtime();
	print               "Warning: stat of file $statusfile failed: $!\n";
	print LOG "${logtime}Warning: stat of file $statusfile failed: $!\n";
	sleep 10;
	exit 0;
    }
    elsif ($statusfile_mtime <= $last_statusfile_mtime) {
	print LOG "Skipping cycle -- $statusfile has not changed.\n";
    }
    else {
	$last_statusfile_mtime = $statusfile_mtime;

	if ( $total_wait >= $full_update_time ) {
	    $total_wait = 0;
	    if ($smart_update) {
		## Time to send heartbeat. That is, time to update LastUpdateTime stamps.
		$heartbeat_mode = 1;
		print LOG "Heartbeat in progress this cycle ...\n" if $debug > 0;
	    }
	}

	# Check count of hosts and services in Nagios and SMSDataModel
	#my $smsstack = CollageQuery->new();
	#$f_hostcount = $smsstack->getHostCount('NAGIOS');
        my $nohosts=`grep \"hoststatus {\" $statusfile | wc -l 2>/dev/null`;
        my $noservices=`grep \"servicestatus {\" $statusfile |wc -l 2>/dev/null`;
	chomp($nohosts);chomp($noservices);
	$f_hostcount = $nohosts;
	#print LOG "SMSDataModel Host Count: $f_hostcount\n" if $debug > 1;
	#$f_servicecount = $smsstack->getServiceCount('NAGIOS');
	$f_servicecount = $noservices;
	#print LOG "SMSDataModel Service Count: $f_servicecount\n" if $debug > 1;

	# Get the status and counts from Nagios
	$element_ref = get_status( $statusfile, $nagios_version );

	print "Nagios Host Count:DataModel Host Count $n_hostcount:$nohosts\n"       if $debug >= 1;
	print "Nagios Service Count:DataModel Service Count $n_servicecount:$noservices\n" if $debug >= 1;
	print LOG "Nagios Host Count: $n_hostcount\n"       if $debug > 1;
	print LOG "Nagios Service Count: $n_servicecount\n" if $debug > 1;
	if ( $loop_count eq 0 ) {    # first loop will not have last counts
	    $last_f_hostcount    = $f_hostcount;
	    $last_f_servicecount = $f_servicecount;
	    $last_n_hostcount    = $n_hostcount;
	    $last_n_servicecount = $n_servicecount;
	}

	# Now we can compare counts and see if Nagios and SMSDataModel are in sync
	if ( ( $f_hostcount ne $n_hostcount ) or ( $f_servicecount ne $n_servicecount ) ) {

	    # Nagios and SMSDataModel are not synced. Hold off on updates for a bit.
	    if ( $syncwaitcount >= $syncwait ) {

		# Tell the log about the differences that caused the sync errors
		if ( $debug > 0 ) {
		    my $deltas = find_deltas( $element_ref, $collage_status_ref );
		    if ( $f_hostcount ne $n_hostcount ) {
			print LOG "$f_hostcount hosts in SMSDataModel and $n_hostcount hosts in Nagios:\n";
		    }
		    if ( $f_servicecount ne $n_servicecount ) {
			print LOG "$f_servicecount services in SMSDataModel and $n_servicecount services in Nagios:\n";
		    }
		    print LOG "Hosts or services in SMSDataModel and not in Nagios:\n";
		    print LOG Data::Dumper->Dump( [ \%{ $deltas->{SMSDataModelHost} } ], [qw(SMSDataModel)] );
		    print LOG "Hosts or services in Nagios and not in SMSDataModel:\n";
		    print LOG Data::Dumper->Dump( [ \%{ $deltas->{NagiosHost} } ], [qw(Nagios)] );
		}
		$enable_feeding = 1;
		$syncwaitcount  = 0;
		if ( $loop_count != 0 ) {
		    freeze_logtime();
		    print LOG "${logtime}Out of sync for too long!! Please try commit again. Resuming feeding.\n";
		    if (
			( $send_sync_warning > 0 )
			and ( my $socket =
			    IO::Socket::INET->new( PeerAddr => $remote_host, PeerPort => $remote_port, Proto => "tcp", Type => SOCK_STREAM ) )
		      )
		    {
			$socket->autoflush();
			print $socket
    "<GENERICLOG consolidation='SYSTEM' ApplicationType='SYSTEM' MonitorServerName='localhost' Device='127.0.0.1' Severity='WARNING' MonitorStatus='WARNING' TextMessage='SMSDataModel and Nagios are out of sync. You may need to commit your Nagios configuration again. Check the log at /usr/local/ffm/nagios/var/nagios2cpfsmsdatamodel_socket.log for details. Nagios hosts: $n_hostcount, SMSDataModel hosts: $f_hostcount, Nagios services: $n_servicecount, SMSDataModel services: $f_servicecount.' />";
			close($socket);


        $nohosts=`grep "hoststatus {" $statusfile | wc -l 2>/dev/null`;
        $noservices=`grep "servicestatus {" $statusfile |wc -l 2>/dev/null`;
	chomp($nohosts);chomp($noservices);
			# Re-query SMSDataModel
			#$f_hostcount    = $smsstack->getHostCount('NAGIOS');
			$f_hostcount    = $nohosts;
			#$f_servicecount = $smsstack->getServiceCount('NAGIOS');
			$f_servicecount = $noservices;
		    }
		    else {
			print LOG "${logtime}Listener services not available.\n";
		    }
		}
	    }
	    else {
		$enable_feeding = 0;
		$syncwaitcount++;
		my $cycles_left = $syncwait - $syncwaitcount;
		freeze_logtime();
		print LOG "${logtime}Out of sync detected! Waiting on updates for up to $cycles_left more cycles ...\n";
	    }
	}
	else {
	    if (   ( $last_f_hostcount ne $f_hostcount )
		or ( $last_f_servicecount ne $f_servicecount )
		or ( $last_n_hostcount    ne $n_hostcount )
		or ( $last_n_servicecount ne $n_servicecount ) )
	    {
		## Case 1: Changed, but in sync. We missed the sync, so just re-start
		freeze_logtime();
		print LOG "${logtime}Changed, but in sync (missed sync). Restarting.\n";
		exit 0;
	    }
	}

	# Now reset the counts for next time
	$last_f_hostcount    = $f_hostcount;
	$last_f_servicecount = $f_servicecount;
	$last_n_hostcount    = $n_hostcount;
	$last_n_servicecount = $n_servicecount;
	$n_hostcount         = 0;
	$n_servicecount      = 0;
	my @host_updates;
	my @serv_updates;

	if ( $element_ref && $enable_feeding ) {
	    if ($heartbeat_mode) {
		$global_nagios = get_globals( $statusfile );
		@host_updates = @{ &build_host_xml( $thisnagios, $element_ref, $collage_heartbeat_ref ) };
		@serv_updates = @{ &build_service_xml( $thisnagios, $element_ref, $collage_heartbeat_ref ) };
	    }
	    else {
		@host_updates = @{ &build_host_xml( $thisnagios, $element_ref, $collage_status_ref ) };
		@serv_updates = @{ &build_service_xml( $thisnagios, $element_ref, $collage_status_ref ) };
	    }
	    push( @xml_messages, @host_updates );
	    push( @xml_messages, @serv_updates );

	    if ( @xml_messages >= $xml_bundle_size || ( @xml_messages > 0 && time >= $next_sync_timeout ) ) {

		$message_counter   = output_to_socket( \@xml_messages, $message_counter );
		@xml_messages      = ();
		$next_sync_timeout = time + $sync_timeout_seconds;

		$loop_count++;
		if ($debug) {
		    my $loop_time = sprintf "%0.4F", Time::HiRes::time() - $start_time;
		    my $avg_loop_time = sprintf "%0.4F",
		      ( Time::HiRes::time() - $looping_start_time - ( ( $loop_count - 1 ) * $loop_wait_time ) ) / $loop_count;
		    freeze_logtime();
		    print               "Loops Completed = $loop_count. Last loop time=$loop_time seconds. Avg loop time=$avg_loop_time seconds.\n";
		    print LOG "${logtime}Loops Completed = $loop_count. Last loop time=$loop_time seconds. Avg loop time=$avg_loop_time seconds.\n";
		}
	    }
	}

	# re-enable feeding ...
	$enable_feeding = 1;

	# exit after one run -- used for synch between Nagios and SMSDataModel at startup
	if ( $sync_at_start =~ /once/ ) {
	    freeze_logtime();
	    print LOG "${logtime}Exiting after one cycle, per command option.\n";
	    exit 0;
	}
	$heartbeat_mode = 0;
    }
    # Send any pending state transitions left in the buffer
    $max_event_bundle_size = 1;
    $message_counter = send_pending_events( $message_counter );
    $max_event_bundle_size = $default_max_event_bundle_size;
    sleep $loop_wait_time;
}

close LOG;

sub output_to_socket {
    my $msg_ref    = shift;
    my $series_num = shift;

    if ( my $socket = IO::Socket::INET->new( PeerAddr => $remote_host, PeerPort => $remote_port, Proto => "tcp", Type => SOCK_STREAM ) ) {
	$socket->autoflush();

	if (1) {
	    my $next          = 0;
	    my $last          = -1;
	    my $last_index    = $#$msg_ref;
	    my $element_begin = undef;
	    my $element_end   = "</Adapter>";
	    my $command_close = '<SERVICE-MAINTENANCE command="close" />';
	    while ( $next <= $last_index ) {
		$last = $next + $xml_bundle_max_size - 1;
		$last = $last_index if $last > $last_index;
		$element_begin =
		  qq(<Adapter Session="$series_num" AdapterType="SystemAdmin">\n);
		#print $socket join( '', $element_begin, @{$msg_ref}[ $next .. $last ], $element_end );
		print $socket join( '', @{$msg_ref}[ $next .. $last ] );
		print LOG     join( '', $element_begin, @{$msg_ref}[ $next .. $last ], $element_end, "\n" ) if ( $debug > 1 );

#if ( !open( LOG1, '>', '/tmp/ngout' ) ) {
#    print "Can't open logfile '$logfile'.\n";
#}
#		print LOG1 join( '',@{$msg_ref}[ $next .. $last ] ) if ($debug);
#close LOG1;
		$next = $last + 1;
		$series_num++;
	    }
	    #print $socket $command_close;
	    #print LOG "$command_close\n" if ( $debug > 1 );
	}
	else {
	    ## Legacy operation, now deprecated.
	    while (@$msg_ref) {
		my $element_begin =
		  qq(<Adapter Session="$series_num" AdapterType="SystemAdmin">\n<Command ApplicationType='NAGIOS' Action='MODIFY'>\n);
		my $element_end = "</Command>\n</Adapter>";
		#print $socket $element_begin;
		print LOG "$element_begin\n" if ( $debug > 1 );
		my $num_msgs_output = 0;
		while ( @$msg_ref && $num_msgs_output < $xml_bundle_max_size ) {
		    $num_msgs_output++;
		    my $message = shift( @{$msg_ref} );
		    print $socket $message;
		    print LOG    "$message\n" if ( $debug > 1 );
		}
		#print $socket $element_end;
		print LOG    "$element_end\n" if ( $debug > 1 );
		$series_num++;
	    }
	    CommandClose($socket);
	}
	close($socket);
    }
    else {
	freeze_logtime();
	## print LOG "${logtime}Couldn't connect to $remote_host:$remote_port : $!\n Exiting.";
	die "${logtime}Couldn't connect to $remote_host:$remote_port : $!\n";
    }
    return $series_num;
}

sub CommandClose {
    my $socket = shift;

    # Create XML stream -- Format:
    # <SERVICE-MAINTENANCE command="close" />
    my $xml_message = "<SERVICE-MAINTENANCE command=\"close\" />";

    print $xml_message."\n\n" if $debug;
    print $socket $xml_message;
    return;
}

sub get_status {
    my $statusfile = shift;
    my $version    = shift;
    if ( $version == 3 ) {
	return get_status_v3($statusfile);
    }
    elsif ( $version == 2 ) {
	return get_status_v2($statusfile);
    }
    elsif ( $version == 1 ) {
	return get_status_v1($statusfile);
    }
    else {
	die "$0 error: unknown Nagios version: [$version]\n";
    }
}

=head
sub get_status_v1 {
    my $statusfile = shift;
    my ( $timestamp, $msgtype );
    my @field;
    my $element_ref;

    # FIX THIS:  don't just abort on failure; retry 3 times or so
    -if ( !open( STATUSFILE, '<:mmap', $statusfile ) ) {
	freeze_logtime();
	print               "Error opening file $statusfile: $!\n";
	print LOG "${logtime}Error opening file $statusfile: $!\n";
	return 0;
    }
    while ( my $line = <STATUSFILE> ) {

# [1100304091] HOST;Application_1;UP;1100304086;1100280796;0;7462261;6887;36466;1100280796;0;1;1;1;1;0;0.00;0;1;1;PING OK - Packet loss = 0%, RTA = 25.22 ms
	if ( $line =~ /^\s*\#]/ ) { next; }
	@field = split /;/, $line;
	if ( $field[0] =~ /\[(\d+)\] (.*)/ ) {
	    $timestamp = $1;
	    $msgtype   = $2;
	}
	else {
	    next;
	}

	# Use Collage database field names as service keys
	my $el_host = \%{ $element_ref->{Host}->{ $field[1] } };
	if ( $msgtype =~ /SERVICE/ ) {
	    my $el_svc = \%{ $el_host->{Service}->{ $field[2] } };

	    if ( $field[6] == 0 )  { $field[6]  = time; }
	    if ( $field[12] == 0 ) { $field[12] = time; }
	    $field[31] =~ s/\n/ /g;
	    $field[31] =~ s/\f/ /g;
	    $field[31] =~ s/<br>/ /ig;
	    $field[31] =~ s/&/&amp;/g;
	    $field[31] =~ s/"/&quot;/g;
	    $field[31] =~ s/'/&apos;/g;
	    $field[31] =~ s/</&lt;/g;
	    $field[31] =~ s/>/&gt;/g;

	    # $el_svc->{RetryNumber} = '1'; #$field[4];
	    my $tmp = $field[4];
	    if ( $tmp =~ /(\d+)\/(\d+)/ ) {
		my $RetryNumber = $1;
		my $MaxTry      = $2;
		$el_svc->{RetryNumber} = $RetryNumber;
	    }
	    $el_svc->{MonitorStatus}              = $field[3];
	    $el_svc->{StateType}                  = $field[5];
	    $el_svc->{LastCheckTime}              = time_text( $field[6] );
	    $el_svc->{NextCheckTime}              = time_text( $field[7] );
	    $el_svc->{CheckType}                  = $field[8];
	    $el_svc->{isChecksEnabled}            = $field[9];
	    $el_svc->{isAcceptPassiveChecks}      = $field[10];
	    $el_svc->{isEventHandlersEnabled}     = $field[11];
	    $el_svc->{LastStateChange}            = time_text( $field[12] );
	    $el_svc->{isProblemAcknowledged}      = $field[13];
	    $el_svc->{LastHardState}              = $field[14];
	    $el_svc->{TimeOK}                     = $field[15];
	    $el_svc->{TimeUnknown}                = $field[16];
	    $el_svc->{TimeWarning}                = $field[17];
	    $el_svc->{TimeCritical}               = $field[18];
	    $el_svc->{LastNotificationTime}       = time_text( $field[19] );
	    $el_svc->{CurrentNotificationNumber}  = $field[20];
	    $el_svc->{isNotificationsEnabled}     = $field[21];
	    $el_svc->{Latency}                    = $field[22];
	    $el_svc->{ExecutionTime}              = $field[23];
	    $el_svc->{isFlapDetectionEnabled}     = $field[24];
	    $el_svc->{isServiceFlapping}          = $field[25];
	    $el_svc->{PercentStateChange}         = $field[26];
	    $el_svc->{ScheduledDowntimeDepth}     = $field[27];
	    $el_svc->{isFailurePredictionEnabled} = $field[28];
	    $el_svc->{isProcessPerformanceData}   = $field[29];
	    $el_svc->{isObsessOverService}        = $field[30];
	    $el_svc->{LastPluginOutput}           = $field[31];
	}
	elsif ( $msgtype =~ /HOST/ ) {
	    if ( $field[3] == 0 ) { $field[3] = time; }
	    if ( $field[4] == 0 ) { $field[4] = time; }
	    $field[20] =~ s/\n/ /g;
	    $field[20] =~ s/\f/ /g;
	    $field[20] =~ s/<br>/ /ig;
	    $field[20] =~ s/&/&amp;/g;
	    $field[20] =~ s/"/&quot;/g;
	    $field[20] =~ s/'/&apos;/g;
	    $field[20] =~ s/</&lt;/g;
	    $field[20] =~ s/>/&gt;/g;
	    $el_host->{MonitorStatus}              = $field[2];
	    $el_host->{LastCheckTime}              = time_text( $field[3] );
	    $el_host->{LastStateChange}            = time_text( $field[4] );
	    $el_host->{isAcknowledged}             = $field[5];
	    $el_host->{TimeUp}                     = $field[6];
	    $el_host->{TimeDown}                   = $field[7];
	    $el_host->{TimeUnreachable}            = $field[8];
	    $el_host->{LastNotificationTime}       = time_text( $field[9] );
	    $el_host->{CurrentNotificationNumber}  = $field[10];
	    $el_host->{isNotificationsEnabled}     = $field[11];
	    $el_host->{isEventHandlersEnabled}     = $field[12];
	    $el_host->{isChecksEnabled}            = $field[13];
	    $el_host->{isFlapDetectionEnabled}     = $field[14];
	    $el_host->{isHostIsFlapping}           = $field[15];
	    $el_host->{PercentStateChange}         = $field[16];
	    $el_host->{ScheduledDowntimeDepth}     = $field[17];
	    $el_host->{isFailurePredictionEnabled} = $field[18];
	    $el_host->{isProcessPerformanceData}   = $field[19];
	    $el_host->{LastPluginOutput}           = $field[20];
	}
	elsif ( $msgtype =~ /PROGRAM/ ) {
	}
    }
    close STATUSFILE;
    return $element_ref;
}

sub get_status_v2 {
    my $statusfile = shift;
    my ( $timestamp, $msgtype );
    my @field;
    my $element_ref;

    # FIX THIS:  don't just abort on failure; retry 3 times or so
    if ( !open( STATUSFILE, '<:mmap', $statusfile ) ) {
	freeze_logtime();
	print               "Error opening file $statusfile: $!\n";
	print LOG "${logtime}Error opening file $statusfile: $!\n";
	return 0;
    }
    my $state     = undef;
    my %attribute = ();
    while ( my $line = <STATUSFILE> ) {
	chomp $line;
	if ( $line =~ /^\s*\#]/ ) { next; }
	if ( !$state and ( $line =~ /\s*host \{/ ) ) {
	    $state = "Host";
	    next;
	}
	elsif ( !$state and ( $line =~ /\s*service \{/ ) ) {
	    $state = "Service";
	    next;
	}
	elsif ( ( $state eq "Service" ) and ( $line =~ /^\s*\}/ ) and $attribute{host_name} and $attribute{service_description} ) {
	    my $el_svc = \%{ $element_ref->{Host}->{ $attribute{host_name} }->{Service}->{ $attribute{service_description} } };
	    if ( ( $attribute{last_check} == 0 ) and ( $attribute{has_been_checked} == 0 ) ) {
		## $attribute{last_check} = time;
		#$el_svc->{MonitorStatus} = "PENDING";
		$el_svc->{MonitorStatus} = "UNKNOWN";
	    }
	    else {
		$el_svc->{MonitorStatus} = $ServiceStatus{ $attribute{current_state} };
	    }

	    # Set element hash
	    # Map Nagios V2 status parameters to Nagios V1 definitions in Collage
	    $el_svc->{StateType}   = $StateType{ $attribute{state_type} };
	    $el_svc->{RetryNumber} = $attribute{current_attempt};

	    ## if ($attribute{last_check} == 0) { $attribute{last_check} = time;	}

	    $attribute{plugin_output} =~ s/\n/ /g;
	    $attribute{plugin_output} =~ s/\f/ /g;
	    $attribute{plugin_output} =~ s/<br>/ /ig;
	    $attribute{plugin_output} =~ s/&/&amp;/g;
	    $attribute{plugin_output} =~ s/"/&quot;/g;
	    $attribute{plugin_output} =~ s/'/&apos;/g;
	    $attribute{plugin_output} =~ s/</&lt;/g;
	    $attribute{plugin_output} =~ s/>/&gt;/g;

	    if ( $attribute{last_state_change} == 0 ) { $attribute{last_state_change} = time; }
	    ## Collage expects latency in integer. Set to ms
	    $attribute{check_latency} = int( 1000 * $attribute{check_latency} );
	    ## Collage expects execution time in integer. Set to ms
	    $attribute{check_execution_time} = int( 1000 * $attribute{check_execution_time} );

	    $el_svc->{CheckType}                  = $CheckType{ $attribute{check_type} };
	    $el_svc->{CurrentNotificationNumber}  = $attribute{current_notification_number};
	    $el_svc->{ExecutionTime}              = $attribute{check_execution_time};
	    $el_svc->{LastCheckTime}              = time_text( $attribute{last_check} );
	    $el_svc->{LastHardState}              = $ServiceStatus{ $attribute{last_hard_state} };
	    $el_svc->{LastNotificationTime}       = time_text( $attribute{last_notification} );
	    $el_svc->{LastPluginOutput}           = $attribute{plugin_output};
	    $el_svc->{LastStateChange}            = time_text( $attribute{last_state_change} );
	    $el_svc->{Latency}                    = $attribute{check_latency};
	    $el_svc->{NextCheckTime}              = time_text( $attribute{next_check} );
	    $el_svc->{PercentStateChange}         = $attribute{percent_state_change};
	    $el_svc->{ScheduledDowntimeDepth}     = $attribute{scheduled_downtime_depth};
	    $el_svc->{TimeCritical}               = $attribute{last_time_critical};
	    $el_svc->{TimeOK}                     = $attribute{last_time_ok};
	    $el_svc->{TimeUnknown}                = $attribute{last_time_unknown};
	    $el_svc->{TimeWarning}                = $attribute{last_time_warning};
	    $el_svc->{isAcceptPassiveChecks}      = $attribute{passive_checks_enabled};
	    $el_svc->{isChecksEnabled}            = $attribute{active_checks_enabled};
	    $el_svc->{isEventHandlersEnabled}     = $attribute{event_handler_enabled};
	    $el_svc->{isFailurePredictionEnabled} = $attribute{failure_prediction_enabled};
	    $el_svc->{isFlapDetectionEnabled}     = $attribute{flap_detection_enabled};
	    $el_svc->{isNotificationsEnabled}     = $attribute{notifications_enabled};
	    $el_svc->{isObsessOverService}        = $attribute{obsess_over_service};
	    $el_svc->{isProblemAcknowledged}      = $attribute{problem_has_been_acknowledged};
	    $el_svc->{isProcessPerformanceData}   = $attribute{process_performance_data};
	    $el_svc->{isServiceFlapping}          = $attribute{is_flapping};

	    # reset variables for next object
	    $state     = undef;
	    %attribute = ();
	    next;
	}
	elsif ( ( $state eq "Host" ) and ( $line =~ /\s*\}/ ) and $attribute{host_name} ) {
	    my $el_host = \%{ $element_ref->{Host}->{ $attribute{host_name} } };

	    $attribute{plugin_output} =~ s/\n/ /g;
	    $attribute{plugin_output} =~ s/\f/ /g;
	    $attribute{plugin_output} =~ s/<br>/ /ig;
	    $attribute{plugin_output} =~ s/&/&amp;/g;
	    $attribute{plugin_output} =~ s/"/&quot;/g;
	    $attribute{plugin_output} =~ s/'/&apos;/g;
	    $attribute{plugin_output} =~ s/</&lt;/g;
	    $attribute{plugin_output} =~ s/>/&gt;/g;

	    if ( ( $attribute{last_check} == 0 ) and ( $attribute{has_been_checked} == 0 ) ) {
		## $attribute{last_check} = time;
		#$el_host->{MonitorStatus} = "PENDING";
		$el_host->{MonitorStatus} = "UNKNOWN";
	    }
	    else {
		$el_host->{MonitorStatus} = $HostStatus{ $attribute{current_state} };
	    }

	    if ( $attribute{last_state_change} == 0 ) { $attribute{last_state_change} = time; }

	    $el_host->{CheckType}                  = $CheckType{ $attribute{check_type} };
	    $el_host->{CurrentNotificationNumber}  = $attribute{current_notification_number};
	    $el_host->{LastCheckTime}              = time_text( $attribute{last_check} );
	    $el_host->{LastNotificationTime}       = time_text( $attribute{last_notification} );
	    $el_host->{LastPluginOutput}           = $attribute{plugin_output};
	    $el_host->{LastStateChange}            = time_text( $attribute{last_state_change} );
	    $el_host->{PercentStateChange}         = $attribute{percent_state_change};
	    $el_host->{ScheduledDowntimeDepth}     = $attribute{scheduled_downtime_depth};
	    $el_host->{TimeDown}                   = $attribute{last_time_down};
	    $el_host->{TimeUnreachable}            = $attribute{last_time_unreachable};
	    $el_host->{TimeUp}                     = $attribute{last_time_up};
	    $el_host->{isAcknowledged}             = $attribute{problem_has_been_acknowledged};
	    $el_host->{isChecksEnabled}            = $attribute{active_checks_enabled};
	    $el_host->{isEventHandlersEnabled}     = $attribute{event_handler_enabled};
	    $el_host->{isFailurePredictionEnabled} = $attribute{failure_prediction_enabled};
	    $el_host->{isFlapDetectionEnabled}     = $attribute{flap_detection_enabled};
	    $el_host->{isHostFlapping}             = $attribute{is_flapping};
	    $el_host->{isNotificationsEnabled}     = $attribute{notifications_enabled};
	    $el_host->{isPassiveChecksEnabled}     = $attribute{passive_checks_enabled};
	    $el_host->{isProcessPerformanceData}   = $attribute{process_performance_data};

	    # reset variables for next object
	    $state     = undef;
	    %attribute = ();
	    next;
	}
	if ( $state and ( $line =~ /\s*(\S+?)=(.*)/ ) ) {
	    if ( $2 ne "" ) {
		$attribute{$1} = $2;
	    }
	}
	else { next; }
    }
    close STATUSFILE;
    return $element_ref;
}
=cut
sub get_status_v3 {
    my $statusfile = shift;
    my ( $timestamp, $msgtype );
    my @field;
    my $element_ref;

    # FIX THIS:  don't just abort on failure; retry 3 times or so
    if ( !open( STATUSFILE, '<:mmap', $statusfile ) ) {
	freeze_logtime();
	print               "Error opening file $statusfile: $!\n";
	print LOG "${logtime}Error opening file $statusfile: $!\n";

	#return 0;
	sleep 10;
	exit 0;
    }
    my $state          = undef;
    my $hostcomment    = undef;
    my $servicecomment = undef;
    my %attribute      = ();
    while ( my $line = <STATUSFILE> ) {
	chomp $line;
	if ( $line =~ /^\s*\#]/ ) { next; }
	if ( !$state and ( $line =~ /\s*host(?:status)?\s*\{/ ) ) {
	    $state = "Host";
	    $n_hostcount++;
	    next;
	}
	elsif ( !$state and ( $line =~ /\s*service(?:status)?\s*\{/ ) ) {
	    $state = "Service";
	    $n_servicecount++;
	    next;
	}
	elsif ( ( $state eq "Service" ) and ( $line =~ /^\s*\}/ ) and $attribute{host_name} and $attribute{service_description} ) {
	    my $el_svc = \%{ $element_ref->{Host}->{ $attribute{host_name} }->{Service}->{ $attribute{service_description} } };

	    # Check for pending service status
	    if ( ( $attribute{last_check} == 0 ) and ( $attribute{has_been_checked} == 0 ) ) {
		#$el_svc->{MonitorStatus} = "PENDING";
		$el_svc->{MonitorStatus} = "UNKNOWN";
	    }
	    else {
		$el_svc->{MonitorStatus} = $ServiceStatus{ $attribute{current_state} };
	    }

	    $attribute{plugin_output} =~ s/\n/ /g;
	    $attribute{plugin_output} =~ s/\f/ /g;
	    $attribute{plugin_output} =~ s/<br>/ /ig;
	    $attribute{plugin_output} =~ s/&/&amp;/g;
	    $attribute{plugin_output} =~ s/"/&quot;/g;
	    $attribute{plugin_output} =~ s/'/&apos;/g;
	    $attribute{plugin_output} =~ s/</&lt;/g;
	    $attribute{plugin_output} =~ s/>/&gt;/g;

	    $attribute{long_plugin_output} =~ s/\\n/ /g;
	    $attribute{long_plugin_output} =~ s/\f/ /g;
	    $attribute{long_plugin_output} =~ s/<br>/ /ig;
	    $attribute{long_plugin_output} =~ s/&/&amp;/g;
	    $attribute{long_plugin_output} =~ s/"/&quot;/g;
	    $attribute{long_plugin_output} =~ s/'/&apos;/g;
	    $attribute{long_plugin_output} =~ s/</&lt;/g;
	    $attribute{long_plugin_output} =~ s/>/&gt;/g;

	    if ( $attribute{last_state_change} == 0 ) { $attribute{last_state_change} = time; }
	    ## Collage expects latency in integer. Set to ms
	    $attribute{check_latency} = int( 1000 * $attribute{check_latency} );
	    ## Collage expects execution time in integer. Set to ms
	    $attribute{check_execution_time} = int( 1000 * $attribute{check_execution_time} );

	    # Set element hash
	    # Map Nagios V2 status parameters to Nagios V1 definitions in Collage
	    $el_svc->{CheckType}                  = $CheckType{ $attribute{check_type} };
	    $el_svc->{CurrentAttempt}             = $attribute{current_attempt};
	    $el_svc->{CurrentNotificationNumber}  = $attribute{current_notification_number};
	    $el_svc->{ExecutionTime}              = $attribute{check_execution_time};
	    $el_svc->{LastCheckTime}              = time_text( $attribute{last_check} );
	    $el_svc->{LastHardState}              = $ServiceStatus{ $attribute{last_hard_state} };
	    $el_svc->{LastNotificationTime}       = time_text( $attribute{last_notification} );
	    $el_svc->{LastPluginOutput}           = $attribute{plugin_output}." "."$attribute{long_plugin_output}";
	    $el_svc->{LastStateChange}            = time_text( $attribute{last_state_change} );
	    $el_svc->{Latency}                    = $attribute{check_latency};
	    $el_svc->{MaxAttempts}                = $attribute{max_attempts};
	    $el_svc->{NextCheckTime}              = time_text( $attribute{next_check} );
	    $el_svc->{PercentStateChange}         = $attribute{percent_state_change};
	    $el_svc->{RetryNumber}                = $attribute{current_attempt};
	    $el_svc->{ScheduledDowntimeDepth}     = $attribute{scheduled_downtime_depth};
	    $el_svc->{StateType}                  = $StateType{ $attribute{state_type} };
	    $el_svc->{TimeCritical}               = $attribute{last_time_critical};
	    $el_svc->{TimeOK}                     = $attribute{last_time_ok};
	    $el_svc->{TimeUnknown}                = $attribute{last_time_unknown};
	    $el_svc->{TimeWarning}                = $attribute{last_time_warning};
	    $el_svc->{isAcceptPassiveChecks}      = $attribute{passive_checks_enabled};
	    $el_svc->{isChecksEnabled}            = $attribute{active_checks_enabled};
	    $el_svc->{isEventHandlersEnabled}     = $attribute{event_handler_enabled};
	    $el_svc->{isFailurePredictionEnabled} = $attribute{failure_prediction_enabled};
	    $el_svc->{isFlapDetectionEnabled}     = $attribute{flap_detection_enabled};
	    $el_svc->{isNotificationsEnabled}     = $attribute{notifications_enabled};
	    $el_svc->{isObsessOverService}        = $attribute{obsess_over_service};
	    $el_svc->{isProblemAcknowledged}      = $attribute{problem_has_been_acknowledged};
	    $el_svc->{isProcessPerformanceData}   = $attribute{process_performance_data};
	    $el_svc->{isServiceFlapping}          = $attribute{is_flapping};
	    # Use global values to overide where needed
 	    if ( $global_nagios->{obsess_over_services} == 0 ) {
                 $el_svc->{isObsessOverService} = 0;
            }
	    # Notifications
            if ( $global_nagios->{enable_notifications} == 0 ) {
                 $el_svc->{isNotificationsEnabled} = 0;
            }
            #Active Checks
            if ( $global_nagios->{active_service_checks_enabled} == 0 ) {
                 $el_svc->{isChecksEnabled} = 0;
            }
            #Passive Checks
            if ( $global_nagios->{passive_service_checks_enabled} == 0 ) {
                 $el_svc->{isAcceptPassiveChecks} = 0;
            }
            #Flap Detection
            if ( $global_nagios->{enable_flap_detection} == 0 ) {
                 $el_svc->{isFlapDetectionEnabled} = 0;
            }
            #Event Handlers
            if ( $global_nagios->{enable_event_handlers} == 0 ) {
                 $el_svc->{isEventHandlersEnabled} = 0;
            } 
	    # reset variables for next object
	    $state     = undef;
	    %attribute = ();
	    next;
	}
	elsif ( ( $state eq "Host" ) and ( $line =~ /\s*\}/ ) and $attribute{host_name} ) {
	    my $el_host = \%{ $element_ref->{Host}->{ $attribute{host_name} } };

	    $attribute{plugin_output} =~ s/\n/ /g;
	    $attribute{plugin_output} =~ s/\f/ /g;
	    $attribute{plugin_output} =~ s/<br>/ /ig;
	    $attribute{plugin_output} =~ s/&/&amp;/g;
	    $attribute{plugin_output} =~ s/"/&quot;/g;
	    $attribute{plugin_output} =~ s/'/&apos;/g;
	    $attribute{plugin_output} =~ s/</&lt;/g;
	    $attribute{plugin_output} =~ s/>/&gt;/g;

	    if ( ( $attribute{last_check} == 0 ) and ( $attribute{has_been_checked} == 0 ) ) {
		## $attribute{last_check} = time;
		$el_host->{MonitorStatus} = "PENDING";
	    }
	    else {
		$el_host->{MonitorStatus} = $HostStatus{ $attribute{current_state} };
	    }

	    if ( $attribute{last_state_change} == 0 ) { $attribute{last_state_change} = time; }
	    ## Collage expects latency in integer. Set to ms
	    $attribute{check_latency} = int( 1000 * $attribute{check_latency} );
	    ## Collage expects execution time in integer. Set to ms
	    $attribute{check_execution_time} = int( 1000 * $attribute{check_execution_time} );

	    $el_host->{CheckType}                  = $CheckType{ $attribute{check_type} };
	    $el_host->{CurrentAttempt}             = $attribute{current_attempt};
	    $el_host->{CurrentNotificationNumber}  = $attribute{current_notification_number};
	    $el_host->{ExecutionTime}              = $attribute{check_execution_time};
	    $el_host->{LastCheckTime}              = time_text( $attribute{last_check} );
	    $el_host->{LastNotificationTime}       = time_text( $attribute{last_notification} );
	    $el_host->{LastPluginOutput}           = $attribute{plugin_output};
	    $el_host->{LastStateChange}            = time_text( $attribute{last_state_change} );
	    $el_host->{Latency}                    = $attribute{check_latency};
	    $el_host->{MaxAttempts}                = $attribute{max_attempts};
	    $el_host->{NextCheckTime}              = time_text( $attribute{next_check} );
	    $el_host->{PercentStateChange}         = $attribute{percent_state_change};
	    $el_host->{ScheduledDowntimeDepth}     = $attribute{scheduled_downtime_depth};
	    $el_host->{StateType}                  = $StateType{ $attribute{state_type} };
	    $el_host->{TimeDown}                   = $attribute{last_time_down};
	    $el_host->{TimeUnreachable}            = $attribute{last_time_unreachable};
	    $el_host->{TimeUp}                     = $attribute{last_time_up};
	    $el_host->{isAcknowledged}             = $attribute{problem_has_been_acknowledged};
	    $el_host->{isChecksEnabled}            = $attribute{active_checks_enabled};
	    $el_host->{isEventHandlersEnabled}     = $attribute{event_handler_enabled};
	    $el_host->{isFailurePredictionEnabled} = $attribute{failure_prediction_enabled};
	    $el_host->{isFlapDetectionEnabled}     = $attribute{flap_detection_enabled};
	    $el_host->{isHostFlapping}             = $attribute{is_flapping};
	    $el_host->{isNotificationsEnabled}     = $attribute{notifications_enabled};
	    $el_host->{isObsessOverHost}           = $attribute{obsess_over_host};
	    $el_host->{isPassiveChecksEnabled}     = $attribute{passive_checks_enabled};
	    $el_host->{isProcessPerformanceData}   = $attribute{process_performance_data};
	    # Use global values where needed
	    # Obsession
 	    if ( $global_nagios->{obsess_over_hosts} == 0 ) {
                $el_host->{isObsessOverHost} = 0;
            }
            # Notifications
            if ( $global_nagios->{enable_notifications} == 0 ) {
                 $el_host->{isNotificationsEnabled} = 0;
            }
            #Active Checks
            if ( $global_nagios->{active_host_checks_enabled} == 0 ) {
                 $el_host->{isChecksEnabled} = 0;
            }
            #Passive Checks
            if ( $global_nagios->{passive_host_checks_enabled} == 0 ) {
                 $el_host->{isPassiveChecksEnabled} = 0;
            }
            #Flap Detection
            if ( $global_nagios->{enable_flap_detection} == 0 ) {
                 $el_host->{isFlapDetectionEnabled} = 0; 
            }
            #Event Handlers
            if ( $global_nagios->{enable_event_handlers} == 0 ) {
                 $el_host->{isEventHandlersEnabled} = 0; 
            }
	    # reset variables for next object
	    $state     = undef;
	    %attribute = ();
	    next;
	}
	if ( $state and ( $line =~ /\s*(\S+?)=(.*)/ ) ) {
	    if ( $2 ne "" ) {
		$attribute{$1} = $2;
	    }
	}
	if ( $line =~ /\s*hostcomment\s*\{/ ) {
	    $hostcomment = 1;
	    next;
	}
	elsif ( $line =~ /\s*servicecomment\s*\{/ ) {
	    $servicecomment = 1;
	    next;
	}
	elsif ( $hostcomment and ( $line =~ /\s*(\S+?)=(.*)/ ) ) {
	    if ( $2 ne "" ) {
		$attribute{$1} = $2;
	    }
	}
	elsif ( $hostcomment and ( $line =~ /\s*\}/ ) and $attribute{host_name} ) {
	    ## Assign host comment attributes
	    my ( $sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst ) = localtime( $attribute{entry_time} );
	    my $entrytime = sprintf "%02d-%02d-%4d %02d:%02d:%02d", $mon + 1, $mday, $year + 1900, $hour, $min, $sec;
	    $attribute{comment_data} =~ s/'//g;
	    $attribute{comment_data} =~ s/"//g;
	    ## FIX THIS:  use a shorter reference chain here?
	    $element_ref->{Host}->{ $attribute{host_name} }->{Comments} .=
	      "#$attribute{comment_id},$entrytime,$attribute{author},\'$attribute{comment_data}\'";
	    $hostcomment = undef;
	}
	elsif ( $servicecomment and ( $line =~ /\s*(\S+?)=(.*)/ ) ) {
	    if ( $2 ne "" ) {
		$attribute{$1} = $2;
	    }
	}
	elsif ( $servicecomment and ( $line =~ /\s*\}/ ) and $attribute{host_name} ) {
	    ## Assign service comment attributes
	    my ( $sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst ) = localtime( $attribute{entry_time} );
	    my $entrytime = sprintf "%02d-%02d-%4d %02d:%02d:%02d", $mon + 1, $mday, $year + 1900, $hour, $min, $sec;
	    $attribute{comment_data} =~ s/'//g;
	    $attribute{comment_data} =~ s/"//g;
	    ## FIX THIS:  use a shorter reference chain here?
	    $element_ref->{Host}->{ $attribute{host_name} }->{Service}->{ $attribute{service_description} }->{Comments} .=
	      "#$attribute{comment_id},$entrytime,$attribute{author},\'$attribute{comment_data}\'";
	    $servicecomment = undef;
	}
	else { next; }
    }
    close STATUSFILE;

    # Fix all the comments (once)
    my $comment = undef;
    foreach my $hostkey ( keys( %{ $element_ref->{Host} } ) ) {
	my $el_host = \%{ $element_ref->{Host}->{$hostkey} };
	$comment = $el_host->{Comments};
	if ( defined $comment ) {
	    $comment =~ s/\n/ /g;
	    $comment =~ s/\f/ /g;
	    $comment =~ s/<br>/ /ig;
	    $comment =~ s/&/&amp;/g;
	    $comment =~ s/"/&quot;/g;
	    $comment =~ s/'/&apos;/g;
	    $comment =~ s/</&lt;/g;
	    $comment =~ s/>/&gt;/g;
	    $el_host->{Comments} = $comment;
	    print LOG "*** Host Comments for host $hostkey: $comment\n" if $debug > 2;
	}
	else {
	    $el_host->{Comments} = ' ';
	}
	foreach my $servicekey ( keys( %{ $el_host->{Service} } ) ) {
	    my $el_svc = \%{ $el_host->{Service}->{$servicekey} };
	    $comment = $el_svc->{Comments};
	    if ( defined $comment ) {
		$comment =~ s/\n/ /g;
		$comment =~ s/\f/ /g;
		$comment =~ s/<br>/ /ig;
		$comment =~ s/&/&amp;/g;
		$comment =~ s/"/&quot;/g;
		$comment =~ s/'/&apos;/g;
		$comment =~ s/</&lt;/g;
		$comment =~ s/>/&gt;/g;
		$el_svc->{Comments} = $comment;
		print LOG "*** Service Comments for host $hostkey, service $servicekey: $comment\n" if $debug > 2;
	    }
	    else {
		$el_svc->{Comments} = ' ';
	    }
	}
    }
    return $element_ref;
}


sub get_globals {
    my $statusfile = shift;
    my ( $timestamp, $msgtype );
    my @field;

    # FIX THIS:  don't just abort on failure; retry 3 times or so
    if ( !open( STATUSFILE, '<:mmap', $statusfile ) ) {
        freeze_logtime();
        print               "Error opening file $statusfile: $!\n";
        print LOG "${logtime}Error opening file $statusfile: $!\n";

        #return 0;
        sleep 10;
        exit 0;
    }
    my $state          = undef;
    my $attribute      = ();
    while ( my $line = <STATUSFILE> ) {
        chomp $line;
        if ( $line =~ /^\s*\#]/ ) { next; }
        if ( !$state and ( $line =~ /\s*program(?:status)?\s*\{/ ) ) {
            $state = "Global";
            next;
        }
        if ( $state and ( $line =~ /\s*(\S+?)=(.*)/ ) ) {
            if ( $2 ne "" ) {
                $attribute->{$1} = $2;
		print LOG "Global Attribute found: $1 = $2\n" if $debug > 2;
            }
        }  # Reading the globals in...
	if ( $state and $line =~ /\s*\}/ ) {
	        # we are done reading globals  
                last;
        }    
    }
    close STATUSFILE;
    return $attribute;
}

sub freeze_logtime {
    $logtime = '[' . ( scalar localtime ) . '] ';
}

sub time_text {
    my $timestamp = shift;
    if ( $timestamp <= 0 ) {
	return "0";
    }
    else {
	my ( $seconds, $minutes, $hours, $day_of_month, $month, $year, $wday, $yday, $isdst ) = localtime($timestamp);
	return sprintf "%02d-%02d-%02d %02d:%02d:%02d", $year + 1900, $month + 1, $day_of_month, $hours, $minutes, $seconds;
    }
}

sub build_host_xml {
    my $thisnagios         = shift;
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $insertcount        = 0;
    my $skipcount          = 0;
    my @output             = ();
    my %HostStatusCodes    = ( "2" => "UP", "4" => "DOWN", "8" => "UNREACHABLE" );

    # Create XML stream -- Format:
    # <{SERVICE_STATUS | HOST_STATUS | LOG_MESSAGE} database field=value | database field=value | ... />
    # <HOST_STATUS  database field=value | database field=value | ... />

    foreach my $hostkey ( keys %{ $element_ref->{Host} } ) {

	# if no host status change then don't send
	my $host_xml = '';
	if ( $smart_update ) {
	    $host_xml = hostStatusChangeXML( $element_ref, $collage_status_ref, $hostkey );
	    if ( !$host_xml ) {
		$skipcount++;
		next;
	    }
	}

	my @xml_message = ();
	push @xml_message, '<Host ';

	# default identification -- set to IP address if known
	push @xml_message, "MonitorServerName=\"$thisnagios\" ";

	# default identification -- set to IP address if known
	push @xml_message, "Host=\"$hostkey\" ";

	# Monarch Sync now sets the IP as Identification. We should use address field from Monarch, whatever that is.
	# It's possible that the address changed, or that we are feeding a result for a host that
	# was not in Monarch when this program started. If the Identification is blank, reload the cache.
	if ( $hostipaddress{$hostkey} ) {
	    ## Set Device to IP
	    push @xml_message, "Device=\"$hostipaddress{$hostkey}\" ";

	    # push @xml_message, "Device=\"$hostkey\" ";
	}
	else {
	    ## For some reason we don't know the IP. Might be a new host? Anyway, reload and try one time more.
	    #load_cached_addresses;
	    if ( $hostipaddress{$hostkey} ) {
		## Set Device to IP
		push @xml_message, "Device=\"$hostipaddress{$hostkey}\" ";
	    }
	    else {
		## bail out and set Device = hostname. There is something wrong with the local Monarch DB.
		push @xml_message, "Device=\"$hostkey\" ";
	    }
	}
	if ( $smart_update ) {
	    push @xml_message, $host_xml;
	}
	else {
	    my $el_host = $element_ref->{Host}->{$hostkey};
	    foreach my $field ( keys %{ $el_host } ) {
		if ( $field eq "Service" ) { next }    # skip the Service hash key
		my $tmpinfo = $el_host->{$field};
		$tmpinfo =~ s/"/'/g;
		push @xml_message, "$field=\"$tmpinfo\" ";
	    }
	}
	push @xml_message, "/>\n";

	push( @output, join( '', @xml_message ) );
	if ($smart_update) {
	    hostStatusUpdate( $element_ref, $collage_status_ref, $hostkey );
	}
	$insertcount++;
	if ( ( $insertcount % 100 ) == 0 ) {
	    print     "Queueing hosts for insert, count=$insertcount\n" if $debug;
	    print LOG "Queueing hosts for insert, count=$insertcount\n" if $debug;
	}
    }
    if ($smart_update) {
	print     "Total Hosts Queued for Insert Count=$insertcount. No status change for $skipcount hosts.\n" if $debug;
	print LOG "Total Hosts Queued for Insert Count=$insertcount. No status change for $skipcount hosts.\n" if $debug;
    }
    else {
	print     "Total Hosts Queued for Insert Count=$insertcount.\n" if $debug;
	print LOG "Total Hosts Queued for Insert Count=$insertcount.\n" if $debug;
    }
    return \@output;
}

sub build_service_xml {
    my $thisnagios         = shift;
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $insertcount        = 0;
    my $skipcount          = 0;
    my @output             = ();

    # Create XML stream -- Format:
    # <{SERVICE_STATUS | HOST_STATUS | LOG_MESSAGE} database field=value | database field=value | ... />
    # <SERVICE_STATUS  database field=value | database field=value | ... />

    my $el_host_ref = $element_ref->{Host};
    foreach my $hostkey ( keys %{$el_host_ref} ) {
	my $el_svc_ref = $el_host_ref->{$hostkey}->{Service};
	foreach my $servicekey ( keys %{$el_svc_ref} ) {

	    # if no service status change then don't send
	    my $service_xml = '';
	    if ( $smart_update ) {
		$service_xml = serviceStatusChangeXML( $element_ref, $collage_status_ref, $hostkey, $servicekey );
		if ( !$service_xml ) {
		    $skipcount++;
		    next;
		}
	    }

	    my @xml_message = ();
	    push @xml_message, '<Service ';    # Start message tag

	    # default identification -- set to IP address if known
	    push @xml_message, "MonitorServerName=\"$thisnagios\" ";

	    # default identification -- set to IP address if known
	    push @xml_message, "Host=\"$hostkey\" ";

	    # Monarch Sync now sets the IP as Identification. We should use address field from Monarch, whatever that is.
	    # It's possible that the address changed, or that we are feeding a result for a host that
	    # was not in Monarch when this program started. If the Identification is blank, reload the cache.
	    if ( $hostipaddress{$hostkey} ) {
		## Set Device to IP
		push @xml_message, "Device=\"$hostipaddress{$hostkey}\" ";
	    }
	    else {
		## For some reason we don't know the IP. Might be a new host? Anyway, reload and try one time more.
		#load_cached_addresses;
		if ( $hostipaddress{$hostkey} ) {
		    ## Set Device to IP
		    push @xml_message, "Device=\"$hostipaddress{$hostkey}\" ";
		}
		else {
		    ## bail out and set Device = hostname. There is something wrong with the local Monarch DB.
		    push @xml_message, "Device=\"$hostkey\" ";
		}
	    }
	    push @xml_message, "ServiceDescription=\"$servicekey\" ";
	    if ( $smart_update ) {
		push @xml_message, $service_xml;
	    }
	    else {
		my $el_svc = $el_svc_ref->{$servicekey};
		foreach my $field ( keys %{$el_svc} ) {
		    my $tmpinfo = $el_svc->{$field};
		    $tmpinfo =~ s/"/'/g;
		    push @xml_message, "$field=\"$tmpinfo\" ";
		}
	    }
	    push @xml_message, "/>\n";    # End message tag

	    push( @output, join( '', @xml_message ) );
	    if ($smart_update) {
		serviceStatusUpdate( $element_ref, $collage_status_ref, $hostkey, $servicekey );
	    }
	    $insertcount++;
	    if ( ( $insertcount % 100 ) == 0 ) {
		print     "Queueing services for insert, count=$insertcount\n" if $debug;
		print LOG "Queueing services for insert, count=$insertcount\n" if $debug;
	    }
	}
    }
    if ($smart_update) {
	print     "Total Services Queued for Insert Count=$insertcount. No status change for $skipcount services.\n" if $debug;
	print LOG "Total Services Queued for Insert Count=$insertcount. No status change for $skipcount services.\n" if $debug;
    }
    else {
	print     "Total Services Queued for Insert Count=$insertcount.\n" if $debug;
	print LOG "Total Services Queued for Insert Count=$insertcount.\n" if $debug;
    }
    return \@output;
}

sub readNagiosfeedersConfig {
    my $type         = shift;
    my $database     = undef;
    my $dbhost       = undef;
    my $username     = undef;
    my $password     = undef;
    my $gwconfigfile = "/usr/local/cpfsms/config/db.properties";
    if ( $type !~ /^(collage|insightreports)$/ ) { return "ERROR: Invalid database type."; }
    if ( !open( CONFIG, "$gwconfigfile" ) ) {
	return "ERROR: Unable to find configuration file $gwconfigfile";
    }
    ## collage.username=collage
    ## collage.password=gwrk
    ## collage.database=GWCollageDB
    ## collage.dbhost = localhost
    while ( my $line = <CONFIG> ) {
	chomp $line;
	if ( $line =~ /\s*$type\.(\S+)\s*=\s*(\S*)\s*/ ) {
	    if ( $1 eq "username" ) {
		$username = $2;
	    }
	    elsif ( $1 eq "password" ) {
		$password = $2;
	    }
	    elsif ( $1 eq "database" ) {
		$database = $2;
	    }
	    elsif ( $1 eq "dbhost" ) {
		$dbhost = $2;
	    }
	}
    }
    close CONFIG;
    return ( $database, $dbhost, $username, $password );
}

sub serviceStatusChangeXML {
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $hostkey            = shift;
    my $servicekey         = shift;
    my @service_xml        = ();
    my $no_xml             = '';
    my $el_svc             = $element_ref->{Host}->{$hostkey}->{Service}->{$servicekey};
    my $cs_svc             = $collage_status_ref->{Host}->{$hostkey}->{Service}->{$servicekey};
    my $data_change        = 0;
    # We always need these fields if we send anything...
    foreach my $field qw(
        MonitorStatus
        ScheduledDowntimeDepth
	LastPluginOutput
    ) {
        my $tmpinfo = $el_svc->{$field};
        $tmpinfo =~ s/"/'/g;
        push @service_xml, "$field=\"$tmpinfo\" ";
	# but don't miss a change to these...
        if ( $el_svc->{$field} ne $cs_svc->{$field} ) {
            $data_change = 1;
        }
    }
    # Check each condition that might require an update to the database status
#       isServiceFlapping
#       isObsessOverService
    foreach my $field qw(
	Comments
	isAcceptPassiveChecks
	isChecksEnabled
	isEventHandlersEnabled
	isFlapDetectionEnabled
	isNotificationsEnabled
	isProblemAcknowledged
	MaxAttempts
    ) {
	if ( $el_svc->{$field} ne $cs_svc->{$field} ) {
	    my $tmpinfo = $el_svc->{$field};
	    $tmpinfo =~ s/"/'/g;
	    push @service_xml, "$field=\"$tmpinfo\" ";
	    $data_change = 1;
	}
    }
    my $timing_change = 0;
    # Check fields that constitute a timing update (only sync on heartbeat) 
    foreach my $field qw(
        LastCheckTime
	NextCheckTime
	Latency
	ExecutionTime
	PercentStateChange
	CurrentAttempt
	LastStateChange
    ) {
        if ( $el_svc->{$field} ne $cs_svc->{$field} ) {
            my $tmpinfo = $el_svc->{$field};
            $tmpinfo =~ s/"/'/g;
            push @service_xml, "$field=\"$tmpinfo\" ";
            $timing_change = 1;
        }
    }
    if ( ($timing_change == 1) && ($data_change == 0) ) {
        if ($heartbeat_mode)  {
            print LOG "Accepting heartbeat change for host: $hostkey and service $servicekey\n" if $debug > 1;
            return join( '', @service_xml );
        } else {
	    print LOG "Rejecting change since it's just a timing update and we are not doing a heartbeat: $servicekey\n" if $debug > 1;
            return $no_xml;
        }
    }
    if ($data_change == 1) {
        ## Check for "Pending Transition", so we can send an event and trigger a state change
        ## when we go from Pending to OK
        if ( ( $el_svc->{MonitorStatus} eq "OK" ) and ( $cs_svc->{MonitorStatus} ) eq "PENDING" ) {
	    queue_pending_svc_event( $element_ref, $collage_status_ref, $hostkey, $servicekey );
	}
	if ( $debug > 2 ) {
	    print LOG "Found changed $servicekey\n\n";
	    print LOG Data::Dumper->Dump( [ \%{$cs_svc} ], [qw(\%{collage_status_ref})] );
	    print LOG Data::Dumper->Dump( [ \%{$el_svc} ], [qw(\%{element_ref})] );
	}
	return join( '', @service_xml );
    }
    return $no_xml;
}

sub queue_pending_svc_event {
    ## This subroutine sends an event in the rare case where the service has transitioned from PENDING to OK.
    ## Nagios does not recognize this as an event, but we want it in SMSDataModel so we are detecting and
    ## sending it here. After initial script startup, when a lot of these might be found, there is not much
    ## point in bundling these, as they will trickle in based on the scheduler, and should only occur after
    ## services are added.
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $hostkey            = shift;
    my $servicekey         = shift;
    # Bail if events are off
    if ($send_events_for_pending_to_ok == 0 ) {
        return 0;
    }
    my @xml_message = ();
    push @xml_message, "<LogMessage ";

    # default identification -- should set to IP address if known
    push @xml_message, "MonitorServerName=\"$thisnagios\" ";
    push @xml_message, "Host=\"$hostkey\" ";
    if ( $hostipaddress{$hostkey} ) {
	## no IP address; set to host name
	push @xml_message, "Device=\"$hostipaddress{$hostkey}\" ";
    }
    else {
	## no IP address; set to host name
	push @xml_message, "Device=\"$hostkey\" ";
    }
    my $el_svc = $element_ref->{Host}->{$hostkey}->{Service}->{$servicekey};
    push @xml_message, "ServiceDescription=\"$servicekey\" ";
    push @xml_message, "Severity=\"$el_svc->{MonitorStatus}\" ";
    push @xml_message, "MonitorStatus=\"$el_svc->{MonitorStatus}\" ";
    my $tmp = $el_svc->{LastPluginOutput};
    $tmp =~ s/\n/ /g;
    $tmp =~ s/<br>/ /ig;
    $tmp =~ s/["']/&quot;/g;
    $tmp =~ s/</&lt;/g;
    $tmp =~ s/>/&gt;/g;
    $tmp =~ s/&\s/&amp; /g;
    push @xml_message, "TextMessage=\"$tmp\" ";
    $tmp = time_text(time);
    push @xml_message, "ReportDate=\"$tmp\" ";
    push @xml_message, "LastInsertDate=\"$el_svc->{LastCheckTime}\" ";
    push @xml_message, "SubComponent=\"$hostkey:$servicekey\" ";
    push @xml_message, 'ErrorType="SERVICE ALERT" ';
    push @xml_message, '/>';

    my $xml_message = join( '', @xml_message );

    print LOG "Pending Transition Service Event: $xml_message\n" if $debug > 1;

    push @event_messages, $xml_message;
    $message_counter = send_pending_events( $message_counter );
}

sub serviceStatusUpdate {
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $hostkey            = shift;
    my $servicekey         = shift;
    my $el_svc             = $element_ref->{Host}->{$hostkey}->{Service}->{$servicekey};
    my $cs_svc             = \%{ $collage_status_ref->{Host}->{$hostkey}->{Service}->{$servicekey} };
#     $cs_svc = $el_svc;
    $cs_svc->{Comments}               = $el_svc->{Comments};
    $cs_svc->{CurrentAttempt}         = $el_svc->{CurrentAttempt};
    $cs_svc->{LastCheckTime}          = $el_svc->{LastCheckTime};
    $cs_svc->{MonitorStatus}          = $el_svc->{MonitorStatus};
    $cs_svc->{NextCheckTime}          = $el_svc->{NextCheckTime};
    $cs_svc->{ScheduledDowntimeDepth} = $el_svc->{ScheduledDowntimeDepth};
    $cs_svc->{isAcceptPassiveChecks}  = $el_svc->{isAcceptPassiveChecks};
    $cs_svc->{isChecksEnabled}        = $el_svc->{isChecksEnabled};
    $cs_svc->{isEventHandlersEnabled} = $el_svc->{isEventHandlersEnabled};
    $cs_svc->{isFlapDetectionEnabled} = $el_svc->{isFlapDetectionEnabled};
    $cs_svc->{isNotificationsEnabled} = $el_svc->{isNotificationsEnabled};
#    $cs_svc->{isObsessOverService}    = $el_svc->{isObsessOverService};
    $cs_svc->{isProblemAcknowledged}  = $el_svc->{isProblemAcknowledged};
#    $cs_svc->{isServiceFlapping}      = $el_svc->{isServiceFlapping};
    $cs_svc->{MaxAttempts}            = $el_svc->{MaxAttempts};
    $cs_svc->{PercentStateChange}     = $el_svc->{PercentStateChange};
    $cs_svc->{LastPluginOutput}       = $el_svc->{LastPluginOutput};
    $cs_svc->{Latency}                = $el_svc->{Latency};
    $cs_svc->{ExecutionTime}          = $el_svc->{ExecutionTime};
    $cs_svc->{LastStateChange}        = $el_svc->{LastStateChange};
    return;
}

sub hostStatusChangeXML {
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $hostkey            = shift;
    my @host_xml           = ();
    my $no_xml             = '';
    my $el_host            = $element_ref->{Host}->{$hostkey};
    my $cs_host            = $collage_status_ref->{Host}->{$hostkey};
    my $data_change        = 0;
    # We always need these fields if we send any XML...
    foreach my $field qw(
        MonitorStatus
        ScheduledDowntimeDepth
    ) {
        my $tmpinfo = $el_host->{$field};
        $tmpinfo =~ s/"/'/g;
        push @host_xml, "$field=\"$tmpinfo\" ";
	if ( $el_host->{$field} ne $cs_host->{$field} ) {
            $data_change = 1;
        }
    }
    # Check each condition that might require an update to the database status
#       isHostFlapping
#       isObsessOverHost
    foreach my $field qw(
	Comments
	CurrentNotificationNumber
	MaxAttempts
	StateType
	isAcknowledged
	isChecksEnabled
	isEventHandlersEnabled
	isFlapDetectionEnabled
	isNotificationsEnabled
	isPassiveChecksEnabled
    ) {
	if ( $el_host->{$field} ne $cs_host->{$field} ) {
	    my $tmpinfo = $el_host->{$field};
	    $tmpinfo =~ s/"/'/g;
	    push @host_xml, "$field=\"$tmpinfo\" ";
            $data_change = 1;
	}
    }
    my $timing_change = 0;
    # Check each condition that might require an update to the timing change fields (sync only on heartbeat)
    foreach my $field qw(
        ExecutionTime
        Latency
        LastCheckTime
	NextCheckTime
	PercentStateChange
	CurrentAttempt
	LastPluginOutput
	LastStateChange
    ) {
        if ( $el_host->{$field} ne $cs_host->{$field} ) {
            my $tmpinfo = $el_host->{$field};
            $tmpinfo =~ s/"/'/g;
            push @host_xml, "$field=\"$tmpinfo\" ";
            $timing_change = 1;
        }
    }   

    if ( ($timing_change == 1) && ($data_change == 0) ) {
        if ($heartbeat_mode)  {
            print LOG "Accepting heartbeat change for host: $hostkey\n" if $debug > 1;
            return join( '', @host_xml );
        } else {
            print LOG "Rejecting change since it's just a timing update and we are not doing a heartbeat: $hostkey\n" if $debug > 1;
            return $no_xml;
        }
    }
    if ( $data_change == 1 ) {
	## Check for "Pending Transition", so we can send an event and trigger a state change
	## when we go from PENDING to UP
	if ( ( $el_host->{MonitorStatus} eq "UP" ) and ( $cs_host->{MonitorStatus} ) eq "PENDING" ) {
	    queue_pending_host_event( $element_ref, $collage_status_ref, $hostkey );
	}

	# print LOG Data::Dumper->Dump([\%{$cs_host}], [qw(\%{collage_status_ref})]);
	# print LOG Data::Dumper->Dump([\%{$el_host}], [qw(\%{element_ref})]);
	print LOG "State changed for $hostkey -- should tell SMSDataModel now\n" if $debug > 1;
	return join( '', @host_xml );
    }
    return $no_xml;
}

sub queue_pending_host_event {
    ## This subroutine sends an event in the rare case where the host has transitioned from PENDING to UP.
    ## Nagios does not recognize this as an event, but we want it in SMSDataModel so we are detecting and
    ## sending it here. After initial script startup, when a lot of these might be found, there is not much
    ## point in bundling these, as they will trickle in based on the scheduler, and should only occur after
    ## hosts are added.
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $hostkey            = shift;

    my @xml_message = ();
    push @xml_message, "<LogMessage ";

    # default identification -- should set to IP address if known
    push @xml_message, "MonitorServerName=\"$thisnagios\" ";
    push @xml_message, "Host=\"$hostkey\" ";
    if ( $hostipaddress{$hostkey} ) {
	## no IP address; set to host name
	push @xml_message, "Device=\"$hostipaddress{$hostkey}\" ";
    }
    else {
	## no IP address; set to host name
	push @xml_message, "Device=\"$hostkey\" ";
    }
    my $el_host = $element_ref->{Host}->{$hostkey};
    push @xml_message, 'Severity="OK" ';
    push @xml_message, 'MonitorStatus="UP" ';
    my $tmp = $el_host->{LastPluginOutput};
    $tmp =~ s/\n/ /g;
    $tmp =~ s/<br>/ /ig;
    $tmp =~ s/["']/&quot;/g;
    $tmp =~ s/</&lt;/g;
    $tmp =~ s/>/&gt;/g;
    $tmp =~ s/&\s/&amp; /g;
    push @xml_message, "TextMessage=\"$tmp\" ";
    $tmp = time_text(time);
    push @xml_message, "ReportDate=\"$tmp\" ";
    push @xml_message, "SubComponent=\"$hostkey\" ";
    push @xml_message, "LastInsertDate=\"$el_host->{LastCheckTime}\" ";
    push @xml_message, 'ErrorType="HOST ALERT" ';
    push @xml_message, '/>';

    my $xml_message = join( '', @xml_message );

    print LOG "Pending Transition Host Event: $xml_message\n" if $debug > 1;

    push @event_messages, $xml_message;
    $message_counter = send_pending_events( $message_counter );
}

sub hostStatusUpdate {
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $hostkey            = shift;
    my $el_host            = $element_ref->{Host}->{$hostkey};
    my $cs_host            = \%{ $collage_status_ref->{Host}->{$hostkey} };
    #$cs_host = $el_host;
    $cs_host->{Comments}                  = $el_host->{Comments};
    $cs_host->{CurrentAttempt}            = $el_host->{CurrentAttempt};
    $cs_host->{CurrentNotificationNumber} = $el_host->{CurrentNotificationNumber};
    $cs_host->{ExecutionTime}             = $el_host->{ExecutionTime};
    $cs_host->{LastCheckTime}             = $el_host->{LastCheckTime};
    $cs_host->{Latency}                   = $el_host->{Latency};
    $cs_host->{MaxAttempts}               = $el_host->{MaxAttempts};
    $cs_host->{MonitorStatus}             = $el_host->{MonitorStatus};
    $cs_host->{NextCheckTime}             = $el_host->{NextCheckTime};
    $cs_host->{ScheduledDowntimeDepth}    = $el_host->{ScheduledDowntimeDepth};
    $cs_host->{StateType}                 = $el_host->{StateType};
    $cs_host->{isAcknowledged}            = $el_host->{isAcknowledged};
    $cs_host->{isChecksEnabled}           = $el_host->{isChecksEnabled};
    $cs_host->{isEventHandlersEnabled}    = $el_host->{isEventHandlersEnabled};
    $cs_host->{isFlapDetectionEnabled}    = $el_host->{isFlapDetectionEnabled};
#    $cs_host->{isHostFlapping}            = $el_host->{isHostFlapping};
    $cs_host->{isNotificationsEnabled}    = $el_host->{isNotificationsEnabled};
#    $cs_host->{isObsessOverHost}          = $el_host->{isObsessOverHost};
    $cs_host->{isPassiveChecksEnabled}    = $el_host->{isPassiveChecksEnabled};
    $cs_host->{LastPluginOutput}          = $el_host->{LastPluginOutput};
    $cs_host->{PercentStateChange}	  = $el_host->{PercentStateChange};
    $cs_host->{LastStateChange}          = $el_host->{LastStateChange};
    return;
}

sub send_pending_events {
    my $series_num = shift;
    if ( scalar(@event_messages) >= $max_event_bundle_size ) {
	my $socket = 0;
	for (my $attempts = 10; --$attempts >= 0; ) {
	    if ( $socket = IO::Socket::INET->new( PeerAddr => $remote_host, PeerPort => $remote_port, Proto => "tcp", Type => SOCK_STREAM ) ) {
		last;
	    }
	    freeze_logtime();
	    print LOG "${logtime}Cannot open a socket to the SMSDataModel listener. Retrying in 2 seconds.\n";
	    sleep 2;
	}
	if ($socket) {
	    # Assemble XML for sending to SMSDataModel
	    my $element_begin = qq(<Adapter Session="$series_num" AdapterType="SystemAdmin">\n<Command ApplicationType='NAGIOS' Action='ADD'>);
	    my $element_end   = "</Command>\n</Adapter>";
	    my $command_close = '<SERVICE-MAINTENANCE command="close" />';

	    # FIX THIS:  detect and log i/o errors, and perhaps exit upon such failure
	    #print $socket join( "\n", $element_begin, @event_messages, $element_end, $command_close );
	    print $socket join( "\n",@event_messages );
	    print LOG     join( "\n", $element_begin, @event_messages, $element_end, $command_close, '' ) if ( $debug > 1 );
	    close($socket);
	    $series_num++;
	}
	else {
	    freeze_logtime();
	    print LOG "${logtime}Listener services not available. Restarting in 10 seconds.\n";
	    sleep 10;
	    exit(0);
	}
	@event_messages = ();
    }
    return $series_num;
}

sub sig_pipe_handler {
    sleep 2;
}

sub find_deltas {
    my $element_ref        = shift;
    my $collage_status_ref = shift;
    my $deltas             = {};

    foreach my $hostkey ( keys( %{ $collage_status_ref->{Host} } ) ) {
	my $el_host = $element_ref->{Host}->{$hostkey};
	if ( !defined $el_host ) {
	    $deltas->{SMSDataModelHost}->{$hostkey} = 1;
	    next;
	}
	foreach my $servicekey ( keys( %{ $collage_status_ref->{Host}->{$hostkey}->{Service} } ) ) {
	    my $el_svc = $el_host->{Service}->{$servicekey};
	    if ( !defined $el_svc ) {
		$deltas->{SMSDataModelHost}->{$hostkey}->{Service}->{$servicekey} = 1;
	    }
	}
    }
    foreach my $hostkey ( keys( %{ $element_ref->{Host} } ) ) {
	my $cs_host = $collage_status_ref->{Host}->{$hostkey};
	if ( !defined $cs_host ) {
	    $deltas->{NagiosHost}->{$hostkey} = 1;
	    next;
	}
	foreach my $servicekey ( keys( %{ $element_ref->{Host}->{$hostkey}->{Service} } ) ) {
	    if ( !defined $cs_host->{Service}->{$servicekey} ) {
		$deltas->{NagiosHost}->{$hostkey}->{Service}->{$servicekey} = 1;
	    }
	}
    }
    return $deltas;
}

__END__

NAGIOS V1 STATUS.LOG FILE
All Host Lines:

[Time of last update] HOST;
Host Name (string);
Status (OK/DOWN/UNREACHABLE);
Last Check Time (long time);
Last State Change (long time);
Acknowledged (0/1);
Time Up (long time);
Time Down (long time);
Time Unreachable (long time);
Last Notification Time (long time);
Current Notification Number (#);
Notifications Enabled (0/1);
Event Handlers Enabled (0/1);
Checks Enabled (0/1);
Flap Detection Enabled (0/1);
Host is Flapping (0/1);
Percent State Change (###.##);
Scheduled downtime depth (#);
Failure Prediction Enabled (0/1);
Process Performance Data(0/1);
Plugin Output (string)

Service Lines:

[Time of last update] SERVICE;
Host Name (string);
Service Description (string);
Status (OK/WARNING/CRITICAL/UNKNOWN);
Retry number (#/#);
State Type (SOFT/HARD);
Last check time (long time);
Next check time (long time);
Check type (ACTIVE/PASSIVE);
Checks enabled (0/1);
Accept Passive Checks (0/1);
Event Handlers Enabled (0/1);
Last state change (long time);
Problem acknowledged (0/1);
Last Hard State (OK/WARNING/CRITICAL/UNKNOWN);
Time OK (long time);
Time Unknown (long time);
Time Warning (long time);
Time Critical (long time);
Last Notification Time (long time);
Current Notification Number (#);
Notifications Enabled (0/1);
Latency (#);
Execution Time (#);
Flap Detection Enabled (0/1);
Service is Flapping (0/1);
Percent State Change (###.##);
Scheduled Downtime Depth (#);
Failure Prediction Enabled (0/1);
Process Performance Date (0/1);
Obsess Over Service (0/1);
Plugin Output (string)

Program line (second line of the status log):

[Current Time] PROGRAM;
Program Start Time (long time);
Nagios PID (#);
Daemon Mode (0/1);
Last Command Check (long time);
Last Log Rotation (long time);
Notifications Enabled (0/1);
Execute Service Checks (0/1);
Accept Passive Service Checks (0/1);
Enable Event Handlers (0/1);
Obsess Over Services (0/1);
Enable Flap Detection (0/1);
Enable Failure Prediction (0/1);
Process Performance Data (0/1)


NAGIOS V2 STATUS.DAT FILE
info {
	created=1122681331
	version=2.0b3
	}

program {
	modified_host_attributes=0
	modified_service_attributes=0
	nagios_pid=48776
	daemon_mode=1
	program_start=1122681286
	last_command_check=0
	last_log_rotation=0
	enable_notifications=1
	active_service_checks_enabled=1
	passive_service_checks_enabled=1
	active_host_checks_enabled=1
	passive_host_checks_enabled=1
	enable_event_handlers=1
	obsess_over_services=0
	obsess_over_hosts=0
	check_service_freshness=0
	check_host_freshness=0
	enable_flap_detection=0
	enable_failure_prediction=1
	process_performance_data=0
	global_host_event_handler=
	global_service_event_handler=
	}

host {
	host_name=localhost
	modified_attributes=0
	check_command=check-host-alive
	event_handler=
	has_been_checked=1
	should_be_scheduled=0
	check_execution_time=0.061
	check_latency=0.000
	current_state=0
	last_hard_state=0
	check_type=0
	plugin_output=PING OK - Packet loss = 0%, RTA = 0.04 ms
	performance_data=
	last_check=1122681125
	next_check=0
	current_attempt=1
	max_attempts=10
	state_type=1
	last_state_change=1122681115
	last_hard_state_change=1122681115
	last_time_up=1122681125
	last_time_down=0
	last_time_unreachable=0
	last_notification=0
	next_notification=0
	no_more_notifications=0
	current_notification_number=0
	notifications_enabled=1
	problem_has_been_acknowledged=0
	acknowledgement_type=0
	active_checks_enabled=1
	passive_checks_enabled=1
	event_handler_enabled=1
	flap_detection_enabled=1
	failure_prediction_enabled=1
	process_performance_data=1
	obsess_over_host=1
	last_update=1122681331
	is_flapping=0
	percent_state_change=0.00
	scheduled_downtime_depth=0
	}

service {
	host_name=localhost
	service_description=Current Load
	modified_attributes=0
	check_command=check_local_load!5.0,4.0,3.0!10.0,6.0,4.0
	event_handler=
	has_been_checked=1
	should_be_scheduled=1
	check_execution_time=0.008
	check_latency=0.539
	current_state=0
	last_hard_state=0
	current_attempt=1
	max_attempts=4
	state_type=1
	last_state_change=1122681115
	last_hard_state_change=1122681115
	last_time_ok=1122681286
	last_time_warning=0
	last_time_unknown=0
	last_time_critical=0
	plugin_output=OK - load average: 0.12, 0.15, 0.21
	performance_data=load1=0.123535;5.000000;10.000000;0.000000 load5=0.154785;4.000000;6.000000;0.000000 load15=0.214844;3.000000;4.000000;0.000000
	last_check=1122681286
	next_check=1122681586
	check_type=0
	current_notification_number=0
	last_notification=0
	next_notification=0
	no_more_notifications=0
	notifications_enabled=1
	active_checks_enabled=1
	passive_checks_enabled=1
	event_handler_enabled=1
	problem_has_been_acknowledged=0
	acknowledgement_type=0
	flap_detection_enabled=1
	failure_prediction_enabled=1
	process_performance_data=1
	obsess_over_service=1
	last_update=1122681331
	is_flapping=0
	percent_state_change=0.00
	scheduled_downtime_depth=0
	}
