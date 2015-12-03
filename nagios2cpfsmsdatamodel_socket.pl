#!/usr/bin/perl --


use strict;
use Time::Local;
use vars qw($socket $smart_update);
use IO::Socket;
use Time::HiRes;
#use CollageQuery;
use Data::Dumper;
use JSON;
#do './cpfdatamodelService.pl';
	# Settings
	#Log Message:
	#Bugzilla# :8219,8255,8445,8451,7973
	#Problem: FFM application takes long time to load when there are 16 platforms 
	#Solution:  Modified the nagios feeder send the update directly to database and create a json for dynamic update
	#Reviewer : Abhi and Praphul
#Inspection ID :75418
my $debug             = 1;    # Set 0 for minimal, 1 for summary, 2 for basic, 3 for debug level, 4 for ridiculous level.
my $smart_update      = 0;    # If set to 1, then send only state changes and heartbeats.
my $heartbeat_mode    = 0;    # Do not change this setting -- it is controlled by smart_update.
my $send_sync_warning = 1;    # Send a console message when Nagios and SMSDataModel are out of sync. 0 = no warning, 1 = warning.

my $nagios_version = 3;
my $statusfile     = '/usr/local/ffm/nagios/var/status.dat';
my $statusfileBackup= '/usr/local/ffm/nagios/var/statusBackup.dat';
my $logfile        = '/usr/local/ffm/nagios/var/nagios2cpfsmsdatamodel_socket.log';
my $monitorStatusFile='/usr/local/ffm/scripts/feeders/status';
my $dynamicUpdtaeFilePath='/FFM-Temp/topic/publish/';
my $remote_port = 4913;
my $checkservices='/usr/local/ffm/scripts/feeders/dynamicupdatecheck';
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
my $sleepTime=60;
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
my $loopcount=0;					    # You may need to increase this if you see deadlocks after commit in the framework.log file.
my $sqlMonitorEnd=undef;
my $sqlMonitorStatusId=undef;
my $appendHost=undef;
my $lastappend=undef;
my $sqlLastPluginOutput=undef;
my $sqlLastPluginOutputEnd=undef;
my $EndlastPlugin=undef;
my $countMonitor=0;
my $countLastPlugin=0;
my $delimeterMonitor=" ";
my $delimeterLastPlugin=" ";
# Init variables
my $last_statusfile_mtime = 0;
my $element_ref           = {};
my $smsstack_ref	  = {};
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

my $ishalastpluginoutput  = "highavailability";
my $find                  = "&quot;";
my $templastpluginoutput  = '';

# Pre-extend the event_messages array for later efficiency, then truncate back to an empty state.
$#event_messages = $max_event_bundle_size;
@event_messages = ();

freeze_logtime();
$global_nagios = get_globals( $statusfile ); 

# if argument passed, just run once to synchronize state between Nagios and SMSDataModel
my $sync_at_start = shift || 0;

$SIG{"PIPE"} = \&sig_pipe_handler;    # handle broken pipe error

my %HostStatus = ( 0 => "UP", 1 => "DOWN", 2 => "UNREACHABLE" );
my %ServiceStatus = ( 0 => "OK", 1 => "WARNING", 2 => "CRITICAL", 3 => "UNKNOWN" );
#my %MonitorStatusid = ( 'OK' => 1, "WARNING" => 9, "CRITICAL" => 20, "UNKNOWN" => 3 );
my %MonitorStatusid = ( 'OK' => 1, "WARNING" => 9, "CRITICAL" => 20, "UNKNOWN" => 3 );

my %CheckType = ( 0 => "ACTIVE", 1 => "PASSIVE" );

my %StateType = ( 0 => "SOFT", 1 => "HARD" );

chomp $thisnagios;
my %hostipaddress = ();

if ( !open( LOG, '>>', $logfile ) ) {
	print "Can't open logfile '$logfile'.\n";
}
LOG->autoflush(1);
my @boot_checkStatus=undef;
my $boot_check="/usr/local/ffm/nagios/var/bootCheck.cfg";
my $boot_check_backup="/usr/local/ffm/nagios/var/bootCheck_backup.cfg";

sub getInitialState {
	
	my @boot_checkStatus=undef;
	unless(-f $statusfileBackup){
		`touch $statusfileBackup`;
	}
	
	&initialDecleration;  
	
	do '/usr/local/ffm/scripts/feeders/cpfdatamodelService.pl';
	&mainFunction; 
	$countMonitor =0;
	$countLastPlugin =0;
	my $collage_status_ref = shift;
	#    my $smsstack         = CollageQuery->new();
	my $smsstack_ref         = get_status( $statusfileBackup, $nagios_version ) ;
	#	print $smsstack;
	my $element_ref        = get_status( $statusfile, $nagios_version );
	#`cp -rf $statusfile $statusfileBackup`;
	#print Data::Dumper->Dump( [ \%{$smsstack_ref}], [qw(\%element_ref)] );
	#print Data::Dumper->Dump( [ \%{$element_ref}], [qw(\%element_ref)] );
	if ( $debug > 3 ) {
		freeze_logtime();
		print LOG $logtime . Data::Dumper->Dump( [ \%{$element_ref} ], [qw(\%element_ref)] );
	}
	my $el_host_ref_status = $element_ref->{Host};
	my $el_host_ref_statusbackup = $smsstack_ref->{Host};
	
	
	
	my %status_hash = ();
	# Read and build status hash
	open STATUS, "$monitorStatusFile";
	while (<STATUS>){
		chomp;
		my ($v, $k) = split(/;/);
		$status_hash{$k} = $v;
	}
	close STATUS;
	my $hostcount=0;
	my @hostArray=();
	my $flagmonitor=0;
	my $flaglastplugin=0;
	open(CHECKUPDATE,"$checkservices");
	my @update=<CHECKUPDATE>;
	close(CHECKUPDATE);
	chomp @update;
	my $hostkey=undef;
	my $servicekey=undef;
	foreach  $hostkey ( keys %{$el_host_ref_status} ) {
		push @boot_checkStatus,$hostkey."=".$el_host_ref_status->{$hostkey}->{MonitorStatus}."\n";
		&sqlMonitorStatusDecleration;
		&sqlLastPluginOutputDec;
		$countMonitor =0; 
		$countLastPlugin =0; 
		my $el_svc_ref_status = $el_host_ref_status->{$hostkey}->{Service};
		my $el_svc_ref_statusbackup = $el_host_ref_statusbackup->{$hostkey}->{Service};
		foreach  $servicekey ( keys %{$el_svc_ref_status} ) {
			
			#Checking For isAcceptPassiveChecks in CHECK_PARTITION_STATUS for skipping the check
			if($servicekey eq 'CHECK_PARTITION_STATUS'){
				if($el_svc_ref_status->{$servicekey}->{isAcceptPassiveChecks} eq '0') {
					next;
				}
			}
			#Checking For isChecksEnabled in CHECK_SPAR_STATUS for skipping the check
			if($servicekey eq 'CHECK_SPAR_STATUS'){
				if($el_svc_ref_status->{$servicekey}->{isChecksEnabled} eq '0') {
					next;
				}
			}
			
			# Checking the Monitor Status and updating the DAtABASE
			if($el_svc_ref_status->{$servicekey}->{MonitorStatus}){
				if($el_svc_ref_status->{$servicekey}->{MonitorStatus} ne $el_svc_ref_statusbackup->{$servicekey}->{MonitorStatus}){
					$flagmonitor=1;
					&sqlMonitorStatusQuery($hostkey,$servicekey,$status_hash{$el_svc_ref_status->{$servicekey}->{'MonitorStatus'}});
					#	print "PKD"."----"."$hostkey"."----"."$servicekey"."----backup----"."$el_svc_ref_statusbackup->{$servicekey}->{MonitorStatus}"."-----"."Latest----"."$el_svc_ref_status->{$servicekey}->{MonitorStatus}"."\n";
				}
			}
			
			# Checking for Last PluginOutPut and updating the DATABASE
			if($el_svc_ref_status->{$servicekey}->{LastPluginOutput}){
				if($el_svc_ref_status->{$servicekey}->{LastPluginOutput} ne $el_svc_ref_statusbackup->{$servicekey}->{LastPluginOutput}){
					$flaglastplugin=1;
					#print "PKD"."----"."$hostkey"."----"."$servicekey"."----backup----"."$el_svc_ref_statusbackup->{$servicekey}->{LastPluginOutput}"."Latest----"."$el_svc_ref_status->{$servicekey}->{LastPluginOutput}"."---"."\n";
					&sqlLastPluginOutputQuery($hostkey,$servicekey,$el_svc_ref_status->{$servicekey}->{LastPluginOutput});
				}
			}
			
			#json implementation Aand DYNAMIC UPDATE
			foreach (@update){
				if($_ eq $servicekey){
		#			&jsonCreation($el_svc_ref_status->{$servicekey}->{MonitorStatus},$el_svc_ref_status->{$servicekey}->{LastPluginOutput},$hostkey,$servicekey,$el_svc_ref_statusbackup->{$servicekey}->{HostID});
					if(($el_svc_ref_status->{$servicekey}->{MonitorStatus}) || ($el_svc_ref_status->{$servicekey}->{LastPluginOutput})) {
						if(($el_svc_ref_status->{$servicekey}->{MonitorStatus} ne $el_svc_ref_statusbackup->{$servicekey}->{MonitorStatus}) and  
						($el_svc_ref_status->{$servicekey}->{LastPluginOutput} ne $el_svc_ref_statusbackup->{$servicekey}->{LastPluginOutput})) {
							if(!((($el_svc_ref_status->{$servicekey}->{LastPluginOutput}=~ m/PING/) and ($el_svc_ref_statusbackup->{$servicekey}->{LastPluginOutput}=~ m/PING/)) || ($el_svc_ref_status->{$servicekey}->{LastPluginOutput}=~ m/PARTITIONSTATUSERROR/))){
								&jsonCreation($el_svc_ref_status->{$servicekey}->{MonitorStatus},$el_svc_ref_status->{$servicekey}->{LastPluginOutput},$hostkey,$servicekey,$el_svc_ref_statusbackup->{$servicekey}->{HostID});
							}elsif($el_svc_ref_status->{$servicekey}->{MonitorStatus} ne $el_svc_ref_statusbackup->{$servicekey}->{MonitorStatus}){
								&jsonCreation($el_svc_ref_status->{$servicekey}->{MonitorStatus},$el_svc_ref_status->{$servicekey}->{LastPluginOutput},$hostkey,$servicekey,$el_svc_ref_statusbackup->{$servicekey}->{HostID});
							}elsif($el_svc_ref_status->{$servicekey}->{LastPluginOutput} ne $el_svc_ref_statusbackup->{$servicekey}->{LastPluginOutput}){
								if(!((($el_svc_ref_status->{$servicekey}->{LastPluginOutput}=~ m/PING/) and ($el_svc_ref_statusbackup->{$servicekey}->{LastPluginOutput}=~ m/PING/)) || ($el_svc_ref_status->{$servicekey}->{LastPluginOutput}=~ m/PARTITIONSTATUSERROR/))){
									&jsonCreation($el_svc_ref_status->{$servicekey}->{MonitorStatus},$el_svc_ref_status->{$servicekey}->{LastPluginOutput},$hostkey,$servicekey,$el_svc_ref_statusbackup->{$servicekey}->{HostID})};
							}
						}	
					}	
				}
			}
			#finish dynamic code implementation
			
			
		}
		if($flagmonitor==1){
			chop $appendHost;
			&sqlMonitorStatusQueryHostsection($hostkey);
			#my $appendsqlmonitorQuery=$sqlMonitorStatusId.$sqlMonitorEnd.$appendHost.$lastappend;
			my $appendsqlmonitorQuery=$sqlMonitorStatusId.$sqlMonitorEnd.$lastappend;
			&sqlMonitorStatusExecution($appendsqlmonitorQuery);
		}
		$flagmonitor=0;
		
		if($flaglastplugin==1){
			&sqlLastPluginOutputHOstSection($hostkey);		
			my $appensqllastpluginQuey=$sqlLastPluginOutput.$sqlLastPluginOutputEnd;
			&sqlLastPluginOutputQueryExecution($appensqllastpluginQuey);
		}
		$flaglastplugin=0;
		&initialDecleration;
		#exit;
	}
		#unless(-f "$boot_check_backup"){
                	open FILE,">$boot_check_backup";
                	print FILE @boot_checkStatus;
                	close FILE;
        	#}
		@boot_checkStatus=undef;
		`sudo mv $boot_check_backup $boot_check`;
	
}

sub initialDecleration{
	
	$sqlMonitorEnd=undef;
	$sqlMonitorStatusId=undef;
	$appendHost=undef;
	$lastappend=undef;
	$sqlLastPluginOutput=undef;
	$sqlLastPluginOutputEnd=undef;
	$EndlastPlugin=undef;
}

sub sqlMonitorStatusDecleration{
	$sqlMonitorStatusId="'update servicestatus set monitorstatusid= CASE ";
	# $sqlMonitorEnd=" END Where servicestatusid in (select servicestatusid from servicestatus where hostid = (select hostid from host where hostname=";
	$sqlMonitorEnd=" END Where servicestatusid in (";
	# $appendHost=" and servicedescription in ( ";
	$lastappend=");'";
}

sub sqlLastPluginOutputDec{
	$sqlLastPluginOutput="'update servicestatusproperty set valuestring= CASE ";
	#      $sqlLastPluginOutputEnd=" END where servicestatusid in (select servicestatusid from servicestatus where hostid = (select hostid from host where hostname =";	
	$sqlLastPluginOutputEnd=" END where ( servicestatusid in (";
}

sub sqlMonitorStatusQuery{
	
	$delimeterMonitor=" ";
	if($countMonitor>0){
		$delimeterMonitor=",";
		}else{
		$delimeterMonitor=" ";
	}
	
	(my $host,my $service,my $monitorstatusvalue)=@_;
	
	return if($host eq "" || $service eq "" || $monitorstatusvalue eq "");
	#$sqlMonitorStatusId.="WHEN servicestatusid = (select servicestatusid from servicestatus where hostid = (select hostid from host where hostname= ' ||'''' ||'$host'||'''' || ') and servicedescription =' ||'''' ||'$service'||'''' || ') THEN $monitorstatusvalue ";
	$sqlMonitorStatusId.="WHEN hostid = (select hostid from host where hostname= ' ||'''' ||'$host'||'''' || ') and servicedescription =' ||'''' ||'$service'||'''' || ' THEN $monitorstatusvalue ";
	#$appendHost.="' ||'''' ||'$service'||'''' || ' ,";
	$sqlMonitorEnd.="$delimeterMonitor(select servicestatusid from servicestatus where hostid = (select hostid from host where hostname = ' ||'''' ||'$host'||'''' || ') and servicedescription= ' ||'''' ||'$service'||'''' || ')";
	$countMonitor=$countMonitor+1;
	
}

sub sqlLastPluginOutputQuery{
	
	$delimeterLastPlugin=" ";
	if($countLastPlugin>0){
		$delimeterLastPlugin=",";
		}else{
		$delimeterLastPlugin=" ";
	}
	(my $hostlast, my $servicelast, my $lastpluginoutput)=@_;
	
	chomp $lastpluginoutput;
	return if($hostlast eq "" || $servicelast eq "" || $lastpluginoutput eq "");
	#$sqlLastPluginOutput.="WHEN servicestatusid = (select servicestatusid from servicestatusproperty where servicestatusid=(select servicestatusid from servicestatus where hostid = (select hostid from host where hostname= ' ||'''' ||'$hostlast'||'''' || ')and servicedescription= ' ||'''' ||'$servicelast'||'''' || 'and propertytypeid=1)) THEN ' ||'''' ||'$lastpluginoutput'||'''' || '";	
	$sqlLastPluginOutput.="WHEN servicestatusid = (select servicestatusid from servicestatusproperty where servicestatusid=(select servicestatusid from servicestatus where hostid = (select hostid from host where hostname= ' ||'''' ||'$hostlast'||'''' || ')and servicedescription= ' ||'''' ||'$servicelast'||'''' || 'and propertytypeid=1)) THEN ' ||'''' ||'$lastpluginoutput'||'''' || '";	
	$EndlastPlugin.="$delimeterLastPlugin(select servicestatusid from servicestatus where hostid = (select hostid from host where hostname = ' ||'''' ||'$hostlast'||'''' || ') and servicedescription= ' ||'''' ||'$servicelast'||'''' || ')";
	$countLastPlugin =$countLastPlugin+1;
	
}


sub sqlMonitorStatusQueryHostsection{
	
	(my $host)=@_;
	return if($host eq "");
	#         $sqlMonitorEnd .=" ' ||'''' ||'$host'||'''' || ')";
	#$sqlMonitorEnd .=$sqlMonitorEnd;
	
}

sub sqlLastPluginOutputHOstSection{
	
	(my $hostlast)=@_;
	return if($hostlast eq "");
	#$sqlLastPluginOutputEnd .=" ' ||'''' ||'$hostlast'||'''' || ') and propertytypeid =1);' ";
	$sqlLastPluginOutputEnd .="$EndlastPlugin) and propertytypeid =1);' ";
}

sub sqlMonitorStatusExecution{
	(my $amonitorStatusId)=@_;
	print LOG $logtime."$amonitorStatusId\n"if($debug==3);
	#print "\n";
	my $sucessMonitorStatus=`/usr/local/ffm/postgresql/bin/psql -U cpfadmin -d cpfdatamodeldb -c "select * from updatedServiceFeed($amonitorStatusId);"`;
	my $statusMonitorStatus=`echo $?`;
	if($statusMonitorStatus==0){
		print LOG $logtime."$statusMonitorStatus\n" if($debug>0);
		}else{
		print LOG $logtime."DATABASE is not update status code is for MONITOR STATUS $statusMonitorStatus \n"if($debug==0 || $debug>0);
	}
}

sub sqlLastPluginOutputQueryExecution{
	
	(my $lastpluginoutputqueryexecution)=@_;
	return if($lastpluginoutputqueryexecution eq "");
	print LOG $logtime."$lastpluginoutputqueryexecution\n"if($debug==3);
	#print "\n";
	my $sucesslastpluginstatus=`/usr/local/ffm/postgresql/bin/psql -U cpfadmin -d cpfdatamodeldb -c "select * from updatedServiceFeed($lastpluginoutputqueryexecution);"`;
	my $statuslastpluginstatus=`echo $?`;
	if($statuslastpluginstatus==0){
		print LOG $logtime."$statuslastpluginstatus\n"if($debug>0);
		}else{
		print LOG $logtime."DATABASE is not update status code is for LASTPLUGINOUTPUT output $statuslastpluginstatus\n"if($debug==0 || $debug>0);
	}
}

sub ltrim { my $s = shift; $s =~ s/^\s+//;       return $s };
sub rtrim { my $s = shift; $s =~ s/\s+$//;       return $s };
sub  trim { my $s = shift; $s =~ s/^\s+|\s+$//g; return $s };

while(1){
	print $logtime;
	&getInitialState;
	$loopcount=0;
	$countMonitor=0;
	$countLastPlugin=0;
	#sleep 90;
	sleep $sleepTime;
	
}

sub jsonCreation1{
	(my $monitorstatus,my $lastpluginoutput,my $host,my $service)=@_;
	return if($monitorstatus eq "" || $lastpluginoutput eq "" || $host eq "" || $service eq "");
	$loopcount=$loopcount+1;
	my $topic='"topic"';
	my $colon=":";
	my $serviceStatus='"ServiceStatus"';
	my $serviceFile="ServiceStatus";
	my $comma=",";
	my $datajson='"data"';
	my $opencurlybraces="{";
	my $closecurlybraces="}";
	my $action='"action"';
	my $health='"health"';
	my $status='"status"';
	my $hostname='"hostname"';
	my $type='"type"';
	my $date=undef;
	my $date=`date +%Y%m%d%H%M%S`;
	chomp $date;
	my $hyphen="_";
	my $dot=".";
	my $json="json";
	my $data=undef;
	my $fileName=undef;
	
	if (index($lastpluginoutput, $ishalastpluginoutput) != -1) {
		$find = "&quot;";
		$find = quotemeta $find; # escape regex metachars if present
		$lastpluginoutput =~ s/$find/\"/g;
		$data=$opencurlybraces.$topic.$colon.$serviceStatus.$comma.$datajson.$colon.$opencurlybraces.$action.$colon.$serviceStatus.$comma.$health.$colon."\"$monitorstatus\"".$comma.$status.$colon."$lastpluginoutput".$comma.$hostname.$colon."\"$host\"".$comma.$type.$colon."\"$service\"".$closecurlybraces.$closecurlybraces;
	}
	else {
		$data=$opencurlybraces.$topic.$colon.$serviceStatus.$comma.$datajson.$colon.$opencurlybraces.$action.$colon.$serviceStatus.$comma.$health.$colon."\"$monitorstatus\"".$comma.$status.$colon."\"$lastpluginoutput\"".$comma.$hostname.$colon."\"$host\"".$comma.$type.$colon."\"$service\"".$closecurlybraces.$closecurlybraces;
	}
	print LOG $logtime."$data\n"if($debug==3);
	#print "\n";
	$fileName=$date.$hyphen.$loopcount.$serviceFile.$dot.$json;
	print LOG $logtime."$fileName\n"if($debug>0);
	#print "\n";
	my $dynamicFile=undef;
	$dynamicFile=$dynamicUpdtaeFilePath.$fileName;
	open (FILE, ">>$dynamicFile");
	print  FILE $data;
	close(FILE);
}

sub jsonCreation{

        (my $monitorstatus,my $lastpluginoutput,my $host,my $service,my $hostID)=@_;
        return if($monitorstatus eq "" || $lastpluginoutput eq "" || $host eq "" || $service eq "" || $hostID eq "");
        $loopcount=$loopcount+1;

        my $topic="topic";
        my $action="action";
        my $hostid="hostid";
        my $hostname="hostname";
        my $parentid="parentid";
        my $status="status";
	my $serviceStatus="ServiceStatus";
	my $date=undef;
        my $date=`date +%Y%m%d%H%M%S`;
        chomp $date;
        my $hyphen="_";
        my $dot=".";
        my $json="json";
        my $data=undef;
        my $fileName=undef;

        my %hash=("$topic" => "$serviceStatus",
                  "$action" => "$service",# This is the service description which got updated
                  "$hostid" => "$hostID", #May not be available in Nagios
                  "$hostname" => "$host",
                  "$parentid" => "" ,#May not be available in Nagios
                  "$status" => "success"
        );
        my $json = encode_json \%hash;


        print "$json\n";

	print LOG $logtime."$json\n"if($debug==3);
        #print "\n";
        $fileName=$date.$hyphen.$loopcount.$serviceStatus.$dot.$json;
        print LOG $logtime."$fileName\n"if($debug>0);
        #print "\n";
        my $dynamicFile=undef;
        $dynamicFile=$dynamicUpdtaeFilePath.$fileName;
        open (FILE, ">>$dynamicFile");
        print  FILE $json;
        close(FILE);

}

#&jsonCreation('"CRITICAL"','"RUNNING"','"PEPPE"','"CHECK_PARTITION_ALIVE"');


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

sub get_status_v3 {
	my $delimeter="";	
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
				#$el_svc->{MonitorStatus} = $MonitorStatusid{ $attribute{current_state} };
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
			
			if($attribute{long_plugin_output} eq ""){
				$delimeter="";	
				}else{
				$delimeter=" ";
			}	
			
			# Set element hash
			# Map Nagios V2 status parameters to Nagios V1 definitions in Collage
			$el_svc->{CheckType}                  = $CheckType{ $attribute{check_type} };
			$el_svc->{CurrentAttempt}             = $attribute{current_attempt};
			$el_svc->{CurrentNotificationNumber}  = $attribute{current_notification_number};
			$el_svc->{ExecutionTime}              = $attribute{check_execution_time};
			$el_svc->{LastCheckTime}              = time_text( $attribute{last_check} );
			$el_svc->{LastHardState}              = $ServiceStatus{ $attribute{last_hard_state} };
			$el_svc->{LastNotificationTime}       = time_text( $attribute{last_notification} );
			$el_svc->{LastPluginOutput}           = $attribute{plugin_output}.$delimeter.$attribute{long_plugin_output};
			#$el_svc->{LastPluginOutput}           = $attribute{plugin_output};
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
			$el_svc->{HostID}          	      = $attribute{host_id};
			#print $el_svc->{isAcceptPassiveChecks}."=====\n";
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
