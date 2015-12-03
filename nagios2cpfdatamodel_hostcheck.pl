#!/usr/bin/perl

use strict;
use DBI;
use threads;
use threads::shared;

my $NagiosMonitorStatusFile="/usr/local/ffm/scripts/feeders/mappingNagios";
my $FFMMonitorStatusFile="/usr/local/ffm/scripts/feeders/status";

my $statusFile = "/usr/local/ffm/nagios/var/status.dat";
 
my $count = 0;
my $hashStatus={};
my @listHashStatus ;#: shared; 
my $hashStatusBackup={};
my @listHashStatusBackup ;#: shared;

my $updateFlag=0;

my $dbh;
my $sqlQuery;
my $sth;

my %nagios_status_hash_key =() ;#: shared = ();
my %ffm_status_hash  = (); #: shared = ();
my %nagios_status_hash_value=();


my %nagios_check_type = ( 0 => "ACTIVE", 1 => "PASSIVE" );

my %nagios_state_type = ( 0 => "SOFT", 1 => "HARD" );

my %ffm_check_type = ( "ACTIVE" => 1,  "PASSIVE"  =>2);

my %ffm_state_type = ( "SOFT" =>1 , "HARD" =>2 , "UNKNOWN" =>3 );




my $updateSqlQuery = "Update hoststatus set ";
my $monitorstatusquery = "monitorstatusid= CASE hoststatusid";
my $checktypequery = "checktypeid = CASE hoststatusid";
my $statetypequery ="statetypeid = CASE hoststatusid";
my $lastchecktimequery = "lastchecktime = CASE hoststatusid";
my $nextchecktimequery ="nextchecktime = CASE hoststatusid";
my $hostidquery="(";

sub read_status{
  print "in read_status\n";
	open(STATUS,  $statusFile) or die "Could not open file '$statusFile' $!";
	while (<STATUS>) {
   		if (/hoststatus {/) {
			$hashStatus = {};
			$count = 1;
			next;
		}
		elsif (/}/ and $count) {
			push @listHashStatus, $hashStatus;
			$count = 0;
		}
		if ($count) {
			chomp(my $line=$_);
			$line=~s/^\s+//;
			(my $key, my $value) = split /=/, $line;
			$hashStatus->{$key} = $value;
		}
	}
	close STATUS;
	print "listHashStatus = $#listHashStatus\n";
}

 sub create_database_connection{
	 my $ffmDBUsernamePassword = `/usr/local/ffm/scripts/./get_set_credential_cfg.pl -m ffmdb`;
	 my ($ffmDBUsername, $ffmDBPassword)=split (":",$ffmDBUsernamePassword);
	 my $driver   = "Pg";
	 my $database = "cpfdatamodeldb";
	 my $dsn = "DBI:$driver:dbname=$database;host=127.0.0.1;port=5432";
	 $dbh = DBI->connect($dsn, $ffmDBUsername, $ffmDBPassword, { RaiseError => 1 }) or die $!; ;
 }

#sub create_database_connection{
	#print "in create_database_connection\n";
	# my $ffmDBUsernamePassword = `/usr/local/ffm/scripts/./get_set_credential_cfg.pl -m ffmdb`;
	# my ($ffmDBUsername, $ffmDBPassword)=split (":",$ffmDBUsernamePassword);
	#my $driver   = "Pg";
	#my $database = "cpfdatamodeldb";
	#my $dsn = "DBI:$driver:dbname=$database;host=127.0.0.1;port=5432";
	#$dbh = DBI->connect($dsn, "cpfadmin", "cpfadmin", { RaiseError => 1 }) or die $!; ;
#}

sub create_status_backup_hash{
	print "in create_status_backup_hash\n";
	$sqlQuery = "select h.hostid, h.hostname, ss.monitorstatusid as MonitorStatusId , m.name as MonitorStatus  from host as h inner join hoststatus as ss on h.hostid=ss.hoststatusid   inner join monitorstatus as m on ss.monitorstatusid = m.monitorstatusid";
	$sth=$dbh->prepare($sqlQuery)or die "Couldn't prepare statement:+ $DBI::errstr; stopped";
	$sth->execute()or die "Couldn't execute prepare statement:+ $DBI::errstr; stopped";
	
	while(my @row = $sth->fetchrow_array())
	{
		$hashStatusBackup = {};
		my($hostid, $hostname, $monitorstatusid, $monitorstatus) = @row;
		$hashStatusBackup->{host_id} = $hostid;
		$hashStatusBackup->{host_name} = $hostname;
		$hashStatusBackup->{current_state} = $nagios_status_hash_value{$monitorstatus};
		push @listHashStatusBackup, $hashStatusBackup;
	}
	print "listHashStatusBackup = $#listHashStatusBackup\n";
}

sub compare_status_statusBackup{
	print "in compare_status_statusBackup\n";
	print "listHashStatus = $#listHashStatus\n";
	print "listHashStatusBackup = $#listHashStatusBackup\n";
	for(my $i=0; $i<=$#listHashStatus; $i++) 
	{
		print "$listHashStatus[$i]->{host_name}\n";
		if($listHashStatus[$i]->{active_checks_enabled} == 0)
		{
			next;
		} 
		for(my $j=0; $j<=$#listHashStatusBackup; $j++) 
		{
			if($listHashStatus[$i]->{host_name} eq $listHashStatusBackup[$j]->{host_name})
			{
				print "$listHashStatus[$i]->{host_name}\n";
				if( $listHashStatus[$i]->{current_state} != $listHashStatusBackup[$j]->{current_state})
				{	
						$updateFlag=1;
						my $monitorstatus = $ffm_status_hash{$nagios_status_hash_key{$listHashStatus[$i]->{current_state}}};
						my $checktype = $ffm_check_type{$nagios_check_type{$listHashStatus[$i]->{check_type}}};
						my $statetype = $ffm_state_type{$nagios_state_type{$listHashStatus[$i]->{state_type}}};
						$monitorstatusquery.=" WHEN $listHashStatusBackup[$j]->{host_id} THEN $monitorstatus ";
						$checktypequery.=" WHEN $listHashStatusBackup[$j]->{host_id} THEN  $checktype  ";
						$statetypequery.=" WHEN $listHashStatusBackup[$j]->{host_id} THEN  $statetype ";
						$lastchecktimequery.="  WHEN $listHashStatusBackup[$j]->{host_id} THEN  now() ";
						$nextchecktimequery.=" WHEN $listHashStatusBackup[$j]->{host_id} THEN now() + (1 ||' minutes')::interval ";
						$hostidquery.="$listHashStatusBackup[$j]->{host_id},"
				}
			}
		}
	
	}
	if($updateFlag)
	{
		$hostidquery=~s/,$/)/;
		&update_db();
	}
	print "End compare_status_statusBackup";
}
sub update_db{
	print "in update_db \n ";
	
	$sqlQuery = $updateSqlQuery.$monitorstatusquery."END,".$checktypequery."END,".$statetypequery."END,".$lastchecktimequery."END,".$nextchecktimequery."END  WHERE hoststatusid IN".$hostidquery; 
	print "$sqlQuery\n";
	$sth=$dbh->prepare($sqlQuery)or die "Couldn't prepare statement:+ $DBI::errstr; stopped";
	$sth->execute()or die "Couldn't execute prepare statement:+ $DBI::errstr; stopped";	
}

sub NagiosMonitorstatusCheck{
	print "in NagiosMonitorstatusCheck \n";
	open( MONITORSTATUS, "$NagiosMonitorStatusFile");
	while (<MONITORSTATUS>){
		chomp;
		my($v, $k) = split(/;/);
		$nagios_status_hash_key{$v} = $k;
		$nagios_status_hash_value{$k}=$v;
	}
	close MONITORSTATUS;

}

sub FFMMonitorstatusCheck{
	print "in FFMMonitorstatusCheck \n";
	open (MONITORSTATUS, "$FFMMonitorStatusFile");
	while (<MONITORSTATUS>){
		chomp;
		my($v, $k) = split(/;/);
		$ffm_status_hash{$k} = $v;
	}
	close MONITORSTATUS;
}

sub main{
	&create_database_connection();
	my (@thr,$thr1);
	&NagiosMonitorstatusCheck();#$thr1 = threads->create(\&NagiosMonitorstatusCheck);
	&FFMMonitorstatusCheck();#push @thr ,threads->create(\&FFMMonitorstatusCheck);
	&read_status();#push @thr , threads->create(\&read_status);
	#$thr1->join();
	&create_status_backup_hash();
	#$_->join() foreach @thr;
	#print "DONE";
	&compare_status_statusBackup();
	$sth->finish();
	$dbh->disconnect();
}
main();
	
