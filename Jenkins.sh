sudo wget -O /etc/yum.repos.d/jenkins.repo http://pkg.jenkins-ci.org/redhat/jenkins.repo
sudo rpm --import http://pkg.jenkins-ci.org/redhat/jenkins-ci.org.key
sudo yum -y install jenkins

sudo yum -y install java-1.7.0-openjdk.x86_64

# Login as the jenkins user and specify shell explicity,
# since the default shell is /bin/false for most
# jenkins installations.
sudo su jenkins -s /bin/bash
ssh-keygen
exit

sudo service jenkins start

sudo tail -f /var/log/jenkins/jenkins.log



# see https://wiki.jenkins-ci.org/display/JENKINS/Installing+Jenkins+on+RedHat+distributions
# and http://stackoverflow.com/questions/15314760
