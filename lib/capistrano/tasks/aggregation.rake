namespace :aggregation do
  
  desc 'start aggregation'
  task :start do
    on roles(:node) do |server|
      execute '/sbin/start-stop-daemon', 
      '--start', 
      '--quiet', 
      '--make-pidfile',
      "--pidfile #{current_path}/extraction/aggregation-dynamic/tmp/tree-aggregation-main.pid",
      '--background',
      "--chdir #{current_path}/extraction/aggregation-dynamic",
      '--startas /bin/bash',
      "-- -c \"exec ./TreeAggregationMain.native -me #{server.properties.me} -port 8000 -node 0,discoberry01.duckdns.org:9000 -node 1,discoberry02.duckdns.org:9000 > log/tree-aggregation-main.log 2>&1\""
    end
  end

  desc 'stop aggregation'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
      '--stop', 
      "--pidfile #{current_path}/extraction/aggregation-dynamic/tmp/tree-aggregation-main.pid"
    end
  end

  desc 'tail aggregation log'
  task :tail_log do
    on roles(:node) do
      execute "tail -n 20 #{shared_path}/extraction/aggregation-dynamic/log/tree-aggregation-main.log"
    end
  end

#        within "#{current_path}/extraction/aggregation-dynamic" do
#          execute './TreeAggregationMain.native', "-me #{me}", "-port 8000", "-node 0,discoberry01.duckdns.org:9000 -node 1,discoberry02.duckdns.org:9000"
#          #start-stop-daemon --start --chuid deploy --pidfile "$PID" --exec "$DAEMON" -- $DAEMON_OPTS
#          #start-stop-daemon --start --background -m --oknodo --pidfile ${PIDFILE} --exec ${DAEMON} -- ${TARGETDIR}
#          #start-stop-daemon --start --background -m --pidfile tmp/tree-aggregation-main.pid --exec ${DAEMON} -- ${TARGETDIR}
#
#          start-stop-daemon --start --quiet --make-pidfile --pidfile $PWD/tmp/tree-aggregation-main.pid --background -d $PWD --startas /bin/bash -- -c "exec ./TreeAggregationMain.native -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 > log/tree-aggregation-main.log 2>&1"
#
#          start-stop-daemon --stop --pidfile $PWD/tmp/tree-aggregation-main.pid
#
#          start-stop-daemon --start --quiet --make-pidfile --pidfile #{current_path}/extraction/aggregation-dynamic/tmp/tree-aggregation-main.pid --background -d #{current_path}/extraction/aggregation-dynamic --startas /bin/bash -- -c "exec ./TreeAggregationMain.native -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 > log/tree-aggregation-main.log 2>&1"
#
#          start-stop-daemon -v --start --make-pidfile --pidfile tmp/tree-aggregation-main.pid --background --startas /bin/bash -- -c "exec ./TreeAggregationMain.native -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 > log/tree-aggregation-main.log 2>&1"
#
#          start-stop-daemon --stop --quiet --make-pidfile --pidfile tmp/tree-aggregation-main.pid --background --startas /bin/bash -- -c "exec $DAEMON $DAEMON_ARGS > log/tree-aggregation-main.log 2>&1"
#        end
#      end
#    end
#  end

end
