namespace :aggregation do
  
  desc 'start aggregation'
  task :start do
    servers = Hash[roles(:node).collect { |s| [s.properties.name, s] }]
    on roles(:node) do |server|
      cluster = server.properties.adjacent.collect { |n| "-node #{n},#{servers[n].hostname}:#{fetch(:node_port)}" }
      cluster << "-node #{server.properties.name},#{server.hostname}:#{fetch(:node_port)}"
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--make-pidfile',
        "--pidfile #{current_path}/extraction/aggregation-dynamic/tmp/tree-aggregation-main.pid",
        '--background',
        "--chdir #{current_path}/extraction/aggregation-dynamic",
        '--startas /bin/bash',
        "-- -c 'exec ./TreeAggregationMain.native -debug -me #{server.properties.name} -port #{fetch(:client_port)} #{cluster.join(' ')} > log/tree-aggregation-main.log 2>&1'"
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
      execute 'tail',
        '-n 20',
        "#{shared_path}/extraction/aggregation-dynamic/log/tree-aggregation-main.log"
    end
  end

  desc 'truncate aggregation log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate',
        '-s 0',
        "#{shared_path}/extraction/aggregation-dynamic/log/tree-aggregation-main.log"
    end
  end

  desc 'get aggregate'
  task :aggregate do
    root = roles(:node, name: "0").first
    run_locally do
      info %x(python2.7 extraction/aggregation-dynamic/script/aggregationctl.py --hostname #{root.hostname} --port #{fetch(:client_port)} aggregate)
    end
  end

end
