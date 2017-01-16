namespace :aggregation do
  
  desc 'start aggregation'
  task :start do
    servers = Hash[roles(:node).collect { |s| [s.properties.name, s] }]
    on roles(:node) do |server|
      cluster = server.properties.adjacent.collect { |n| "-node #{n},#{servers[n].properties.host}:#{fetch(:node_port)}" }
      cluster << "-node #{server.properties.name},#{server.properties.host}:#{fetch(:node_port)}"
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
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
        '--oknodo',
        "--pidfile #{current_path}/extraction/aggregation-dynamic/tmp/tree-aggregation-main.pid"
    end
  end

  desc 'tail aggregation log'
  task :tail_log do
    on roles(:node) do
      execute :tail,
        '-n 20',
        "#{shared_path}/extraction/aggregation-dynamic/log/tree-aggregation-main.log"
    end
  end

  desc 'truncate aggregation log'
  task :truncate_log do
    on roles(:node) do
      execute :truncate,
        '-s 0',
        "#{shared_path}/extraction/aggregation-dynamic/log/tree-aggregation-main.log"
    end
  end

  desc 'list nodes and properties'
  task :list do
    run_locally do
      roles(:node).each do |node|
        info "#{node.hostname} #{node.properties.host} #{node.properties.name} #{node.properties.adjacent}"
      end
    end
  end

  desc 'get aggregate'
  task :aggregate do
    on roles(:node, name: '0') do |root|
      execute 'python2.7',
        "#{current_path}/extraction/aggregation-dynamic/script/aggregationctl.py",
        '--host localhost',
        "--port #{fetch(:client_port)}",
        'aggregate'
    end
  end

  desc 'get aggregate (remote)'
  task :aggregate_locally do
    run_locally do
      roles(:node, name: '0').each do |root|
        info %x(python2.7 extraction/aggregation-dynamic/script/aggregationctl.py --host #{root.properties.host} --port #{fetch(:client_port)} aggregate)
      end
    end
  end

  desc 'set local data'
  task :local do
    on roles(:node) do |node|
      execute 'python2.7',
        "#{current_path}/extraction/aggregation-dynamic/script/aggregationctl.py",
        '--host localhost',
        "--port #{fetch(:client_port)}",
        'local',
        ENV['LOCAL']
    end
  end

  desc 'set local data (remote)'
  task :local_locally do
    run_locally do
      roles(:node, name: ENV['NAME']).each do |node|
        %x(python2.7 extraction/aggregation-dynamic/script/aggregationctl.py --host #{node.properties.host} --port #{fetch(:client_port)} local #{ENV['LOCAL']})
      end
    end
  end

end
