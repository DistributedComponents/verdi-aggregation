namespace :aggregation do

  def pid_path
    "#{current_path}/extraction/aggregation-dynamic/tmp/tree-aggregation-main.pid"
  end

  def log_path
    "#{shared_path}/extraction/aggregation-dynamic/log/tree-aggregation-main.log"
  end
  
  desc 'start aggregation'
  task :start do
    nodes = Hash[roles(:node).collect { |s| [s.properties.name, s] }]
    on roles(:node) do |node|
      cluster = node.properties.adjacent.collect { |n| "-node #{n},#{nodes[n].properties.host}:#{fetch(:node_port)}" }
      cluster << "-node #{node.properties.name},#{node.properties.host}:#{fetch(:node_port)}"
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{pid_path}",
        '--background',
        "--chdir #{current_path}/extraction/aggregation-dynamic",
        '--startas /bin/bash',
        "-- -c 'exec ./TreeAggregationMain.native -debug -me #{node.properties.name} -port #{fetch(:client_port)} -aggregate-timeout #{fetch(:aggregate_timeout)} -broadcast-timeout #{fetch(:broadcast_timeout)} -read-mic-timeout #{fetch(:read_mic_timeout)} -device #{fetch(:device)} -channels #{fetch(:channels)} #{cluster.join(' ')} > log/tree-aggregation-main.log 2>&1'"
    end
  end

  desc 'stop aggregation'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        '--oknodo',
        "--pidfile #{pid_path}"
    end
  end

  desc 'tail aggregation log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', log_path
    end
  end

  desc 'truncate aggregation log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', log_path
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
    on roles(:root) do
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
      roles(:root).each do |node|
        info %x(python2.7 extraction/aggregation-dynamic/script/aggregationctl.py --host #{node.properties.host} --port #{fetch(:client_port)} aggregate)
      end
    end
  end

  desc 'set local data to LOCAL'
  task :local do
    on roles(:node) do
      execute 'python2.7',
        "#{current_path}/extraction/aggregation-dynamic/script/aggregationctl.py",
        '--host localhost',
        "--port #{fetch(:client_port)}",
        'local',
        ENV['LOCAL']
    end
  end

  desc 'get amplitude'
  task :amplitude do
    on roles(:root) do
      execute 'python2.7',
        "#{current_path}/extraction/aggregation-dynamic/script/amplitude.py",
        '--host localhost',
        "--port #{fetch(:client_port)}"
    end
  end

  desc 'set local data on NAME (remotely)'
  task :local_locally do
    run_locally do
      roles(:node, name: ENV['NAME']).each do |node|
        %x(python2.7 extraction/aggregation-dynamic/script/aggregationctl.py --host #{node.properties.host} --port #{fetch(:client_port)} local #{ENV['LOCAL']})
      end
    end
  end

end
