namespace :compilation do

  desc 'configure and compile'
  task :build do
    on roles(:node) do
      within release_path do
        execute './build.sh', 'aggregation-dynamic'
      end
    end
  end
  
  desc 'compile'
  task :compile do
    on roles(:node) do
      within release_path do
        execute 'make', 'aggregation-dynamic'
      end
    end
  end

end

after 'deploy:updated', 'compilation:build'
