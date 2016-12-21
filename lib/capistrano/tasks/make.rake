namespace :make do

  desc 'configure and make'
  task :build do
    on roles(:node) do
      within "#{current_path}" do
        execute './build.sh', 'aggregation-dynamic'
      end
    end
  end
  
  desc 'make'
  task :make do
    on roles(:node) do
      within "#{current_path}" do
        execute 'make', 'aggregation-dynamic'
      end
    end
  end

end
