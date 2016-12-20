namespace :make do

  desc 'configure and make'
  task :run_build do
    on roles(:node) do
      within "#{current_path}" do
        execute './build.sh', 'aggregation-dynamic'
      end
    end
  end
  
  desc 'make'
  task :run_make do
    on roles(:node) do
      within "#{current_path}" do
        execute :make
      end
    end
  end

end
