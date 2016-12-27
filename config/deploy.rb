# config valid only for current version of Capistrano
lock "3.7.1"

set :application, "verdi-aggregation"
set :repo_url, "git@github.com:DistributedComponents/verdi-aggregation.git"

# Default branch is :master
# ask :branch, `git rev-parse --abbrev-ref HEAD`.chomp

# Default deploy_to directory is /var/www/my_app_name
set :deploy_to, "/home/pi/lib/verdi-aggregation"

# Default value for :format is :airbrussh.
# set :format, :airbrussh

# You can configure the Airbrussh format using :format_options.
# These are the defaults.
# set :format_options, command_output: true, log_file: "log/capistrano.log", color: :auto, truncate: :auto

# Default value for :pty is false
# set :pty, true

# Default value for :linked_files is []
# append :linked_files, "config/database.yml", "config/secrets.yml"

# Default value for linked_dirs is []
# append :linked_dirs, "log", "tmp/pids", "tmp/cache", "tmp/sockets", "public/system"
append :linked_dirs, "extraction/aggregation-dynamic/tmp", "extraction/aggregation-dynamic/log"

# Default value for default_env is {}
# set :default_env, { path: "/opt/ruby/bin:$PATH" }
set :default_env, { 
  "Verdi_PATH" => "/home/pi/lib/verdi/current",
  "StructTact_PATH" => "/home/pi/lib/StructTact/current",
  "InfSeqExt_PATH" => "/home/pi/lib/InfSeqExt/current"
}

# Default value for keep_releases is 5
set :keep_releases, 3

after "deploy:published", "compilation:build"
