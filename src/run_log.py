# This script will run the verification once, store the cache
# And then run the verification n times and store the logs in a folder

import os


def run_verification(log_file_path=None):
    if log_file_path is None:
        command = (
            f"stainless-dotty --config-file=stainless.conf --no-colors ListUtils.scala"
        )
    else:
        command = f"stainless-dotty --config-file=stainless.conf --no-colors ListUtils.scala > {log_file_path}"

    print(command)
    os.system(command)
    if log_file_path:
        move_file_to_logs_folder(log_file_path)


def move_file_to_logs_folder(log_file_name):
    os.system(f"mv {log_file_name} {logs_folder}")


def delete_current_cache():
    os.system("rm -rf .stainless-cache")


def store_cache_away(cache_file_backup_name: str):
    os.system(
        f"cp -r .stainless-cache/vccache.bin .stainless-cache/{cache_file_backup_name}"
    )


def replace_cache_with_backup(cache_file_backup_name: str):
    os.system(
        f"cp -r .stainless-cache/{cache_file_backup_name} .stainless-cache/vccache.bin"
    )


# Takes n from the arguments and run the verification n times

if __name__ == "__main__":
    import sys
    import time

    current_date = time.strftime("%Y-%m-%d_%H-%M-%S")
    cache_backup_file_name = f"vccache_backup_{current_date}.bin"
    logs_folder = f"logs_auto_{current_date}"
    if not os.path.exists(logs_folder):
        os.mkdir(logs_folder)

    def logs_file_name(n):
        return f"log_run_{n:05d}.txt"

    delete_current_cache()
    n = int(sys.argv[1])
    run_verification(logs_file_name(0))
    store_cache_away(cache_backup_file_name)
    for i in range(1, n + 1):
        replace_cache_with_backup(cache_backup_file_name)
        run_verification(logs_file_name(i))
