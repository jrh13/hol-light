# This script updates dependency paths for all files in this porject

import argparse
import os
import glob
import re

def parse_args():
    parser = argparse.ArgumentParser(
        description='Updates dependency paths for all files in this project')
    parser.add_argument('--prefix', default='Formal_ineqs', 
                        help='path which should be prepended to all dependency paths')
    args = parser.parse_args()
    args.root = os.path.dirname(os.path.realpath(__file__))
    return args

def collect_local_files(args):
    return set(glob.glob('**/*.hl', root_dir=args.root, recursive=True)) | \
           set(glob.glob('**/*.vhl', root_dir=args.root, recursive=True))

def update_file(path, local_files, args):
    print(f'Updating: {path}')
    with open(path, 'r') as f:
        text = f.read()
    def sub(m):
        if m[2] in local_files:
            return f'{m[1]}{args.prefix}/{m[2]}{m[3]}'
        else:
            return m[0]
    text2 = re.sub(r'\b((?:needs|loads|loadt)\s*\\?")([^\\"]+)(\\?")', sub, text)
    # if text == text2:
    #     print('No changes')
    # else:
    if True:
        with open(path, 'w') as f:
            f.write(text)

def main():
    args = parse_args()
    if not args.prefix:
        print('Empty prefix')
        return
    local_files = collect_local_files(args)
    for fname in sorted(local_files):
        update_file(os.path.join(args.root, fname), local_files, args)

if __name__ == "__main__":
    main()