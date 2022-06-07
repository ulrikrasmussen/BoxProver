#!/bin/bash
server_url=${1:-http://localhost:8000}
echo "var SERVER_URL = '$server_url'" > /opt/boxprover/frontend/config.js
/opt/boxprover/boxprover \
      --twelf-server=/opt/boxprover/twelf-server \
      --base-sig=/opt/boxprover/data/fitch.elf \
      --check-log=/opt/boxprover/check.log \
      --access-log=/opt/boxprover/access.log \
      --error-log=/opt/boxprover/error.log \
      -p 8000
