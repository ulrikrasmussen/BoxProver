#!/bin/bash
server_url=${1:-http://localhost:8000}
echo "var SERVER_URL = '$server_url'" > /opt/boxprover/frontend/config.js
/opt/boxprover/boxprover \
      --twelf-server=/opt/boxprover/twelf-server \
      --base-sig=/opt/boxprover/data/fitch.elf \
      --check-log=/opt/boxprover/log/check.log \
      --access-log=/opt/boxprover/log/access.log \
      --error-log=/opt/boxprover/log/error.log \
      -p 8000
