#!/bin/bash

# Check if Python is installed
if ! command -v python &> /dev/null
then
	echo "Python is not installed. Please install Python and try again."
	exit 1
fi

# Check if Python version is 3.x
PYTHON_VERSION=$(python -c 'import sys; print(sys.version_info[0])')
if [ "$PYTHON_VERSION" -ne 3 ]; then
	echo "Python 3 is required. Please install Python 3 and try again."
	exit 1
fi

# Start the HTTP server
make
python -m http.server 8080 &
open http://localhost:8080/docs/demo.html
sleep 1
fg 