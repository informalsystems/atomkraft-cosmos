#!/usr/bin/env bash

java -XX:+UseParallelGC -classpath ~/dev/tla/tools/tla2tools.jar tlc2.TLC GovMC
