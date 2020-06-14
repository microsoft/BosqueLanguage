const prependFile = require('prepend-file');
const chmod = require('chmod');
const file = './bin/runtimes/exegen/exegen.js';

prependFile(file, '#!/usr/bin/env node\n', function (err) {
    if (err) {
      console.log('Error while executing make-exe script: ' + err);
    }
});

chmod(file, {
  owner: {
    read: true,
    write: true,
    execute: true
  },
  group: {
    read: true,
    write: true,
    execute: true
  },
  others: {
    read: true,
    write: false,
    execute: true
  }
});
