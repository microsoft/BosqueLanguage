const prependFile = require('prepend-file');
const file = './bin/runtimes/exegen/exegen.js';

prependFile(file, '#!/usr/bin/env node\n', function (err) {
    if (err) {
      console.log('Error while executing make-exe script: ' + err);
    }
});
