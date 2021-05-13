//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "op_eval.h"

#include <boost/json.hpp>

bool loadJSONFromFile(const std::string& filename, boost::json::value& jval);

void initialize();
void loadAssembly(const boost::json::value& jval);
void run(const std::string& main, StorageLocationPtr res);
