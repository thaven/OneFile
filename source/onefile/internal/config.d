/*
 * Copyright 2017-2019
 *   Andreia Correia <andreia.veiga@unine.ch>
 *   Pedro Ramalhete <pramalhe@gmail.com>
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Nachshon Cohen <nachshonc@gmail.com>
 *
 * Modified for D by Harry T. Vennik.
 *
 * Copyright 2019
 *   Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */
module onefile.internal.config;

struct Config
{
    ushort registryMaxThreads = 128;
    ulong txMaxStores = 40*1024;
    ulong hashBuckets = 1024;
    ulong txMaxAllocs = 10*1024;
    ulong txMaxRetires = 10*1024;
}

enum Config config = Config.init;
