init {
    // Start track allocator
    run TrackAllocator();

    // Start signal manager
    run SignalManager();

    // Start train processes
    run TrainProcess(1, EXPRESS, 2);
    run TrainProcess(2, LOCAL, 3);
    run TrainProcess(3, FREIGHT, 4);
}
