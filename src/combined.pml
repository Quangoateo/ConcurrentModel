#define EXPRESS 0
#define LOCAL 1
#define FREIGHT 2
#define MAINTENANCE 3

#define RED 0
#define GREEN 1
#define FLASHING_YELLOW 2

mtype = {ARRIVAL_REQUEST, TRACK_AVAILABLE, TRACK_UNAVAILABLE, MAINTENANCE_REQUEST};

chan train_requests = [10] of {mtype, int};  // {request type, train type}
chan track_signals = [5] of {int};           // Signals for tracks (track ID)

proctype TrainProcess(int id, int train_type, int track_id) {
    train_requests!ARRIVAL_REQUEST(train_type);

    int signal;
    track_signals?signal;

    if
    :: signal == GREEN ->
        printf("Train %d proceeding on track %d\n", id, track_id);
        track_signals!RED; // Simulate clearing the track
    :: signal == RED ->
        printf("Train %d waiting for track %d\n", id, track_id);
        train_requests!ARRIVAL_REQUEST(train_type); // Retry request
    fi;
}

proctype TrackAllocator() {
    int track_status[5]; // Track status: 0 = free, 1 = occupied
    int current_train_type;
    int i; // Declare the loop variable outside

    do
    :: train_requests?ARRIVAL_REQUEST(current_train_type) ->
        int assigned = -1;
        for (i = 0; i < 5; i++) {
            if
            :: track_status[i] == 0 ->
                assigned = i;
                track_status[i] = 1;
                break;
            fi;
        }

        if
        :: assigned != -1 ->
            track_signals!GREEN;
            printf("Track %d assigned to train type %d\n", assigned, current_train_type);
        :: else ->
            track_signals!RED;
            printf("No track available for train type %d\n", current_train_type);
        fi;
    od;
}

proctype SignalManager() {
    int signal_state = RED;

    do
    :: signal_state == RED ->
        printf("Signal is RED\n");
    :: signal_state == GREEN ->
        printf("Signal is GREEN\n");
    :: signal_state == FLASHING_YELLOW ->
        printf("Signal is FLASHING YELLOW\n");
    od;
}

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
