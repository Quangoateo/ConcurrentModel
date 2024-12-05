chan train_requests = [10] of {mtype, int};  // {request type, train type}
chan track_signals = [5] of {int};           // Signals for tracks (track ID)

proctype TrainProcess(int id, int train_type, int track_id) {
    train_requests!ARRIVAL_REQUEST, train_type;

    int signal;
    track_signals?signal;

    if
    :: signal == GREEN ->
        printf("Train %d proceeding on track %d\n", id, track_id);
        track_signals!RED; // Simulate clearing the track
    :: signal == RED ->
        printf("Train %d waiting for track %d\n", id, track_id);
        train_requests!ARRIVAL_REQUEST, train_type; // Retry request
    fi;
}
