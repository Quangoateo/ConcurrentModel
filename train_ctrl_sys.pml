mtype = { REQUEST, GRANT, RELEASE };  // Message types for train-track communication
chan control_channel = [5] of { mtype, int };  // Communication channel for control logic
int tracks[3] = {1, 1, 1};  // Array to represent track availability (1 = free, 0 = occupied)

// Train Process
proctype Train(int id; int track_id) {
    printf("Train %d: Requesting track %d\n", id, track_id);
    control_channel!REQUEST, track_id;  // Request the track
    control_channel?GRANT, track_id;    // Wait for permission to use the track
    printf("Train %d: Granted access to track %d\n", id, track_id);
    
    // Simulate train using the track
    printf("Train %d: Using track %d\n", id, track_id);
    
    // Release the track after usage
    printf("Train %d: Releasing track %d\n", id, track_id);
    control_channel!RELEASE, track_id;
}

// Track Controller Process
proctype TrackController() {
    mtype msg;
    int track_id;

    do
    :: control_channel?REQUEST, track_id ->
        if
        :: tracks[track_id] == 1 ->  // If the track is free
            tracks[track_id] = 0;    // Mark it as occupied
            printf("Track Controller: Granting track %d\n", track_id);
            control_channel!GRANT, track_id
        :: else ->
            printf("Track Controller: Track %d is occupied, train must wait\n", track_id);
        fi
    :: control_channel?RELEASE, track_id ->
        tracks[track_id] = 1;  // Mark track as free
        printf("Track Controller: Track %d is now free\n", track_id);
    od
}

// Initialization
init {
    atomic {
        // Run the Track Controller
        run TrackController();
        // Run multiple trains
        run Train(1, 0);  // Train 1 wants track 0
        run Train(2, 1);  // Train 2 wants track 1
        run Train(3, 0);  // Train 3 wants track 0 (to test waiting)
    }
}
