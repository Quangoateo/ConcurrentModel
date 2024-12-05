proctype TrackAllocator() {
    int track_status[5]; // Track status: 0 = free, 1 = occupied
    int current_train_type;
    int i;               // Declare loop variable outside the loop

    do
    :: train_requests?ARRIVAL_REQUEST, current_train_type ->
        int assigned = -1;
        for (i = 0; i < 5; i++) { // Promela doesn't allow inline variable declarations in loops
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
