/* Constants */
#define STATION_A 0
#define STATION_B 1
#define STATION_C 2
#define NUM_STATIONS 3

#define TRACK_A1 0
#define TRACK_A2 1
#define TRACK_A3 2
#define TRACK_B4 3
#define TRACK_B5 4
#define TRACK_B6 5
#define TRACK_B7 6
#define TRACK_C8 7
#define TRACK_C9 8
#define TRACK_C10 9
#define NUM_TRACKS 10

#define EXPRESS 4
#define LOCAL 3
#define FREIGHT 2
#define MAINTENANCE 1

#define VACANT 0
#define OCCUPIED 1
#define MAINTENANCE_MODE 2
#define EMERGENCY 3 
#define RESERVED 4

/* Global State */
byte trackStatus[NUM_TRACKS];
byte stationStatus[NUM_STATIONS];
bool trainCompleted[4];  // Track completion status for each train

/* Communication Channels */
chan requestChannel = [20] of { byte, byte, byte, byte }; /* trainId, trainType, sourceStation, destStation */
chan responseChannel = [20] of { byte, byte }; /* trainId, allocatedTrack */
chan emergencyChannel = [5] of { byte }; /* trackId */

/* Function to get track name by index */
inline getTrackName(trackId) {
    if
    :: trackId == TRACK_A1 -> printf("Track_A1")
    :: trackId == TRACK_A2 -> printf("Track_A2")
    :: trackId == TRACK_A3 -> printf("Track_A3")
    :: trackId == TRACK_B4 -> printf("Track_B4")
    :: trackId == TRACK_B5 -> printf("Track_B5")
    :: trackId == TRACK_B6 -> printf("Track_B6")
    :: trackId == TRACK_B7 -> printf("Track_B7")
    :: trackId == TRACK_C8 -> printf("Track_C8")
    :: trackId == TRACK_C9 -> printf("Track_C9")
    :: trackId == TRACK_C10 -> printf("Track_C10")
    fi
}

/* Safety Properties as inline functions */
inline checkNoCollisions() {
    assert(
        trackStatus[TRACK_A1] == VACANT ||
        trackStatus[TRACK_A2] == VACANT ||
        trackStatus[TRACK_A3] == VACANT ||
        trackStatus[TRACK_B4] == VACANT ||
        trackStatus[TRACK_B5] == VACANT ||
        trackStatus[TRACK_B6] == VACANT ||
        trackStatus[TRACK_B7] == VACANT ||
        trackStatus[TRACK_C8] == VACANT ||
        trackStatus[TRACK_C9] == VACANT ||
        trackStatus[TRACK_C10] == VACANT);
}

inline checkMaintenanceSafety() {
    assert(!(trackStatus[TRACK_A3] == MAINTENANCE_MODE && trackStatus[TRACK_A3] == OCCUPIED));
    assert(!(trackStatus[TRACK_B7] == MAINTENANCE_MODE && trackStatus[TRACK_B7] == OCCUPIED));
    assert(!(trackStatus[TRACK_C10] == MAINTENANCE_MODE && trackStatus[TRACK_C10] == OCCUPIED));
}

/* Track Allocator Process */
proctype TrackAllocator() {
    byte trainId, trainType, sourceStation, destStation;
    byte selectedTrack;
    
    do
    :: requestChannel?trainId,trainType,sourceStation,destStation ->
        atomic {
            selectedTrack = 255;
            if
            :: destStation == STATION_A ->
                if
                :: trainType == EXPRESS && trackStatus[TRACK_A1] == VACANT ->
                    selectedTrack = TRACK_A1;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: (trainType == LOCAL || trainType == FREIGHT) && trackStatus[TRACK_A2] == VACANT ->
                    selectedTrack = TRACK_A2;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: trainType == MAINTENANCE && trackStatus[TRACK_A3] == VACANT ->
                    selectedTrack = TRACK_A3;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                fi
            :: destStation == STATION_B ->
                if
                :: trainType == EXPRESS && trackStatus[TRACK_B4] == VACANT ->
                    selectedTrack = TRACK_B4;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: trainType == LOCAL && trackStatus[TRACK_B5] == VACANT ->
                    selectedTrack = TRACK_B5;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: trainType == FREIGHT && trackStatus[TRACK_B6] == VACANT ->
                    selectedTrack = TRACK_B6;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: trainType == MAINTENANCE && trackStatus[TRACK_B7] == VACANT ->
                    selectedTrack = TRACK_B7;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                fi
            :: destStation == STATION_C ->
                if
                :: trainType == EXPRESS && trackStatus[TRACK_C8] == VACANT ->
                    selectedTrack = TRACK_C8;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: trainType == LOCAL && trackStatus[TRACK_C9] == VACANT ->
                    selectedTrack = TRACK_C9;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                :: (trainType == FREIGHT || trainType == MAINTENANCE) && trackStatus[TRACK_C10] == VACANT ->
                    selectedTrack = TRACK_C10;
                    printf("Allocated to train %d:", trainId);
                    getTrackName(selectedTrack);
                    printf("\n")
                fi
            fi;

            if
            :: (selectedTrack != 255) ->
                trackStatus[selectedTrack] = RESERVED;
                responseChannel!trainId,selectedTrack;
                checkNoCollisions();
            :: else ->
                printf("No track available for train %d, requeueing\n", trainId);
                requestChannel!trainId,trainType,sourceStation,destStation
            fi
        }
    od
}

/* Train Process */
proctype Train(byte id; byte type; byte source; byte dest) {
    byte allocatedTrack;
    
    printf("Train %d (type %d) requesting track from station %d to %d\n", id, type, source, dest);
    requestChannel!id,type,source,dest;
    
    responseChannel??eval(id),allocatedTrack;
    printf("Train %d received track allocation: ", id);
    getTrackName(allocatedTrack);
    printf("\n");
    
    atomic {
        assert(trackStatus[allocatedTrack] == RESERVED);
        checkNoCollisions();
        trackStatus[allocatedTrack] = OCCUPIED;
        printf("Train %d occupying ", id);
        getTrackName(allocatedTrack);
        printf("\n");
        
        /* Simulate journey */
        timeout;
        
        trackStatus[allocatedTrack] = VACANT;
        trainCompleted[id] = true;
        printf("Train %d completed journey and released ", id);
        getTrackName(allocatedTrack);
        printf("\n");
    }
}

/* Initialization */
init {
    byte i;
    
    atomic {
        /* Initialize track status */
        for(i : 0 .. NUM_TRACKS-1) {
            trackStatus[i] = VACANT;
        }
        /* Initialize station status */
        for(i : 0 .. NUM_STATIONS-1) {
            stationStatus[i] = VACANT;
        }
        /* Initialize train completion status */
        for(i : 0 .. 3) {
            trainCompleted[i] = false;
        }
    }
    
    /* Start core processes */
    run TrackAllocator();
    
    /* Start sample trains */
    run Train(0, EXPRESS, STATION_A, STATION_B);
    run Train(1, LOCAL, STATION_B, STATION_C);
    run Train(2, FREIGHT, STATION_A, STATION_C);
}
