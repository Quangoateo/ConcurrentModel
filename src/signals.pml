proctype SignalManager() {
    int signal_state = RED;

    do
    :: atomic {
        signal_state == RED -> printf("Signal is RED\n");
    }
    :: atomic {
        signal_state == GREEN -> printf("Signal is GREEN\n");
    }
    :: atomic {
        signal_state == FLASHING_YELLOW -> printf("Signal is FLASHING YELLOW\n");
    }
    od;
}
