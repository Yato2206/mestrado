inline chooseRow(){
    if
    :: true -> row = 1;
    :: true -> row = 2;
    :: true -> row = 3;
    :: true -> row = 4;
    :: true -> row = 5;
    :: true -> row = 6;
    :: true -> row = 7;
    :: true -> row = 8;
    fi
}

active proctype Queens(){
    bool a[8];
    bool b[15];
    bool c[15];

    byte row, col = 1;
    do
    :: chooseRow();
        if
        :: a[row-1] || b[row + col - 2] || c[row - col + 7] -> goto FAILURE
        :: else -> skip;
        fi

        a[row-1] = true
        b[row + col - 2] = true 
        c[row - col + 7] = true
        printf("Queen placed in row %d", row)

        if
        :: col == 8 -> break
        :: else -> col++
        fi
    od

SUCCESS:
    printf("SUCCESS!!!!!!!!!!!!!!!!\n"); 
    assert(false)

FAILURE:
    printf("No solution found\n")



}