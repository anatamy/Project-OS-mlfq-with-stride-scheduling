#include "types.h"
#include "stat.h"
#include "user.h"

int man(int argc, char * argv[])
{
    printf(1,"My pid is %d\n", getpid());
    printf(1, "Myppid is %d\n", getppid());
    exit();
}
