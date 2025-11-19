#include "hacl.h"

void hacl_free(void *ptr)
{
    if (ptr)
    {
        free(ptr);
    }
}