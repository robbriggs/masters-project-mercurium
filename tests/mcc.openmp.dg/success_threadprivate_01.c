int a;

#pragma omp threadprivate(a)

void f(void)
{
    a = 3;
}
