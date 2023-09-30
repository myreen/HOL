double f(double x, double y)
{
	return x*y;
}

double g(double x, double y, double z)
{
	return x*y + z;
}

double h(double x)
{
	return x + 12.0;
}

double i(double x, double y)
{
	return x/y;
}

double j(double x, double y)
{
	return x + y;
}

double k(double x, double y)
{
	return x - y;
}

void m(void)
{
	__asm__ (
		"str d0, [sp, #8]\n"
		"str d1, [sp]\n"
		"ldr d1, [sp, #8]\n"
		"ldr d0, [sp]\n"
		"fcmpe d1, d0\n"
		"ldr d1, [sp, #8]\n"
		"ldr d0, [sp]\n"
		"fsub d0, d1, d0\n"
		"str d0, [sp, #40]\n"
		"ldr d0, [sp, #40]\n"
		"fmov d1, x0\n"
		"fadd d0, d0, d1\n"
		"str d0, [sp, #48]\n"
		"ldr d0, [sp, #40]\n"
		"str d0, [sp, #32]\n"
		"ldr d0, [sp, #48]\n"
		"str d0, [sp, #32]\n"
		"ldr d0, [sp, #32]\n"
		"str d0, [sp, #56]\n"
		"ldr d0, [sp, #56]\n"
	);
}
