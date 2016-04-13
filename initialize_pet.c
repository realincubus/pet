#include <isl/arg.h>
#include <isl/ctx.h>
#include <isl/options.h>

#include "initialize_pet.h"

#include "scop.h"
#include "scop_yaml.h"

struct options {
	struct isl_options	*isl;
	struct pet_options	*pet;
	char			*input;
};

ISL_ARGS_START(struct options, options_args)
ISL_ARG_CHILD(struct options, isl, "isl", &isl_options_args, "isl options")
ISL_ARG_CHILD(struct options, pet, NULL, &pet_options_args, "pet options")
ISL_ARG_ARG(struct options, input, "input", NULL)
ISL_ARGS_END

ISL_ARG_DEF(options, struct options, options_args)

struct isl_ctx* initialize_pet_options( int argc, char** argv)
{
    struct options* options = options_new_with_defaults();
    isl_ctx* ctx = isl_ctx_alloc_with_options(&options_args, options);
    // TODO enable if you need the arguments: options_parse(options, argc, argv, ISL_ARG_ALL);
    return ctx;
}
