{
  # Previous overlay
  zchaff,

  # Libraries
  fetchzip,
}:

zchaff.overrideAttrs {
  version = "2008.10.12";

  src = fetchzip {
    url = "http://www.princeton.edu/~chaff/zchaff/zchaff.2008.10.12.zip";
    sha256 = "sha256-sFH+6vhQPkCgmzeMmz1BBykVxZi5uoV0g/gIVGlLS+s=";
  };
}
