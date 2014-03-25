fun factorial 0 = 1
  | factorial n = n * factorial (n - 1);

factorial 10;
factorial 100;
factorial 1000;
