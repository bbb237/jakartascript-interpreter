const fac = function(n: Num) {
    let x = 1;
    let i = 1;
    (function facAcc(): Undefined {
       i < n ? (x = x * (i = i + 1), facAcc()) : undefined;
     })();
    return x;
  };
fac(5)