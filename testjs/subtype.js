/*function (f1: () => {var f: Num}) {
  return function (f2: ({}) => Undefined) {
    return f2(f1());
  }
}*/

const f1 = function (x: {const f: Bool}) { return undefined; };
const f2 = function (x: {var f: Any, const g: Num}) { return undefined; };

true ? f1 : f2
