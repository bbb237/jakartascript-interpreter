const counterClass = 
      (this: { x: Num, 
	       inc: () => Undefined,
	       set: Num => Undefined,
	       get: () => Num}) =>
{
  this.inc = () => { this.set(this.x + 1); };
  this.set = (y: Num) => { this.x = y; };
  this.get = () => { return this.x; };
  return this;
};

const newCounter = function()
	: { const inc: () => Undefined,
	    const set: Num => Undefined, 
	    const get: () => Num }
{
	const this = {
	  x: 0,
	  inc: () => undefined,
	  set: (y: Num) => undefined,
	  get: () => 0
	};
	return counterClass(this);
};

const resetCounter = 
      (this: { y: Num,
	       const inc: () => Undefined,
	       const set: Num => Undefined,
	       const get: () => Num,
	       reset: () => Undefined
	     }) =>
      {
	this.reset = () => { this.set(0); };
	return this;
      };

const newResetCounter =
      function() 
      : { const inc: () => Undefined,
	  const set: Num => Undefined,
	  const get: () => Num,
	  const reset: () => Undefined }
        {
	  const c = newCounter();
	  return resetCounter({
	    y: 0,
	    inc: c.inc,
	    set: c.set,
	    get: c.get,
	    reset: () => undefined
	  })
        };
	
const counterClient = (c: {const inc: () => Undefined}) => {
  c.inc();
  c.inc();
  c.inc();
};

const counter = newResetCounter();

counterClient(counter);
console.log(counter.get());
counter.reset();
counter.get()
