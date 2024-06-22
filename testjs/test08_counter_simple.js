const counterClass = function(rep: {let x: Num}) {
	return {
		inc: function() { rep.x = rep.x + 1; },
		get: function() { return rep.x; }
  };
};

const newCounter = function() {
	const rep = { x: 0 };
	return counterClass(rep);
};

const counterClient = function(c: {let inc: () => Undefined, let get: () => Num}) {
   c.inc();
   c.inc();
   c.inc();
};

const counter = newCounter();

counterClient(counter);
console.log(counter.get());
