(let ([y (let ([x (read)])
  (+ x (let ([x (+ (+ 12 (read)) (- 18))]) x)))])
y)
