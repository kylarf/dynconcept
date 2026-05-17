import ../src/dynconcept


proc box[T](self: sink T): ref T =
  result = new T
  result[] = self


type
  Animal* {.dynamic.} = concept
    proc speak(self: Self): void
    proc act(self: Self): void


type
  Dog* = object of RootObj
    name: string

impl(Dog, Animal):
  proc speak*(self: Dog): void =
    echo self.name, " says woof"

  proc act*(self: Dog): void =
    echo "wag"

proc speak*(self: ref Dog): void =
  echo self[].name, " says woof"

proc act*(self: ref Dog): void =
  echo "wag"

impl(ref Dog, Animal)

type
  Cat* = ref object
    name: string
    lives: int

proc speak*(self: Cat): void =
  echo self.name, " says meow"

proc act*(self: Cat): void =
  echo "climb tree because I have ", self.lives, " lives"

impl(Cat, Animal)

proc exerciseAnimal(animal: Animal) =
  echo "merely the concept of an animal"
  animal.speak()
  animal.act()

var seqAnimal = newSeq[dyn Animal]()

var fido = box Dog(name: "fido")
fido.speak()
fido.act()
fido.exerciseAnimal()
echo ""

var boris = Cat(name: "boris", lives: 9)
boris.speak()
boris.act()
boris.exerciseAnimal()
echo ""

echo "now from the dyn concept"

seqAnimal.add(boris.into(dyn Animal))
seqAnimal.add(fido)

for animal in seqAnimal:
  animal.speak()
  animal.act()
  animal.exerciseAnimal()
  echo ""
