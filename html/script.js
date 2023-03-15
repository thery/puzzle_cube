//create the scene
const scene = new THREE.Scene();

//create the camera
const camera = new THREE.PerspectiveCamera(
  90,
  window.innerWidth / window.innerHeight,
  0.1,
  500
);
camera.position.z = 5;
camera.position.y = 2;
camera.position.x = 0;

// Our two colours
const colorFree   = new THREE.Color('white');
const colorLocked = new THREE.Color('skyblue');
const colorWon   = new THREE.Color('coral');

// Our two mats 
const matLocked = new THREE.MeshBasicMaterial({color: colorLocked});
const matFree   = new THREE.MeshBasicMaterial({color: colorFree});
const matWon   = new THREE.MeshBasicMaterial({color: colorWon});

// Our six axis 
const axisPX = new THREE.Vector3( 1, 0, 0);
const axisNX = new THREE.Vector3(-1, 0, 0);
const axisPY = new THREE.Vector3( 0, 1, 0);
const axisNY = new THREE.Vector3( 0,-1, 0);
const axisPZ = new THREE.Vector3( 0, 0, 1);
const axisNZ = new THREE.Vector3( 0, 0,-1);

// create the main cube
const geometry = new THREE.BoxGeometry(1, 1, 1);

// The six materials
var material = [
    matFree,
    matFree,
    matFree,
    matFree,
    matFree,
    matFree,
];
const cube = new THREE.Mesh(geometry, material);

// show the border 
const geo = new THREE.EdgesGeometry( cube.geometry );
const mat = new THREE.LineBasicMaterial( { color: 0x000000 } );
const wireframe = new THREE.LineSegments( geo, mat );
cube.add( wireframe );

// The initial position
cube.position.z = 0.5;
cube.position.y = 0.5;
cube.position.x = 0.5;

//add the main cube to scene
scene.add(cube);
cube.visible = false;

var isWon = false; 
// Check if a cube is all colored 
function isCubeWon () {
  for(var i = 0; i < 6; i++) {
    if (cube.material[i] == matFree) {
      return false;
    }
  }
  isWon = true;
  return true;
}

// Set cube is all colored 
function setCubeWon () {
  for(var i = 0; i < 6; i++) {
    cube.material[i] = matWon;
  }
  renderer.render(scene, camera);
}

// Getting the difference faces of the cube 
function getFace(ax1) {
  var ax = cube.worldToLocal(ax1).multiplyScalar(2);
  ax.x = Math.round(ax.x);
  ax.y = Math.round(ax.y);
  ax.z = Math.round(ax.z);  
  if (ax.equals(axisPX)) {
    return 0;
  }
  if (ax.equals(axisNX)) {
    return 1;
  }
  if (ax.equals(axisPY)) {
    return 2;
  }
  if (ax.equals(axisNY)) {
    return 3;
  }
  if (ax.equals(axisPZ)) {
    return 4;
  }
  if (ax.equals(axisNZ)) {
    return 5;
  }
}
function getFaceDown() {
  return getFace(
    new THREE.Vector3(cube.position.x, cube.position.y - 0.5, cube.position.z));
};
function getFaceUp() {
  return getFace(
    new THREE.Vector3(cube.position.x, cube.position.y + 0.5, cube.position.z));
};
function getFaceEast() {
  return getFace(
    new THREE.Vector3(cube.position.x + 0.5, cube.position.y, cube.position.z));
};
function getFaceWest() {
  return getFace(
    new THREE.Vector3(cube.position.x - 0.5, cube.position.y, cube.position.z));
};
function getFaceNorth() {
  return getFace(
    new THREE.Vector3(cube.position.x, cube.position.y, cube.position.z + 0.5));
};
function getFaceSouth() {
  return getFace(
    new THREE.Vector3(cube.position.x, cube.position.y, cube.position.z - 0.5));
};

// Check if a face is selected 
function isFaceSelected(i) {
  return (cube.material[i] == matLocked); 
}

// Round with 2 digits
function round2(x) {
  return (Math.round(x * 10) / 10);
}

// Round with 6 digits
function round(x) {
  return (Math.round(x * 100000) / 100000);
}

// Normalize the cube position and rotaton
function roundCube() {
  cube.position.x = round(cube.position.x);
  cube.position.y = round(cube.position.y);
  cube.position.z = round(cube.position.z);
  cube.rotation.x = 
    round(cube.rotation.x / Math.PI) * Math.PI;
  cube.rotation.y = 
    round(cube.rotation.y / Math.PI) * Math.PI;
  cube.rotation.z = 
    round(cube.rotation.z / Math.PI) * Math.PI;
}

// The dimension of the board 
const size = 4;
const divisions = 4;

// The board
var board = new Array(size);

// Number of squares that are locked
var numberOfLocked = 0;

// Initialize the board
function initBoard () {
  for (var i = 0; i < size; i++) {
    board[i] = new Array(size);
    for (var j = 0; j < size; j++) {
      var geometry = new THREE.BoxGeometry(1, .1, 1);
      var cube = new THREE.Mesh(geometry, matFree);
      cube.position.x = -1.5 + i;
      cube.position.y = -0.1;
      cube.position.z = -1.5 + j;
      board[i][j] = cube;
      var geo = new THREE.EdgesGeometry(cube.geometry);
      var mat = new THREE.LineBasicMaterial({color: 0x000000 });
      mat.linewidth = 2;
      var wireframe = new THREE.LineSegments(geo, mat);
      cube.add(wireframe);
      scene.add(cube);
    }
  }
}

initBoard();

// Get Square
function getSquare(x, y) {
  return board[x][y];
}

// Select/Unselect a square
function toggleSquare(x, y) {
  var square = getSquare(x, y);
  if (square.material == matLocked) {
    square.material = matFree;
    numberOfLocked -= 1;
  } else {
    square.material = matLocked;
    numberOfLocked += 1;
  }
}

// Check if a square is selected 
function isSquareSelected(i, j) {
  return (getSquare(i, j).material == matLocked); 
}

// Find the square that is under the cube
function getSquareUnderCube() {
  for(var i = 0; i < 4; i++) {
    for(var j = 0; j < 4; j++) {
      var square = getSquare(i, j);
      if ((square.position.x == cube.position.x) &&
          (square.position.z == cube.position.z)) {
        return square;
      }
    }
  }
}

// Exchange the color of the down face of the cube with the square underneath
function swapSquareCube() {
  var face = getFaceDown();
  var square = getSquareUnderCube();
  if ((face == null) || (square == null)) {
    return;
  }
  var mat = square.material;
  square.material = cube.material[face];
  cube.material[face] = mat;
} 

function resetCubeBoard() {
  for(var i = 0; i < 6; i++) {
    cube.material[i] = matFree;
  }
  cube.visible = false;
  isWon = false;
  for(var i = 0; i < 4; i++) {
    for (var j = 0; j < 4; j++) {
      getSquare(i, j).material = matFree;
    }
  }
  numberOfLocked = 0;
}

//create renderer
var renderer = new THREE.WebGLRenderer();
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.render(scene, camera);

// Get next move to solve the current position 
function getNextMove() {
  var i = 1 + 2 * cube.position.x; 
  var j = 1 + 2 * cube.position.y;
  var cubePos = new Array(6);
  cubePos[0] = isFaceSelected(getFaceDown());
  cubePos[1] = isFaceSelected(getFaceWest());
  cubePos[2] = isFaceSelected(getFaceSouth());
  cubePos[3] = isFaceSelected(getFaceNorth());
  cubePos[4] = isFaceSelected(getFaceEast());
  cubePos[5] = isFaceSelected(getFaceTop());
  var boardPos = new Array(4);
  for (var i = 0; i < 4; i++) {
    boardPos[i] = new Array(4);
  }
  for (var i = 0; i < 4; i++) {
    for (var j = 0; j < 4; j++) {
      boardPos[i][j] = isSquareSelected(i, j);
    }
  }
  // The position is in the lower part of the board, we need to do a 180 degre
  var swap = (2 <= j);
  var k = true;
  if (swap == true) {
    j = 3 - j;
    for (var i = 0; i < 4; i++) {
      for (var j = 0; j < 2; j++) {
        k = boardPos[i][j];
        boardPos[i][j] = boardPos[i][3 - j];
        boardPos[i][3 - j] = k;
      }
    } 
    k = cubePos[1];
    cubePos[1] = cubePos[4];
    cubePos[4] = k;
    k = cubePos[2];
    cubePos[2] = cubePos[3];
    cubePos[3] = k;
  }
  // The position is in the right part of the board, we need to do a 180 degre
  var turn = (2 <= i);
  if (turn == true) {
    j = 2 - j;
    for (var i = 0; i < 2; i++) {
      for (var j = i; j < 3 - i; j++) {
        k = boardPos[i + j][i];
        boardPos[i + j][i] = boardPos[3 - i][i + j];
        boardPos[3 - i][i + j] = boardPos[3 - (i + j)][3 - i];
        boardPos[3 - (i + j)][3 - i] = boardPos[i][3 - (i + j)];
        boardPos[i][3 - (i + j)] = k;
      }
    } 
    k = cubePos[1];
    cubePos[1] = cubePos[3];
    cubePos[3] = cubePos[4];
    cubePos[4] = cubePos[2];
    cubePos[2] = k;
  }

}

// Animation speed
var rx = 4 * 1 / 100;
var rr = 4 * Math.PI / 200;

// Keep the current rotation during animation
var rot = 0;

// Move along X+ and rotate along Z-
function moveXP () {
  cube.rotateOnWorldAxis(axisPZ, -rr);
  rot -= rr;
  cube.position.y = round(0.5 - 0.2 * Math.sin (2 * rot));
  cube.position.x += rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    roundCube();
    swapSquareCube();
    if (isCubeWon()) {
      setCubeWon();
    }
  }
}

// Move along X- and rotate along Z+
function moveXN () {
  cube.rotateOnWorldAxis(axisPZ, +rr);
  rot += rr;
  cube.position.y = round(0.5 + 0.2 * Math.sin (2 * rot));
  cube.position.x -= rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    roundCube();
    swapSquareCube();
    if (isCubeWon()) {
      setCubeWon();
    }
  }
};

// Move along Z+ and rotate along X+
function moveZP () {
  cube.rotateOnWorldAxis(axisPX, +rr);
  rot += rr;
  cube.position.y = round(0.5 + 0.2 * Math.sin (2 * rot));
  cube.position.z += rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    roundCube();
    swapSquareCube();
    if (isCubeWon()) {
      setCubeWon();
    }
  }
};

// Move along Z- and rotate along X-
function moveZN () {
  cube.rotateOnWorldAxis(axisPX, -rr);
  rot -= rr;
  cube.position.y = round(0.5 - 0.2 * Math.sin (2 * rot));
  cube.position.z -= rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    roundCube();
    swapSquareCube();
    if (isCubeWon()) {
      setCubeWon();
    }
  }
};

// Where the cube is going to
var gx = cube.position.x;
var gz = cube.position.z;

// animation loop
function animate () {
  requestAnimationFrame(animate);
  var x = cube.position.x;
  var z = cube.position.z;
  if (((gx != x) || (gz != z)) && !isWon) {
    if (gx < x) {
      moveXN();
    } else if (gx > x) {
      moveXP();
    } else if (gz < z) {
      moveZN();
    } else if (gz > z) {
      moveZP();
    }
    renderer.render(scene, camera);
  }
};

var mouse = new THREE.Vector2();
var axis = new THREE.Vector3();
var raycaster = new THREE.Raycaster();

// get the square that is touched by the ray
function getSelectedSquare (raycaster) {
  let intersects = raycaster.intersectObjects(scene.children);
  for (var z = 0; z < intersects.length; z++) {
        selectedPiece = intersects[z].object;
        for (var i = 0; i < size; i++) {
            for (var j = 0; j < size; j++) {
                if (selectedPiece == board[i][j]) {
                  return {x : i, y : j};
                }
            }
        }
  }
  return null;
}

// What happens on mouse down
function onDocumentMouseDown(event) {
  if ((gx != cube.position.x) || (gz != cube.position.z)) {
    return;
  }
  if (isWon) {
    resetCubeBoard();
    renderer.render(scene, camera);
    return;
  }
  mouse.x = ( event.clientX / window.innerWidth ) * 2 - 1;
  mouse.y = - ( event.clientY / window.innerHeight ) * 2 + 1;
  raycaster.setFromCamera(mouse, camera);
  var bxy = getSelectedSquare(raycaster);
  if (bxy != null) {
    var square = getSquare(bxy.x, bxy.y);
    if (cube.visible == true) {
      gx = square.position.x;
      gz = square.position.z;
      return;
    }
    if (numberOfLocked < 6) {
        toggleSquare(bxy.x,bxy.y);
    } else {
      if (isSquareSelected(bxy.x, bxy.y)) {
        toggleSquare(bxy.x, bxy.y);
      } else {
        cube.visible = true;
        cube.position.x = square.position.x;
        cube.position.z = square.position.z;
        gx = square.position.x;
        gz = square.position.z;
      }
    }
    renderer.render(scene, camera);
  }
}

document.body.appendChild(renderer.domElement);
window.addEventListener('click', onDocumentMouseDown, false);

animate();
