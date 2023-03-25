import * as THREE from 'three';
import { FontLoader } from 'three/addons/loaders/FontLoader.js';
import { TextGeometry } from 'three/addons/geometries/TextGeometry.js';

//debug 
var debug = false;

//create the scene
const scene = new THREE.Scene();
scene.background = new THREE.Color('gray');

//create the camera
const camera = new THREE.PerspectiveCamera(
  90,
  window.innerWidth / window.innerHeight,
  0.1,
  10
);
camera.position.z = 7;
camera.position.y = 4;
camera.position.x = 0;
camera.zoom = 3;
const look = new THREE.Vector3( 0, 0, 0 );
camera.lookAt(look);
camera.updateProjectionMatrix();
// Our two colours
const colorFree   = new THREE.Color('white');
const colorLocked = new THREE.Color('skyblue');
const colorWon   = new THREE.Color('coral');
const colorBlackBoard   = new THREE.Color('black');
const colorMoveBoard   = new THREE.Color('black');

// Our two mats 
const matLocked = new THREE.MeshBasicMaterial({color: colorLocked});
const matFree   = new THREE.MeshBasicMaterial({color: colorFree});
const matWon   = new THREE.MeshBasicMaterial({color: colorWon});
const matBlackBoard   = new THREE.MeshBasicMaterial({color: colorBlackBoard});
const matMoveBoard   = new THREE.MeshBasicMaterial({color: colorMoveBoard});

// Our six axis 
const axisPX = new THREE.Vector3( 1, 0, 0);
const axisNX = new THREE.Vector3(-1, 0, 0);
const axisPY = new THREE.Vector3( 0, 1, 0);
const axisNY = new THREE.Vector3( 0,-1, 0);
const axisPZ = new THREE.Vector3( 0, 0, 1);
const axisNZ = new THREE.Vector3( 0, 0,-1);

// create the move board 
const mbgeometry = new THREE.BoxGeometry(0.9, 0.90, 0.1);
const mbcube = new THREE.Mesh(mbgeometry, matMoveBoard);

// The initial position
mbcube.position.z = 1.7;
mbcube.position.y = -0.7;
mbcube.position.x = -1.5;

//add the main blackboard to scene
scene.add(mbcube);

// create the black board 
const bbgeometry = new THREE.BoxGeometry(4, 1, 0.1);
const bbcube = new THREE.Mesh(bbgeometry, matBlackBoard);

// create the main cube
const geometry = new THREE.BoxGeometry(1, 1, 1);
// The initial position
bbcube.position.z = 1.7;
bbcube.position.y = -0.7;
bbcube.position.x = 0;

//add the main blackboard to scene
scene.add(bbcube);

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
  for(let i = 0; i < 6; i++) {
    if (cube.material[i] == matFree) {
      return false;
    }
  }
  isWon = true;
  return true;
}

// Set cube is all colored 
function setCubeWon () {
  for(let i = 0; i < 6; i++) {
    cube.material[i] = matWon;
  }
  if (currentTxt) {
    scene.remove(currentTxt);
  }
  currentTxt = voidTxt;
  scene.add(currentTxt);
  if (currentDistTxt) {
    scene.remove(currentDistTxt);
  }
  currentDistTxt = distTxt[0];
  scene.add(currentDistTxt);
  renderer.render(scene, camera);
}

// Getting the difference faces of the cube 
function getFace(ax1) {
  let ax = cube.worldToLocal(ax1).multiplyScalar(2);
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
    new THREE.Vector3(cube.position.x, cube.position.y, cube.position.z - 0.5));
};
function getFaceSouth() {
  return getFace(
    new THREE.Vector3(cube.position.x, cube.position.y, cube.position.z + 0.5));
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
  for (let i = 0; i < size; i++) {
    board[i] = new Array(size);
    for (let j = 0; j < size; j++) {
      let geometry = new THREE.BoxGeometry(1, .1, 1);
      let cube = new THREE.Mesh(geometry, matFree);
      cube.position.x = -1.5 + i;
      cube.position.y = -0.1;
      cube.position.z = -1.5 + j;
      board[i][j] = cube;
      let geo = new THREE.EdgesGeometry(cube.geometry);
      let mat = new THREE.LineBasicMaterial({color: 0x000000 });
      mat.linewidth = 2;
      let wireframe = new THREE.LineSegments(geo, mat);
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
  let square = getSquare(x, y);
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
  for(let i = 0; i < 4; i++) {
    for(let j = 0; j < 4; j++) {
      let square = getSquare(i, j);
      if ((square.position.x == cube.position.x) &&
          (square.position.z == cube.position.z)) {
        return square;
      }
    }
  }
}

// Exchange the color of the down face of the cube with the square underneath
function swapSquareCube() {
  let face = getFaceDown();
  let square = getSquareUnderCube();
  if ((face == null) || (square == null)) {
    return;
  }
  var mat = square.material;
  square.material = cube.material[face];
  cube.material[face] = mat;
} 

function resetCubeBoard() {
  for(let i = 0; i < 6; i++) {
    cube.material[i] = matFree;
  }
  cube.visible = false;
  isWon = false;
  for(let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      getSquare(i, j).material = matFree;
    }
  }
  numberOfLocked = 0;
}


//create renderer
var renderer = new THREE.WebGLRenderer({antialias : true});
renderer.render(scene, camera);
renderer.setSize(window.innerWidth, window.innerHeight)
document.body.appendChild(renderer.domElement)

var nmove;
var nmoveTxt ;
var forward = true;
var history = [];
var rightTxt ;
var leftTxt ;
var upTxt ;
var downTxt ;
var voidTxt ;
let currentTxt;
var visibleCurrentTxt = true;
var distTxt = new Array(20);
let currentDistTxt;
var visibleCurrentDistTxt = true;

var loader = new FontLoader();
var xfont;
loader.load('fonts/helvetiker_bold.typeface.json', function(font) {
  let textmat = new THREE.MeshBasicMaterial({
    color: 'white'
  });
  xfont = font;
  let geometry = new TextGeometry('', {
    font: font,
    size: 0.5,
    height: 0.,
    curveSegments: 1,
    bevelEnabled: true,
    bevelThickness: 0,
    bevelSize: 0,
    bevelOffset: 0,
    bevelSegments: 1
  });
  geometry.center();
  voidTxt = new THREE.Mesh(geometry, textmat);
  voidTxt.position.x = 0;
  voidTxt.position.z = 2;
  voidTxt.position.y = -0.50;
  geometry = new TextGeometry('left', {
    font: font,
    size: 0.5,
    height: 0.,
    curveSegments: 1,
    bevelEnabled: true,
    bevelThickness: 0,
    bevelSize: 0,
    bevelOffset: 0,
    bevelSegments: 1
  });
  geometry.center();
  leftTxt = new THREE.Mesh(geometry, textmat);
  leftTxt.position.x = 0;
  leftTxt.position.z = 2;
  leftTxt.position.y = -0.44;
  geometry = new TextGeometry('right', {
    font: font,
    size: 0.5,
    height: 0.,
    curveSegments: 1,
    bevelEnabled: true,
    bevelThickness: 0,
    bevelSize: 0,
    bevelOffset: 0,
    bevelSegments: 1
  });
  geometry.center();
  rightTxt = new THREE.Mesh(geometry, textmat);
  rightTxt.position.x = 0;
  rightTxt.position.z = 2;
  rightTxt.position.y = -0.50;
  geometry = new TextGeometry('up', {
    font: font,
    size: 0.5,
    height: 0.,
    curveSegments: 1,
    bevelEnabled: true,
    bevelThickness: 0,
    bevelSize: 0,
    bevelOffset: 0,
    bevelSegments: 1
  });
  geometry.center();
  upTxt = new THREE.Mesh(geometry, textmat);
  upTxt.position.x = 0;
  upTxt.position.z = 2;
  upTxt.position.y = -0.52;
  geometry = new TextGeometry('down', {
    font: font,
    size: 0.5,
    height: 0.,
    curveSegments: 1,
    bevelEnabled: true,
    bevelThickness: 0,
    bevelSize: 0,
    bevelOffset: 0,
    bevelSegments: 1
  });
  geometry.center();
  downTxt = new THREE.Mesh(geometry, textmat);
  downTxt.position.x = 0;
  downTxt.position.z = 2;
  downTxt.position.y = -0.45;
  currentTxt = voidTxt;
  let dTxt = "";
  for (let i = 0; i < 20; i++) {
    if (i != 0) {
      dTxt = i + "";
    }
    geometry = new TextGeometry(dTxt, {
      font: font,
      size: 0.5,
      height: 0.,
      curveSegments: 1,
      bevelEnabled: true,
      bevelThickness: 0,
      bevelSize: 0,
      bevelOffset: 0,
      bevelSegments: 1
    });
    geometry.center();
    let txt = new THREE.Mesh(geometry, textmat);
    distTxt[i] = txt;
    txt.position.x = 1.5;
    txt.position.z = 2;
    txt.position.y = -0.45;
  }
});

function addNMove() {
  if (98 < nmove) {
    return;
  }
  if (nmoveTxt != null) {
    scene.remove(nmoveTxt);
  }
  nmove++;
  history.push({x : cube.position.x, z : cube.position.z});
  let textmat = new THREE.MeshBasicMaterial({
    color: 'white'
  });
  let geometry = new TextGeometry("" + nmove, {
    font: xfont,
    size: 0.5,
    height: 0.,
    curveSegments: 1,
    bevelEnabled: true,
    bevelThickness: 0,
    bevelSize: 0,
    bevelOffset: 0,
    bevelSegments: 1
  });
  geometry.center();
  nmoveTxt = new THREE.Mesh(geometry, textmat);
  nmoveTxt.position.x = -1.5;
  nmoveTxt.position.z = 2;
  nmoveTxt.position.y = -0.45;
  scene.add(nmoveTxt);
}

function binomial(m, n) {
  if (n == 0) {
    return 1;
  };
  if (m == 0) {
    return 0;
  }
  return binomial(m - 1, n - 1) + binomial(m - 1, n);
}

var numberbit = new Array(22);

function printNumberbit () {
  let res = "\n[";
  for(let i = 0; i < 16; i++) {
    res += numberbit[i] + ";";
    if (i % 4 == 3) {
      res += "\n"
    }
  }
  for(let i = 16; i < 21; i++) {
    res += numberbit[i] + ";";
  }  
  res += numberbit[21] + "]";
  return res;
}

function getCode(n, m) {
  if (22 <= n) {
    return 0;
  }
  if (numberbit[n] == true) {
    return binomial(21 - n, m) + getCode(n + 1, m - 1);
  }
  return getCode(n + 1, m);
}

// Get next move to solve the current position 
function getNextMove() {
  let xi = 1.5 + cube.position.x; 
  let xj = 1.5 + cube.position.z;
  if (debug) {
    console.log("initial xi = " + xi);
    console.log("initial xj = " + xj);
  }
  let cubePos = new Array(6);
  cubePos[0] = isFaceSelected(getFaceDown());
  cubePos[1] = isFaceSelected(getFaceWest());
  cubePos[2] = isFaceSelected(getFaceSouth());
  cubePos[3] = isFaceSelected(getFaceNorth());
  cubePos[4] = isFaceSelected(getFaceEast());
  cubePos[5] = isFaceSelected(getFaceUp());
  let boardPos = new Array(4);
  for (let i = 0; i < 4; i++) {
    boardPos[i] = new Array(4);
  }
  for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      boardPos[i][j] = isSquareSelected(i, j);
    }
  }
  // The position is in the lower part of the board, we need to do a 180 degre
  let swap = (2 <= xj);
  if (debug) {
    console.log("swap = " + swap);
  }
  let kb = true;
  let k = 0;
  if (swap) {
    xi = 3 - xi;
    xj = 3 - xj;
    if (debug) {
      console.log("swap xi = " + xi);
      console.log("swap xj = " + xj);
    }
    for (let i = 0; i < 4; i++) {
      for (let j = 0; j < 2; j++) {
        kb = boardPos[i][j];
        boardPos[i][j] = boardPos[3 - i][3 - j];
        boardPos[3 - i][3 - j] = kb;
      }
    } 
    kb = cubePos[1];
    cubePos[1] = cubePos[4];
    cubePos[4] = kb;
    kb = cubePos[2];
    cubePos[2] = cubePos[3];
    cubePos[3] = kb;
  }
  // The position is in the right part of the board, we need to do a 90 degre
  let turn = (2 <= xi);
  if (turn) {
    k = xi;
    xi = xj;
    xj = 3 - k;
    if (debug) {
      console.log("turn xi = " + xi);
      console.log("turn xj = " + xj);
    }
    for (let i = 0; i < 2; i++) {
      for (let j = i; j < 3 - i; j++) {
        kb = boardPos[i + j][i];
        boardPos[i + j][i] = boardPos[3 - i][i + j];
        boardPos[3 - i][i + j] = boardPos[3 - (i + j)][3 - i];
        boardPos[3 - (i + j)][3 - i] = boardPos[i][3 - (i + j)];
        boardPos[i][3 - (i + j)] = kb;
      }
    } 
    kb = cubePos[1];
    cubePos[1] = cubePos[3];
    cubePos[3] = cubePos[4];
    cubePos[4] = cubePos[2];
    cubePos[2] = kb;
  }
  if (debug) {
    console.log("swap=" + swap);
    console.log("turn=" + turn);
  }
  k = 0;
  for(let i = 0; i < 4; i++) {
    for (let j = 0 ; j < 4; j++) {
      numberbit[k++] = boardPos[j][i];
    }
  }
  for(let i = 0; i < 6; i++) {
    numberbit[k++] = cubePos[5 - i];
  }
  if (debug) {
    console.log("xi = " + xi);
    console.log("xj = " + xj);
    console.log("numberbits = " + printNumberbit());
  }
  let code = xi + 2 * xj + 4 * getCode(0, 6);
  let val = Number((table >> (2n * BigInt(code))) %4n);
  if (debug) {
    console.log("initial val = " + val);
  }
  if (turn) {
    val = (val + 1) % 4;
  }
  if (debug) {
    console.log("turn val = " + val);
  }
  if (swap) {
    val = (val + 2) % 4;
  }
  if (debug) {
    console.log("swap val = " + val);
  }
  if (val == 0) {
    if (currentTxt) {
      scene.remove(currentTxt);
    }
    currentTxt = upTxt;
    currentTxt.visible = visibleCurrentTxt;
    scene.add(currentTxt);
    renderer.render(scene, camera);
    return "up";
  }
  if (val == 1) {
    if (currentTxt) {
      scene.remove(currentTxt);
    }
    currentTxt = rightTxt;
    currentTxt.visible = visibleCurrentTxt;
    scene.add(currentTxt);
    renderer.render(scene, camera);
    return "right";
  }
  if (val == 2) {
    if (currentTxt) {
      scene.remove(currentTxt);
    }
    currentTxt = downTxt;
    currentTxt.visible = visibleCurrentTxt;
    scene.add(currentTxt);
    renderer.render(scene, camera);
    return "down";
  }
  if (currentTxt) {
    scene.remove(currentTxt);
  }
  currentTxt = leftTxt;
  currentTxt.visible = visibleCurrentTxt;
  scene.add(currentTxt);
  renderer.render(scene, camera);
  return "left";
}

// Get next move to solve the current position 
function getDistanceToSolution() {
  let xi = 1.5 + cube.position.x; 
  let xj = 1.5 + cube.position.z;
  if (debug) {
    console.log("initial xi = " + xi);
    console.log("initial xj = " + xj);
  }
  let cubePos = new Array(6);
  cubePos[0] = isFaceSelected(getFaceDown());
  cubePos[1] = isFaceSelected(getFaceWest());
  cubePos[2] = isFaceSelected(getFaceSouth());
  cubePos[3] = isFaceSelected(getFaceNorth());
  cubePos[4] = isFaceSelected(getFaceEast());
  cubePos[5] = isFaceSelected(getFaceUp());
  let boardPos = new Array(4);
  for (let i = 0; i < 4; i++) {
    boardPos[i] = new Array(4);
  }
  for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      boardPos[i][j] = isSquareSelected(i, j);
    }
  }
  let distance = 0;
  while (distance < 20) {
    let isWon = true;
    for (let i = 0; i < 6; i++) {
      if (!cubePos[i]) {
        isWon = false;
      }
    }
    if (isWon) {
      if (currentDistTxt) {
        scene.remove(currentDistTxt);  
      }
      currentDistTxt = distTxt[distance];
      currentDistTxt.visible = visibleCurrentDistTxt;
      scene.add(currentDistTxt);
      renderer.render(scene, camera);
      return distance;
    }
    distance++;
    // The position is in the lower part of the board, we need to do a 180 degre
    let swap = (2 <= xj);
    if (debug) {
      console.log("swap = " + swap);
    }
    let kb = true;
    let k = 0;
    if (swap) {
      xi = 3 - xi;
      xj = 3 - xj;
      if (debug) {
        console.log("swap xi = " + xi);
        console.log("swap xj = " + xj);
      }
      for (let i = 0; i < 4; i++) {
        for (let j = 0; j < 2; j++) {
         kb = boardPos[i][j];
         boardPos[i][j] = boardPos[3 - i][3 - j];
         boardPos[3 - i][3 - j] = kb;
        }
      } 
      kb = cubePos[1];
      cubePos[1] = cubePos[4];
      cubePos[4] = kb;
      kb = cubePos[2];
      cubePos[2] = cubePos[3];
      cubePos[3] = kb;
    }
    // The position is in the right part of the board, we need to do a 90 degre
    let turn = (2 <= xi);
    if (turn) {
      k = xi;
      xi = xj;
      xj = 3 - k;
      if (debug) {
        console.log("turn xi = " + xi);
        console.log("turn xj = " + xj);
      }
      for (let i = 0; i < 2; i++) {
        for (let j = i; j < 3 - i; j++) {
          kb = boardPos[i + j][i];
          boardPos[i + j][i] = boardPos[3 - i][i + j];
          boardPos[3 - i][i + j] = boardPos[3 - (i + j)][3 - i];
          boardPos[3 - (i + j)][3 - i] = boardPos[i][3 - (i + j)];
          boardPos[i][3 - (i + j)] = kb;
        }
      } 
      kb = cubePos[1];
      cubePos[1] = cubePos[3];
      cubePos[3] = cubePos[4];
      cubePos[4] = cubePos[2];
      cubePos[2] = kb;
    }
    if (debug) {
      console.log("swap=" + swap);
      console.log("turn=" + turn);
    }
    k = 0;
    for(let i = 0; i < 4; i++) {
      for (let j = 0 ; j < 4; j++) {
        numberbit[k++] = boardPos[j][i];
      }
    }
    for(let i = 0; i < 6; i++) {
      numberbit[k++] = cubePos[5 - i];
    }
    if (debug) {
      console.log("xi = " + xi);
      console.log("xj = " + xj);
      console.log("numberbits = " + printNumberbit());
    }
    let code = xi + 2 * xj + 4 * getCode(0, 6);
    let val = Number((table >> (2n * BigInt(code))) %4n);
    if (debug) {
      console.log("initial val = " + val);
    }
    if (val == 0) {
      // cube move to up
      let c0 = cubePos[0];
      let c1 = cubePos[1];
      let c2 = cubePos[2];
      let c3 = cubePos[3];
      let c4 = cubePos[4];
      let c5 = cubePos[5];
      cubePos[0] = c3;
      cubePos[1] = c1;
      cubePos[2] = c0;
      cubePos[3] = c5;
      cubePos[4] = c4;
      cubePos[5] = c2;
      xj -= 1;
      let val = boardPos[xi][xj];
      boardPos[xi][xj] = cubePos[0];
      cubePos[0] = val;
    } else if (val == 1) {
      // cube move to right
      let c0 = cubePos[0];
      let c1 = cubePos[1];
      let c2 = cubePos[2];
      let c3 = cubePos[3];
      let c4 = cubePos[4];
      let c5 = cubePos[5];
      cubePos[0] = c4;
      cubePos[1] = c0;
      cubePos[2] = c2;
      cubePos[3] = c3;
      cubePos[4] = c5;
      cubePos[5] = c1;
      xi += 1;
      let val = boardPos[xi][xj];
      boardPos[xi][xj] = cubePos[0];
      cubePos[0] = val;
    } else if (val == 2) {
      // cube move to down
      let c0 = cubePos[0];
      let c1 = cubePos[1];
      let c2 = cubePos[2];
      let c3 = cubePos[3];
      let c4 = cubePos[4];
      let c5 = cubePos[5];
      cubePos[0] = c2;
      cubePos[1] = c1;
      cubePos[2] = c5;
      cubePos[3] = c0;
      cubePos[4] = c4;
      cubePos[5] = c3;
      xj += 1;
      let val = boardPos[xi][xj];
      boardPos[xi][xj] = cubePos[0];
      cubePos[0] = val;
    } else if (val == 3) {
      // cube move to left
      let c0 = cubePos[0];
      let c1 = cubePos[1];
      let c2 = cubePos[2];
      let c3 = cubePos[3];
      let c4 = cubePos[4];
      let c5 = cubePos[5];
      cubePos[0] = c1;
      cubePos[1] = c5;
      cubePos[2] = c2;
      cubePos[3] = c3;
      cubePos[4] = c0;
      cubePos[5] = c4;
      xi -= 1;
      let val = boardPos[xi][xj];
      boardPos[xi][xj] = cubePos[0];
      cubePos[0] = val;
    }
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
    if (forward) {
      swapSquareCube();
    } else {
      forward = true;
    }
    addNMove();
    if (isCubeWon()) {
      setCubeWon();
      return;
    }
    getNextMove();
    getDistanceToSolution();
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
    if (forward) {
      swapSquareCube();
    } else {
      forward = true;
    }
    addNMove();
    if (isCubeWon()) {
      setCubeWon();
      return;
    }
    getNextMove();
    getDistanceToSolution();
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
    if (forward) {
      swapSquareCube();
    } else {
      forward = true;
    }
    addNMove();
    if (isCubeWon()) {
      setCubeWon();
      return;
    }
    getNextMove();
    getDistanceToSolution();
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
    if (forward) {
      swapSquareCube();
    } else {
      forward = true;
    }
    addNMove();
    if (isCubeWon()) {
      setCubeWon();
      return;
    }
    getNextMove();
    getDistanceToSolution();
  }
};

// Where the cube is going to
var gx = cube.position.x;
var gz = cube.position.z;

// animation loop
function animate () {
  requestAnimationFrame(animate);
  let x = cube.position.x;
  let z = cube.position.z;
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
  let selectedPiece;
  for (let z = 0; z < intersects.length; z++) {
        selectedPiece = intersects[z].object;
        for (let i = 0; i < size; i++) {
            for (let j = 0; j < size; j++) {
                if (selectedPiece == board[i][j]) {
                  return {x : i, y : j};
                }
            }
        }
  }
  return null;
}

// check if we press on the number of move
function clickOnNMove (raycaster) {
  let intersects = raycaster.intersectObjects(scene.children);
  let selectedPiece;
  for (let z = 0; z < intersects.length; z++) {
        selectedPiece = intersects[z].object;
        if (selectedPiece == mbcube) {
          return true;
        }
  }
  return false;
}

// get the square that is touched by the ray
function clickOnBlackBoard (raycaster) {
  let intersects = raycaster.intersectObjects(scene.children);
  let selectedPiece;
  for (let z = 0; z < intersects.length; z++) {
        selectedPiece = intersects[z].object;
        if (selectedPiece == bbcube) {
          return true;
        }
  }
  return false;
}

// What happens on mouse down
function onDocumentMouseDown(event) {
  if ((gx != cube.position.x) || (gz != cube.position.z)) {
    return;
  }
  if (isWon) {
    if (currentTxt) {
      scene.remove(currentTxt);
    }
    currentTxt = voidTxt;
    currentTxt.visible = visibleCurrentTxt;
    scene.add(currentTxt);
    if (currentDistTxt) {
      scene.remove(currentDistTxt);
    }
    currentDistTxt = distTxt[0];
    currentDistTxt.visible = visibleCurrentDistTxt
    scene.add(currentDistTxt);
    resetCubeBoard();
    if (nmove != null) {
      scene.remove(nmoveTxt);
    }
    renderer.render(scene, camera);
    return;
  }
  function getOffset(element) {
    var ex = 0, ey = 0;
    while (element.offsetParent) {
        ex += element.offsetLeft;
        ey += element.offsetTop;
        element = element.offsetParent;
    }
    return {x: ex, y:ey};
  }

  // For the following method to work correctly, set the canvas position *static*; margin > 0 and padding > 0 are OK
    var off = getOffset(renderer.domElement);
    mouse.x = ( ( event.pageX - off.x ) / renderer.domElement.clientWidth ) * 2 - 1;
    mouse.y = - ( ( event.pageY - off.y ) / renderer.domElement.clientHeight ) * 2 + 1;
  raycaster.setFromCamera(mouse, camera);
  let bxy = getSelectedSquare(raycaster);
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
        nmove = -1;
        addNMove();
        getNextMove();
        getDistanceToSolution();
      }
    }
    renderer.render(scene, camera);
  }
  if (clickOnNMove(raycaster)) {
    if (nmove < 1) {
      return;
    }
    history.pop();
    let val = history.pop();
    nmove--;
    nmove--;
    gx = val.x;
    gz = val.z;
    forward = false;
    swapSquareCube();
    return;
  } else if (clickOnBlackBoard(raycaster)) {
    if (visibleCurrentTxt) {
      if (visibleCurrentDistTxt) {
        visibleCurrentTxt = false;
        visibleCurrentDistTxt = false;
      } else {
        visibleCurrentDistTxt = true;
      }
    } else if (visibleCurrentDistTxt) {
      visibleCurrentTxt = true;
      visibleCurrentDistTxt = false;
    } else {
      visibleCurrentTxt = false;
      visibleCurrentDistTxt = true;
    }
    if (currentTxt) {
      currentTxt.visible = visibleCurrentTxt;
    }
    if (currentDistTxt) {
      currentDistTxt.visible = visibleCurrentDistTxt;
    }
    renderer.render(scene, camera);
  }
}

renderer.domElement.addEventListener('click', onDocumentMouseDown, false);
renderer.render(scene, camera);

animate();

// The big table

const table = BigInt(3519828991796078708383359266158645651313091786664390134528681391155745539891079394279881992183290176285713150579456977369346851728878106272942836887283267776854001016953811480068507561268102976310246239265579352690845181298207357263844094202162508572715087959512681907752699676263538493155202385965479878677203647627535120739355603597222821150525791750998518379997338489635269866467524956896365721413258401016121106391276130604089403678889268779827580457678315598824523734843146770647357849625450732602338045916223755836503406066474024478568037084911258282009418522075378364350471729600251886043216416134772627926196671015634893771817203940857400419768400922211166771603792361324139424737731559272985990279077541129115713625569168665399106833047458526551116457985997702394716374859114023524445889573594090080761988331643227213946893052313273937413100159087582962924210676188589958852693872975936034395815787927260244274165168224312061026915042039573733340034962358041835996751498695928115909884561089960948612108695637683579156440700191324763933880155299436285108313315470552228304607461882536443524226885986167804724253291517093240838407819130554197033216004188391676799799266074907599335963965380940098240436807772917770265175396604276991343847384375809274465173294958631855566851609519035086200643277135837539595018002447812882887970492211980379116698984580084244095062443814250562954099072579010766547310425648051345857158022564567366475299665710233970144611414639593172481942413493949410405843586760021142078389751149350541963262609230812517414976088659837124910131276964866765227059394620465199069410626402261429512828732176805530635484602367472073393103357430572424627445529683238728051021913911731271317803811432756635944052662125216840382949477643428326415022524019852258519791024510569269931607248697928022189520605472023180094791044206181423376151978524679465239300937912955480751789544154156635953981840001538684676716735063930628346831587676990416558665904132658707421827127415987170430238355530488828514481463464443652361890865873640417842251165981798993710389422520031471609122463953727050518735372966594175730929318110857409737624369320768344765460170029580952046293541151120435788884259837531335135720827514669842514912080027132398659644509416653525411317301732197615259976505712583648042048620744536221851520558164023046205465656884334192594783183459463053813925413097176587066233444834441416903692748532032528472501748363868871634460080054998474219927829220383719497666209682714468927358218737372606047852603088355672930609486381752648888618268444505903955907494842720445516923396183167320575071746722963371973914287917121218536641267623153301664395905245848622358458569537307697541123702652034582898172699152565620013332539601134031194625609214859494027356261910180702824267352682590199695612528690738525400075177181662426460832002080563193312015037420869810397090825783618057506758863344058703858149630275356463708735413633078072997834889031627273471331300099573412087954229427854691017256415503846186059767061010567479549993866477578106689897998967559112447443830075830499834753334799792393244059150953333335813718054613552821315007592286094105018365491846630053232389989916434233151775661501626293541223496203527478641591246363351256767178621878019597622289894933699710372638993491385329817459409683595205903949595641906158439092406236450513527205025418235784244381214124981673024696746142521955236165340419309546667776222894766181310636427925546131424529301781074802360534442931553020322392095566297796527421281999618392064326163468466126984992618012314359948066718224866825261724639625103160799903200327944736598927883664519275217265186720409083793956222776547808830092854798659507482820143171828601984810098489590458935609783935970034271777875821275375312093084738800090641503032264801231534668022440017723945965954233727451380686631218585441328988797539595299825207493282922945705928668925163322337131027795244513921480703755067174236924179182168940062304920149221202825510265426040704434125921514176224423055650662475862999626220593063329271077204219182789156048814111220817482872076197364441641190637958707910574175631667776175695460225386582705033316593988796377749486565375060567427166370982445354631293720786086279614620607832274568058635981673078863326121134115893148116500353051812762644385076615891450091520815126878605527236277768093895495307872523541753088114519413019704647147968319096607373363713412470708651538310285567707180852424898764915616093900301713343622254177813845702650146690087005929214072629015700701971875151819289204821566745987778637362634533190116026071962776566535271993055273600924916640771212985162468583063435097306735257100070699886713996393895206780444184417521007958214121649083731983284566684565994845625218770136388188405840875768060181195306912398646360121450238106975858113169399831244426189842965164176378261550640508292928648867397425702108830174787179612275085048098287553635312290620061641716811103824976389543124655313711373136608993500210224595721887347926564077136004984632453469584727007448170407491012001400146409108565937177254252524802749557284513804145915892801100729049545771911491347747505981447854077551376132979176993638100887787625855758754142899529489822265139580237721521047313070623197375834408866036729346111343285929471846986349708970992014571608958373224367777084957651872887423251615108883420993792109772215011157174302190219013436787185732166569532526209774878022825908292462346571092831959590811510842160141254417155923089834018321648911022675525474575650168428610841189139078117548074485067552050785585665426363516827917567326250224062372358424425967909881355190248423571337057659644468249580810590227265909360110421569977038669598883611097272524836186681972215925023901026713360619469234808609791708156577801921724174469414654417233237575619455353164579904489746614364691226438532047219212052958023420024779180587531721024102614368792387365122349665531288503702307061234761149671195755379035239368681941947802578605398739175895804863764528745912915044412524851522174107702462372567060509310095103085476493247983842945715212053310722196598922096743477471828400343520755393417065235177420242722976485771838318780523185331722604964609804306834183618172071973416526710773369700052881698428530399780418625361822136430931722418261300888668156800914399851509942904591151702253913636090638469244367703253278699309723928692766560809556600957969111328379624917296871701048061088550397086156630680948633246756556522831857406902843379289780735409919596246684235737887837101093377865849370643795844336602097731140092097218636655676181318244686449462659999472722665698533983666932506580201006764374061042770900180318081799796852434325923812454516109927001021680272022676866544876458611525552447109295821221804893436635617718367111541617519699185936720911220201730096876149774114881976582506726333184119138618426249068218924113192456009739692994023140146531399457276122185884870814071058964569910269422495824605148719175248280499190659122393004631676275879628774262834643949739424314014459641830734180664856493887460716715131672397368169060382017065489517497187371980541025356160352679121506838179920685878091893235831692599404068098891884878829032935108108220145293536864598060812283351550583651838245491870185445125516713938309652169372130990356157184175340907700711056602323994388977096492689681670496009327608488930820060979963254227801804099466088081428834707067221577758350955660620580926840130793258043030980826668348702009332098167546961351577566275502136319317378951797689188058448309853571213458148414222026116459763829816186902197909798326484554964655226633538444260493850602704014022361148329267145199013299878946533183538803657676532775321080112085855912141339540619727602894624673921773557776975195025134583226403212102260558933038329721049840543043223772705745165147554616947136005220777031082809069085682354317083909035789210668798018078034324876944237606481797793509783963411110919552829975337097818048227634226869216661126466543728437624654347307956891780650633980921332550668308114859549912597077699365833917740470962596783111983027612858218914159607776120139879716891607541826269006495286729065675813488422073190150197233989109725577013243199663655320444963704408311477187633542069484628575527860532273604878780455066805527368088742543284338365523867633533152357952184530566986401843903876079696860662481820253660327789151626652553137252411381212130809965440549553235001313452417652776914791071355726543208122506291243525345207288000671434955138271703978470643292917006843703718212143830753465444783918787104053726467091235159555926621513186297489657857653168996092799618027629930473582459072252488476055916983076142011501944575823392403071853372449399601574080860990591185307089414655172054221209194602039447905007646970844587257602970337017590321257679332158765427495922734017588915399111940201489263710197857022859603514436218760664878910530288883638332186464980797645868458042351078785924210987522063538939181486094901471703921922056494879517929016068947736726213438025197577642143254380998941636591271130531269639320636005248822242199694182232428756080645865202194694219530327519142973618700206875457115387004132120620131225469731529513669939692451064896213647651016740992197035033231881998129586345297597230420821360898766091791049382049489813683738023500942350574955650259972038467182907330929882738008393758354151142558788391655588050202369651789779133134086569313625868794381633097948924945744996908980406414814458677055160560448614730218888287858246605044234601301294991012132263591103126744848667532801865856274601716268499901644578284912356739618676869421635496255487918545938548981785457681967664931533259945230448281981520041633261788612613436437746089371150942810743184484909482551177200604272353278987503407432454472679925287279974164689364122600524481083662099147049422500869311402086112732946802905821575030754487331623320099426198789953904264886479873353310214293515642282640048779853268868179127258006782842709372123286923380737147569154362751646183586049681555319004396331756700567824187722545646391132891432694842235379595920504555112979706034289867855959981831547097495768002546656675834991533411349462375511471675492826646065266583087124160527281113459237874638198755913093910642157994065145524253976976046975944707031104381608999614235581941881724778346450968490773257097493933270469494077366451283781525043313458121673964104450049763929033639970641024686565571960430912558774934635347134355341179300166532354761227238226519890820333562613416603714150918348283360836646022700988110005744275868607741430157038348387853000932932470638428612807758050987595604011169674198849100381662971891274858718650741586337510758393725954437485248829434807974643576242528959985256057924783982497335533110417928639558948978741030009972238803133855016661650601646012657251725802087458571520893406580587898073951340884581622753701382093753837887075630758559633321415127889759363542584538495805111758028534864597711399545965886272224924196515270252628605749636411079835691672845356490335733607622317776578610929106942843474882444281327727284420816927553415447750344744483982225555084133878925543189068016002362411272790074267649662262010601541072463444760417746027063568808714454678188608340931708538481067811506569552832892415772191437780935495336255935358810996873871194777744789544515014568755671361293315613482872990711419208206018219746892584692492500437349270382679061183981467439109651358542610928652392389726550073801126751837546585368144539694970447031070640361213821831910186812207699241157275777120244496932459931317902690180560628973615230628139763747458007705404011282472962951888217695094735551472904698256947629835179815320375638482550439436420116002595880577140819309622560543084746692560948220633037448837091017308165213058303032662568321720035090399084462789672871104387898731872424568976779058254563476929444585619078612543208606214030425455700269677058040386261449504052072395482875837016385840071314838842683304440882240512169686656184438176263987222073761304336011926419296420875647569840168819940251870296110589162783321592974896516128800462256589485145532638332255879775759740482180312656452074372901409722944638819636221781412517600627080913830662761533649775691315525377341367875830848393771631986930705696996733763475825862689249362281648503875397329803358850384277930007113279431216641015727939806690483093644250245895795102848169631491136068184840678767456130562022113490920372770588217824756358522686563190426127360837582834409290240947675045238800718882121478908199831237136840948422683302288469348016621216180817778402426716147111929500374004455736552544476519731943727078815279280714206717555375664298632501162047230688711437501102163216878026366231919790069101264195487761195931199048194139649869691666360690366129321783019812083827586364521609885644086069448868818943356051579717035232448185324201317609156726146556785235790681598891219055475828712134228522884321814691847210060103155839580270282747029242711713598144210943065908488836816897791092068861716883057137597741629909426923852700166906299722794495277942335579971328609660117952452286424324364011141582901632174346841935957997997784512736268955972307965872445432315440734153674521086470295976645346059858881691156002250339027438931621779555722961109593750268926403500240508482272898921342653114239181438128713380199764747160228344649729571321465587974320871599392865772243230089309296626070630607102634457258346519795322222006895159219764050426014081013423797944858917880954032451864016703291562530857477511714697493291541710901024186933718507182535823857686951498598955074350678231084578903842881278855015002101168371032313831099138118793145214326821560318202619359816991479509467772445728684445448163890240340442774691379555064673776926464518409220613527226842226971421475784038671111351440585747000375362295949007138188860900319400940798522686477085105624013978043555331648606987950689958883140914839689020396993975197832630738254527677551887163802318011391822192142207792202480476718956416355928250378730624360617572513007639792978174603744096116597044226107856920317191163627495696512502744385499555192575728519795936738152053189938468068147701311544982695705918865200628167590742354957394473108622068836366912416335605874851128761249274477114197686260607816623243261012389305970271030459929119664756149796052194871501184483803805628914459165384639984651108951644403692522716613076431336805983076902305198886898298026349440454022368285012701496058364220298213609780041878044917191298061653788477024761202925297247002956311227249836533771895713036365745359806009754573402826083957152081843495573781049527503014782496386143773027067404804943570425621478026386939152869730196259975831551134873167792324458777370431604510510698544891725326869324884790559444669320763939280993802069353003390245137560553565958746150215060035098321831945961141081828829884242051753202002400943361814170989494835109440085915408694351540737639191944459807619375691567536852920388680115861890467310274798503150101776517898269699600881159246468537222778635081132817714652305248376951449457588105494128898581076432900709294223105911884773202679978913929936982768253673005472001322906033586366417998006075903512264140101976445628123023981235065220747339173418211343330109497238213006526621674710628634146852644747312672161849950992956874057132571874872719915016104264152597713322952525623672751577181860849588161707068824721659831032333620997239179508451794196917302478067971934824619225910267559398886675112282112873577470415348269628644431919019144401155780948104086152520777350758240702757508982784961622807444585414243518338452435819764211226848604492257432845220341858185907724105421227497923198631793842237614792611205770467140179116762208260155067065244314056030460614501305542654931340198866666666702518703646679729471532554301777356038893423069898727954504981962180760337630869579951805838821033052579716389641601770362441850604384308040493198505914996010947770850552079359345356871443408064229186149877308843170552044952278428980451553368277945883232236039333570975607508440457288583709031111326166163467225803186610692661323603440055585836009104148427244562393056314632737081666603273371505641445624365687026951180376257852695884967022563998591143250455296968573621315457385710468768155260152697344385575083173749054131478278695631317424818561312145072076071560337060314501618513326576071301827202424481450498508100443298730912066417276482100021498171384751552060849160721198741763602340228561276988844519685180394293732868056579489635807309431667317397481196760210916203691527151514755149633004955216932075539609828787067279327228788237925362351094049243783361934320309384001959475609169740489979605931895137686349186410859953278877922780946931069040348422576033060802538172251725172100553667213244887999843317579585614853506381914276911776169234050419810494740389714284548147294426883452005645286140081244130424726807587711769507973637240113502688111186174677563877842009228849321640596577367809199031259359652274462240168796149885085261332747302409340046402947182455886513619560969814023443800352664098722248064061607375005564004683070026088066391782292081039800368282444769231848644448903063215706200616387007505422039358697347283059198798610207243640800226351356436582517766881747269659197133897296825627412120258369373089522813210478214265165284917701673077349364820704678541210837937824343683071115897024066327396791218216524798884339228208615904170696092061258589764840858095042895650222770233235780341736033674439789009874954702542166606269394322606793122862995242394738363633745205246054484707706588446035130746890651298734935068604282865508899297813892313182348222877279727145256959819849148856141971064823592869453280670802433463224931485186744271488998370491777444777913534370570332058464826314410272545265910450067954814591028952179372152252935852959833124094588852733062072168814070302496291716326219239243204560157194508890272074658970124769968101317075556779388101993853631084967152711406139048095720393929349838278750330285215039837751231270766559166532244968712315390361072934294510064329298285133240403849557496881693066207584148355030722862367299086556222505141928758233602854361218592906407294636153177879574914279115547351249149531819725423082646942769948693983895859812785773797687789332255687915493327067669650382640885379674161534870976727442832403894329140641689635870023968919184901532780196905556026972002652306186995583906749739631379436485025377329566009558576187929349284782711144422964464336463986250132141850853913294902579308529023152484096111712996300475840724913628365826374015406423313790964758481248059350314104195538838820851016608719233429655323150888265382484191776779324500719225577525030465573181894361129621091429248164055018388827209171693895901871583992927064428790301888646124154200798557402723838656416497800169653262288428399878021564125461659498044611922288691743365112723719693637131040641383590721634921610493106274625744194131694599564398165279642761221510593889187879974356755455783993062589564215562591483758705314514435647277927238865019076068947497790743475587077160242980045989715527743049957324095841671038272232919140226966489527319749034123074850005553377955014073809425086948858070953060846186793430780821956745897215087457832299439410237747221314501986184021971997482022387937415957708230066647614700083308674475098159169433395218292242145992818218871121868548041663588644589999589276964000449944030455373655293202958110778243804266526479037756239609677712054432703558793461700991264179168926927716287003389610215931625086203177162182928416398094816066316147291388888570648920764492044583396969332458219643679416508946336435930852291504791124331377723803935356398834063086019610098402946459188956053933412850222054756483299470728423352114508791683511489181547009275869136526555647360758715275645404650599403803991553221351414065278926445960883893133357147101677124988907233746815795129718784414381513952923948807913466107473003355577380181122660522038801585220321989769647788717472671930781458367292510279879986321938010524050655916931861479171682172538863923427933624555594923752895158770322220620770882122762965235781074346255650807241190612614085688204958079588823896696582944242543594574145219665869055986100615043402670370372084361346386533086040327835930318711317731841073461246614296805494050622612132608515913219277392877130882347643961607296147704868068758277314873821742092160527591452145024764817557461317149993702547170426528911431738729555254961513225619358539932710131061132260010706609946044080871832716950981026498187126105545884584952073825075801794907149841853754783792728278981723768315479406503938953031221230451777306350503921445412112802199356882118947699271301421951278508526062747689371041903348149746296218750266156891814651361260520084270466089552664043861787226128752735063076799167350703678933843120225113253125683607778590535884811284503677450345089434960092127985025922280189303554034063855771062577432291045508564669604658155927747183987928917440690993754053569743980930415366489030988774891811281432303547249800348188686487799743763520173458394263782053112595904173294622097145913946802298291871642069201214065561683023018023463066944943266996113126537122339391860869830637401755411109090220159306979585601328397103272597981238552172477686875511832984765340077301403090700563845402903222545023842536170021671951345148934944722213156261444107019504135345656297974956390523182625484725407706945128841997471894150849630978096245803947988214393676847502038111862527994781103141581829862221855110838740736842673284579032922562646116054983528098634309660024857810762118992054936385794712448677718921494207538130206076325761667943361558398202653868974743338898110103772328535108215155823729291264554033898643320970832106629356520738652748713682130146614289855710131904901804428082785725473429657373967975996756794422691232368950090702663852566559353591647432252409804479973216018404508273516846514626299160939889216194503807540754488071420635968664656712127481674724927789890748735830882286572562588054899886389795303069207736115446794045431528157097724918541876142749835077137101997552090303473041462808153572905852725156418617206784484249709651406729188311730110932943365822709113638537890361599855865461359115725656620896046623870882802971028654502812293424213898601716621083599711873330151911195911881205165182064435283865780009397536864464347388602423757127263155153739158168805192954468386732262899204974036726220293218864251008705838454832089153878271837494401494283334756508517737473867598816933837126550635899512792876905814567215188959385884273808197075956058889321212983149947314257119531267831310824735728718230142563460617304440826180842346127716485793136295951324029495086510895354692616349720823674058717217807842721131709300330761682801346654312454610512885617086795177636766216007160767295252996964458803401620827748525682364246719828553840046217412230874848459080865308428532581053019548037756119917834265292564059545762267907939693483171439280634718780450862645004568722294893891300205952357685229263770870219250894876098819119088951027884917695430113596250739495409793640623145066418070046352852386992296572057822205926721892776293390327706039516153807845573634300324109829993467806012431519028394210581809595606508885348286041443732819042534420779468251445023673202418144142530232591064584008009268830476960153284723917952325634022799590721093806698689619312228098153117652582183707511954457283219822944634286948483494952389305598913091524892661069448988022889862099245928983568956372559755333254555002489551759004494565458418821942981342097269547855459573325774755354972123415202822233425083127173288146838175152613692135845702313840402130299387576073393309578022416953906908602134660829405088230734799959078880133228184441408966305333859043040499794707735570684513808498682692472374831742199965368635177491482813436344327658823455449802699588099403295002928757115857790917652530972342425136838192748976090123353128539166367028966453376182446783112414547894896112146831878420684934190131333718389659332648153596807943450290323665747898331137655722942501942342955751811334939240882969086932624479038863126385451271350564120408786805407864038005470630300162728010730563255489491346519892978509994646858422049392412477703998698608263269793491644217801592967361235378290574499107252533136011519772998488877545963646614339130015237924447322931339475764402235163446410765419386837027020065444960735415463300935559402715376878818485597067097491019974007846839150981076012211419030810618798665771686443437592764047530748062140853964356439692266106698318035983878917069626494271493093066108930130339385223885466341170567052297295267669837031957731477617825272627318749512364649630493341117895005291969853870990962548283804591177237369376131247870615737617629992846710883111023761119322205735873156386661206671146851526526859153058867840430066272492308932709152761191135994042983738510090294056073592032067380713550999880394529947720865310819013461112909625136372607050228635971840442875790816632991503146235948818622903655615700992180923519837736863110276586295944062499371038788924470688766795700818041874117189644633167880052985074938995458058966183598378388680986758822390238781209106325486475013121982124420532788703498525982923927845345839376206797084434543019420210603643599616463233968180967967225760365932032695517471928598961189086014893177947768282625613967579439231435684077618452454667807667738292092815891802810949232025957614996530027002858853249201357546400819973614504600303254207575682317609235074116153409295906184969236796590959609244373846480739314839792983920279162729471130507812747772335153629585132044874324314618548164401043929372195790255538275418436068738164106824738551009075298321604998833360406332318378067810017624443839899529453298225932261048190981830521480156913021174831740768710579371897504599510615876684634856307501196519125801549692244953296732262800382262472839027173453390161057101805872800612123503386088217564231990711140777076063366297346276919641886231286620649820247908952888257897768590337325569141155296168984870847898075155634617631475055104619620510814043065903288396801189309879741992464038833138398338327083480233908468257226545083598632991741261547844754056549706413066841091607944161591307853371096861229083212436498311108368724515507915881933367071912142227925519826503602819085694789547254452595316452121378825683254646418860269199580855573759813565253683356471795994325314868106441722924641022396228231851319560724694547825091906764365444716629006847948736385910848660160525253673281840560039619800179837959006464948675326059068283963288913949226961772066133623249968109262090186620188258824212241501424948301329197211524528721082870813588847463850205707664648613116048228107609001189647146605821678257132726311959254633272854319537520066323634449990601832936774936391635538230532362333097172236222198032806797282369973928198505305805354656638010112479551992114320252590617475443288081408734287377205189918999487441935876263441242714446546116501633384607818145887626706393986069480610652959367949298428971628539453409372208640903376429151896960532705375932569350639840620045215334581165512004269290327982188977221496739014676792628282506796409783685936430943796037082127739017580169004891273642353471805544519217473409563787243429975214188244435160959798925465513728124001791361242455071494232347819526807892959813421086313572124539209728691120260063060376356300372731094710067322057833651836280372109954846080501932597771569203280779033578457026206366798670212998687656394933014648147477976407887338812476746257909294942037392510362198142487636701654012111823551685136923358682069275408180011378002258741707871117830726044342221282452138824549444848739009580786690773257801559942263831073911651183350830783601750276161773512047006652680851582679213720914446797120073963628478357784122005391712207305671233470887249637647918652430990619957427047088777096409155147820117225217125464668199161886591439502151537202446618265412869149927052468127703262932939438783979502152221278524114389902243058995815053886810618071405964114321599799407554010746980772750046030370197338613648031867273200274424440258233573581992148660787702278507143910257895485489051938965410120870313653117850196122809875074856636995168174190098338811847348469862008353280573484669926285641144940633181283543573000137364810132286651109230237941727368021761522105041416969035551406328751314942636194061940804377469562365083882153390068554066622141362244731537536177599642616646257528890774052079434158215530407349357167858856836265048167766902957907323219199120175773366834965859346748812423821628223211183971849003756466385919852408201858410993867016856186887790557166744076920752540586155578444890326480620752709963371399313351031236966736906332559322739625468241154040744165743847198610701105428953317493000877745114977769181443031119358156550596065387707070938193807660024185289360948841175255432783101334762637379668078086068953912376953232808138624832115565843233525705735244357729436652017213766644324880018721174746602008134833949991308168231415548023566145790531072877513127067735708600369223212885978154732413216976720411827053438251700183908240402610419641753998663132595363148999544746331271009320859155154568026808245723087132077682665286276576302241228951542618093072309465683568411877301396424556713933990734290335340602519067413296114534812302006562110090254619447458252719813663435571244773336955768759540939360333077118786126897170365477191389101975264407366526188643943646763209201775836680816945019893940084551487366160460446355054905587290308250801575846239824064533127651197231833386174305685940259092022148352077819340289832582757113295765359990537914547652438995564909268715705027598622499449545299325265805289723182202954672153385374847685782674170211357695271314908869727704940709552823860764245840371154041838364402965424564724442339498186968093444223721071138419733543974390273814766615259415726259395305836083832550647074191573659326174494238286893875613896888757808837204737979056253188459908361824566329989043120344638404412223072827124545805816503683649328078875021902696551105354306990265222514232974267789287964146051253470750193996116330667786424931341514726455122906791228809379782275644850423040837088533472931345690527724998680442531802056834050784191756104618557450514311036533611708143899014445585632384621260410146429375902265432606746640088599155200490728490893556267344742207545933300000047751096820666992849202207598960033385949213852072147649719267136417875959932050246403637968533893717190517783277727422039813891144157994391967418931645065557408415177000916691168702996407613085411152073002405930920087778600781222961969358455964596438404543283331859873513983137459158485191830561721441022169960206582850329523517311749349679249913814665139740545499156194721530186430467060573396699978703088268279208616691434208514880118784360532057500264310080015506972904435206620175331075595742513469900383625848857897282970740595798045513981056921706092303893292228510876874731905799244329330351540005533513699606092571493862707705435616306323531868600838757645280878450524622344797588414183070289009084067221031033141909973797109764029536690917573167794305816237222634463173292886698438880682272343040707449084024351741708765008272376889049478326056826778065336681771480417106006505143209455846259373058916902574169447110138462659033634540140200157669856241265492118260727838567926422890214793168241904238864681581677769085340004877555325791422341057958581036388322264795955645753479603868981128495522855325164639280895032425454341309632235287964171649395982832540900493637766975494269705432465233329899403194127347605115318887187703187312952046748588899792411866493340971003524942138632944434402375223660190734816935720250369780129831426248657673752625072314140058221438067665557648409299779503951639144841897144817712075866257189769828529122136774378966198803217337926962905971159658386302642673491843457772220111814417933130278522988303271766108181956967512634969367542452572258911720717126057653143136096377083151783517177601255162408186255646097949749043132887674271628485443387704994553028547761245322769887436139478778809676317152316748081581562532622891241546550737076659302781932827209590316938191108835846053255792349274082299798984886250963278747735135183731531885072079050438321809382383489431331748584560266960251399402191481860851110826090270744844539621571605304109717523882958565817232203375353643170778941845643046092733008962314292411292038032351585141609996817753534166934704602389638067964565814686682440850958665726287895335911846954777458041424821040437873424267052727307403192177460047022093131940986231140396392780376225688791414282026703627199384420857466248584221259161601543608529052597186477586630293485386370915473724546829448880648584438963064539776370776952419539262616445261645629883242120340392915610957098043269006284016731748028610288490501293359350076356829140605220840949144865285959230714044777494803172184730400463318951342112449937737213175090233546375759859750725198654397758248185900724345158387394338314142870921973870927364516676120696356289179493573992400406612436987514087254216683146180979950755007267650618029487451830705703307511219665801667726322350267847730002756114672739286771869245030061172586724405767448926686399806722392578404407427168167910907313028265981970213664328663891850326381286811730224764576161066567305035682123459055483327958041560971229084878805229575319586015008947235628325899518423160821956902842291035678720991212500002305230000778116300733630261824717156308037538384508821195976313343982232501630371602761545266275131377641552746672736943916938101890840988044482489687658476225740079612722611177905353041670288521293415131586242241293829952656283020016618232636180289777735272825836706131103924408252744142437973785462350518168291604033501439706780953517405187732784576826868907340758954222688131021579612781778090096455731550339104613168045974432490357093447879546149287939743224739796962232660668659968369602090333804690237633832858039591648874717728405715473408983442638545982009212587134716904967170264207875641409826092280912501737883168673957612156104149249106710235750174026522138001607235614063405859918489117640938434882681940870258994853284021815173909767779568005582106207070643897821583748314838004137456336953371903193504938683713545418477832306121235345924824475167657216431738390793167134296376794814332074104337774188760145445431368425214893794322160991154976465224343912438710880520448486331748208097287220615768230212915908160495293912669657459096793920311361908587388221422589109892426446541724933988041234425661156199726622785658514939925285648487056890250251752385727003431513188209136137563797055904550109096779007719080358884407589728331491148008263935657422124531021169699203223729815062732329784623771877047259797175012930201904632478479461382469676887641898728233455277761074858568555730929194138712591262285452125404534465373570209575303086256866070526696978200013782366916095048065103466368568282518058663477586536275240529472119475020675562491112069432116273637390741653492930464458277193799054956085104734007462649612823086935188451818513307150288328597977772729736398821021956684800994246001594595644273241640503498987851617310632086568046497372273540590065136669709743225005278959583438260870504640615891007160563650704531415797952334940106531455128752800664727138491677452706500519894046399556966968438557557524293870156135860982653192122110834216255621163259926235836182307850829230325593001844746831607314107765700058829698786831306543021284967496870018101318624787674599144637657684350929723246982481288645758677780992845337422257017221831023109313349660446216313522131657290825720044776589911611333164565250136892375103331787083278803750345339438415224541012907804092219450368483358886001720659376393489689607754867361525057257621028978517741830731300454702796109581617448427747145173950536316915786560146531506036997872428512766569416158474618219236747962231125940688282154424269099669475675542677011792353366244433505085965216691059820321618652057207775090558683347044348431322093777032076595643908812512061652944794254819430293489660298029238964969802830838631016348024557127518574879821690508112743726182870430369387889052895076020814538837276089998835058933387905412674108347657028151572482853396855471842889906635397295989185959874298451381863591670334500951203751460364618668275994302857237302927977062315794710620614930286752218816338119638621535891327317055731383715412265754390701468159215010198031209421226685835267198918732091256509738277705104491442492405035784378313889129646641614899876906568608529228622181201450618460176098374738189773988197627159148860824139605492693347588299790411682117741803682371701845025199486517008975984639766611782669594093116578443049890783120188203108539784867006131606650766368258686177452948045586792588720582506026662929683301798284915909108127780184740175793714873717820381645471380524382811649324123123083925072420362045281114263008365689343456906543685302837426697602907650051345651381043436404343553560358654085173146669566271998445995707803220735224203759676680321815301356564078675414310782925924404974975812606593860654693507485806107424287196595997771475251229798810568933966940272732881643993102139354047635273389425899576361679085205460022381452861450680542549644151858888884399131330073402705419761409646346618889043930352610586259274012305962309813918548268351687246508001775895117462035874239926318878500910072700485164868226598305946457677589063281949047835796789356718861564911833007732491766596113920625707662969149277520759708373034392127475922320332346693011567979269844686562376484698232632705370708221839132694542157928911318556704341258784298217130833937384008752180134274424384560733031771329716421907148731470983071696090668672945686876805283002467719750725305180257771253307905910720506132197227646131727729634601795415148603738771454178914421425102798707625969316545648665118685948611094355004384772035379813705642120772050957825047738644527670646441976540022048154701818325298255586979342791632055807059493998736089184584788660100430386520086312059493754202659869166337803805762644572433469599301826449848673469759103232291853764774400006665881007756738999938273240320181731228999604366777446324423040195519431980214759864950349501812842532599590416363779435706084618113010518116537740669881487791000355596552594253561174725982980359074569411978693459445265289055971344596426329773958351429037339195395675192140419707739803644006196879772000319944906708093344444266053060911867698980994595109112621280890316656354016023297241331673434000543337125845971836064365167847744859109871826599901266791214902509822725744068578086946463543280968135062344410720366497673991891142368964269753028365632424682222544757773492066268550752246986204065748993195440387646774204827668275699145291418082193070336997006531348288441976269873239546889878346900035427128293059787639329671079195460457091456470480605176960635599071592737141161300754378907460818931349099079216579478894214790118577988048905796858437814303678068250205075402683969997349841126393664154912014638162114025029264779939119637143893318245906373137437244687331135281693060944033345472866782222972565768119817266049589072047524633180361713311597545560417912452944072230759299832680781658214442631848545735581979844000343727186678865131119212239557811375153722931598321585568726678792263165209516794305316010073982451539347623978641820815615583611506743347994826885617520460543763052509001342552823141830475119774053862080507500751510600372371124300240365673948057099904753828050848590017302141664389001684008047027604317266749578990859851992760463293153539638383432311582803615955100392090175951434567858705358386686729544623014371662076401547042464543519192467000260669172763681811552361573831078747393010663237256335865689807531065408706768035686035844213991473004342482386761476077137728605413845542615712783162630433350714125036121255122515048105425447236943228668679737109097311062348223085476431558233878628366897871918675527061706179209897095276983878540868093653799487059560447599584853547414098193464253139009070932394876244741776913132859541274095772399365773985851378720708618521426513189962822349716226366912019572680367941386998289905943617392433328720867426348876463944522503352938866956211530566404962489327721643419865697559427218838902101272435789497815801222049694414575152050270690338523204787056101129472472038516980444789201542809844967957190330616477881406547586632497976314691908740441046308866009945574123382018542232896570710997160925644545697343784293562521261758623830658770135053878071426650987225049322314970262156661280719732318582206808375788093957172481549670078296848261065438235644254070838136582500837505671095663884155556103065064535714297454946126174893899460999772872316723667608572283428389824038956706416508996316504142218723874785786784853266400008035371473376605029607045577220490854407272564437449886862400255946868192594080023301805853141275712199520734117678994741307464647027424867452007115608961034143998212530169281872307854650320056548340084434817769323770404944233648536942852756169399339100467338951641640252237013765486610532437422129994610125104268955628679629567643534268782404542280752350346482484267746827488038964319653939715771991431900614483402305931797054451787768493325769736822085804605700274474775190776403813388700206498721987437143172165848418812981977811781261928995855812735678754070929400946088026508030352479678476655407687650318503382138050168299605448587099554489112084731002425380209388695465419462074805242979222311957092705080482747072012488926672477319267244452448423349159922506630892339309855301693335459481391203113794856267581701308924137145287974170192836617614726429320382887484662080599750000218641133631265515865137421631177406747826311385331273707558172237091989418348703067574809233782322092345176700915746683644344132851778559172140361342980337407422486904098690475331657364261174322138460774127008133142376473335072739945664007545269681154596597114224472082284354624263373341127585492673199563208143210946115590934307485827619037418334208970862116466510746900955148783804736493363528733024886065585730644344036451438393962126391353966213130344368354596319263578060619888155286037674638704401801357373490411639173346824371111657530900654662819574306489240812623211448818559758332289633268589599752994931164815313443405176483937480003349663007514246658684896514504276090570298633601664764701594072596864288403469727075900489438663284810046201917806746162873264546994713949170783192319870188473141249729322991327525890788068949516463108321360243102429488109969670215997334187881411026764074685129135945721208471120593694895011203647213342380097626228639889804019024887106077656178202262758621913047094036349074053125253170756326497002473234141360234602456828091073515474435669137547247988601684185512924521084892106631364005074237636652024734551066538167655464114844459355599961614121244803652594840795914358499152160087471013197683634251565554537026389615033072598234392741000133297569262708041839485721972559517042349807739105521264694979753902440572412769157584840657335118733470275290895024689163096780076088795908661312648018623686928891292724638979118320783504502572165123264798389971995814104900156862415173050663219396942251119833803612986846783193349362449292282896999933974798725194568879122133553454310501556833481026262660187056952556176443266484686509315140426133367138125729061445517304301148641529035692948693868595905900748910416401345528111205540686313912832651841827760905666898267474943473019037448075166862494624585123777655867368172284080248082250761139436336151746988896807761936136414215997196499201245154991324153379662504344566662535634897120937707562952210269370306617162325567926589396585162655484608402283780340134121547283815787869032694333986676007983954120968177763911331449096352712589051807618679340672739602978482916248567868428717625470777623886659093411264429724036821592083889575996460461070890897516663876990232334895894827650920656826106718015690572812572414802715700014714045511896611989098424361327660208343446236479180619792022493949445452369718305100910332235090345528157650130137070439023549357193175026960858118445571618100881470691008834758911524195116725926664882145298812165127921939936765855665292653880722074833085763129919946605993807017078523401510759938921565312859100513586621550472168326810187475468411782557395049954117490561244091435196288869003480574405530677240774433317110045264215127624488529261133535842417696974085567848697618502981435510955867402984740301682013892559812976217392539548446052755961987640594863803638117722525505643361876423895430945422507887158646769217843856612304835544318042543022200227409889444037382609710007369037838711989683446585038369441688268056303129380781921828435617137982442626711564362451715971510164393679068410455768893640719876555483057147717237823828522455483189746055341953063435652949233692597640347449918586021275875647618975101914360858268404971945215191689311600873977956061408576055601565254712084468528097443652783625731818076134514388141364239054803282514427762467112724893729346098172085522727825052936622748278167691429648680928003458176139390062194898816496399258974447448899237720407722269662047274491014181998861225978984553624992581248524057214390890534939794042600663510698374829098589738542054917793420178438239197888547705082356355697020975438693893020101352815191753498709373857785627640260973405063238597878714253222458191379601781747691343906905230931514142870640784044095690830720330779317378515126791375444181555527211640171745272523284887365886922960182390033616430727505326840405337796056242838040287494886927503000109980927073121951093057282477424049079167251211476354290416130276471481661410454839387236112903787547397715020694050868443336922810984253301227073122580648284713924999561785109442459368402439661434106354988153869786647277829603230837626599689669569497242571222092714980975232346846987779657619051645898288276417724044018612377185960311465371270028265303380871240590467978513985051963354003740233678929773042414126447222676408648655188702397458309637102215655442313994051987565938411434662148084167867906641614947097260297048087546285354536062640741194052920659611799961471960192659756569495127449165185917869835092650250295136444648665179562774963360895997681515146696257871538612687972890660431732802368205107728013003331506505008685400688800746593651441187447008085537308095714030299035557807187603745137759383605214547208468724525310257531303802141165218650268737119076826552277632990484595682687834756204881550769633334843639221153509930921622518292659562703551160508697117276868321401873180998106091506511677855852945101655576835011807477846026730752063332711032520605479867623765812725733380009058928606869428881411924220145795375057139041397913386025965593527035455921494399192896575912198763849397154100676633939835230777468913718612890239761251521466448042616276796827257827167952750343124905491411768673904428922904347130406398243980679663185436606841019149400644584731749264819279933713905919337077241099553750293298435285536361491315121258180911152265825897769016111933481977979393605023608206053786622855380077661349217523894798295385582306984731224376339940802941285449358955191333196261965312830059271860005543127870049712040309021686661526866280478631050394182791591066023378137504142756138527628934795378536217282434930213297188819728270921533292819612334873543143855807382414068792477640696260913663903437773338795063227351882083919639122709776753453609438875493118762706303523484293261974518905059586203411767439910281597556014973085235671251833472030028182379743918290176324905195793565501023285257074101686850128232037647813883305498055794181483508218804621418159060213950647170669470717988979943769863357523920098818190619779073474539917418261424630486659675156205377420848743698452391791989188139795337701108814944504394990143520893188761797783030301873941788479843840721048152702883227611586870175691282263264643368102821878961911068568233742901718168428270257964547495445739845677576841516190060349529482569954110810515372780129209789846503497151465851322155617333514160536157273319583406500711664092794449445102398102290832290896709658884782505748512748191888168495823726389465630791529011451528877590721113433713889450029488602938363656396382251999333438190453956758821412384577445812670438471954773480617099105458363335277091007960723059184070585075364584903076753298130901426483250951241698770421593566649145730341396619052131153446807171557121348764773024933446207839046157429303332722477739610367578736366576443344752232674647046105586319936759842689055941377224360269129350181497247850714708890497068795843876617968825553903988613719382173490793279861394199186742777985616330253059611402417648664523469115705292837525591258550675201030959852915972862037107606106785332460214626552676599665110612040261763849697443286444929608020764900450662904110320901219358890739618821713437435863561465231662609321516139927572142290974185504141056086204578261281875149788813222381740961903357484240568052737889780989899358447113171926749697766934014850358714597207973327713338912773294277518054537359564333929428099621988082143123127233736560321433377508837660038638097824097096648366058718262020060834344255717720216106245747042846034993824863452728887487496635584302105521628265976183522124235763421606666387567005716970570831041897870429422655247119372529971720868749757800091617663445273847106085766386131915219635790362523988483912206395751170346667000322167599005033085766327964194061018857937124123000728028222033759457479185762773590437266528114737281289469924036202941715877157416737057241202788888901703684458976266420496283449770944792163692628330128023986863646724043303042186390960160400996802220933233546100991498417493580382795708454377274459699726816826713653235096331396367678925264156193793813350226307316768355232184391977878200577062038334418133315476523395060747211088924528408930235157128628590323859498960592770559212752962319475202835626859118871718133464699304000819489124706071814247774193867922396059512813375995662952256896347976652285364254243115036167821195670376289706200802381888381864629665044154412720021103179667266558039304085288517335698900748444766656511222560775022378418683245465996296784824158672566502687475756120526261503165266352433696407883805572325661131667522564040241383180180183230027029807209725845631637288035783027530492267321152587096678742804480801086508480255626254226632172798952985641548332930734181366770785026559078700107508843381828073355014965136833384666771966273728427710760079661592961598727148299181555165730792029468387772818391405778241492905334743510791931112411811013557200688317898719870757817153833805907157495024534725789101161726598494341343071806249712904354935114620291723906570902602714499521304657530821997021171138990156163141655189869686631331622546509621789314530940454396345973624436206629166760108581942367001900105465978255880491249439824375073879910102472762075485237031389008029388105903550824135309006773717301434423935100739189067987065485735920578120352662513292926696015078302482560445531951788020556984677821422205991482210546556598476466218151237343962781069211126844865938620311811541789839957650601074264143727473834362285976294625243924971112533895063732508173624904166039495559411576520742611839270334241292933915274287167633556130429792701283644851734077874970775073913549188928587875601738645083764829363780619015115309786280774885324086413531336645405631571651031563490383462423713047034469625189333134170451826819474169656229830357447666468457849411731267488147917930337168744851162749924345500260222338640097081304210793678418158414112196698807927690912538245367241702524898025837004374328515569579042835576962742648828764972524588897480160574272176586224092782298763851733542838341837975769010173240901022135054792846759111188760444454983527529539266788967615443367690304737317422481483218933331531871130751916045729597111087172596665242970762311525858462533568741152740361088773441235717218907578823989619464003361632360856137762552437181726311202542012197750768080102931043927161966941071761593207775706659780289597211001827950757502526213352087838297719602479709909452993208538171012127577873103435420462948604782446826193178678112477512995255434078603545962786089166606241182244617803697306509980329924697418515764845220190527728440525288558995303526937781688747303636430936524238363026194485690612273974329500587428055084821468784849291122754116407777871041960082076799894071516304076824805052062351581542861556973536183255465851983642577960830504491209992469032973419625900618262207786749250765930635111527122261386347698838227878398815055324539984523297786688148974866158743495576703915138458905744892042919400195885965768752346059845512198791972589098898006799414546871248998439141236233215366635098300117475917684938888816414402363130851452893180194544706363303678160761202992243327575541097362759355569015193645148593065627670299743592992909449390006365289531379978404371624869081678442762280292253931077786433352693191732487232128205414194482713056035962101169980597293254916038416850958787351802557611549732427610292711064941925743229851538766470263381539996206003876765740050697713126631957132658888728109903658308805375183321887155107874656820800612310881493999504430355215582974648697922320034711232903019442080661292060767143014113306279114002266436211036089171573880772170755048945424412243295093198514713059987184081511045475671553147244657027077333497179366403793981320656943299425411210921604436343601974085656283366206801293804412497441464071736894207418141069116124017301290538451164888119816084566337914842455682382158939450209557038222568825943290286788023217084684165680379029080872274281845885180240384406058561978975478564262159578395156731988919315768852234471258151907913717018305448888440783616044745937592435514331150378528313438118865869762332232261911029245156265199034915901321464160237270608679472424940107305609247238812491040237000734614748541174876400341967741149921139480112029587714144187607480054830278854584486329110404374368610466806788128929758172790630044319898243703206271953987441927176642109606438756488540328865454868066477443130731186597307286053725929542874063608634700062050769826936290844840782306194531222551770046543078006561669558486378875112964171522138002284777918620087224695652660121168080228539904903584402498252757851638498678565193430912447279368519208336335737292650745905642769409520197228571121600846833936209874643049296647125089781538929699222656229908172209051274486869569137365741373255155382673791557001919564577154312527171257178588071927401995132297684935930827692535172608726791295172334054395430558448434271601134114156168448391287945235548355054455598059978798823355369335793191534965251428439144438723531390602188555939337249603232518423948360878178847242543614508100089902408498830785322457714114289131652734951654734969914094337272397404228721831972193251945085613629720946439171570059700930522293198208320249673611780040788185601909617614960915781086012734781427175170906369708673900985549632319323680727714789799461192434597137922925717105317530028281781278165867647342729273624240917339191499956620798236070970026055105895049558362097354053224482284734231421851515378465599650122648354606052596831343059262837080283292010227770245985025721924464114203927186126256747104643294152890687527370083239494286256355627175948412916345907090457966369376834262755406554308138773198198011722291123344881622041919932339432015163066877268947174462779409500666387550906240995024760429709646439620237717148747550844387005831969322574378395568777870891948106677980812194694243788637527010698090267530183463656073016354705329083114703313277088448793225094673391648649050910690599476922773788936822686502310633575752383145719980251051092937844403262603015600634927861389836765499578680353415036745560289180312626626067738004815485574652842513869575870749449380223808284820084589702394969710850744022344258639180860823033583906575575252018537392274941708207225629545816877583110907416599147596034419474179501859675122283639685052096255834577719570270441727326943487154225655994794181295716204899951770496857854760891528398863733274410174051273089261938112393244551318479641453966405004788050499105581242440156616704322474917209459244659253749906653499354435395829301408771093251943104133159987726762732096213337397747481439604384711147400757179326600864874483990768349576613277450583309726858344354299768566223078327977123658944558756646254784674129639743879639240403565412487708928333161849150106285687829456958974308047688844106487345028491338670766553369786910715217984800756357035952442977854829420928405721399526327185162136505731575893353951755443115435036247023509342787508809132461409727931808820755754968147914573659753512623328654203329932833636400261710153525365233952264754069631645779539130050339443277736988591003956378631779487950758849654076824652514889288830925625787223731831380563545131125251323213984500063776886403778848459054529312079241823272078153276696644697241797827839788079647074295765807686798724720941431313913209131302970659717139045995608045820243851490317470395477965664484098429212842930177215663613943418343346816818935718297873724565741673490987568006761892548359977035421035410575971606786388619942931948542805989084887308287360284503946715733131510093826817197189037885370233636317215429977797877923141812102176991168364431756233155791074487991931097812380036844540648873140432619023711570240404948168759829740118908773470763005254559028225205787443634635649106406257583046370563976902283341042361859385785444159982667086242380884605275192535325227052494278809725155753040213294784399168591215111114525199827586098668165888049263099276577899762934084546022583294614430711911976189195827413462814934409671804080862516966831027394932230340986556079508446543424770825991755240936461206239817328735251041804617590895639871296228690833036208625620475626387430484752516432433765582943184591493034700469764372230788022877626748414006185177295820712896073761035020777039242646985969805505995633009867159127552027264241445330868347226335294700372432177207385063420483885668740234039809905235994170782421162535793640885135089493949484442111815900458137631961530191118941343850198754440571363866543073665612445682221449030695345813825468391906123801857732972004525824923025820189974657116917577297779487493771659561224870384610817877528691078147162251796266212937807893250120991920602934327797932762217774217414885101436257439530516463462831459958582583281824120705681078272835872243161406877102283868541256120203597783209323037831784543771264471301016526299672634645093897764031210875168760261153282946436368004105384677175929752986468062851841670240311763858853701823708743196599386729557974862589986144396878881026078474329534456812532376265977873299329223336643081858487289147552525433754719070888641708376301258863739045271599258094782996222562265778244797559137363955208710654985770998776083259879127545552519646475337028584330773972996459855537502234335133717636478907782709523245691096277045619612254704649510236472561221987886329355250746733603404396037713869503489866211050440057199458305632624702678408474924817402093707287076353674316531461083010322053806411475343544619106286196927843324855326813545828019600624680476572831648461639520270420071608327215237336775929918470189417659156362306803720938905541760599645808888802532610062764257729663825604723308279524521582469524867659632725320645618160543752208914886762968163162968552039058072563102788639451082117189453296551216808084035368944334354339356520727616837546928532260702137197089694296350723344623931883745589671342585319976110009483116095888650980339087503929666964768311468386303203341224937469808773957535130175529620016426792633797021541087209581512516022229305614062682427011004559252500996615234813002113653668681652216137353976064812710861259498882110474538324331144048043367310008135401528671723004315034388168185276123550247981250217332262760921542620947160422153085126871112238929629665430966338926910371048232629341339472001796332109715319399462770111036678799172398056676578596468351056862570810312826505898410903112599495776824033238609252745200645265579680981451990508239499275318565465950802911779053911163447800133674406025293114054776821235712024963261987561487761887509988314727038402850311415696209595818723313777928133033523852501861999812469724270925315530228203825715104653088296751163332907486792338320836616879836938975621847663837771915172520490854089222170718441575059640616280929086442767722711403482616747912153977452115215119033966054802222581129884434026215888700241966842172747805682494822607060178743431624482229740606764155680294031318106102520908674997850919601667507571802860594129969946445523141496505124364195511899323883597079017730382254939030605766563500223540102375494819128728426531053431865937855981515828484015227181500693723823628129164243412997625102246477111020054885176144685071862191394720319972943638465378691859478656226892545183312973441620555302276052347881817186721403991272290121177376090242297492916934385395295529570596274988573396860176891323237117085314100135766361084652096273512424647502516497630045256244498927906077496343945413017279608051306345684974916466819795846673123342936515558294637200736730686527542601027280463053153951990489640837181960722998561880595509644210724944803129780467831062980776420282857251241180841272987708648506004008801206266211505393765785672804917588601687230469296850052340956493898280393471285146519039843793478767826719903812161673833047476600451763044919424523301501616082833252429600662402545375684291087746570917127573762447156213326089651399652296135455044834618050360047175037039492398123578124479285669285818290601160779771758102738840258895688546985568149975348801980890785842505454900475720865591820848285645191771184039534684521377491439243772157043679276863938936418156163501278718049860705361503267185484433525325602077034158656604966287596904200694695260696128558026876260515226454446871219747949992776533542776850429974320540273205320618838188330165205009930278922609117347376681799381229421429557098155111031289431819620896230609202296575307885565779779026383433791496242329716341076277640704029168455282338947105547301607494880278732297034207528330989691440889429332729389770090252793534213797211473718980387756741194839255589475313773052381284742011323918448022099232266424389335081542655667282260352666384567700069672699503926062550441489215179443841825785041476669807022788137274365528079305785613739218390486512197812767053247533065176776351991965869619740697141251383330008397855569132422111602401906386959674918018499401806394954981225318573331066667299818283028577101653629735102676604011895999686319473940369152454721848249625478180154219833549157491906052190366639532916384994177608251230152865500465062419811339624336649967282677272446478324092896559196696100000042967798713751888098420697282938365579465289671473382115411571562258197482468364086848331313469694217188217517381323822442562271574298750601558721286580514905175542184995381106667628053200397085567163802974150437235424794113786145562642230918229362166557512698060034731895648891242313948528681969315081930328481506205189148156594923308847229926959617280092320088476121303117447100317257990998847704269576738725840426970439108034106101604136141977037657411445444711999686929075975936016202118191003696837532086609166457990801279627653696513284734676404292132044574367219363681155435611659119225030220807317001640373460674135972351145059771619916699705243912449987534324160048054950967582690442874435034738647970134341751421222663607194849948764397166170569875138915668224149750669823688128590683957164379660719348157564461876852488734515496262180270510643604554931935341672761148387032157887379846498707148316983076844033552884269181464012904772523745993919606645668368362887144302783942935887965108488037070327705929241782168456686613452933532671074495045995533485962178481238767380138657779941867551774750169043897482712400091578930747455709777521187548475598701954682828878273798111781334407147116804000322751247921420212483940424824856068648050839609860756102734590615745306402187861780540688633411400598457280512785256795557841963783752764476878394507714398039848954411995245801522148015426795709589623625602709899621690758189412236828778558179648812804595563548530799329667560370677576075016548138809775714592899114677593292270299871204200575210847322584770670947572529504022971982177711251796270660486752343836524596029150530536016490300572639517860665277330409926071924626395226506611963367400575168364825294928504199855546531856681448283145169278500777172720027988194753104517071830721564177821725943923102533886330441512779658820835036348698301112054505943537207941415870499856110930722311687657468475095329996202807426073381961087939653439959283659480891805048609987480570429168685704215350430055245321871863639306634603693276999820885247048315533502924448634460316372480976813886106261768022205876115452319135284928183791923780734572087988995394665071189994109789219431257884271439594643037984477096010760195056140431738474363735951936463187298838820754487460242119472134570779724469167003908952928886696304660374570272782400854778073687019191298792147264552101213653023559401664304674882558893458615048583148637171388827139790740333462942930841018453444576590416189816189003064546041274632824570602853537892175850906846153063179454749607040563179042505539155701177616291869068867967708150130355696805988670233578798143092356509164173180609928890283179260782420453010328185780242496400998320810123988025536254058092900578789650788756767563187770018220499321256731331397511798889872440454286249431581345784056439218750356701684621323002768905455146761572363148740459813114121986181554621533142825361610240220171100552653647721693726309918558732340302229484240405351764431907077191814841057755798471115619425648382627614757471795566721504724007355527185155593795239838757289002970133320421122166587468317491319858306013138987137553066525832766098719885083643888356826663546599351855628385686278212899996958934326700212100556280173646132416969179350287603426765039035417915054410878929623415130558805019891519092579713719962130983427462617820028641352989038542381029951743325804696136539403815801808214182360780277326949836999275768576445390111761416768810703127452572722996549384039260332238954830532127865366585934260558216437820923330903384090917288015556554770756839074305680010166564980420891627470983858680133335848755620277900146046633511064156449943234303293846374074865675238308048805610370832488922594819711816069040282545986561697818897992876709628966092357214021903293324605334683145155004896228832464711781253958042860526589952057012478018706515261893534343975052214429443488281124568833557680454547892904627070332357956100424037668288748860677638298697369008432735514634218967065015933761496807751554049877864551928917568106591314421423746559731422638703727708278367268026201477396395717330320085803952528772956477565812422968333641425132921175332028562486334551145049580728200249719919792617821445452949750516307028701756440541838438739224933544651693727132167427201498763017478986340830637005943824421012006521592404826497923318479223041617139470974660994288345028694068627230167871210154686296789640816483766590064141304091085966747664901965308529564775612677040832127565871235523902474604122179048774717845425339286672992635226199174547946943549390659304809501834059082869465803360491205113342297858967321427369317371253448986303707572854015415510092570515325091795402004851308726017872789025221574214533289298327409493396383276405383905182199335719174095884139292358132097154474120728899877512180937546001515625126109168010891522050784655124335915496324903121492504367865818006763230183604332722216686163614739371268074004661500935706911747573851913236537675416734572148314990323754421686210816214294515293259139968505407014323477375049155165908303196252440014465920424619993641889066959160868443641412547542410959421329706926614899729460964019890383906570132263481600380190031577190860644901990711044930664644584367550248006047035132605665612606557050554996317486813562328859752325807092657588908311513355795495076037348143253184886128267448167178143269545437292469739737923351556094635037432906637893155766653994549335152539631513316946967928210859338232339348383044523559365983686366796396310299063372020869900162386095960494826699438001362860256725504824666918236178796577665053343767008793051285943658891482351474659447948132591472511778659978263942751229009887135235607853683904342963511064384520570470909311765755754940800730529459019654860416997301453008456619325286134959298209358318148762331666643830030067604851981637827158790184986323239542165278100511232406893935650429838710544764782553013670514591087274675550062712521148497660604436421326153091776866792672135968055241903722789557416614884256463165562421938889570234715976015703256018597543597099343260485867176448376900936173578034933952907279068001035924200119251371896138453586194762654101697645536851614316782135658347410341841008348041945126726946940922638913617089361591971814785065964491819800196370037808221734060915804289500431390152029841563307593137740541080523137779888312394820398263140283858498426127486496421484269301410860496642653085642614110144883302828658193875798197316767966737527590553614554582574847604120975722598959193696190117828849731092939024343538886854322669689590717548325146023652638910966695405723142455147402993372449489205688657769470155649737284652168562417534487592560780793072887507752944397035401072212599832702501625890108234154669818453721557485667628619537315452972356666175996030105531903028727286521392742527068783956662509075366085713101338944601469480863292668300636730635618223121319353890835985453682519680468991783095640877214705641101953595422560208245622400888588800098313242355418385230264499507147030222048224039717933153902657842738595600881293839126598884379772838593590394577689573738549241976948705430989885469202522437187229616010112558551345160423909715656383787532188499557465904932198092840381743262945264778196920801087657241494482158813464577411308041826813012647204263396131103060951225536907595404097188592356578676191592292096388758564616357841250556534082399541673416909304969127554936538611615075171157480648119203761040116534615318030720370843509467038398641386243746830459254152408325395208742195791468293831097468572607291978069849643712235791607490329367712101366984439281094113066549552391158247776672135316385883099395099592233554336386779010106120211728913223944643765388581247763901448721351799749800403948509316687947241161460792882774878564384826195376743689096085647777924009024382316868401051944680734057831940833593242229945628311524683583940044189676471756172449809517755529881581102446650028267064296579434400343925674703635633459086071794343777976075827636460858133003905954957950013841131625064247004798253175288097918943637991311760548219624816158610828897658647817558659235909727098473657061640830030701036459047220423002070941998654354831893373020243728248038576587587838532185945076920184537449729842558229470841425492292027534098709441187085507097372326803851456065932921940282037120798099609424911384974875061670481784310575435501309895303172685934087341231577615083066092610923524684377198399218236827950611526650932140622925474361335068365683165629286338829511809335171950953860045996499470467849959933387590710032867137247816344330829692983258388175839834199188186010224047289771795830147588190631150209380192033617396247553770656103119577273399880226558480213200706294125510327689660946379378146220014193884866898861375064853648696526869776660374907402042440676173886033897036729580537531037524717557512265343695258014742747625618125760887520436293070883949451230759543361028414222193676968242306980945023474748964387681937493970416365498055634771289615856731923033376660109039106993457269675524086262599005182574739470987736964090375702759215656329596536464318043145719779128733558013955631840990500759484556461639683804127009678077350725814560848731298259186823984769386686579318650890009409766468039784760881586302166237159369865613630080332607148513668283333980377992694437363589228811370701714465281116941963540073288081734956411597039330641219578909431652298305796786591720621096955348724723896597170720735014873396627983642665953510190517983724003927437433019012047870889268941670195448997880530715189164801778608619432152553119286208590498519481794499297845312780684196359074508010094595017907027258645922473127625964128145082653088331016627039806778051435541352778273216374112659265196231348937830461945386304738044107357267746629634934663729025283510212464501762478229357665696335624894068612565671246342915764902385004116338164550344783902642725921495678463980196322300363593124428185899230582517313096199862866037268941944557329537820570453066598030153154618528644922433647981693515706821579058432854563403049025702893965491370199412331981676636611130459209667768362878337959572102438022642707610892590127709580737273060144465886390747837611979924026175925701028409148165947043222475279784167382897369997587523044877836876373536362942764690022758678834404320512937372986417987888271134398125620805493107860062770882991587874447112760855086433642509909433658439439244336771445350583714777661315773062674690451296634018668830081965671761747465578467393328027036412869620261512281698358562244365608138147107836692678636226518677404667282023020109621834343225220783765615986379843856285879887834035893225026272616750396559873864238436585096170470086836806235869065598066525785405632520367972633879584926788525566541348113775443368424603893630648899859625107303322010184707898973550284638402887233861384975938132389090247517877607191773817341180885990064302762927122921503960394766343311161626168238173792662132644418736765036778612194411560843148687485761050892627070987672368779944332020046817336970028987181136808855334070630741780267227677670638021628632730004738536475821430298221373969331152158315577584131931363163355861186733821660137513275279505849514421078547097420707279241903174882822264821347500995758519153428789487666069904813091854076312106535143165123724758539141743020263798327611943798710305385672074172972524155793112908333874837809132985323907619549924620317175523942982600773159608621253029356183719779677403918021851214197783770820259487792190259316211537435900155221350568379589811736924384968431386216738233028039563707509250332488119765681309670782402146537278824415346104848203756897402244016990854853807808009143502342927909797822492621238565005996336996092451993701789217955169260496099796589000626281648877033072170682689217519528496105752890377691754248847655943528073403472924601455606449807695716175455855952772734165579814627684687098992389014586629781287306901867306632747345385226433125758850770868915073364583473732219334191277379094993927219057563212151740549343446354548673258605585400624225062724826100548809985980785083957736136611639382690564422703803481239182362630993997456126298749925949698220416224336718790925936658648041259447223473245556220514099577950514646778060666651130784491639687430708863462921973728718831578987643760532908239395934847876853477432034123592080708379270835161968808932856230641219651551751603480401673732181257962058320699313978969355536779959093136124386142660168087055026479429036430323512769342852913918669275058933034084645332837556293515482543470699278291377609918404174953091036934720059889155207953338618221970723076431110267716746915176745959202698072854371989989361570468252968419908488663009228007695662302168565980621843886605271013555562470941708642277493156057266690848580616116963261205947825846445862000769907760051470209483242280902692034291481485051139695917418007050764834691396616144101906091698536197674653915032380388176518105640289593285609546608469496437023943416364321539736936139910673653904601491110702140608985015391574060093484967608249150367685494518330652488652321360050920067489640188535397214827056825737924945872419694910452996213980456503536642222285059606260632022192140372174118928179139564402660734469195535959738284994413799474812095059475581138491449799689839062742536067671555889714151783629964788517033214424174702791929304676583605310265522472231347597075188205749570974733445526668563059702733992415057015137907125501985221884230504602258882898432469744701695994572708794866895305114934641592654710762626193611615923958444572374299381630617150639041935121060507388120811555075919891897224749100894006773929880347000326420343507493228475332928701218717124316190349158632785012667564825564950396724098926213101349526483806696734157423410263940427702903996923298309235756852130687903008189030549286357043421973150821558494908328023769536175970178157922955706049463514021284146286333986031219613759267251603589833344502864392810376391216621416148709980993215623868629644061652581688519569829178874928596052221495149163621812772393806146414067719595218291190072697698031478379643209531352681375975440753298487474964876483394378886029797351915979801171969508748304714206004275258844464586779896299779207093429486601939548637052857087200163463782009671800669997653317877226207891300087965983501388061642282735964627908573964724393966939642077463332039209787271273272125687922914208353580152129640087471505357015637551604980974387447447870028837737429438534648638673099230063795281985876135245809478917980648455328198761101718224118648584211996335982838298140787255527071714448126641462724851027856924784094319364505294870913975223406496389791873972778970677833353938192719155076609146346479640262684808369937829004022053670580959171850664976730906909625697836866506591024421660822026306073606677118888470291418886831647806336145044094454710676036843615527641696327757423949093082859155494176830395256145761140109349347798042196127439340578192525663952021624623219517078761198810615599949914707598472948483621514307403851119752311439521087192060717685138908944040348643012784444744231394162879689660638095949815054473775691448257218686785501809500259147692161302356978543185165268332449327856339659536769940759151163929651390765775404044586315622198087585249987663835502374801361212661653279008456447380873898178374641234324259659032157077904067707615239133915524850385103254439598910878106707530206512412313917243646478782784219342350262328297481226015570692033806397593715910989842967582194790665325552849010654942892761510842808436650167963997054013467132221840469559438072234500440445953904669427327737686825389219377167301012181187214804254471611475585995760106112119048885092544677541910085005078152030201388380144755008387631784626857483834570429452710790861096095928639873145255712302920774658946219917916628368498576359675730936014710485394992054312403817545734721081842735444501887151135546203220754319629839594973067682023939038725051586190842534464824074746726407471642363261594095614614405061379144099043793122183992730774874868343220777091097956909039639031392640698832660485698729578487496863183317906252538590419611993589733266324362759330025002878841767797047305604645494328980449204187846582529936717413009467145067756466166645208394205607432674209305033452846367262077043763218979710632249849347468527395384406109484116608232484116312251257477461969169919610593463362048042383551912631677530863592675414298563988993206373897906276424838739110555480906116268017762400068460907400830376834634298780111707656197787726289232040686369883155851373271289648029078929176831481070176837182906800821269595926889998975579111339891979620833812113646178072366135933850006758026794871130803109383808899831359346760642034856366326797668159833399052657095890423789451345644814982077749318711300825133416908977232310981909909510073720687853545057332150609097205706229916148507106024847592113546344369849293638625560442141372259967138657572421330758454066520793134887903286436149919854695865324433721065318624578340794134367567177463677994588420820734647107838913721332360202825438738569793051429432858280136701286360725480240689715570106240986646075760920712215329832258650930584945902269181463448674776825477193547732467677584710219068759341189343876350368789941294805175276603095107436623516584517641348096220320485348538328617016666750492455871157165400477553895520056756429998996133249011120214659778982572344817776987983858955725255740067617459201597663733549301181394607886295024271643330481846643000584933622990119738528472475972495336924614931032274386102541857755031610233400255632417919015240395090767117360423117815538643176586535358184775368377429375529546510602022069336492399897706406601695953648315414833390141800613616956306114029601123767051333424090531805494285642155315772088402070332977320942285964909152546917572728666920237789270182260619216258271537986584784126823731442116420177491456343080070280129433151669543085706107267971962699716902428454411061921960074896868596370382493630130582311897898483432169640879127637749384629906936189718972149524562851495187499854008309092088852767796588730345483699292543005886391751697253937771618666556531169151092835763445679833445401416348281736093446303762073655845207682917529891087368002281390122479675379640087053258117589995959546640999960252944317109490082944381725195842259276367485920909805404136409510651997156830924849937636030250994649955999165639400305110042655054987217020592638217044299784788472554420049956935811849459708475666339706998414291115116795773177909316851866013144417506106707113551810142252409570727293779981478104376650154135438035022964878134820717386705673445927177541443709164205656321484904008649571297280887164270452740397665573145858114883350407001538705703807465062191044967083214351894173181617147812326726854604954286041255654988669524471784978776906545789132325710407407595290494650474793784560889720396334175401781679234486838827933605857744118539052931803982492431659370317775847434118108218868312317285264729540803613399078132425975579298693653025861733842330923346194246753382101878607363733053260564546068975176777894857893859965724987492075997198910496560957089940325052091669391428978361380854705610790766200950420022687930216829012479014116720252772101646064706629748441973872006422960819058775853257684620974049537091352996495541803699252821330542026070494140908179864892336305922225389716894377318371631715387689070552066405149989920128082798420363945812000496762773314641387041722105897079086533807776129224562097587031446246291237959687414001585344487901568066720202312278234507395893000272707415489840142376260505583383891390642307787404327101900904431629719910731687588590945851752342167524994930370867385528237857233972896141338669895711820467555757876788584271287976330548779629896362615771318238161134150159390599921421777501236477582119801243817905290284639066901996947442636738566864898740113253190106795593164452349433642117917991312052833453976989120723561694521701547319045718938320378100769303455193629326561650430700819561692833254092346141373024725373330699454609842465939502742046857505648671881368473631625244402841635105268028826906954013396803632680465914569557170005940281872713718989296457015397041707631568762104206977809202962698712319417606518110764093932647537725729111790189835638910922190392094387065287191619975713683770286885864413174797007885626765318199644376515196431362703772313451235664253252776444884987674213663865308562148177805117109228898504222755753017996001176406818782853679599380016822603839188479802931281498501697826487202269744436256886158720046684049688092090544102308222436215371388995903699255670572228897904715657446260132888885938267872607765931537856130187619058423208542224869862016829881056447003129820112914221118954911278350625277219592125139533228678157156531073730632069890124613703806112434636416052047275357565770011230714425077510821188645929596088051421363656027809456030737393697975884976354281239178353077987601128894269308595402988031952042606205509855365924684656293611053839216252810567481190019060240627844930866679453943617230368827511634914719761278036825938828627186785253190637159200355630973983368606680091565289740735481348579429918298738458982959196602273872874957407690776586116881752192868525688454843043399795402985452721249625892422177097819205020227546417719097886100986062940672856601134123165172091655470764646077137566170452751568021443979742051061544006274250104247843990686402829388544094158406213135500001601479404821987287269775126774809555336528544582756906168988392493209531787606716264231397708196381738710704085623430272674932130600439500485969001419613257922606163296114594985507905997128493025171899797385052141510335101906216240943160587942592155777601612415824611550195682568843203442631583200457716553134668171465977039161251622972476354808803491868290365511943323437641418524094850907141444645481426656398642517405645627722032903025282120701606604058817333075488392865700365892878180625303051807816182174045851074623076394209933184366013329892106301723377658684786295468701200285040847069006466959831091118787685433787424745790445493239400458353956057675143963452650314496511023292192768708553192299991439353707510766975923064345258281434558278777653073113693113503865719223845083465642884104845447283462270873439090834365349761513023583928648485114398636303332253434994499307008275705455358977229277188279137979169735529827112161421209922856447094681416013711193118237714480224322140718808939905380220595487655250837497464378391084528082401658252255013741400795143168402392591034931809997367568124154929885434941762500569691262644502414151758898938740729643912621299579945267699320014577359313390712586282424491664794629798876177440617239147112961733231037799156770162764462437917327754866944465738360442946756074561601952088421147022172670172444121757294243675535966929228000440842603310996877136601646239929065409429371456788655607947496602320262784297661953116115621667471953384341523548162466255090599902832240157971679007314074702546227060104856684108888842244519231528309136422010889608389355039326456602959154359187104370650253138427733423380446011972984137138894398726217208135750396525660378823977259761023827976073918854873408490973493406669159781840009766041409439195747311736020497950672090457224332242328728645933162714733560030697909127879856691208422000491082757191582423247615281949187805810127444720939167253134470504933105348707561238265857067885762700771575157322277808143227536689840951021137478206207887847338733858808595253497021014796597689501943903691967944391172718699226562161483789645401233206230341600076915124885946494448951435031863504706968280537384401258894185317862478667627830144070330191228854904583292803753736450907700718121761365184527137455842812473248114135537123855217084000269389412286878733089623668522076093554062453377614622053171085105556996343802258390210825395972905880793838225097308014005752536821478984822901610836069491667980584081194540723988475662330371634474975135603666195032039793185119206817152364831584723772733174938492714826170009356898947649058558610087179764544026943403600331100377734079880907911641587593001841041523575837238473763050564737571207795869896536184176759508741108864853035722263732944524529563839094338411549641566784305917753326559032951928913066292707444132615905093349674389170706908322963791781538749986637908442716152120817220644085768538394437125370371948249686628033624178970359795761022609936514517963456111016421827021332735583216509581532364446210733015131009454103307607985902009385725769363803281630928970440564434345719739943257528563809566801166885809493656020270089549752627258769713017429337108750106365202997854671617633343557875742845413826875702364474873273480420809502993694089257231754696130902516393372520076856216779721413831047539086995382897352717495906660422168037964204139895533735706352891187817711237963801315956237716577660899419969938969728070500587354708928570238544433839770475459852096477667844365727138996373256580122384156418731097353075195449351783008508972792122108531397906510929540066052599263155640767625543960279865223488754014210157368245213977469403370063586690289383833290542419433056430643037022913661631368015900860359834447880582864390152980983002087386722447096481896585152474531615236251523373167699179627381029452556107211399250041514257850860617332154496659010910791603889080798182931361200225039749276183448167914106683620549851883514848273974293388005671721651650462616854633852791292596958956708122368165990950653948702025449457662654323922297187644733052096974818160250430919567518538660663937916238633340422098529382951689829118385200757385469217875487065814810999236851768114477045178829131128100286810127892402389381059608896876558601425490766149090960061301063302396421407507081404766385168023854829423336823239757194448239416933636511702299755075312725822071640346749904519561702410708131810192441798320046633264435290707270338973603005531933184353128737810357643457541756644764334278054988192884504989044316155288258322253312314818591312717839325526151048875650064958083580625761607093223873420174373907368577318731898971770507396325605123958477711390888841833907356831189080436432933595797980838167412645622670316966393066542251276312282421210562568906705827026829984386519979372362005127735879553096014761976667477853929199636688966290260076711608568113630590417845067313626603561407858908239824696525977049572092025191882638220039572950953972450469388901799700856218364034384983064413542153898892131015274395508090534199473561658629694113680054194117724517902349137431112299781185231528560811867132799124747149381833888862870232054236831358373592969358719823934437298736613486355162698701651356811655163334587458818300245044283915106307361136133501952452189704351101764497281438084051677254457280685302549264590976671274834731018487415034730471098937740501599326053767346047595040121729368507314754930708706894435213185382559142731738433786959832153448667364965595556396592955116880710182082720048701208700581963809825982576644302914723699170914028215399485469567831893096277281451637738008521741442227781647535641940304189697921880817551799378060063754558026997899189097658652998321716499133138491306115975804238812837089712647919268922183610621346989699402830416732276639052048263871891871420264468695028506533269852497494294541768802280367227639516162723803922495125000217245548054804508224643868503535656337385571897127670338917708902121697041319338864835319792047108056629209507772030229803892586981200494530692267558834420956152148920876569301756179658375585780029694151733973754911912094895639815341507585969879555439224147546217254119233247773640754284711284577891726877665930639144667612328147632637869376717573465083752730995974769953779024349021109461594244692220664432567497437091235537591019451609100226873549930781169674755111035478835721455346600632635876895591728056418173787086750984711757385217269746146171100547283689750424578481962204333274009014133816506332405093311109269173367985759666758043479147061895067046371113873303354459634356838064960655532638199669094858250427407968061416601668386351859880873835874512371712033933887827301611443285421246943845492021401228852925801305631173034633998624192807403242629064175129815272906000796837468058046899420128340233222886796777940571147232645409716024415562973696210800610263953683951211314956573058254540034649048714821361978125485699453555963391736066135441935036854582065089920885964900511119536877175055316872560330844309171904630439200820408460120499383925221773618339798636589902046574076371790421589361225400257788527838987650286952877292660122164595635028076826492846218309763150226345255341103857385014392506231604783186464824598719340390283897431043172317428767355447195576328452757735284693057556118159974499853702144110879534377877453879392961844128298944088130205234033833097016369056024455009018801378637440209727984571498302237977013898292160502258636891771947970682701016791659081608316349331243285678100237172057024776653650870607136018313240239287990394773499696482503018053391531883766623763424671620406102204508869827479095509859156780225527087623407729500182501259384092813796239949019233512905636408157009180919408408662210964347550121139040477454762622732157557138774221898787085428220755648931091026528411772377770205928900837367934028470198477774061904273163067892568059063878604579200705474913194814547766016158231613138280141171253330811520434896061910856011342272457069222595203765204713878660511562536080321908437997080969747124152231527248101762730766362563718425191139141477623238694503734710781285067667346127200257107328783379018388969562447844549839007121097458383627178002673756017911976789628513201203048804960185859834407773045133419780385350417322312946825991379533408683011505973729351726903950063513746936309526456143398346842593336290101620187482345745383734142748673925364610671312179362119534376729635918599680358548365195345571885258115513136508836152882633235828204423162678555005374873221030626712723574144850353985171833645526260357401481829288753179991994689348622865365970296044135965081154564057411437461632713245461735850854517896272033798896216635237870284610680555479954361736595368212576067706816100084577414247870414488734382154620013998243413801591386342309176414274156406135213906854983859403697262265564356059814236242751363110957266018897458503674457679198586123691129007356936123825927462146351019508345853506813402423472120148586957932090723554376755299500974005616478491986828466568787097150207321107900180692799308972516511846934716166006760198055522510625526199066200018660804124271091283094855166862058991261887136966344781643985724674685379341423629254836314827604623530770539235230764451415276857661609506118196144649746275941534456091370108703487787852816158231155981926974227183316792540605430032679012271273124043572207436143942249542210107899093798283186026059389102910829845109780875433194991138421498028677364330527445033562364446709838934448071584470540011809051222655422862908629245048038302425089126768640813261370951020717929577813164714123365350459771598007624878997257665970647298692766376990184120832457945985936886440537575542824820864373282356242687552079284143637529335653663748552273249017169574491194747896927281275947942749182186794570930982037454880262068653494149788479916031663596094740032513947355507830641378300700578813546324475191079185577455095318914682192664962373406288894312325717106311820390822780800306531686407538653008353672147654200632379466383563196998271081294103101690880373096619470606130819144415627036810443755985288081114934310788801833001904862116898338797145686514637411511010336155997749814377785329390243235246100122522946887598068104539111322279248622982263569127017274406350656051178145053104731705262956037456044037364463135960313706084188344261573506486179994329590977708300380569918370663197243161193374869857076922879271562594231916931320582496399860877171744828642535420810427177476558795584220744478133880195104037054278450834580007519780843648733472521091577582603532777943429280478559723999784961352602748368663100829846162929813990379013925758742624686131979758114022752587349599811309092142287006384838244840038016856769326041968476652737694998910618611225671796551063698571808924400038846897798130915127264323346128631702229158125610023491009022982024597456122050711542114177989767803654357531632460250323966497360283837694587581726670427794361799464303258928975113416370413961584187344130050802644516934649181541149400677724077711010979854292723712055698911134826635024632476125488584783094130287268270666685789002833594929014542692828292193265292652964798847987337517548921581522156940533920372924738978358433551946121417961042631320453599699593028662629357411626934125411061190717885634131541995752276278844405511104011974631027689626608361473911116313219255561007353587044984323498343992558168935227534578354760691555145418578223396702110876349770657552360245968566001139246869868015045785648664841450044392592276752821150673188996352600036056071271297185712243459580172956291279822619574075994706266125102925598531523457257086891002789989583357243367153274719956298476536209934555319015690508613911624411801738831485833479178716696156105817124280906697783913562107118821893081729009097701776041685871318894286827249944561562227127288949798339853108773354940614588116340806837642564374476223698412624310970487602701879414729190296983710881901184127829588370617068642287318223495524913956760269331037817747210196987128505914085627150402998437496675350919470790633440236136611308318076337643519685290201012034585361333843325775791092732571658602118855628048624638473412202735813718504430694489899973634930330443139010080381160070072390137437815979837968365683511375671236580150769827307026622392388607536922311805602090578276246339398945793682562363717996075677401786869782570718612235238732519528334876767117545622891249259464811251639364839105054907020997914433993852143661147917273171749325869592483268481759781650260966453906613400035206714883398146171060120784022677576469294569884485145043855128559089141345964269329208753490709232273354710151460626772290850916956006671925704898134508279766338791211631074256846279713571428239100984665249558880022175452001361802622063808671856154707437157296049859109378031230430008927270686117185772635941876615632106629371347134544589023544577661002158966949172140141902476940831589260066599413810863875092634181615757920919745955099374648203577560831406216130938412339236441960431646696404801388954657718216697754820199296620964497947386142660325162415140672018077761613258797114629040045028141986331885942153888938530439381514678639004300487266455738316095669887294342207399001371358072166015574816016365128453759378779713584238374389598428802344985891952160764330458395915346500039726447579156561448467613603314440220930136145268925079508194616223686199115102684361620659847797317181310451203165757617027973901779514568755953302929138916550661063434244782765935853904625681914201225670425541804086960031998027150303661692848125559681955988360996120839494982598980779489150285432513335256373082734381662121884249583819564690271768458801901901787227424783661336113634854475648870594307725080449064150475889978539966056437757380355623294741999107008875285496310518587517617999161757739313952819072721816146288453482183941957402245801503645195656478581399057464971772976464965724763777169186402812370792122490886819163944371771392848425335023997340345175223379834969926830278770161794283129304784991834081889844689101398119396616128716720269660239396489895311562176868954875575219208243751839804520349769302857228608956512227199653167385653904265342394368597817527001825893459109071707338193841308028893216883262056950360766762424337842101000609157038783047737045531755369669704848531498235437429709548648547189317457271105248465131327545670892895803623177320674736026817938427924805727705691443922009178904115763419205622956069342018486885053331759879236982622222708514747061558599158600734193975961968723314559891539230041053093242731515089420199242001170120203830446248808362048559841199087079871499021787450629500932498823322345941918472233947320352666075396764510862963007270663973018090341996562482444676178309375140504532142880076170770526925172764835214163443173581639912557053179413398056105354261263271992994278592673654776812985272612774619057096084244440315917431254084126578514906131994607710297714565323104407044229067160407432278424706191327075870070260407296025090325286961386026913766676411830170065758988503329171349451665672405165625012211659531959033303854472206143956229023392125266863320232612701204227879788545576877784593741304624531717907991527459996334782769759760487554841013263778360845389384553313574808639136269567906465180121399251508994295133476147257081184404244295843944048288566012916985607006223531588988154566004215777238471025536679256500978236491335901738762928973188354451393809321905377217604492295840441797656677087341661291585167173185014837088085778831323103257753012131320345141497046433295094629863911635550579424284503760478097399200334558906869535490844471156364335685921810636878781672686059008251325341716328659171048576690338125489233546969339116584441092701444935995283569596755608920220173483988301400161861748371734762480159405558798503628482107061921197595971636854156443248966198009204741498283560808816307432467879890482536832357136277478847613227017072332387093580657389625593571408570068720576433415916142012579108424450619231767204343192541133236442980696173756449322591783581061326989073657036846936029589289163679261364484947401245337616301521562354230738569986260998680312266879286527402096355789689079676529472928274318161915223635675835688671957797431471450024281446862509556061940082109041213459488513732857302899077107780971670314083661934349546352707423036628105332379891513157897970415819599215105713133534965169918759453706346708724529131504011797263278519076079575762844758425979470551378119144202474251448068837986776941653430624718293376880331470372593947840485475279424035368589406858739254871285533381380038220319241182226230830777319797098721814696029273189041694546146420282244339004603754562902725807260775548611973651363379187402210871225800452055042689401836681872909373407341318222656132880397403347658690377591977344493887926157978907984997895295101199397109169356188211612228542286457790373261545935672813309414000373286927171666232760407119515849456293601556613863225520233933766642774768482312544702804042751765570353177522973283185623671412668635514267287294276421807883060633535733331515916392163390731006998155508605655118029270059064991683482022383431723379795958092147404436554193406388197209544649151154211785942169820587619344242459004715940978909499544915835086595386921090841537267290276301850254980999298355923807460054963462619313330904512887318224288560543437092933748580019351470301243659376453496495741842964101754929629748765574155618427716204250591687778994694468745295557960294604598297516046264223260915683987028315092195369850829851637920960416653584284677345196859980815897680161023296349793477356175905326201849235055417735668743267392992936831024818439422100686839724572894291723517975314797377892408379434739022681091029910969119143083142018299880704821547248545426464698658172055274164338726444862902915551190985810754045584951057443270908288826820614532022272601454285097891629865395543449546725859332071758825422447150863519957947575214631618220769486748824204904180603210773417499543122385782701295215540728488933946180279692320790723426229319745533866613963337498947767653732993305126218867624860006305590106606326428478939819839906347671601686104034095261367864103202121186198016181532540096452486470349623115957890788206527796867316474351069071232571534581411977660745622641732655294241066777502851418070664112477278938376431634613657798698550946388404991455324666581269141103581514818269507012191597871120804843074701744627653516990757138493172861980580858890783493187690258677899843277271063473483565966468880515737110464969780224168343419551218160930264630442888493524270183200328289178932573884695554112028443282027470925071329603648687747851797517500894197555754690584531859669701741772790883879004780259094736986068172627984341149464172322735628067951987315849456567407947824533636250934926365902542310280187753516035830791272561433635223219025189529187069023779898598749479857387216648310324968331113060419892732488398578436840855924038364270363190975081211246664479855776195498621439744685707916614154477756364608660150747588329842995036231874840310232464355884726432697533614509955574489121542212802956473025427623283529200591702880266822231733236368732800515171758783606573740484186310011333375045678571505941522969868363291912544709500979971174294160606030915223041438029265791818943197244893590502017668240145956262569428514971838740187115910501970836512568243417111314626828245981054462357596811317075865508625440493202327831722160926254789527450163022154854508614175294614611685300228141988844649476015624387173400601271949215724831210181855319257287437635596088365636128470418049441156347489791205311033046472719608167986227597719013513452712233356632395069738564995922174272279743473838741606972458045866896946394292638946224630541380015444295509995923097024924852943291605842982732899781300204370832980296216884994996797132520569813462081971752046991908562918658805321776089239450601221168795811673421259940100769625277302750698460618628411448840354484140102792228378581877021324333262920355008851382625181840133587415850767902467664916267223393062382803852548812814222366567363297963719032242694670114637570543892550856200624462535344987660912774502180424205754206682132315385397058383398625448755783378447415183128190772025926354916610363644688409472117998465808203733118436198656372539774692749447656440742143762346448337220792630096244455871938083383948111134684727861736175594007237775255439072244426631766033638569883507027216279090742868629850429848624334409476678768392179454010403934124310543187969581945509003978026627304867247435730361642884280284704550888846437807055047428384015900374912468469245768437068274659234888912661564646088544900966003741699165122180296941630150458429408213541700808699815274335933476525744962010790703109439371903342326870672127332568252021711270659675904740285346923205678218782895840277919656846455720687196639999081939311369409066854777397262469990145798099541913935109041523505214181620544577128627751050919953142302862713883193703406338138112106868121921112089698145256262907538306538944138350782015414631332785054064127006281830538029889755574344249543045526552510423260746690354375058576977246014846209442073815271881611049434844134244643424556507283325397912755451449718563396443081318501950689940831914801937091700876638426933571878799876526378760811238510557157759781903744645911714549198795227732915812923168628185206078035894086887524797065236221744905319366302553713216848975652678197281851123160241807434543822547877755517679652600284880588562093910231345005143534231218800230405018163270742359804241951541310992110260862784654716009178527113412349113994390678957619026160622094141743722357745894273643381142581413799111451740847591138942886301658224711886488776662284886370710729166819966463954558193135840743293702742213295827324031190254270986829071886035252075954417067581139814038099130408428201859774074388652194925362469350683762856231062989393425592474902960020771075437789452346261897768156027843581472888076557289956418670926810151666619757402671059525180970287998250322730901585512333813630195015941894974328787817763730471638324693555306505400446262805086987819659563694986678276948730691542053777441798699919823406156511051463015587324606233784070615935352571801069064696491615807861407115350340439549077714496695838888902669098473891228474197330964586540295723229854608832576328452100110571114422447776647913120279946840114740095640455267314648548573115745598715839646821952676338901504409311318292438620221716261970333937218847544838484142155818568457354716977734762395951754062270357322473387210965778565832453791107063405104087331478006200691063702269004775678446135318462496849858331634300923577937495316542354003259705962329138174615279633957179612218304803139584843007296154926080125633576540651328953308215527628999408833862176222121925232848598495724942302397718272453220831637612375214417597213951871602015099700668903793995735286187720813338632879134707495432481093044078374555430377740925644799026241166687629778281740180200891476024126906273482835905891780951859534942543087872540729346843097992830084649463600120557297191831631814859261364386130034569373969822385854898454262572874358174178466221917132714318424306393529434697272451085569570355616277051660481405606864239882819514480815622638316085166918491494268366952577294637249679617133996658531070805019046334356107029878098931760831668578875418914687724051267121674327753981846256398870587970591176316103102400421207898660430880770838526022826411987669856033574647699561940930949361494495603457358578611869261542270115633508988839235958747084571433353831956319196442648290817728969507760667209240353788447193764573917777537682871166304998939323291431466709196956156030292567902906382221902186798532443044516638928081294928388081654096612845591390355722997501030555905355673648415596388613772981648279476895746507356216956619866986506705079352578832070711680758286300220506889256456955636762715986957802690927301409625765609871160150516877343666223666251622061153065396214184719117646193768867352453610772809555450842870152508880439834824218600925867726755245643146690924156478651586197917982761169350440880092148766290329834519984938853410583143910733422330706111784919933071582005431083503697961040934227603000373978675928972321366576588293834689053789811012027249386322468551343538099515049878108914439989107319870149186108797929619923656281344830373843833504071832752860041911210868996979848222327541871065359766630401306960955314145136324425798171053777476932064662251974171622957638551152923532027020650713413969939703127417066143290835093812748730898818703802825569060838063468988684176172086189196488995109072397660020288925368513155879697695965868559221100566619378497258263178854444792847761327496100729661764314548838120485842637927531827914286399521029127323031867510168630567947834433565291522533119351546953648696055520706082816763789130003285794610778594742197052859998790979703640580797126800046493590326686999794080605879005679216509433627998253891544056911804877201630888342037811565688780702701037466588768782731641643213283982042525908826169742227960466768947854452474804029363936437699216689390665252603339867617296631888045492927505984866255647540707411076808676749368987114014846312450633957487572078024279343285736626125637504155943050458837790272673749482423282604912481560588100832757623260738896429770349726035149664956303646037791392018585024928085711057419277414688096092991702213488666967822620449402392741701127621851282426463545501997559934033935672866749433151019588784643430781199047984903242024842618812911605503780970749943988593978093205628947490597534857835465465623723214745343590733148028156578712027792211763224210997692636008698226500617320729379650763630925182186507674506744045873130219022887206449384139882718982318147474259697777618941397639129123986309978481068204545445639059648795858523664708061495366159786619251110695752107358408976886035509904465424429598220470331202926188257254880338294339394737440349606122219006734913330291326291569692675311217871104260062334880785792738827813971468918343182997845412261163388765514301207848716974847458890421078173679879215993554174670394514069124310800562905319813816563801761263289200177761241748268729074387977014626573727073424082142621320228570715738229274183306331307549321250625082205560326394982760541953448062638302421364225889053537559226579115929364938397009738734514356392815735425481500365967199505482119201989641834495643662387882399743591654636215338332669392489470377413507608229141537880596259246757435030763732220336883723353728765112223721892372776406059557309750603900920314247436683559206229145806733520142852840882729924276989506178862637466448239276592954418558051266276604407009705166088555010717893719605642350082733305953882918264772150639606571506418049299376187652580865164498198675772166522463894455510967349513222437640394015769453981810778947445874600375926355478268414298352431343045554019233743778187734061828480760752769460449294743909099952055280871528716797116564656842161582723836075845072935595300085969546561089059979237487925337426758573526971703921530521438704822978075490027788278729049877691753003151205783289098274988196232689107409620218256491086912199075831258800231755788354431872867436655780756321381973914374780777414318211357043749693068928935674386969232712438319851573142685766206528354676598411499950594495544259767422418316337666253206959090154964119688812918893578978661678475480318097144515947974013208239971393342725943874853052156339982907578541885701710471149017388856498665802565597063770204833443849133539293765504467134558500578186224569598436895685739390180907008382735581089528830599742089719874261429055773422999285010037152125798328017694040548388305897492855557647789305503432299931576153604039245518179851500137883057530536608341155985077927696146732028639278051447819200092874551884759861699664317152138639801631116712932371578115185634701850552419384502470010450035037482005834635148875591955617905480775332216188921492581658963608049791009028415888694250344918646508727577651351842124969191529437505380045663879700443938893055279861922593798378343817926821209310542651238687998306056849991407056003975320340246409578652744293701299505253472287332422995826781489336112652407060009944291243744779361602675106444421620818294121243216740977348602399351236591294115366284126518364834245028984673296341650593219873769043611037674253128366182232793936737216321740862567069369304778566906752270646635210660796485414675201158473112977247120200673912454160232528124645871102542210873203301366574444894074999906678795805394234252283084247538447345740786553305689285886308470906217688539681494309791957155954975583828092056361132002867737084580400461815420121210525762722111062467819034673970040051262087912789964110247486383646141954884349144979687110331348103335260502605740274394177308888026751478078150094256312876199296900342668371795648997158707767980210746665772796814070665382150619704146382605590516306565022798336374112059259232065058464774417434377151582674189498903786374789529580493569597271967944925252067481365039730249041228690823201979702026461927496602081634158092590155860675839810267104306604444640491843945759480379741613827388611483289792257652174823073208826743631129754338491554409550715516719945871875962470295190491442772623998975115599884637088180815162619489542355585433879785760909646610826054260937210990659431612108818992765470658156668383804461858651366962925969387621651120871367117949868030869172842445340284083637716808419559311228689687542186240964679453388893262397756022724781918686849459070863677287663876225569334090872603718698992056806232207615916091090175073826730076488708563523435856873338419619857274329778497809399616458656553163549910548351149922162572483945502500650967591725568564568459956868849748285818465621539212932780902414900327386592445962897009426601933919016547852362459948416234634912048303025462396908097866618070017165806090555817319759586068031937055378789516848293559694173021975402986910560932492246270152033197008250409918299400948221771536242277108395224893619977305628964272047671333171142075581433368979795757768141949584085847261954357532615884409160167018619355664208909001794744714253627024926101273060609605317808313829389299619637145129980967377162284306198229782444903343199193844794840621349476151190686359684095190968343125246638320472564918560856596708452890110236885591836062454622311345362576243979572731220153932544687607057187323712700554674199547319269315265907863856189762852744562086922334537476469975754722519059149854543095849001751670528762505981806528393617765437865983070822427560142067543503103362958288892682424922813607316342693010062372682442476169048564144840697198017566957511032108924384998651909088628390197202023056914620588521570407891561003009305000916956562995259638993655968745846650867285363439653540108417697090656937940793565273096038662733170019271830344998581990957198954337726483230180817077907250832819549618989909682894665701274659449771050572406829076193601021718009803160214233223611221716220700427007978364469921386635754385324547992417977889291928701843652316175052947947960330462265084247101167996408807998564024757666959552913969471290941822649861123460168786328946913602956611803434733124271788597812052573586674993616612307565532531264394594539094328560982781224832259193758821560190916080252789654239657288945438038217210137569511239862847417147678770612756312455945580591064920032193809929809857070758852522053805849296625099929057359030408317983856004557769450000836992781711178914213614252259811306560624628823843750640600679853487401156125361171989008146474378294818473748557954799515881706930949841554834592726654437754338292127742277116826060560617743116180932631377641136061787618400473251043746678441747638462326520675634156005582458466592011618839310281740670321618449018267361714537445750563589978683650161264145116101863189152778777982463162911946371743191238497388907111642025855405924177270212557395727690415873239730630726003251182423956759617859103352092797136631348384832129011823018505082115949575254112615582978498729520394970234966975966633732866191728455557462060987669750094054187690018029160153177449709861239046111505640947869433521737396833850714781446675686952580057597892316066504569294702773096696045549212442337351035883127245445531277315791504079984048875157920558100332475065915025076037938393727624940358392032161079074620390919373839738030184850037527569043006878129958424484234963628591227997100101643198586049972393832412518216744102382230277406118344327114202969125654760683326701438638442482623614732890646434574153757473720484758236068685564865752630788838876598939604455370396591625992139872954870508405373785804102034775721136536314049857862108951600200401109976479030872246614860817877734625126955651859682799635630510699480590627552914394365768612905218342099708769102574154335928549792785872118973801716631827524101568378835945221757235311242903552396812673666285177316013548339583179503875849581590528428682216191007194292227703047523405163741257035277564750688817729211629734014217144979830479592295336699337589435549322221999769812101928775294027663446024966667230308943574567670090109882548277752227665249334062464265294363261388756560974408503298718226732542210075536316103049112298564747286205888148601222563847772556336980184531227925920852525315132011763576635675940027142540295899830502674131311213293372897439344874231662031742958373359295832144797951979439385886039987571885413112032775193349899035822022747896863042410611285110299015363880885440199865930794457550031776061876982283472129023358945276085850453439647280297877288099258302755865535717559742738122214752246927676702981070498355132005409618340569681084816770986264680985992004286382321063825525946253857945446773967298587477999964185679531556437582440448551526098528192606317662147965907287462005452280092485136801426454772133778831265567251299252706111293263119680244338589596116183814947207155665249196477916778753219603754617652825708191524252108017113190546927525779942834952868886222760726463635574470538465985979006936321721075451432048966402869535643417610370523660786963589131817134432669898017509071727384030092226312372515020360947080807379676092426882003393913876743612792506918499223949996285698719238899127196275453631981127877640490097288177288328051697213278910161384427609179032006813756462966173442870607278430238211797777483026025569276432848198757632390835809738821424570560264837891005103359642757596517388373316353883271569046982597351486210135850928846439060431166641325191071741007373860676408448345725639053241155294951189025433646323073494790624861575286587682905320740973702066859003865647055336708909031053275514978727025944327685444362865125396698590702707916559463846687784265488342465936639722183699648371906289250857750252823621289084712187184659464656104972606482767638901877071128694757796788688631624576326236807129639063312677454321280770886030676959029698776327798575463351088270680782164643191454615354031162723446787403705031125531272413495367593478543448518790749903966855290224531305413778950518265767306043946216808754269679618350437717131464280429158909553757989102435549350328637078634684672540441138471864809267193214070223362983395364267194364523704544357294260374941929611777792053923010020505397849943707998448555354086740701620162435898392068868572517176897743217067275376162884390330112511413885284269983240790694058675988495372428489504946983335458865515551526893758562551745304302569709435882834395348237426563681837300266730508577882302593479319250853060047215789143682728308281252780732864777469434360407035643960239630847752276437361309739886312270636263260104230955765090905229735628290929262316881017001263847300933697511815211615469550108917107510382565446070433936996879896376499453312184943518023200609103179585312557122816583435414014872970214529462285572775672996206210793364943100372260227136579907166879069906261878767103211840536570480163830337759098906262270414858982135506230676682000007943918169847153659614887587988372467921926441252979570444082822228066451847299455069178163062588310199972231915961082644211453816701031463073098182128966631039369862081974021220320466731196178588466188671512124102336675802805969720533984771667761105426779055727421380243584065243713541396673817247136214430715787479849059197158917983242576541151516579921575188303590417365883936152456270754527433680384390009709626090364199441505359627964018390592447568156879337401707981259400728782668305758852524062165194527548304918323330815991273099393548701140354655748093836460855959614194482445637106489980316339196883551708243575604018509386729737277810806126366667304226965166274353912085840936731031169432943505238799239088254150954097360710980812906434184181786723865438859025168060137908787583479319308245008804450857798827215687515967460109700977324356527727074358740717890400631675873213511139610724186277352327134030531836454017437832477105523141545774387676141065585178485978706095319575747764569525588166432684169655114776981643845127243456962770619576353607112227196991329006406897638883570148433515887338483439216627651433437226540528661773686852159480768522053902402672626915281762671039884889730023331486945121051239837211095264356350457973945940309118697719840504388868314115533379746994763863399760624471105340792518613053074734180057664908326571908607618979450335729359318707006666152493109606274264714821930019991578982322895136549459482089791320979759551172776948806365584057320153988056184990709037815753704284875641880587267438032448792514908029236919738691547316325754823809950981668953356459103290980451779883884629371325579108020322504605185883457678733675675984353579912661683844923191982517031186332518418687340183575969426486124933673737675793167304993115975159863912613543190478385134706009629512386072499866229349052818659247794989059742350574433356933982392779894725093861389431049825881343775210838889103639708436611751087770546011622057135227927366227708872006458893555052982545019214252409389546599346644358618123911670155457616843461131338909599235324935106422329216552560182990590136318461454651935926522296342813151509160824687184167203762101095494766064354390927907809424595591892916300123874915904695802229484908972821113416565078590793781127770340929490328816102020771898512543994377233395922810440390590706281327051553882514823792398273015232601786656375587610478185277319879386363257682096137333743599186574533069130830578406306456152473401204981499263929151579334052533377534715013351433931959393225825146469193465651324560015016251676846031261468570167006858031435247455624782678109525403400192125775009131213137675988647813152523672118924139789607848979505962887947663759051428833198277392494707815362141202699402628329025847118064182621854116596393219571425088272988237506949288533514172661878697190310767319616291728316000894103721068987036978817383579773652188160155811818407834241831536282860360098784799493758563306720303698698489936635304232772875044134036905223743957297344814237800742521799746373349187551600864281231196063192141112424726498636670166477046390771014111229129829572884614344619177244448856812416027658116458238496537253563844968393892013410522892329409605375340723611544176468478644227166374668751894062051027489550184741752289089199619452111615233144922761757375576026036183383933482098535743334727812018265180421376410337134201012341754903055349798330398030927495775189971079482454809085259520976902054401256025280881121199938672034821254745259569713702145484579839782255956880794709516837556084413418423989360795587575941471993923934097557740220754914877492578644673375221615308702648297663953662108035450825409443601451734292825829573639353173852494211307015818634126907687101344925208219864927140250632746053812365167652193406950084532786883544749490517596958227551012046502085098462714121596303700760571780079807565474186798652390005218917721203640984286189743040461700728251416650787792886175607438136338076828318496811740703435931166857969778515169069274250104338678693540823987564188711475922220865846455823767446407626742740108882657387628596107042874442777276733485162504957644130669754961566771996393135627184727175367574250576394770538685409991599057477685287227419724507081600951926308996030592304287030288003732339012103266178233778157849312184949552538524331402466042201326842434520888117798302468703724725771257262303802024218204968955555207332655202724044221889023092250746402832529225239871010441132054946094903193502713910499108127047976702519955955717482489994134661738166304816149790756318854497102686921011055551133275916955460740618698098588837303484357428087424332546858701782499252839234209231732322472333024749266212502872633119605790693783341011306327822139428557055694936139566822285459980946372189482684490052885115449344688538224046029958281486946660395978716386454688435109706521011281579156479695541998705003297366302260459370612795461860758271809564377823771313977211634134663648712913776611890468053563254410697903343317997515769570951605682189802621175332859877206365156166416822833069805895456880624922249106734263772790510165128130257092381595187959485028900246812580256043895527098730736855955537125474085832605572848028696010321680904513005227263294301090111374037693198321187098685677936211870643299340374681893622864973620347942620183826410831201267992840555403364888338994913107781136066360243773707692629333476925013864688891182005161388199897595900358056571991947781002175314209703818742280951365858403721801598668199294287416843010249039146059386928878826184416299214532622795358040783424778203258579932451501835993276116005679040452665290559831394083097919292338594471220720155151168356828558743986177486029896094752749608719327648675877541754832457171058382312979106623240124171445821205352663808402271338948415715904003083768210332774652938808421587381749522644023506347222464642805414696508754208638554998439651102359281210300023410075623484132748925209289206307859035032421759619153051191145293651204730802137720240053953121595082036368079807402171832563583769636814418711140331212317932992976425911689822061154421776535007888959516803935714417615166289704179224384037040663340802005931106460074855579648303073559809898511055639491892448715756878750029348082028220293201955030115170842386443287965112430354571703842228135742313147753314826147884397575033600256948168049403001430563987525485801100190849008961813699214106564076636410379687028788074926424534690286881562498792215785074018962588606556099105434073156609329840684756202464089984251507454520743861449431394651373004102288664042945521948504133517593940289106510977118214697167120351854433031045062282480486102740347139643411385211725496948562118418052295200363322348250568655138641171711367948624875685748514041883866157947217964382424036621974348355224884766993687754883158145959365907898800658251108652504140861587112072495141117013488372999751961499954706934713964879608387346581020850127682526493684599765029797238804816365462105966775147144550705130343090123501930084149309761835004469944300701508331812443633698276231362580492125199273251010359324548632240440753676872186346571848305512465888715848794027168190067539496462694281013750691372683521713976771056887129638973771111206326528231252815635928310530323636046015591803557824503434418365326855316271600836171295033577023395998871256945114361047855903599419264030274450862667308005198284131151766983897301468940993856938050160687540666761981464160178387139523734179732965463406115400134327288414062607544359274461477725633235317856525101990036027230580160748924141433696078313245362055302089759899490124758338852584802137520799628930239237721570521352621477350100486807811304812842350438132304959818841364515777717934880574313983592270807426426600054661274594402303122839934133596812904829033321926325917649770261160716661966731119447661026355831859043779154547865559661886550599048563532149926258538677118671324705517002384715092364653043041239261483701103059796545006940067187587635758503816771479022524777405840934412538091150480366541520530220273019930838289495827254696443531313160617010985381094209026754484917455321357988005662234210455151817974267576008080448468191326798763802913777066492891657749991277646436873719393002879094835339626763422123390476357184606586776134196248942191213883789685666649994632322758276336217183791932001259964583137260352112503274010714723971957939836802323237452694038855454687424588512285214269541646879493258687437628026511647848268292365167235462018713455821265780564670085657083384557583153681780402135109172010760527488714519590975332105523572462704641024977295295799853006943159566172149180722751116591645400267755185447571601439784745227681488038672302785851998364029861364868125882164091728968810875776529610371855699888291830899487729062652740064043527771181136623012532954170856415398685036060272613194915316710113594103355026236446254573270844625837189297399392837875490487188385226379880387756447526391197696237593764121622741355391886833872822062039124812922426738677425312673428820469135632447875403144857123971370450191944481835878149591788594348582403399951746009110833479600815659755494993141751475772207960459938009144652622414225480106399840403440932251772573979914092619767395369221238979536800380318422224187709370055616008382191460890990702533514683483252547524882920177392932751547026670292467814075666980283740231546326413436813243924141559765400110653562710073863894477102813862451600294307089763365419730610604556595537488309479330092981783102001017506142074873731870443289882099239731714893276694945730787170131531221651503434100813527173692516528741864514790266048006333476735709910076583472319758968454766518800576353242978060723549844235019478818434683165581185879502997157907582307242284706375383287640919642083317564894136724411403496006615530311641047993768628990085055915768408211546531419554467635354271554605774621704927246032838423828254148172154803439514488738233371644668989488142230223882244864670435879116944545281580509957093703446709218938642999433775839678628569220538045319287407619549052687373958391274542099423949778737780500883141239834509184078823507783832127558230162207410187594100894249012119746669584633070063766803699867969164410632170015616280242012661595009278811355259895476144084302976860874916610796916196703822957144904715871468366288677154943959423967158843974845598782870621823924958084932249710841540292147152879198939388224292911172641849221798219240972004265942519371392446065144192613148809036790753160816908815119899630605157962849421638191040022956204912303691541772991775157940041285896855156556476122652452582286896712420124117401872866725067412024821242495348417112869482662284812108137579990811779720931540458311193533441454941126995981173001136366947946417038015650614311296360754922910827073766744397709638190827241674073406072235238315906224828812317214205749611216674740821497827152107622563577334938065605967987790065137887489487217247188491317482374107884114330844884922118154058415789165963549760158534798372057295404305777772313999689931114703710320309072227999250965803102725886755368909919612829193948610921366615639491489015649829165977336699816991341815619690941469821232911275887703149105178572400768803360231179385251365500054133763268183628232051217613352419285838030142957338817368799352161571005683062286142072775965834304396245586961299545837827368358128794561692752351783395836635582754567790418524991299825401723378585559531422338805807277350277065089362153185493371369318967590758555842216158821189573135573198597205949002900678711807080238561530972237662949093428836339273958438297426437791129848414666342669818216813485346402430195403925649535852261232457877643531522121218694544005289152882231764891303058515413298452177312960190800733436426637652479875027297169231694059744410017891037143643583080439168651528284303981772253543174392755837647677542735418956861092022941123690521119209408395751667359543452617544379365940245391818803988788333878649536346083748103783836827898098975993942891029077551724349075120716033933085806367021340194252754333712268000336187749116371889122250698824715123317123882881819699484514201946886034679863132736050764750167338195663496281188338556049073720179810044078620663547679938159895566105134765891543935441110786323129841176742043546481734476936706716365473805324227174628197263203074490300290479892656806480877600995734128789284740812781376967681656132962853834155184314514942868487194195024232286797108786658041989313351634473785249142494661208130128202304901110218388950763177058875456730806300630944874828461669973397847102041499679486623657778445356817330818802756482373491900305863718560481255606015071902712477446581198433077226009870811354198834059700462621464475190147210441910390437540347302893727020939017014206893068829210363394980389229053753417011404553315629331687080934778591236569508214055137858916229873142923254899778613126780589026686303753754256989761963078591110853731816621287439256516030927824395130513604840681091394236968559272664495579131086398029581988564367460662535853128969685294814803774981675137254116146161308318084431495057824336584208108725797820700599306852677400808698897287091104469086244161894112900418751514533747191954335675787620183708718550061915141994322728649650558975596586413505127542676612100997673638348818864194727811289453046690907777713822749559903475557590748251479418559290736539032745318756781235288120380066136910221796291119881061984012760492738350533056582115000245787010570304243412605170966742063204605900952201385058685654001755681740052933869364984355850176516322936314111658486409885425485002179156741992726735464958289262196263193124162809425184571955256560729343364019700573772619231090624702496788103720824125416993165154393656765617683457704290138229391554624250924455015383629385810966023789321419817516795303134100948591025963864611021546521600947231185946960342635561629523023020201575206947784331477648568946093313435344537566686895191697630761975670565906318811373682473570312985902727805491681871858004385533037213352299661405042580453442994123250742050488402601100157389497294170686316219687014225303627834543383118047988412976415200208285140632675768396214823644106012022319900340156875467720794157319828259125380707846729294199882425593345626965144013194723770350333031183462000520894059156565902033542212497921286241352761569039406556088909606202943718449175424292425071182409783670431788141431411556591650327938871149481108004805824923607321847067017322973398212961660017993668290009081806988982300848484614123024950468222730058881440945626887941704935162151311491787884057719392068226036734612319796261377239488017927387803063732695985133793802119741469649769504884267857861764700926010398271051670994848798851482993793259378826566230633989176895726250811244045443757675041990663439191702450283910961347082187658969095962700712790239860002829427746661782982567711387550547164830165213287692861386643992793742188353698479195832145853714964697725616241198282068095289178313376057057108479602722626883722584370425639223532056004225496910687145946880034865091332716841509198670332460842919479698042811374329073192826093216905091407753512093643761717765438444482905405186808749091239007558564325946034379551164212428194779630603739319371287482405481957218118426364313906060996843143038632427268777938866733518864551611852296501442920214253347474045275031900122297804920598446609973733838783113468487457880004610461257593675461050310644552350920104054551926867233379749208917518097480668719333157149374010276365325449599040589954489701762741037585548219825395088705424782337772862462051380152405807131374767190870364077731634938864250472728928115211019554210131465445177295209810027721168175834819481944006701390303182710721638313897745734072006623058889347526673355869807143348779906970921422260223409531438940753598556567839815306127609422658503605261955297499905132678134046781632651719596163310721518385279713493310366862175122340763265038399900675006794891504847836498367074200152596451515702385403223570508008437390583212728075642393392582329452513901934630626867340052820748404023926098856134668377999940386631174962029246694559981813711752640069048627235964942452781650168998418738354423116029510375712803744776196047284049710520745669182321608897420450213916696412745854651635860942696529775308385492887932040673022581304575203514462072260601267068651701357472797420544323083503515757982348829406626508308829972712420939168899236024988529522011290059426857346189620612591252300869452409245855298824878654862296360102201227808715452328303717732545940180634759119810278753348144833193557284776441597640308525520769669965924794657775868211091342161345484530704903790635194309796725336693380412913703215795126353310494587711689912601908657242421679133761319234296078585037200193158280739433867881400855357275599349656870164636945925892384947966986609755759992359919846839053592582808805973039077305999916444400020964036881204980290293888178273557983338989507514893920864245650748670700555252602592273515493378264392500907661273709741756469338291230972686397315709406353881374500968911279827921478844448735839476880555481594049678492970914372412345845319747538420309767354111888707903629429115116432120209534428697273050820313721514801962522740120335784751280779025907262134181214595507630732468965421269434227585811832178250555022108758288837006728062715797513442547643141649958708507580953681440538350092974514675172923931042997915055509629657207723932912775028793430162215198793705660370415381485296606156292085184814852752662788724453254108905873153531937387923177919858252766379975490124917108602422721558821347123816396912822748272704990168773731047090508145282901809466888058060083955830669531045589065369304734775148933416375765749797388930355479780985174138783840139630667980580681451073592387644242110302323157940752233794725845674094952128305906524584252949644912952290202926034474448153573307834139396777006418132791038567149282873203187991383633745604088645902328982354072454261295188342410442303085968119136935429879273915255630594281671783236183896900779983617609024071885028785935101224243148295820220236088860892276485231776333049154432156160509956703727600626815137983423279181576153176803738171546108939572245780425615772982912648410237869675654513477938257547655631317034386827916153547632392937247982090561946076642243869339964479478969778851545921155520081453082409642470590184735035477283615762937022469695642921420862426515858010603416919617558370504739137846785795848819378568947357829824153288732976667701009251328051158856396942249611504572541818763549397348684576818453976278448698763861394544005545409768316609808523336366123423217755732413779194951256341957173601857719567436083608891484910423230277297308286414977973831612029707923473837163055396156194003564945494153265747034144099011815379286518023650064868787398919103643652229942061065225131274653599690246149178765137203207954770379490907482238618732346301213898978321981118130099894944228815419094372548453930110497805274377974032322319076391894867384193939004324993389596930204563248343679032486224276101740671062670478213694796623854246977677998479550588604657430646100336228485186123245980736646103882718453713137624054036696385253630723614182838864863899170410730162080728597864607371448004275884919726549554122362286826920971432670722170777421961647876030468502945624556193677992320400091933697546172325860260293271172226558716744103378042508975327812372959889320324182062698418677403979851173218763484488697260095181981738672094567057476307139987351167390759643422993931378781241868436934151456026929285578469169628598199279450751940270544630976902672848012532443701592400587472878329802158741949710997132674254247761660916639086192100093989605962803849053606625680303917261348874177902351069991428684244537100385575748489978210411006272671272429788092207703745977773670191437411255093510091484627930653338641594167036097965815634441428740321981620823783242468109533129027234134811073012953374231321994194023787076374528304952358929040994338053018764592599938897603074380289356469698407068607946093354022469654551866813888346013672803769880587391156972082304134216128890902500138886365462671670536171138915050077721183508220351776665287439776729036421422735691427967688979830661972424959804654552032860712208946670558528519282331255023370276535810116485032601767474239783531560449185625241542338271615260325962915080106347762251769438152537839784040033583387238119679189942462383851372985752829469085206370840087129805939341125195075407085490178495289046351437501005909007419778561945508145557280590008758880221392452301372213757220078527920600837503868292141041227437539036156425489601652566632327074035010845075358260497403839710295407697840202242780660733044693717726241225759579903800711864997894338890317820224676441190168085952926628339677658574344865100576830030856070981995928468538843945591905724973367495219434750444530327804256763465581080299396836654085058593032277306481033214785639056060115854316986231528145540706731386994898144806730636342182734541898116216010225289260885154261929983436954800317806808297541237684767531513397487778514882007044912072612470768033498901365807274675428255770784546207613366202531367322601125926985576675350574512462492916147394368136883061574022623412085134106941488566064632787970951878406895823982012240682210733121533476824547985314785702921910842739884713354985842296257437072714443155208588984195937706835276027758466425326484100193044362195613453374861347550850501701970006510205575502044765048239513276625866217006442728335952051818434043562025564074629404104212085664361622730448340971632677017038845173526544935117589615885163881772285113320044370824457947709402483777626007588597694819534404501297148851249764407670287158222847531929843648704190501223648870899830016670791032407740558392910146264051201019312180734667244535670475832627232847755869267164326854194425105393436609232425064081484794166090125360893566700314242281294749094552485854463044662230063366380088406615567511696583701787526933946948482406204135731747693218269645628741281194129112507299967105416221425361464042109115246954016877767485535809165317290136501048025960878134638008354689688403682296885453901900757123124149525418195415959894956824682090014405659577796985480188672724958766877755060667514953761002043937733233252504565011342513417727501301582254527098682196969433259654169066574652691555236308386216196867554984979518881849676524190488357774961219587793393426068467133452417927894026764250215334693776693550114980323506620365182773116683123651164654235614273561292162402638781429162463727552358771146737091704170380476394641728460213472812287612938902093746318457985137267563104830552100245820627467748908725222763010773288122012344123284163620091629852461902648334526600539511409077718300183443749343758506439286708966078789922704596393415233878340282568643401551277255511147900398335311453970869142808323141048283142959937127851264049139586657428668872528448407376709567008896213747566592185325400256329662332584714580509870312057178395263159942190642773944408567675820042086708165129903789030864012523571312289506876479335413810147921031202829825390776138231775284914194777284521351057388597948015599505905934869608416071484995428585383055463649705168045269641980715086209872256983591494707587474155529967218564321089648392040381456491344216906157018373053211468815482000195855669669428582466198439924650976816958761215678751217906749278276021478775890002699511512651658745162265987847256862263127427759704652381413652091164133508897175992120991968794004036289628083520703594202524622572455319231785596378910014669050765581063910295441579318384279390915570309218108971596614709671320177387925938039207073456832962512741925549491980563983706420249467856403857327753047806326045274365415458445975392108090519540542492019613964479344322233908785892711669300062412554995323793392658001865768864496266233759224900550954127059444806743603225853898248418925844164768819338090531332091526009471558984439805217225084622991860338458442361445344778985284925388526994937870409187766957528291267646531851313865899154488020873809607169040276579091547763086581811793674785645125365242231951652103718879303949320567501481835202223850663490780175716356497837380215651307685442939058388118356084958783274422067422523633972334845235744401736143567178693843984327791190406002223764223017446847047760233287227131802069715809566597268976286631907715514732393978889354592546582689187757160891008558851278580977129129556174464805045183082299547798460282249284348096259933898056997914085377025097604234328571125413534751176809518716311064686435769120751109058537986902972076887047302417029631204080792200659733254088630775928131971651499289932946869825977378103609965634174218023405621419310355210183617201431225129575794947844242526354866119486498664046255863383477251364455742353076564616564844547974402788219341557887098108242404298915061254497511513870917025914104323039796187240438403713438174727301909430831600596772795939547507324250567300238651323590805466966189986462527213050564926338126190758624366595853620445346690799653950738641508102883733732953794178729938241556708403898940127341542314208152076061799420642292410814882751607809272804679215598095051389878024432371303252423484682553845929077618497871298485814286516856219482001642269089585316440438517198268354649056918528040352856615587607711868123760171256180973121859429935591452278854931290781673738929746265380600277847811784265904023333877977237403076422146988236849338779302487877046402494356655096816073904134366575615298780676364530376611830842021359083085714014687406516760632912967251987021135317183434001548049896988957448992148884700898977758858496789906245533573981585841167661780087247728863042637666159981731036042974623860260919286424005045516570182097666951486775681106298863051879159262418919538546026988540450360628964991019609419472946899755541659021333723146868913291774266343146746829194957226429863886163111374385421488163246806561912351810938098137291130966171469337794721932805740253376411224069954921048210375061007431852516363892708671710718604105205251021096751880224232900717895647150009305397768663585048833965999697956084370119106657071181022713581354720663938868442208299927728081844802601264451143948890548967502501046304273307909909075575079661299732345262922335301271300383286596434026484742852371846430723681332057196811698165002795690619243349182344793123439141664803952213045449371917175609809533090353458626417537005037898695115028194440317142006014701565762422416862938848362947312591877734291857625126924533504264656470726156464400938933864022849440434050906692207882833282038413370374232573511882984369230278364699526447500827651380996464576778850058438326257086995282877821851237929853126936918901730804818515713161456831612409002828538941205141745776383528893651980665288472022226707449132540370154962580728557661928704439906160213736798574233788031117282553077672100021385719442551363576711593148063760001847687720584438237746368698443150267086150239431653863774476755771762072421064617454632323183124864712305210382946281238046158076518581724741132816150840291485703024674076899479767360290274903316103172058976176583216621423727456378174419495358445909956177813984024833363021846434452280341794381076137284679355218108446145254144012183974440585581616610918827757998852742589212024746687459195626212039768079272156278342734016537451691256555435459852458389200978772239003029921192817044824286022894442853817557935005848520313570486439379617485319410266730996294670658543831053162179962124780015215801982710951798145287662281902538542698191689115677349101785114736527602686422261135324818329590405652567175562973706964112368175637259437673348693276036301058465658897291918189366397704716234644202275394778904873884377479488055584256640117729679746183997763881008099846037974586879174111266578722598358558054897162934984260571700374041318040037401659655781215455512005037348582786045994406747482686982851482397664934832894850397069673422028342566094803129220687926025684058034752508742447654529014865346069131045307507494988907285844354562605622260343288438429045881185461909529807173416382461709755789733505061473009029515344767099006875391758233548154937579474628050022830755678121780112319565440350132475252494050072927638835257583744073437394234123198681880636585438772081674751424874994303133875547075504640772193183642973201014582318416377413834079341658601914468223894769402903207570042673204081427966522338448096370708892729497594158287136316113712835395410052143033261173645167621236271205230206285836521133318784532537057920185512005645497867218009092277525735445816433220772474607299520078021184632402156628457583957709652218854156548096401831766920683066762500322906328023156429000216649631580239547847395293241837753380377646938716134375767447963287793395897028816644315071952502329469688321016428531771094934285268465991874480310092469155473459652921382826014327006888232759630197769367656818452586568860325456813373295291861249776866831535802637261137234694330151149913564321299127276441629618690732604637779748848644149802921247531564902036468978464183346500047271508235555143864611192554935597412684678682120301344473766203840935860021800393681878367811829356627347550401666119867437574867429315876763975606068793202426553774750223060725853732163453053059692874739977336295687359716695139683644408058968920475129548914499494752981190667146176188437681754960301367557701219415213084884472000252118679813274878165536766331557326549077364146398685693900013112997813683689787517491117282277045912452865743094364750513637324177736314475839223170915920491839272754924240534705774285271246937256923190934036692936137950552726602262855683207628456812114070504687881145730266454973364936767299558147931591256960786242993028089897975484104764387913042010612895225842088642496286153900748465696890214192111683395904862362968020681328808747182442916776063974592581821971149512143007074129332179707066884848992500291462360845488121234168703845401248303641509794437112337150732287192408862120467175637729148423047674841960808018422253618282541284900284404057209776205944164620476588014452984152228413591870892730278922025556643578613762634453459891475362775672611964756578396702960606231384914512662206061324939857614323695675680792823833395614401100754057683393528235159126044178845324159077012643131869967526815970010553300332045196969076862693155317825137660018280387171023180550411013361808283848020070522413250030789279825384351104284609068734063461068624958302017068739051710681131532311803822079644505045589308946985710182360834622318673347222050663039577144260317685736581041421246729325080622512278368667012694418822055907885930075369061905179397381679372140013699895233202101460746127397218001937950669786448795702391121984941219948595774798504720832049000985870663103824713805400491780194105596402359688358131637573962792675582952793291488222274904784018363897432997191139365885333672655531038964360415022881418043760742861803342703443488808951443163047104461885549298309324275621830647457419239827511577912259827572891082514496290099654622403253380750177814063599446560545466334841153339441689483006615442227891921824431369690069504106406690775368271876486999977323111194959479370631642902071803982722095950955825320233913606987335704863160983022967942924953845217404494394571565045043133642317733306110687927841498611136814469901375668903274821122684142524986631942418533941035428296660182364565780035079758008599229190948526838933302357348316565933819182744819704768762562236230102141004676332303547475424261982211957037095154344797608412578661592537580734131488219399740194598750323419002919890742417026880061689812781333187466802195095389881413659210273612814073693964963674145161728176104832805451566800420520529111991943556953178212270549459235753241879233900309845070540267506817726946612118083211529943187416691679430887055948309720683776895181715302560421021890868489933203539170502374358759489719826823200952641521167313143846425090567759788542793996129828547937763930110018515465408638569923617421913481408686705547692423217653273921660826133745949768503838666608837030044146569319444273779494508683916113462457618657605201623772503397156645105198974385629061584026433636684882930881608179770181114669413328048630929222445667832894993418219064602651904451192770662960622433140925754895646023726472127468591332843664398907345698521750783685909937981009313665092316975334570258459977688520134497239204037107495935047198380018911453919001821392785125420328299461732339930627479622129414785481110294626582445690477137885925767442467488367109119130271643887472761896953032151835202552371558123166947697187641020346498583472261802667176212458903684977052481992943859472218232211642758714203195727027351365270072524587293338288386806389518533526436057834643748088812019094162000322606694021479821357538591321311938665446634783898436073425853234522772319575804179364593922866990637597706814067722519983845067245441777002107159328853271789826604726820399274539990527173359181726644610615653979437792843076785760924028586223902564308203953245785597032385123067726676720731067115152209207035574350308001105043626878468945106336583638397726144290377620321814846976540213680695664887260603357409928238478137577556263171297841825509270043736054843044388166752518336885856966878942788401364147971063247327334824266290228127812825633717978850941141303383096514766576906544553988499053775583283802470964899885163093594453926794717987913900212177700095949515540399599802316756948849767741596124099104441495108432416346461473144345469464521496976482877486043245238951087197101909021755815000873838959028231440784049548221236628683782129563550732931327314543112863291829083029416992157273104586791046351641856882941572452245451273724332762663308088779458356086972206013844451250045575049923988697613513863557478368519453192026299917718614187367302544130330009972385620453873568799430861980819987521412144627274891545177944530090911278594595562568711702194885622272497954010811798899900466709283207823128747682406570695842808036037794160802616126628247445458040746972313798590300500554295353881819741769325541246723837214883903327367677052871344645861233162747979502009758173756786961956991200689998072708091227924174684925049059515868436551676507114079609578421478651825610864184775233379236017013514055391044956240795124429577563386621706669160945526609913370413633520063827254666021719930347574288948742664555142747617418512121859781955561102997469769873819761750293824432428821358234979226260176588167415543834344058756076856429822604077347830729858188005011517111439176465656716675196434835013719008308797373980550775751125597639054462927936937173594634788350973925479895013232461366116059689135416317799698290538117746155770131179515474334983392850555964801484392557167169388291756401741588009412811629361956790050211162145157484396985936437634658815284645784459527645860714955045101751795909552566458891180915974147033334523539128262951193320604006436433171803332375513251468536793471645890623663515100906065391283355867246198003318539020179781403084220005252446831980498955228863687461956223080445498660769257297009463624539613042939565535873861077236514603307021273422895263930663891322695218118642050937474081420564293211732504387411531472404148919095420591756325043796119614777164100748888367433338727554968513386403290621023463356347627169929699642149217854193306231314738916480732378565147373495362673200068277667955029825575026039107457012837979587746357438824311709534428014588313692959796150100630002215011844462121256249611618178673968866388971384414607602333177844311867532829538237223982325788418236325065175787016001089532583466132470499250575432783779458368481219942656078578712175808903253290240812486796849550877521630150070949190776385599682591668170563156117084520707121412897587850156719806011345124887898597796463776431865330704294743178863741943468732410466556859546447047642012721647190115523663874001462072253980841991553867345352674532373209335310991887244023254706811586726099060202530692502565652327356009480751298446525153416311891562918403751897376785779895340538045813007780541406463046346924481811414040600583365462586671402114371474933831855326135566820696836014084217599062489180121691268898957917380010937622102811206449774550484303163538186175880709158782757879684541795116714722844561800969766604270913973990957436162061643714896877945304067847714029558883395056788462225058255889543615632041336656324889953241281620915770867395840246724131237544081569841338300077794087349128828564723824347155169945727796002632543851805809300758104371206323039295411429307155848070076204889695537382057730900005159044969723806091967452316353679409011704694590117263234288966910417623972091142760876505129343309032620202903044115096744371694515531285292345193886524695748570223995638930852992981233464970059762349884417836458902255956901216785288865881896038395011331928118707400665742863223569978149257717354450021369177170364011604197092519200012276386385129870531907116338213182367844746581532937290514447475875163774297152076386290032202724346440499088682940533134085704020595627689748097036958974593134981644434856350580496129518572313376071085128864502745746281946714067963967005369196242602205945903453544525338299187389363019695601048532904065122424281121827305290585240509684373141033079558534541299502692235214019652371978818341698842094249520762522236734066912932780694672940933154522535083004568440892925460280679616994825044426535852435411116960149700634516840989338480415548552195614258450228482490706966230264449029351833049744989286951052442672368356138434893489884306555696473305057723880004424493476083485297333193523751568899146180266989272754619488458479537037038805973824255674838222472740715883540343976328593406834525417689653223563182112492775517446046801288381376633246297036704302470196468348218046019708894904683860471352444281428575334611496832885509801188118272294740162014794493856421542888915928888843398384445399606689941012091326373460587616816258437789528479114635543595721979875657331395571355402852036771545089801723043112468010947822225066332491638976809136689082225667888288321092232353624849954521348968151831710238334252108292959847514521756777083169703982696075814838820877772140620561778637568867126252441593062466421155586505355191888177610195627258690989571301240151385192885561581498384524737059036397056165788773649049728451272228908586597000935424775430653831529658954517179556466813101802173332733290399060944685196817798415523765502834558653607116782288335323169399766394091542538503710225546909911747655865524585566764327662397583395698610906119439903900541692482113820577311872718876060264950338656920707659175366670730604833901776488521385851140901862773712147634961802394574929497060398751967006067139321740318564735750220503776759408779277665966366541425618523506724335503139273961623018729158471880428071677683769021467749573087665597852280647289535723160962564588723944558130111799826989654961740210415727557269195135962106684846851269838011851722208931012380950248408742011895116872611752648753762872795030258774178055923891689135692899577426099915156276574763166783686059354416900538210677993557931289634988970402817650902354882212716567725791459711043243300106919048058808250114300663713886503579358202389859447016261045786697079955368952004260886463274550045530078516947795521675901725912305640048222937518199601470327428211511126501070755104095145762837251917810270090694793180532002245165286305858778443679485675466652680084194370986716814659627288705512345808669405366980094620990215726202879190581769173295245918339623042820927592261247667657650704345824823767181906761359226000925088170884938640777229992601401851235449790911068647001423810415424452127557945895426214799863340751607477013216495841955346115806367739597904789999233837297982507326381566997710066899307014786293141904864582038618949306510439906643921671351635572667440521421696052779813634034865410267711347096635938668991248798400509295280477951103185257815163970479286301450322518230585338236165944845937402200457501315650816833969850502540919981457632119418390335060829233353531063236583246726605610362336913650730373965759975141610282458032198418950796044986023239818454253620382799855688133517757051133725160285307570686929239941257356550746959166204858828114645085546657728544288537209949422274187938484460280133588396474587322742207338566178899025103468036590113842164456018623797832795414533911966544599684308185607972011133927289892671181130123288900308701316092220756516648144994141951067730463859398025988908249202953460430863490441984654938089742132901377546069539341961442720940723899844536200634347107657083265826786738478190967058000049636666718024673124134342417689726041266019477280646446570646793243279657758465694893028747702356955478699875126154519778205089903297136509792660345938906466402226084246906563903621844803762834895616141911646986704686132378992877326568360821918884880077615163392327941156760592272354774121866547071621089527336141162996505681149205695425289021990751978768994000693931667985317349467352038017150436075514103198923928699103928528574897612962850525295942269604673699497750233920183354114018175945945064123749775319553964716203275976347994650206358468252186144786566116553526439385192488789641675138603101526060017592139869554384115182175230208331822697250003320823424752796464920882617173544391879743821495377736793469836232852804182850897862461085153021713590142113751407490790472137350056540300641263038448971533196732319378238611178787752283164847067969558827910584733500976730026465773809403209212631587683821011550683428881890832606182304282316359795260706435722665256580447009551242904320678470517518255182870535787773200576317484635369303614243800754018566668991442157726576187249277348787091201583966883126260657159917811438575835507645258316574321435605362306271549716914485828902050998353693490028762972208607476164594454680529933918067221697868177328911326320045389500759186086074701615724390337161515540421746443549724224244985435063871556130066335281508352521456416614951578727222043760044500887095665014422874073526135905719766282700229477857276250888847396115446343348837722695930248902064976975995812671124037895596023209818758461611260368491834836188965639252855433180397365125328512314333564720081070507089261962027013054985583296475516164902840671156148613329040027325129907210113803671342686162833846132509447988397563570987073168485062136928223087983217171182815902749622884524096236964434983265742569796511776634972911656326917305924962616825193335313144334739187145286670229490479896338160054367803581108263168255327968442025854102198083208022613641849697860598137807120015334156006118170896833790397320436320601829497862764114795031589180389732053655410683682338416888608598184940731951033556957087490532746097272064861621890479807541437877330812097335250300234223490370432765391744043535539178797355705226937534128405762872872923714301945388349938574551112222938243083425067047478267367807389831647408814215904114532113446641757694805599703370272931982953353856290912635071589049360454404876621421703674135134049042250717244040758509433280171385531291475500196718525188509572646937785443249863700982778800021640387074727918822036126780188599173226212769554745861123989234459989797757834011381472798929266184978667494035444761715954913439036225675043021325977624767959453877702954403237348252339614958337838309135014386936742290388701650744815840574168430041296259180471158153143226779441459655618509340015263225936715304866113311476488867265335095381326312980769356198141057822927842541046670996897618193291822973449007228231415236606206188015002700454611732707021498658278476448889015347438506883711116891671162536172318910435120090276716100738715008226838124765477745735003532294249622150444180057950071467028802872833714954908954629607768201020522783880294887976827010574420597556318550750395514412787987671251419311125942354620222218245089014557463741018829474350424271528691865461647645722906450131989261185457876728107385106000497886952348938917918194700126808469206154763176886016068643877044385273501487175996631990175474500433136503767190577291402629616736202203729637785236429187307713109474104039255558460051340608788978266256639886692090089823020810683187278237641523231778461947477164469723081363942512277980080743012338643893698387602383729611803679260126051069730132128571302048384199846982170636331887043922868432119516848389997074571500259245386241901360888705556316330351565820963981167602677834044712788194461461192619978963304454970658002738660502946213935426853247484670256510831730864624373469041094883810459129635994050352098654151710341622620166851173191964808252909416914599953968985630294897058920581938791021957269580091540100255505669565420085817582950555277677252396081309688302487200594566502151406772786251929495049311688075379730065381584258359960735976637438005033140054395612679821585350980503860433657468015755426281394767980251894537538857436886333507524233997745596345813790609507742235368316622749945119074739737465379889663398177392727560280189426130459007416825333210467214021907792959587817592364729882933963778035191100175893873166064324823354889687326300073640830336014537520964065851543887129442767983599138644891091560687660501113771981449005472203827686711211323237153598547860098172672038654832989565688037137013227295414865318178090074304470990283702009107171472317503660914813037328072199091207419084248776263171587921738046413231716045105876728912518552459994183789885553968316303587328425993309698216068351590500462704274927682833273551292813225294439563841323640817946151294301608084766631853924437685447342882507348151202275176487630678561238063293855873017872662985608038503912267359629607956846781688635334374147467089749546901016847982281043827396383859718714185209949867967280205392592290824141774112576539074215676120551360153672043341602086416322532559828753989926833376124180538884154198308395087327684340040462142719682988783219856289228636628362317734995697392600953785434422751746093054347813867076643052307029837589585783109434877481519931451216944079689169208365739385463547024974826661228857451013238213338617603381666749293203628668888988483164396456623376449568618524466309312944726712129940961901466356941430259252748124538336176032096928167576220804184288770665614868333190109454031157093585511641844829916260177438858049763646851922678201765819927533399813140421498055168802621092974423564958475983528710436392813683635890777400088287617964168513367414936701361920622427783812797188726397465335485590962670354674291464751770349375438189047221446826669755330389926041281193959949240120681403882116208905291364417810749631302261373810601605147798248361211923531729765118301582259936871797844234173905510740377134806342950757866568648494510678832020690324633984399101912915500385066305448628810252931341982819624122797580875327575345527636070361933021296098314928018784648614799263097238425221915802465279394299958118059794319902796581897576135597276292878429511677639935804400472263906324662939385676999499949150842350417744842810666211980628141554183623023697112702618122295098398736858050696896921043663615425351230996193648163415975003096726204024093572185009158082882268609933814605993936215990441509528731575881509501822714334085753017875828721437963821858159788698421734670647758107374562668153898630309294325694548017532571713032629468754007560391288881836977706562307509275521586097505509769588347522032936619720021533671690673341260054825703760692788511326736648346917545149590052639043297406426578023527613531039671072173201137419713575849271542037032390177515100253251049786589396947470089063072113155130908897406412199014897885196049420992906541097024316314904311438056755304872635086184905374432290377367152099824693885656913183499200131025757846796371159411223527229282799863925293657559308126420153682031240328122065752423536238768949004206863398801436783658552935607633848906394183557192360092636307545966514237793339764785098100833787400723247482153669023734779979318861644338279144448581292909790208740517579504316627830429817762906341883438776682769061752658104837870245578753334833970431913131173718866270940559359417568833408242651204922785870721933182001332673923713545953518965996308563942330207646907332946876578495859594120631847331946353813327771359330187982498651308455179453944616622343704950124971825386705324045339184642289902010999943727300438714900733821128585913925022674697637423128773533303303275303426606580809781459063992591805307928628647139503016643204680755874477426313556692203072675684807015742860625544795137857277401539675499743429906632682656844228896250934054992202513138729370420451572934703998593218636648604656762598690306164734764652798614263622996963925021440385938002641523821229957477944209086068491147804775447001436709673336856688444519344116604369462523392173033603657385043466401654998500480695495644707741895143089588780755430393214930595250686646606726587647864296059101569743822969970071773634540558410038165433117131977666170049521842106263965187842739553868392536057422794884463899303105511344868940399859196786547938281079508028934045241193199738230290717092422575554076147753330469502537666724442183363518889750131619719216985634200687212985101351917781282320962662665642057488131950077162799204170020671186157852689011691478557314006631596380885980646159942781964284029506524746050988760688185893414838348528692018116819422086114654105640461387276672497349507069761880991216937831848282321962308108022516493097002996150480977898219963098542087919548033868640700058353796211245910136248609053128357183076435504747966892961335457615280739692767367379944146829322201863617269036519071071078737330246599724203352181839586192340767613886294116978165216572886993524559730370917873388089054257889715412337298147336439063032132892335961100936110976074498242855013720433361706338502440362375031024651902596164222279075610859833209479106569412880334813338460643536676597375897185815866376028356182333083607299419698190450941235509774790834808851383392695224510602328586999195364428975410088400309843513733485097661793484310063303196824569551153677525835997925694503373791520781401919017928060577334393269124050620044141652500851511810025683427799138922862609951959493527637572930872125138239340154296025464980652090691896715219124828902970243815476512355798660393394948570198220039368623208375542228106191330318298344533187272557743101477328145177892389550546811231660000026064690100228432278606557241052228932498149461609442035729260731210849376079134166717321728463734119229467001671044265014752400002800378158657507363287374396264500603415544143689503311008231495854748828456506747829919804187260886453338657429316819317512789749219299655064350186133989921089596409669543769716022279108415076220095073050358418354286636474355608631248727088462454761137088338434506100711071932385469877436575810954729587061555302976739191407005041402124918551654813660463376247715904577060526094172215391393914328656674282835128269401721035400597151265424543792147749544326561433724065075277562049022045023501912733803060360283901800587052257029288006593600322052805970875499562795052348832609462212146934664740400608805230787741400425614083246473524962741358204167525702300630402917163325301772639065446035167316455390866824723464340666067819412817765519779902901722514095846485933007214095417526301807903329199012566774764416347909645929879891938166185611616422321832887611092356748700909837938528020032090772862035804945549370387973239674426522842778978008853675991708328723271258411904011587263184959813276070892865480368053871390942910487278929291808380865686115475289381471195010906463339435955357778709415030135122167061732668891360479124210196749376182843618570944780376935578137387324437329000673235174415223478724095473610664310033990979047106180565905485226941336847302861384549679296836638782236162208914846954031792392906951111278173448821070195465391930274363926789357318380355096833788527733182174451881196187584881705869728657496789720684820002982801188072052981598200952275149586051070127601279811287346918656684555823006786407195040872006476531594576657520111543581146452812946873484838020069336906450690626689045278515077898634327071000938910688121031186025032748278387816201048193557582472596541915268950398621431079885397282468651390017757350591414142360857546823841331969454510951649157505967055794401485930874882394719646973576152069732731532058886155303195033856916392265313280726880606153882022651202268147170387302237221075768119231356883094862095767546425532943613378222416347549774182735202041218200212294623863162048673003531406989635150285154181598399564976053738929039931823371003425066782096496974221532435985493625383979544734425380564700127359617958754026486537292540879731371233270814306584642613614092519128025797682836920410738715763798805315998237852784247091222102505754881945485860030858659441584480475221037214537666246357124573790933005917671509785951871214148131107811098215660066725188532091552583482429587454396446939409855419074794607261169856222997572079978236836971595589420769891211513711889980032721475519470925455435062405704610352494005988193059111438975206691394909928669080411039220788053885735420913433667530857397426174115735902906976155228991008097113177170959075681564214084203269849959957525421887505541628303382405206799393832065318741761221636004442770701919972313089885729506151929434921768624005468288354334603780753684500432117344653331634686919960310866460151290052442728105444992523006622738023971351407913313665479374451888745384009771517948066193379445612722524862853162582761166482389662460423341574949466355993015926242840277858750601392721839697135293300745480059405468973341107781798407681268776872826741355282200839484652083692013657413495771691111645624328830462489414906576094706956915969171343371717905284960597948291731098884531154468958782912158999306116910044045615096653158957823793817758133373341489655751402694756874293873170186295470860321646539783491724485952858760613890103696056797804884324394393664022475917630642305617905085530493289994690665798457860666296560007887568111688726791839376754584585165920009559208927071314667338775779025054923025281010585689817160279854263508553217101888762257739311929052808564397505940809541923654817530824056544615828267876427578910923875493058916870422824169575842552287651976834931966255742623627431693882318193981380449302393043230397153621364570547010840655435406597637485805803024097681971519856610527178760349523441433249147322024581636200112894854939470736889008761299074362956256014484288189153441617125331702949698238172939660330207517718401597415513425861124572448874387591497681109444233692637215034456712906579432056628490327836574290951825045864163676494511963765838496466834088511805440716496771909920581306770627974543212042901447310064085880471285528502223309350887090800257490642178892928660944511398558517331119166929148977422533220045765915631211659087908048069116611498643986450651616607068637725383458830619203437787913291457593318722817617455966813251834059143237429164817113989589586861619777041723330676857378758404415671413103134397461147730069746538575206608672564562400156193133636986392155251067979258052118319198333950155504710923557027557338457995204738898343633613726041549660506386384906632415376351932417576954438850367397855531132833771586972613416054552217030929096211864418092661187181194839090351914915448462375421236232507951853778942922683177681066515483538407515375495747936321039557862810473742327171737970591633885740704455949316332717101490111135110122206504573205302634143074963418102044500862517127594541949568808508728195326545107146951557273185234588484671602111361918015615874217237410185544663430495028885896088629145281779049059641583341142914814761794644427909629653850557944273156539752077425458373952861630108266998185673466946445829802463824919113030940180646518272042045849515359247279306240673556256746057606133081789354928511162652792848034321504394873049892802891341776929864856188175172568023803426768169734239545916375138851389675638159037471346835900287874130610382067118003935075478370930753066138109436934499677123155461571774084935320807872213364364238982654962926242431148898490129140259428242190073002567338390262039635146405041257853028654459996368227447089490282182286437444726921616911191678701314133937576719967886384715976489797318349805372580532964620270353308148148912513099833937027007335332522980221605426014855336486147819342426653520063486003980273781565447115158629122412668689018672899842959932617450652372191232648531121149235873505773859791248960878265576923911798312281956165050588738744098187389184076048779619071535363704233206497988333806884004416606869529308942263337113584432666360112112495647014729982996741602606215051772149622489929806783511573123788922542221625420592717704352494918641586239661577571095953862343218620417404021188701262126013990013821695854661379915176050269391757582372271025195874370577962985974094242914035013625499005872031081988059891656719049666961496905285785378403465262149946301375196682757893023149193466063948164509073704410226526319957992666558033246149809549172230515704744266722121571583853171993459372559416106159057618320001438889954894779259560809867380958237473046173758648614002572960786544464896423393972162508318868219139896535170617896484705807934018323110194973984101639784605581492242570979254429967563369803284010366899935147259649927163792513853451579155902109426783169657354235787011309777649973110333720311299225561199287565151122127501245027824486872054797216653080968174025028274707542469705426475008890046493182332674898567015542042311629716555392854874246305513786242760491541856580730398838637340585287304804238421745964970943691860043722151557496845829103761344444965651167660337520930688572977287678275499100550032174880351643929045461591177975681894214348517437750713476495088009714394227314413939801695433334258195508011706447029276705276914899740894396466038066760323429083740157235166277569664067756432110493810201405472247136686326018651581223041039498645231887206863984227888050378888013805398412367582827217690098007991556487963560893282740745170545515504724670281464523555482638121442994451779741024255n);
