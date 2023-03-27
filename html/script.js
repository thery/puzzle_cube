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
  // The position is (0,1), we need to symmetry to get (1, 0)
  let sym = (xi == 0) && (xj == 1);
  if (sym) {
    xi = 1;
    xj = 0;
    for (let j = 0; j < 4; j++) {
      for (let i = j; i < 4; i++) {
        kb = boardPos[i][j];
        boardPos[i][j] = boardPos[j][i];
        boardPos[j][i] = kb;
      }
    }
    kb = cubePos[1];
    cubePos[1] = cubePos[3];
    cubePos[3] = kb;
    kb = cubePos[4];
    cubePos[4] = cubePos[2];
    cubePos[2] = kb; 
  }
  // The position is in the lower part of the board, we need to do a 180 degre
  if (debug) {
    console.log("swap=" + swap);
    console.log("turn=" + turn);
    console.log("sym=" + sym);
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
  let code = ((xj == 1) ? 2 :  xi) + 3 * getCode(0, 6);
  let val = Number((table >> (2n * BigInt(code))) %4n);
  if (debug) {
    console.log("initial val = " + val);
  }
  if (sym) {
    val = 3 - val;
  }
  if (debug) {
    console.log("sym val = " + val);
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
    // The position is (0,1), we need to symmetry to get (1, 0)
    let sym = (xi == 0) && (xj == 1);
    if (sym) {
      xi = 1;
      xj = 0;
      for (let j = 0; j < 4; j++) {
        for (let i = j; i < 4; i++) {
          kb = boardPos[i][j];
          boardPos[i][j] = boardPos[j][i];
          boardPos[j][i] = kb;
        }
      }
      kb = cubePos[1];
      cubePos[1] = cubePos[3];
      cubePos[3] = kb;
      kb = cubePos[4];
      cubePos[4] = cubePos[2];
      cubePos[2] = kb; 
    }
    if (debug) {
      console.log("swap=" + swap);
      console.log("turn=" + turn);
      console.log("sym=" + sym);
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
    let code = ((xj == 1) ? 2 : xi) + 3 * getCode(0, 6);
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
var rx = 5 * 1 / 100;
var rr = 5 * Math.PI / 200;

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

const table = BigInt(
12245908618043163065369333578235940221741637473834052616348448852178318481367566753132770989713907976184487529245778770629145741310507793049868019483526545409762277764796203030019736858745732618887283337911752059393646453542105100698751681444721228772725875057767139928787514314276336758093575549358812978028076000315315445023688278860171782282984807929422749929047848452678635759158324079423688871982560054519726678972627047921730317007715730434766614171106634482020944875386609007097094620164442866143943931389204241535229728599347677930761222385952601600944389013923214299971621043476371503840686098791716860457678408613402817750718354767305293398949529432636590291765944855742642459066981969548851205001403682763855924616195786906562375183227701152132416616495645288339420761014891615331342865556438884900712474135430671633567041244261648828522687783823861986992290924481177158547352766960642044181134160188984985435074135195901492754428175663558377616144586327421856432796451925090744867723542306482625147176937380893016707836140760343070545116580687626045790445062047135815236353561435536431488715196231457804663201387743106516901560376370014819816367454948240746288473593252735093340776378728521057299701824603342617849417226539695394165064339141993565574872038311996715884876434883647738372614861572367329948274864026679387057684993166896237119914048485124055540800485437503973677952222131137403262068967482676080492855039333312787477738849039556809938119800642937406450391347789168303752722769572904732687733743254524140877043315329777279469706221051648782262106513391150093968223557261131782287338110388244533441369025591869240579349257446746628266783434409967831410573093709014274495548448065289799600970919007454486069754330039900183705847177901527268346752969465015911758945396931069411516353324974365017549531936172400116544092044129368225935593639200273639464402074341061646811709585702371288532648990091786081396431671509364322620342977509397444657142670802098418744953941246949603475363346425020086116164469502916751616514848272351870279922622238693682782099995497046690193121828992425766904421480711326547730669036505692787037860975463191995304565433537104413095070576922158664164742254056011792577401196495601392717759789905196590304412601477005291802235779103879863638693459712656408398674547213404650658661634273276497911809670548117023341436363188578342000986193270040263707709439579382507083701252098472926231759320539391161115417836765639738264482831568226735972600823121436620626911026492701056469341916986340025955176726552439319964730363578468304600942920437920479491339936554623421145923020947919823812232136888148859907617246226663642551228944091620860274885312051967391273067649646235461913741732022610185570781423933971337800637152399884710177513149349776490940607461535815653471649136449296935308324730293428303976248112654150659211639791761627060362775098223112166913466740147172366216830499573140566017131610363134147763765889175863817424993673696606739584593324729253874089693935081367509811356790938360436089636900318195148347825585352423917118675631975773935504393500220795868037758561281667679383209781634149569248417436371444296308828444328617117719169527714474786226878485868155408097349683457198144580817332017872281373364543018784336914753243979458056941249522388499476584872214970095231449749480512456481704712887180810997135064093299084794142554966305167921672323201884314688703423417067834154516217590541737436758755520640030048243165942890529155419764974150090040247198609950769574234108723382306777245624364518867738775919785666985679458596156681587874257567619594882603669412774787646487236556735603015335919008591732081498200310973907162944326239286888347676934843589237767857229339195347947791582609219610410847400900335659052090912224939289289102423519353056492959406531202983003834294930180987625122671695079746841680677071503340789226486200521872842335103423330448839869275697728257901306545314062675589716977468752256005454949358822407453599845973436156158296321410662878978759519363809746000113072398162994539028393588981599504787968589936334662917833414292020282855206609616729062849020228624006648639355350120278534761418542560295310939072191314335828363811142511897238406890113675945516812802176225242424981446070315549637366866671319873167954230354628960728861776367761023860432559934885799058785965552504567893673027161319520609397627080733870664129076955667051183604752821843114408013869884040241360571597420869113221805502954410548436530654111433141392883185507708936056354289783432121587569253961808868205236270978259556235175306715024436007797217077849839288491560016449662569082672610505844758008208163025046616968403825122945898732049171067308455780070654442328205132882030017014097465922587822266750537438105674129179130693924032735022007498463517920165099038523388187222625419317675017484194364411130495786137539243750878091693861667309809040608983681627746365051092098455125564154445109354533433488112544983517516883774054555258909880623849865422465945881214836903720649402548430535672215291845148378507302067849535151934386791591204901251310229283801789942322659215470015169156210782002897351472072567179201940027208709603049317426100669062279300761387273430000846653840118391697389430767378352735632139832018351698178969950323817974878028289850971071946267154209131856301963596522660234984716429638059124260537195423918866883636976887175797597653520597330710599808295696190458527828648492618826232751321512707315922922060443629738821095170786733770566293788280210736504399803742414477353377277414206267979261507262230195987480146306197815160914161002654167176427661437538242823407768560047161836714618075711270629357889102191098814818951122976428264737643765723746185206333839609391250595260264761755180117462083200521211805325267226539816275251204353399623585865520397287221883228271449163872967606063787981818836204987785399635854251524487208781216304484960278982914009367895847793568434940536714127360913089534018308352662977201079941112401604118087880724497687624406317904545927074428873905603008438250379670172669457557837446053968061015494373353156442026574405635056010611630572197898916106477615166102747820785277781554490064552719334512823470229651807059536551404544582852604397210222156022575063813619567124734987778202542982859682320605243879691908084835682890710970989471807399633845888137536165216285260195973581046217873295768149784209698967990648732456376759516049773956116653540039696518255230466248735498904118261952363458816447514092813731745043928899601000903136932836900439132899733835170922877432459909850050908295797622139093673043557819206057994345597409831666684103422315365038774463008746678683666598588313400043750844870207769222373776069837691227658724677950726380710306152333058570192663377425852393671657218022077943035077340347350272438220471093766943109915947190463263090646080462611351901298055621607067837220188120950414454220784935290647837401326694532286526434913680841265377094022887278122090393053622012703832130459134882659225914816500561857867156755937359262210352025790951014052903045547630062582429570924844207841783837775836704032855877280451542550418903306109874473209962141328087419317857692089076033072018321882556079250624072298263344172440336214374105012965578431446430706154340758324640619538678547335262379076279468793273563015761473177771978848744122922466132332797242431164104441381642138487371400049232988384564789375537607663086218918385593028935418393987962460922367461593376570178152655942920088945380310688160285669628070914713209393996213068146603195437612760937165143108006734164992443897677201668463056287850149709936989489566569151334370052726105356351323394097560903621993792131770936171839571665191839452929896358567583956793119620570435133470193897554408670250284831162758143764744466705879535335016940125398832190920759616341877982910436508362550863752861479504424450806792779898074064724870159022031289008091379014526705225822379971276572403291853159734523323187364039779183624847920661011609953106881581672267660463449354519052946703260194926797735372670309808239309789825607066909566543526858562750936171656911595340040435545899267151591316211661253923867603937248922397787688069472003032725579209569813210973681393633077996359894665636301868950837002721296195608535512093392872367700738034567735324768121907172502224190149875487672685868445778742988633722582697925158457852126131023833877940805698200390022361217026418998104159401337791965710324307715158945094413012319761134237541107306731113570087637041460964087148753369786170140329372184977102911118750033964525344614093747485695493268411062332489173730630283911696140439958776174007681281752900910872570677598900541690563307038116298229892026303965829387799116373599096180264076997892110146003404311540342039208045815557340186636081863659523761310877828734203302963571076412931078063707668026807876724680523343979469931420148468939217066460480501355844030949657162077183795024470691975846784528067844835703505226925386800731108588128400738042847804736599291152928922190253178098624507837493411990025474435610419132672247746824075037876987504930866324616238280059850035520405619178414705240257191650545946938467697509539398937381066899319858181962626787648267947572123700572939606267499186489828710911940993828272606374664448929676643094452441500032767830629483453939560595653234978068639584127223440730291060626939383965227968608960657715993033359054135867035992999827954625525189990818754047510031074377924626189918457453083785041649724219049624450335710837767139362871924565367712989177594259195793138546361795409774800128911173091384627352965046322008040721749486395741519254824079032963677264962771236577115263337614167845902152694760239286453868266590229433347356086602830092473132978830324531797052059437506469692182371468103033891089986731061197042627032401836739006474990681379797751617475642545204098649601512366681829987356820543360101289555766644444096652902618267338825421864196122505386271244276558124633541966141332050369828011729784045538445460251478040748452805731028633349810754030336441228565720662761171794971185498252461374125861393622702400891251472557645967677058266485680132817326589064072106892479930667812242343731358739240206730998135158704385711947346384956924728592519424411878086286191207439562799316564838045043053800608365402664634512615508426759749232989680453610516239761446851102197907884852178890907979569093647179447287478048704936268586576706079032131443054105121781087401123096299149938266572245998885511314935838032471998313835078412956105628060345445275393493518547337368267405199998319351787542686628704116670890368785057325940500026545808842732050713363704704125300358044547043724896319012826269202061536904260372321494164109125149411602035746773935159667723835553530058327096425128707514145870083713816294840700931851815069160673065755411810253142568757451998392964733452636572639357446904621577694148862310185407596132364893679723807681883984853560821388278535886826380747196614246645941769350482348010526047289419829773593019783356539294975352501585586914024879493655154755511028398714906327217439816856350770424150985455182662663801323675285124420350518068089885837352994131710748906295854148622340686211655361434820973856377976413238146269824014955465117232619140656100010152227426932335283172085047078726282789680376810865192108410543582664145450520162715151030930302466729732142181250584480123225207153661885909263862840635302944871259045901461960900821595092251781100395378617512661863811068840649198373328109370108410651687229249202939325794635199487950613263411202630602314252732059028600018040198802568607248342697503718596219257184271483654162691547859916632086276754866404364596903219591715422678882149233068363876954341212276181164785311426311110112822027727414378276144472077089193211040182932818273107480906800803118260340765363830365611084065815368796619399839264543910030824909362192437459612966119124849756374069912282088807465044195622696045933666865358559832307403112494827897298470444346413589498468564037881929928417026855007441411182547738578686331503705785310110729867555187772733745538545957236327676104145276919198636443298582034205649237185751044974155964582484019481165850443339706456642510607817254188141683068988839463441024612236936120180898563527960852739974805796009935498313802339878179462282082843151300613903502873195495128604976308031442540123306118589726590635914075350610140811256519466131406072027023953845414623434578556586103175183445522375426094028423075078790447715980467235674181191840976308397215142560898667040621482921437364350609597714923434182474185464059987008805151350104445037993605914937456082231027350554607208817762235030416250671196360566707666114087196434535173450817786344224205670709305876593346788941698253103036242043550026892623537636338386340511021244082142824877449268360459367840833264857438196024339676494218016459530770620135928415448534390799238461162393621113650012245026505618706228387465889647512132818895527304819561685491798148054376972398089865763512421413577176168588017117437420880194956896070355093146860943588228293120764557748524571206053759333546663603579673268325455068560642850252522948734259199622284821310435035641382641878937845061537286717973136201992299074750697307223122116554224753574780049710324225288030146717502117961514599720722084309487061921994324984587742072938509177714041807551195278346119469020458355284631013038667487716271982360009215307632402862878859827264285759129530509169088652075437742455612463872493542183643499696630176572062908447655652424346473747344294024657983287676840563023610348203877654302980951075145983664379953018801452136158902120514583712740556146902270084281613782469633928266232127762735239520118348764663805869458343898232090025351301018227170907569762870946211844444774969809739262394953017029653107496660428532927447868548308259022390880176567320033697904955049711132137993529667816203786951578585188840316792770280298854764081022453732635626575616652383054277587140103287617748136581247064084661288835092064650840873759806811268821818196407356743593813869498300840942738439659568651442153882991929548847336655959301105246776609858012502769758513448219365886085204368359125538123691942315202389468436523000633428634244780737422789386102164207885704896764354338788551358061062598143687073427857721076961932608083797191587927150824983308605454306222176925138990497689837421332320526000840312710718822092229931283520475027544979766198645368043180855525782580319552550524662704436279849617670712430857569364345232183574053509554372671020898220438021188638921454293504247790700714267686418467394136763045979548425162361656510529087661039755189125046165491281927724911712040369326867034809022171905939647728148294309288574890646619106939182411422774189595876268986144958432925452530593047206658370419586743876304893916316060522895537817365389788022334953282003756470967712053827444778945469369083314376319692121609722279704502545108042113595227978291577404101323781149487795459140887313958892622036410633977923949091892281485278651982681803107293014101569487913523755652071827398190921519654565588259155330560099452315299907693742946970424264749832276037465997550119959431408365517941535858648203309458814334010490850351937925951141349409297104952246620348613498601606859950512392753034218695634276538406310905382737261735646963502591236860052159991400225682704915163528438978902918712498481900099425683647623401578262369694972534424218700790935528463101966326809409450321006529767429211410351615835589017497966010444960335294365097079415251644112802031513442874753923677478762951061230379404694477599565937628164355966578167281064208357144644632668019490500940642328573467242549710632025465391100900742196512980419467113699845142635994146586082918438486847316894265276441160738147746672741290814432694900736344389643708019489026077848086354301765141822434615524645097469412219305572524434049509488231185468505902396536586800896450014057243135941181158991732697588819661814533731582702201831244443289378010180594739753541470282385250930122895722971755208972617695637159040865998336734896124564496516020566957874829189215842045865355650421605652882156057324268137748417268141583079098678829510908966309789670794984525011999408341022184582771295966490352769100668342293909190799141372489893834668210277130991839463947684095893261536735427993187823278189895655720708760305397428386500990473976571092984934558341575053807890234212074988493727871032579768402478082481115093121410443581584692724253880534065533157020511557303253902919304519616421398575865221488394178724588008185213059826639118000489526722113356738003007412839865100438155904253511251739823957750981468686489227672855035444851240401874692951987557837799153180356743110376810229570731088579415414020222304415137109236919991800588621244822171707237671886599948980979793211750626525498152520454097288800000845162689225934078997174088764888368728620901672527581569255768089835396768157793817814015604758167643396695142959161566277474438263038832581945562425672394434910174831053583019047297872591981761235868780644837580554560861701309018360872617694772364926507906048407515596739943536643748964966618717008509301873093767185020701679590882779946075683354858113008728103127256573580506458583722590901164457546580762770987246636602773942930535569540798948121937594153878000099604435078031878538384843716104147018381030886673305547069869805626283649401332907786793232223022759533701827156165142787113230075116968329513550126599006004361716166850684832790769598217704948202550107902956195868382927949395926335445270984335721691907547853470960445370673943089128258073483623847362530166289743038479050792442949528068467005298515928529859687107887048394609486921476819553936944164436760988499929370471769911128879086490906535253490947598629879052380730477330682342875105494912344116396837640191929669470522642527902141108026863423690537782601472838655850200160983718890275153334907376860588970151191690375298225931972604918621978978886017904780377556921132991829857085883117290086493537495463532139964840847031158425125437680762483832512605233611905075688595370906378204719241204938210427269084312838218367525132304990969493536388527010303751239578159085824502884506476423495733985722429845484962698807873066947458894403878837736975695315509177178292758112897219665682646132834083375836087953450357620069332383099878119609794896211615890445075632223013857729714114366895342902020290510202468790549638033592263853561888364220754790028236651994989494175228742122524423716540563188280528022426370415380987740302604582961842037813967791764354266156159998458853075208594042841551847714210431653793202078075651150918504038015000801856455402016019600707867131183374191796529155812347323522630108443033808399543262134319665040042166822276281803783234038034570689802213045946875908129169802202806528883533453063010620734961259846962757027448642513460687354861070840806974174938147671996558076239444928082968830179940372747844124763489366789973845343868039773131164603878132238005666585489784124115178616627763721129535263953319675322049085131392461870941587795685626323859739282290687952197255566453019505455745266867435923919448300842601320011670922483963656783718037136871784354830682380771630954637476659486879344874573712121738076319900464381611988760876785534679861867953432633452531725511309914408100901497032808119483611116931481114827805902122396618777685972357369727089110567775762365136500197133925019926048259361557448464765948835072482009389577129559639652092081679166725007335186110878237291230515935120339805370178025707157165400619860420126599140816608541143283751209392242892354957165386386591695301734534837083656421198467584645415055768017141425946470476908212960092489976510281133216351575896903266792358594365794700073260288887474487584843497952264159793333648643729552200566096298979801067671656627586320967913706482990859071025294647671867391704182733972544933431810436663123141893604603608391700444704435964901508882836216491823269169989616111536808007496394099564615077443096789145260378277588345166926206872250386182984816647100360325904768130236069773139178793299005999445636934498360080839581585691702806719422562435787523927631960838275291933718801223790008135920230673683365292204209884886229688556936221909999838291988034357529479466367278221915849884026730544731028218623481245011024361384085321100820630479468608088880321014118819584354848908859239340141124278283947863256469266506628533390352302947798218618836080213230663530140320477138162159905641411547786075849229535265648016223643562469122075358615729564231648067181393227766186706669794882552771062062323524428546981261473049775824502379908899817972565236523437879598370986326952926194104559135326520997875365655864844023319813004110603077127013785370724437684944973849708415063197889477315108936933350422122364426998153863208268435141099112525979951572083072566073533989651004103970689437911560210448721122676031186789064119272567081469255081640129393825542779643827709508625500770064808166418984119709206048515299534600956659877769248828444079603886928461149401413873280451425876904232892919783486003072009119163111247937495935795254080611968029916770269205473066040162097398372501208172029448354660876447139265069447449798418108856428457291078723049398355288972851805245434676150721675892304996902196118939732681196506535099058044325709512000277199638110040854831822962790875197487176344446890946916306968102121255285004215894578077057271595155764225685917883293283759269958120194907503488174720096810320972125132689300841885175364663547806762596488248727684209065879214277769108772956114423210045369481993324322261938459702323879119087183861009685821732057096564539849007938325200791716319424187584764967081765476215730669477419787023187698210284255601065049761821068180782012448227134485614241285646511325323370738587132816284810184928113074338275408790698014049235448265136899081806591608250542774781823467847331627591105479934511279237883272060290239925808621071207507289599078773930049926777356119247776245364734003752484361879477331592858880966659689204745521559648892868238160663251313875535055106814955658673077586134746484897888031185641765531256061147397843587659381791950376186115168626877360299654216313206650821354323964510223162280796284008862662030271204337511076362223021332303000081942520506934747458549290209163555897993107999375804678832514447641873604593638288515665801902903364558443574169001833851886704309664442939869697408207875491734971543562203306102257011377840189928071718511753382486253501020951004621462581776586067708808236504235240072678386129374821708673267193556449548706121901634975701971067151218836834685065195639783439536257643376813704172715622617350521741802051360271624346913402953997584995774922626129229984601299721136122698943839112261063444094094060484814142160422288021441385141215113979896689412279986416275744662599068146057638554917302648519169715921528141318995303433119894918573439227811086004802771434537904024702953000150958271948918044767565473006236270116611984954638668615754340258687711638464822305578059300856832263598413472884760259295768360336966099382569996286464887179464010535125352768930938547300217317744816043310555782530321208630723176636823372535046358536329147649996642963231007495832541040042895641531833426583525622283269112652640528960828004902382227820551943818101830061104542293388866451701489773201708855029131138589702623767364949316958850687863736382672896791362853309427576122703240602424345825999604567259090260682889230639579806622241298643921787384172708894705600641694614100524401306434720073219991603774777445133470713583657518872741155478985815042900001634336748209516449792967622443252003924062769663987770691717362995020374791728210108670271078563024345567291896103274914829722216555915613865493197381298744982279593112806334197267901919301199757246109907851057866193396356420257620645597949880526784293785620229994621450064888141481379878324002688461079600587907966168067615712770861129410763555511151069239146201883687691773708354777402508410081644461291853935495194844438646010584131969762419676549430783076295828378821190174037688259362810690085930368998481476479354724586307575872034883466613961651321049398464030105327153650356719496905654749842497021945951472496090300699611969269356864506284237767764797453704249398215780432132485432529042321179470023176844443152556302741192387928343018394736107754621647789869699965876828872290713339559499440860595690241672644243521195381992408151894455464363190775541249277831967496825854134402886407725024495637173866430870423078801440242887234016638949595450441309506995249818655925739721717290359377913280140803664111558047789167108119202172621835231579294609433839072554475863637699749728101635672360172823386153708201315518095874412722162287548007331464414929546204506490157037907272191312047018710113007264182627013554164843167222882951040108322871863741546088856404776604429265876633351167716757047812980173647983316864862952790120640964704796612348289965637166088180116483829281133354406218421602174353038798093027552795292890372319561321825764053297888333060401770857510177534059751127440721885969069073472823333364803540046076347691331791118828583463373153856028301096235039338528543195394208725687289802932169150831362798434555835732054659995184439368974037847054119075769570894829121413699443028505850967413046061371701684878287874446656061117601377106140798805481279826536195950456184754770277148348250420435995783918016949225415061048424523379774586566221833301771848465168695737810270904096715384445201513200689744146116226353573691329905475160062136077438958698321638412658785565182298566592128899492292430914948070243455026939149510492264684231366042831519085668303098457034823338679687217392051038177946399667426007297811257801535999406715695277124322810063374388369549880396116919004492046922906806515271310601596063798439684838935000869347533547295383323827185645137032635035177728830168429989373380891855582504954558804141454545159455631960588493874725045137127190684171101923520309668374263065033658012734888569418460663163690507462494912202545483822293316047347125447690170015374659613956472547902780500063988257833553236894879187688104836508562468202207059295433749296077503227299590990360766849623842214474062387135413588325042365439437753565815879488752961914677466032895873021269123450119862500873865831191574638008975347666520185444292488189658773424208171762320513058585291608589536528121575146969273021821078410779771111470795420162068004740297674867060091563917781531245678572063129571288534249479340734909136987859131030198661528368010286533319384661041225173379921306482921535762762096584279553068701406871704214785456469613139591325694675540961058921293206360486753524104989285696855207083077542063908424647952154926623682122834084319625047165330906324028228753248579954939888262230662146040370295600818522316523312484154421918504084522385259011810381455169115334802284897843613019968288239039487106869100055151987723623402802198963212435045102340075185829435495659594416251196442728488659045971170414785369875569160729736593578793048808443644361995040076542320081238435878636694261152468396138389845385356441856799412775746990755964920264428537388630012035567062942785851070795352868913904543992386682407251060273718233551883610690829441242330574659225572590327896777661702405794907043330258852378829931245115138703884125861792214166994154318477404918498958967412413030781399336959430597249671689706732886613652256695988796974148049021679997027142157635924926667199088877804462470138290946512183685190405126006603778999656916225586055789923635815174221811958595882228194479604782233671748419262320840556166309106378854723681160215276542546238299043199898525911585540770320486176750633925420845094629126016626195246675461867213667038345295138642195962840362573593039528992364702865008246942535508444143149905897674205437377239464303126570800556552070747612859247615378915158355667105724350228781456913088477426884866012444406917114334746672180593778775949079082496780497339865390221116644601698370952864146742472338516073696624692537539542868142079023396955272466855742492854421210825348855818435170311886256805111501956404402352123228790592253612675863293606501800264219546643621914273118064152417038838670155174621663510846327498008081735864538238270094094608435657101539197088535660830876694603069397969646038404992903873847467362374321573267955839085891424696749603388457139834850980423395922762390175970850090225036745398378175871823710807988432261868735443262976081750031853193982370546081394799618471177383379880454869256264983292055502898637172911066564323396624785626395864666099452983554397701108916673985802295317690196064187808957209388964817383561955065405269765587125019999749447446106992392029826907840381380160051543891052253083151675370564204027358026672833472811740222652546098326443985481992546806622208162506617171873612861625537542317561043850394916876172265705250965122831551471604820179707589699918294778921583679359204488382144037697522819959183454186279287258436610628847994295102019131861321617224918732334381163804489886726475549232856728616685090634966443336980963604960522035193228647655238853414916001486299358714497561270773234984386849011823298317973251836216010038946487899686587066564468605430209065756774995340679762037582230318992001736603735670473676993696999289166860759906502203637158797554010073393866941037529351642035516928363389628980019813355282770105877814078262447555921726816921642281112217912711747635294921959842594181329381406981228396846572188662696112458382970784424622044730711082484882019230505862712173397049039001804104868060559512840925479126568715211263672193678774198196402022348895288270522784726868339254573282428024535425182237008062106246682698609980698476816005313534960789255002466050396040454205133492549529883443425703956644297697643982008065067137441424195580027965740698260759437594803041135304186914743998039568208043663985860328568968185919307752429468796003556282210949584114847082468059860759156678683931208921819783079458765864886155473973851131921563182506195988909705089235045458353247828937275724093911970311176925223734884251160383861355224893064268265757543328244134742585199168593292606588869528832386597853989634133246183742856768013297679820658484972207356725562453995528031201765642433456120416688905032421207396211236193840233193289259401422971910542904154987729551873236089507303123608909828149386714991117252216446098215656982682613083006410711780977751358833867082874499422216200337674552158052839893177286164964794968223430101106328625353761575933244805344534892761911331938153472726263306985892019108573848919642240029808583128416314235866275088921454626757085897346153450112963848832016658742482975294713656890422974901919441045031725991303470086677546113255413514197636607914439954841060927997899855528924022062223426928027322329351361334117947785550335465845591599038691170728439020639354331073795345113678535480654796235738045887728912076345357870144895724823352220530883685477509641412566870226176567233516940658007573811060847989537672489351725539765071107526488109652050838883503568913007409290558404949858567483190549050978485025905219199892488525461022472022939412952304807784451835264765198143197330710286829407499146012903127778580302414450355076333881322317789364542537998911730949011845556622165548431230346409826117388357845447013244858909104282988882032678099447444737460938250103179325989740440955077910596213961648048737601389767144628874880205383943316539874070155255912805023383586405432678078071929606853507204097942336162587967955016592391618640175823931374852091573078236451578455480686146192545250281634169144362016690591807272583163475638043625892648518975434239242145528782388877525149378391539659145304930883866218501643416650740615722586895827150149945242859456828159563486462477076945141550435215973261334179340551028283765317163561800057508879669971253936938724835656980964432599844213942729438824200150262225995764855017996428812892060637571235634017564542349716830308656933605882355001856554948619447447401421899869737658114296289157119464184863852820616326163850688871719006437546447016375984816861587310975588060962343836717642797433480341942483821705012620905232595417062916612217848284823775171689222225281688620738681785336558199239292325706699471177696629481156318575288073673123819337312953987629881578672793155153470856232311368363042342081663531511900012920154675581839253967940493157334772914726396635441271698850110042321052474180096369771827466824075183906259845260440040545923821081368219455954258965272840530107668141887508679802450642403353847495614491238870431575336522336712221423339637220192070945656052694986448173321102723308061889666724506437053674211764112994098253776818652276584642359814377228843105306964120795432006883888479156952841366383437327428534289217297289688922380935061373054895135303816961139045639739802814139454001117338718729539361337822561886855267473742803605895741256122357144468306580609089021419920520596288312773418620516178699737970987999645110986688404348242514840503913370992241106500318802056720867262301571812850858677787530657601191481876092158325780177664651445807533579430995551368715597856375240631636260015448531689939915848447447707673190387646658966598778748303381428619944457568853272115380832443424275649841861448658940741760464278457389396593859599303380088390632436634639541344947452499234315799463221515121176395226867902713583398852854551927357256044061172667861111084485340892102978309034212138387990805622953706201537234199111430059905156897067108650508488883074674145476215339000422303593313265929054032759769853148042163375836872081685394406511957883011591633306113383583730036585233706054579366459063450970389171676868685524007786426230526185140144154343952642181950103737987260522222869027633409380466856925283429405827360170355781395428554984822825767631110760021148483923221855276828225898135040377691482634812755749146179967452200858666357054917480060232128475934125022694044814426404049856757201483966747085410152054173496192053021615480930953151858890745786997283420888836374831805745238573662132574118248012932668524853326447857637863437768152674182450380004250285735827365323655930951242299275522740152768855666626117876745447121052272440751294036702396141888638194649690226099080420983926621947753318274326326358721547993023464862227296917693336427458650646134673004730003271846260662009367536402362715162449966341984666756536292467470235912178963346335470626336512805014306415572279358776890869986893749691246658608701748435747330500909454504581589717874221807705995209238569548946275414105750481094815027821534603476955221676135332585057046567666528537371549612448356791232634277024444259331402233694855109658826995960532056466850147629168383909136786810739837972679760990592562543104410875105630385851895908022730899237432215503414875095003976001237536397112558969648269535307341973733809320390690558108922826239922026388207635193798664669959669935916275336592326136862652927691033030818209375850134599079416154001717804056338878656944922077054050984405023306507946930363677256754040911913185105893781911994079775648006844468999765783627703450334621317886407523195069808697932266174126518258890192238383722351357509369057608520761757870000563168306384351314175033689553883032009799063998207312542955638309774024713278611155440401802886373918081375027235743742283154685562850441701691231871637492938772905625937522391145343105683795508529320466729268125211692826139140139971408495396728003660004923542961414873481184314990618292994882325690925696512243859743300030565888166657262365157646832532308538087391752705789820122089935896281531217301726225465976643718631923611119384641347016910458681623749646950170737776825721974667092695265135148940165909705337208159262224263052773259228896649195650207806387020992513052888581257534495568656333144193142160464728948198777844515706483579079906826043281800054479329417900097913600401040431709639818211003039282972215381511878259418160761759765563969176239785434489473412844225705971193328657495942973709557028982359703507147588543861556522692778624082522619628048919981031506198529413132276759381222699059369338113559940195667797982999046465531767710388963945827751059698256168796432622963594682896432660643612275074942651763942484255484129137769431327271448438051597166006670424445600182680558156034030232098452310316901802217254679945583641944358266210367835487417523875625403816442642097353889618312757929074993069670169767017888292466562172234676923792490898697614095944948415468871838327952516193170588705291813165597718031668639318477708051415725033213413835913214092065904427239572905943735251554382830455924645177284104172875308830984266730849851887071060477436727283323195646649759528650980459886837993865902351249997451959523130740595261700942527580823243507943779605328319176687593094625781239827230970973583664247314454107169269762803417325437311273837870440118843873354525349050401800754700404477809717387828210497663522674578289979525322360061754221075984520455594314980147109010257623045191181887816062026351477454721985345442927547024631959926337381404308339810024971908437138575180483055391660709633973788273709982075037214741156678932727042691141609612089531298441575299867445474628591020184227506890394516208440746542790146412812589415349008466463682855468646278879491695347117758234774766752735528503637502313284007746554354422105404197099749038250174527775746605761711614101765672581676764269217943102564239879960547402672549685899321132504564336967769095301853823523628314455042622422035749540474410978713029964998325417840008712778358561980659272303979347067444549749371933349391017163441890468756273789361518568048716720706585614560789745435494255814648190471525205439415019887960425422193325598521325758167050670310898778588042741492120949144013180894120241128557509199078235707405039228278904212557893918597171088840771455025416637838622075971315960986523807948272620707331968731802867583551563233415693148188795992315870383102083901547197225220437470159557661318261417170492029717831600017389092775028240137828997853759102071314412108617599833050490436331267239275923438394394968566003987463560995149591459328423976204175480747493703259388476185285043562737627444587262752540482889047723313469314322402483178348396743719291325331381232737885012694880740496710987785458808821024747637680186415618350769465015743199729193983987697201936760205601770853875568823145561091845566034838954593017586999056735856945365502190945021703144437189216440200005364814201781478710700337269895681040513212662368435336653870046080771525281429272059687949873231337826861743725870503693906351545777252308889060436129218037713693319948945281566789455896033371086928831233966656905674177719398191881289282098938660251111471979449864891184849029713145876246272483149490268691892487558595161998476784655294808163263426960269009450554023400871430217746176979229425716362215525059361317585314265719743162060600979592997170039460407144498976745126775362688582168361905771042828663606264734474545947345671953837423179509194833846565042383849656283256109296384213854529531889658042872038989026507670743610252628444295493033082186818932891050562049537049850420791429186894463889358659031042832238175069557966693378892932601109936925135856794622779743971074427727510298944019839173395484275946492503638647757522987035359535783569381191612136104707842945953098835846884554058208854128998801733167418773741363650860865166596935874165347584911976013122389501022768621805811148900174072261935177429521488188463068510318504984039343855552012535631388275726864718561908131467798774636361366393782921118231536444219839685596900479506207456791204542288824879410558342970689753494145395268397421977904635377397533895298128886267537534125857160514057075836737396967631458066100999515215992970732695359357877790188119927586725364303625079889615357474238046118157996457200009266450927053436492349993891939201446115665847430033994565198365136846323375420832072622826626649229498092570047234969197136450705737753659362120107131888199630351422539013210646672747536828150480915269483615093039666701471945811871802371597798236768897089403703888408943785539368308216926724449363439868207693163178058809199040227316418314828841585492274762739305740141795497108839901153951744775024343945565029764690336899506896054032111521301804103251265225324198497074703132225454113110039127710588491489933941741953845196855023514192650974683865877367485549542834344482637388280520375567070309744601573163738158822995271070041056059665974908928872526516596405637817410159688382429887466875706657215101716830663636225324705039871858148900708869759624764114345513967470147688164084051737454241529297665496715781139651230229719694438052055152233815315268147582478636366984136265306992329150543412899835653515280175888630801838743795689697281675391432458659408810175700336141246404852138809699580505337486365004865794626127090127644803131677109683859283117836259400565763099878047017404052629432384941297702289648746149797140699468408909360841741053655232547860765381921422202742547809763936781205393308572282210799383464178880712827134725514009437993576980842089716287287747796515100222421912860979025536340649645630567701556754569679277636685419832344942351198638445441981089311554400128976879233471447085352493301426166310590699129993937514524577533509516839125886774652303440260087211234900702586061463335814765670304205297644064152462435915510192520589589545843177581097734679484259646360245653378639135734187564505626054184649820552445858604316928101579516101020366264200883215409159676650097497420682454406966272042641656510527442526945842960827944869394007748395950021030686947897761459843583475760020187430437572910536835227183542391124639942539778700773374988975662971601868648311908245831114443239063989233387502611272641459003876306396213366064556918655186038607464077950285836352485890262098818920163046161450386673892458731580855007616004178035006624841976338156229672835313563463873538786672949887977237263649801794714163452150091826739528555736695353586458879069543617294923767103968871893453794618398333397777076631592463613444861414577488238071911687279666147478877147300089481326644238813412146732242575476679088689617485604270191803917116879738522069737188574592990825451561014125807870709832344337077159282079149211744511776265504874660932050893271584218216020934442668096485967478668668830858410546002995154227549359402891958184497733292451598787457259736612698246630108325421061869851667646065339451448427348030288641521671177270851197415782993705999253880323384471492348592044094758549723354487371285229832332248625437919938404917930271736367940550315709936543718016726254340572859370062822529012887089169980632082169278189728762528457956890170229524241930659485266716516937454269524352850267533197191963532118872054127648015986105497829064039772296542795024517321498682501496926663848734281481852492011402163831848092066375593173119668618660483445198494181210370500553808625560342710550584709893378562400632959068419026845031053432546290274466296949718423877557382509564896320361634733127282616658398182893624718193014802537601463017381112551879022384042333743935192755262166117059174355551466374870811762169601538939154071648136968810349633324763147984389585806436555222738645337075604430711522971810205555327117067683108129752666003244281209590233453868415262615433184458824418701889239908569325611565362547321834242255747149065517526620109619501532227361265728397656287155740898611897475160103016460377835853713616495570697225438638382181436691757536599924249891281878197457932626741482818405258594362547437838884201978988710644081307782699609155618549771056139441228948380870418968601401771383354052185482128759357686849464938130751359947116638291856134045180523658890857985945701530176777912261561431882380833077016360414785357315676855279383301924405807652071073365144900370328001184856754134240482997697116573378069474420005547762032086467520546943301752817449177349766244964579020878061594844711431252789081774504388353941531319807593331065679187131086231382957256911225806572497503284287445882539951293875380230259989723790298837124599063792821167131445204001639421792211163584027388974027590191001650783508900831333250101016411933351023948479821849602223285695532832934119870187108640775387057445603003690853099776447303420420094819387659048086993021012101075505692253200648580834548974246780420445337497627569824641108355821348901672749345132509685118937803260035969971434035556350046782037582957147071045464102551728716126477043955150489149893884665010374841766014016932909654008425298827371102377248527941198893450986502468556874885834998318110226697295447692022070175240201929759289463039384548423145197232006879488554915254992091817545438259106128274110229869254075925118114217700618773269881695601107418509668341364370736541894986756047602434881906390634580257005328418849517254309647730094016344060286350082708289589396320639426381722142149190360737884686994635613372920049545743607625484305549346386603927771639929042892827931757121797422108424268479715307261029904915350344823666280473937315043008012936374456772387604128260754939039641883931246242898721260954834965495496448137503501706413876307389871254101521742597440746947426561789564902580765409387232620186493283812037436343189167442069512515452846244338208856589913936018291413574794288930911534154072186318314868774433196456763556677188064141871019274849999290404490512878068417010264154620099788933961812952239435487552449038111024059305784578366089971072345093818176627954413487563871343269960729112448439238344167981839572034747487735045316559112698154795562898193846400219347485999172880427384298025693577493981634279286768937007314716456771293202400216554361963250646085999457242140162449651309535824040551551416269906510454685490620156695628842645957446039382385916337376068507285098113881975466645859900278652349317230131728576460212263000498872713974781305416403738956345907276981907320634277078010150883625242604510364003364951122818587139465966032744849327402595430035608864281701574393188726664783593835552113740768144089961467764523015304532960964517596201888307877733737568346790587381398360682093577265887762406535114687335716401524134191278129736532646839965778937454710624516314932548788066641105951324502105256789102278050451519420483213722785422272832946376479566235379424475618744496005169077309497084956325614967909705339013277711636495073018970419156087702702368233671323501788541799109640228023705332039478653975285093301111162083132769597715444376421584361299236275428885614664746588183033303981150880391802171622897515378647589390503834882935360659113352509292678802356762798598095693072941283095159248846058033287622963008276902431731327543725617156187743096435123265213379547628657753302604813229176907591797366147464153986694582813322492612023948733190066290888879311263396097404096672411758796776051327968285315417382948419271862919723412026937320574766742801496534066650358549744675997053559944365509926186156927227714336988257749114067740747874136425641269217886116493909910590996709031586519903281329029217659956585650318858284035635357549007098668884134285095702478192378074583358214528466369970888527216015754326843072343714368435715242537307621925756773826780648903316440392640106892738136450065787225616737989384103170849579202218701021512239622473842211012648767848890682784205603062342796590102597968917220628569311676358680118582805875291726270199043275566347595723208314454335088235384695710958741088788937382696917371860732479055959025675024292809795972548547015907442981719545550074914301337778147101817942761936383655043222413004154398304199562981021777003864662564863984124535227122511946004453925933458260931895945531026308208420415144165617638529932709938769367363097472098035555638901301335785965124167496090754092955578119663069991839442992656052445603293047729236247099644200428079943398946832913510985450888017651382859101999186704597282734292796324750859877618284402332543298691028201483310598774243451572861754703080359484552783082541160714745372876760680186538621033106328141414008689629318982117489033439764281413068098442712201422690569427564366836726076976532094967567917444837992139063562050843648998259222270151725930442504125231746940347845939764157551980846439254432124178406859656931965806299309558734544872427637605481680625986500168179162899750477865663117977394090913104706950210553738235109543219121575093863752685196324555612510963910564715155417466516057457477941224907002017143547262172396560182119892940348474569812013163857399083341066437289656681570597199407310946785469189685524389789629864162426268567223349068356734439807806705148455202508467666729223201470081922821257514621937906241490668708656991291900920363193552127146154755872024376404865488585169364959386729469021789367492830181078262660624791559349316215262092770786693934913674678904359365508730663405003155329668322884354084704603613686917072341943148162688385542758776759271920507513858151341584212301004961734066605774932502396169950386310311831147139882237835880787653467852945551571488350822204351243014248129013190636795855446265760158719809156519849151354957424896891143715292698868027156609053222625638057432835748791555672196799332660091699223599164871312454211952821441012279162850133530347684503258707511985499919629729617392291219130823790037196988341531966321202282047086826825295643785199399451229653717756087665455518087161585540447051465247109535286125071428812432697156548786676974455714182106687521037046971948942909240350675602179884029013279186329692570537796995296825885405593645120243678324842076393134494835235613578405417772136073994491759899091567961158349368140787415975985518765531393127230235152948406430646089374123289151026308695632047428538122905790445663102680714122597702611049845840594743245891193331420875189514496066971685706201703394856127554306251936951139643821980391539056106194134271059770505984097836744595871221956619992563654720233776679504147394824875384383524924587546100901598140549437405167136538057869827581198301473382195056744278975471580846451226159098627599918455618271443274402547827990513701937818975927149032856372325577252121736997872810812819987503085199116411421443187971385086712977462793893539163016669203509031110677213070456992006842061581348551848490967244981873071782378267381970990539895112294970655087563680885953376889577659981184727056945260079849584229625750760179275091154829754294123190238957492689744996341172809609942451523686253992990386992312430362988826602982079544103979382779620785919428777529837074125127726444749591626396819976167175956325598794187243138220809828282474431897317988496256014361463608914480352779248403409540113095091125508454137016737257256044201258159301310864342377002135315332978121410454837971977144999671621351542567852758417775714682245787160727104050819510137487189580161750078986775916105017227693133625144118932247001626934727253594164002190039825356742447127818911576080490887192843789299896451938539917905066530686162587681116989143298491266486217983600535089571245114895942799853915589467232929983246967944434060679500001095587179491875160145723745199819100924576621595777422927954860731470239144226607491258531021991450733185261441713154726248943360133048710098737757499981757215902182052233144519692585379140111891863640592980366328370603206566118367380864672936201841355549859296056909470739506647971108989190931214912345270527756256208813996855954947058237885517536416072812106280369251259933312967205415406711320940975761300966821639311324275802841065582166773966019627743642885857537726802909780096628020419725723522683082758980881443396019647658909616377669859244077739760536726730389876120647871285080294782630653361409289643620412793726067172603190252042415673080266385565867224657972543243668354543863342494791440406249077218992403290400000288610642531927831147828554803540207254891380501027098034671066869708158680603036180332880012947245186978446546799930774029049164890383227674631809883584170950258792799325524664329165628497640988459080972697908920080926901763740339234305984431539154733136012574385255351444200867136086834175378127607762251782421342468203313064151704912575489177073329401781018874361256901008756029652512861572145206909998617963768723795599364171434295670080332183190012127849625878661740870270589988431585634017701142617780617525329799108008269313062511332171644009906976433120102929247026413540632914613667438155763225368262373690016880156813876920508456862361036722101652729821281145108688951101257801929848827874669312244994285168954617426320234367560463548781723174297835327765763829009104091850910141884438365746550591722515122698980830848707195427836444066090788168712030336341349370340096262802425663958741389338475271681656214474335508987864237803107737200963530433146183067597237683013075223417780957193270856940564984020551927523446568165756766236297124728726027109522555856289561710004986939418882169683554510691743888574306950081301407821730626587242075747357657788298516655159100544294974668276815533476159318741313028432933788078679428413719022415658406343717820919278431542941880871551212083486582607130245682174856452130436877099365590249923628191065171404587308350179362127310393164364762318824992209923323980981515056352515470453160948308260474068788898024675051216575482428431346911482257955566379119835072812188755152275186467933411025135014472860874510642426400419405650073781628004233862983857456663160102086332045510841457119242724056336906587118589042077119834592488127311313925911755322545515160164157571476774564169409307491829696094185695605021744366763111392591840896153903986727904133934015605273965161598160445630489246742707841526953800352248567657216688880504851623483742347452115672323192429113241049431269043967711070304632547601800037743957484305664727956366488472148210108780721114954597778043301213088692084445976712606597061165424156666013506122351995001354434822329106786091263334187129662905832625536761066438145714613048269055004723480812816143733760351727989384301117780843350838672115887959585676816826331608196129132274141677410236416426126929115821570313616229640359476034704156445026498531041266047679035213695171414276942575575451616900550926058227643727679533557153165919520941656878897167545681176007181242579276286382424225374599957324572176941872622422249405113366993591828122096179887070012007644937598688425605711165496273323897091849364530587422273321606847496545628248557907147851091935641504644044336859901961994126689735498217128915190688842389762587103087449694600581226635644688741122255640685832637859701008553463350426849393177606750348628056483113753166378648640925848703777948044258682774196230338388044626585657156843282787569502033813626204473774149463330540101431933277137467117572608108178908185134111067328930137723958352871141749317453017270854187721740315059419865451215512670339986936333344745627578939171643262368975240748242142486940943677942228670001296360020299895618888840156842688970536102277880101602648547036882273242607508633838565884678635876487053658546983595983970767204459465191249880823704770348963453526103099249453577168857144269878228743855423252335610319891686690556595617642006438924239353765747715174966427593726585700842472178513297748323744522375832394750265670946830883863341558080093784721947491644911893683318556376554394289049933119602909015535526883646999665015667440453512524384401795805477804723464584955262243953990662926819955713403433743232572721194515902791046602046104473875096795498588802387745187444392235001437191851697443384554245083143817379973332659185951762903445731531889634151394714638949629737438607241161111489893412005257080126225943040628201756242287121496626295092249695054241274440662569954156873829186805493597406062930174087969229138285064582836824388545328373677882696913530720055835918035856124718812484079489373465229224481208264531078072730939322591423403804588975934171775029665165171165613115948807561999276777075864033354847114955006979073990636845241542545397733749187295540803934167506213232500151964069908326929673756827404382919796898869993022130301869219871356473205415354096947512730330199536056009291297015546570604140291286676799723876093874335468983495537199720238675778376423044471579836878975057013573879464609236976107032182584578316381190603727985571862270009759035142977777246783751207784589031102019119684900475874574421771057997508190364352698047393217927732477191591687473540032080514018871209784819057084295512894034919342826318536811476939138022098109162527720637710760350598738943069596385625893991584391573082836723740962357623731477964900044416701015530850627216265963466273419184286291320713405122770744752023445456710999572467089659001429741635485470379057155755077059009616635255974496245476922753462812269704422089626149842758661301564602510084366898207213676788891645390204431574426826470758823713230464573157062903211977165380100829786623130739691634677689855412379725339721606601962810072528629227668613953897322132109948421089908915986606571376545130730722570751297248310585897827158441421488402414247064224793228083425682948235577161605997226962781885255591412328761894943679674791419096858357068109946315001070304491164654851493973087949472867709986528479327098426362028916427179211656329292939926447032334691562514098959696436019057865737101683352355731802767600353504180068166371114999072341007431350139870220751919664199776487764875321771067282710113294443199099435331385603382869367616660076384101310553034638197704542825402264980735241219199988193914270250772867707928573499487115446627967183385402707958140314032269219503255484072901274003810047394383963763382131443675332954498016954217265247831390425291608677135479647980625378096916823364481875122947349925819843553145278962910608460601135455634546017667582595735097423174359287175950054325251683571761046075304548567145400873012103610973396270389747923449479446256530269166502917902429942594923295979445580723735456643618413406351926586783849794023091277078731558936581925528406662489235312803541838801140594883186721894343644883951811509090488344671895173543544714805563034640240150932153982476172370665977456766489350325590548577688029123490214888570970919332067039386690314501321555479722811682455615315262193211459060984750765350444136724241048401418124020602300216163833021423532110400521239391323153019796527215870082081617601460803778110457877592519187933291582598776393632980617609974271788064877364249111183488521257237055954814762605350599643375322491546880399326916790292977313595108598862648251843090649879626244279055566094619646388736609096421356528941715150452674948858363403053545440010150629438388268490758841151663853983780751301770253026116973208117537466956944465106635747445172996434600473992280949161649508412652551480014068934308934588014918409161668048441828320818094307356233821857159681963754482809342655536143131273646242878006336561765578828825193428936295654670008805538270812928738916235251100383565141925967966689167328421117219375356526161079898335193496073858857593711726170488042334974075581528257663994934463680018913309983395078465739930348818614958516442313989241611608482607556624064913345678091545248387229283293086999069439320229608194733927448584748949872192090981071974020477934083717430057420169052309263752262010540007308910231147910537156924245279425608080126810254344205424481537880341413829455899631633153655059554491208189155378807086854361915023950292931842466839855722937476339385893317863571298939822753221952308340818670823990940927023574845914663023506056676116294146528389332563467223682497166787289776678234374309843806734292795731228370181781442987852996824568315534293121729954951686983982599761192412820810820088031084192497753936584596923784130017912691537644206670214884033195187781216385803525279970031963088299691402048441125344611897783370224257913387307821694908449926265409155651785023361997063854176043603856763289647569804843676314208583125109518525594211427802396716339894688806445285738257553925735521584714711837004877175669817002269932751125199524702353904240798645356455697633170473672961045817263753748378181962988311549267237715615300821206071446533656317407962765986984424193191841661853599085964525757674985004986419984680359051109076757772400525438492091788176771489347910905060220410026763892836422880830416310234798600353305705650560556637224781373382244804452623704181368959791404879593439904110187145806024143735758813266203041994880824790755099584429164934031966352655510350081356699620467504080877543778788274016136582938126252829022114702876636318515565494665074769095146721648273962849776362336896280405307638423261061839378699451475076866893014694346210380928794063842020677926872160358656815902254344086799642015224068541434685324021665791544168638065058753773013016028485912560340460374793192435113647736836780405205885669267069359420044466362114328036106645682132559449678748292544491586842108994372868848026245061775499274949643451730711630129372883505203050232110865477201345670693603519652876621523424941462226717252193114039283264320701015171127360155171874925936693475649364750992446759689073263819804971737049384482266765453922174153807220290135205012026980235162539478655339641401237273245099590435730740982560521363211706034527790553787776241712644680081645885092168084141257762750070035459297798994078612308546793161540684675192030398110023792714285771536588689857804901544880673675729459445632736087031935537188956991517941849988850043379498077619253060150021539405188107255245683648277954954368840316677017915684706328780261343539890677282669809601821673157731173554953838552332090212406330323270428883877579846392523476783344904178677795525589175504708065270655181010303307235814553782656419114765046354253523358984463926961466879019147768632699424759018919395093465206212176196966080819843929655764833191887398631656292484765104746628823325598489777615372191596516888320820055091945553800679024121419207483705638704771211097515264981398066968603858408346584529230096897013690241456481556580122023774883872824328867349469431342281502113426534369277931731158766564368406586885441500400946615503789945146528980283208185034754778922590912011618614417642491108291136965091642856866874751077164696297073358620852021877560093216992531762532631354585691069252767857874346558155126423563328125941449612035637519575298026858966564491496427618182317565111232236706831808596506925950481734788018460046683226877714602839170835182199010789566117767223717570701581884162035411041347471621568593813181325726153006814134580462301023783269418172417443418156544653305458645521820647344836661181454743099359068434975955492027750529104577934104107197041354749771717786040185576305152781759665378279811455627156936448045634544118573625506887361708229682528859011937319059583299639060349518346658457436627086641748138994610005068674894700934946538951884773674561198000041150451531779624152794461539133427327878992720196210128321762264517487228403952118283909954035035318739635199234796172328668930694085549800603869569150276193003368198417698187459345806582413065204890288066739249798253172912696559234748068427147180095386292609561067701527537794957118711080559402446506255508169240260222648953653622193966276285777399314235300859126049840413332821679090417459502377754389255635229624132525165870211686283124730019116222395943628398348636848189042930107496593391947807093174051054310211646498948190066660014327188725815720916502034781933764899050005892075551770006680913595589368910308272848672978419020754825444456690831529960979800844219256340171881533712363549712938092504522745871169375483445135965513937193537102896925215940088814143716163859199227542103977430112679375427389924970089678812521981296273823246910354253265589593913039414289698066292941748377487171649912998627975993335321020610843725242708585986667627623602143281489766400046515241650571892332240095488338928308008902791481371061017067500952856281832841713667694811431611464109236632310038764662246153839058931288409104550907737367469342889254280297803868911561759577818144239041892111575592860259894912390916194019155269235176837452213828273335839086265425854823454922383873000259648766735885864064736519340181762250670115116551526713479209808627262956171838603735583484262292890282351528951936136197590113985862386616826037100748479497169052177175389725432341241914937481466645332569675456316818923772957008576604811607499318860926737860273982792114912048350959455183891903586928787644169038791822678430785678607266276952233629586329882575727463572561505264733796883744529965297646376649485786436621939867603489081713022658903275372682919056851857654210998075371299342940565966584681079368189893748888476714606017158114970861195933582043700900239032900525687267817067885159779851278451881079771262906720770723832628331309211643010903791388795695554397292085952292223546248818239513699778443120109119569430733403293016621931298732508393797014449486668640774196834657738308405794942494080283844970313177464597775265409299203920354012518205824056516427684167151691667958363729343173405165600673841977239415795815668455942711111140078690253987307614885354979054525248409954938626557811506268555529656267535903556246515957811231271072194712687705932496484727372880708756184129607629325225238390404893123258463183988624525857852746223576543805947917287270046929997850252991047686238952172190774020175736996237037497836276620654063534617077007882179925646855168618976788498936812497151921934892464612052421472758432939056069318026852237228365782569006402055051437794294500784814467455223629067093695213418475828326560255776799101917226962823717959717868151804364348047301017886042387743057042749382926424859566555462140498320674682665952712290604264553329508817319948440365378809178748409384999208065888700202100423376251722652794629272676112089291623066391663786331361724584935335328675111891512442845204636341185733023819110603901357056828442536136485475121875764859902380472669500183580006247474792721747837027963300166284755102354831519609883680662484505488641645365981701182025055349060801148182268843552486933023593086923129366238882329383085351224461171203099866604166450551986698860846982841949990497794015415896579980460362122898407303887846997159756222216747529482928054755265258241625155112035559332559873505357254165764951517296893707084638328138780889583775780795089220904238164381816214605720265069755614631510160343620094769809955613762650962474966981730603500955678301559594054619516712427227570367457906967054984884903525494198249758573894036947046519442250098919788733021592409428041662048199619100665254669219662563566298458416240206842751066030847486299670102312757364225030634440698857719127372417080269289030441001374125013985921099205669370615228482195268270598875063603283463770003103133824544055222774610336503725450222233578410162587669284887488899133663085363207048357630191230603273432374156895944649089431899573472332205361593774570941431216958856323361356279927765742664874547393085236559356092045906222801203082117171706863775681308111953660583987854920453729054608445482455574201016553355362544853288078349710371771786841157120228060172767656585893618331648515728702993040560545901231817212737858193843790008669233722025095118124383472500314559009862157391155441981554787247818298074788365867697679963004328572945685030651821110010802277009350156233417764801451659219276774939671977216888052232812941715264801264749036168522260011524429347243022283732440573990613378305042165479592285032576003560243037407350362467667884804288491210062329934776240694920781608998544027870940000484370330246732737925503539977406762411500202120026682718459652353824383036324020461592469553109986042804093557736991359980488909074436811546459721527094394222654597138733800585259648556467278220502051278490332966289385317177570031055268802316027449648920921828206814613216397845367149110414812851588107508620279262908002447327758123221933704178804489868026716948981714571965854267606158867746727583353288247842659768070328817039522231559091565938388683167250354789265766889382948357376772379783331715324729401002534726880436465186100024879632696589333784236540452091642888799934645515400496830832358062909032572536429089928264387962168171658244963337932449099250722867223278952405525440700613827867969843745296537261093408906950315185560846787196598989055787739096602918702695119320549485782476686505897117785770452991974517271764673115243889762243299141094370360413677615562940687648623431642105531054465347860559192924106529318574028404860415904481330154578656670675101520785167235551133370173059104065409040603673896942240142213922353325516935160211321816806825996244664904658051964919760247247964457551314892000387433648658856122684253166845198795902635560041156003909770410887405670446196883627651061962699394129880290136563954544499071136553971199973141377013029272311668118590731677499375421692386377195229331134809558241156705164434110038677637339851320981998133318795995829974431246132325867120897520462894378247514800808271474992411105817228498781696702701877174588579473877334108952826066546028681074259607678201776991903277863910568447829325562551794803465416040601951508344751316147934932015420613401096492692000218972375696295518734713155345546886783021856971658672226458665362213492558016666581219607109952472983998142466020698171435563836084989225370702346998381694166115785579526293410260067026223732723273662494526243122844940776913012316013338230287337584794839860144018520389865073096154912810398094733988357856413822392136035791243400276521852893579148889544558518814105731784048030586519408447514466385931089438429051948009537351303362653526419734319646449665176442130783384047820489869887977415370472089500239557990602855100325619332271189318116738157676644798650389308823274151163155713637966491276636734032095499581074654840963068625153950028090764790429396544782796053227954378778699116883274236561895238645754465267488306637599132194455764915468266355431294376872735501250496135886733693158044408474717107791437173699271251065257670729583974703658463822723498267193340454355860343923048303797784175355227146592798680760260429922781650893740592737445404817147228377946368764467749277677884268360041122104532787276193242067883769620890892610408570270423517209998298988876017069345904970518211715708146324992637266133298282134414133421044316197148881519124276221548809627226728902230750640758909380216906749406646466372854652215625545059698326276187539092134948926643985750691653564102095638677835942648622281958715252184095600044685717472455921856547747243450666320545751295241276656130812156742691463161933694112921390583834724641349649127737369742375860964250809028634882427032014224648994199789800883638151014133193935611113736671421733034048090266977300247320305661341779604611305706043557182419022798181468194881591479845334914134201553977588873106382781040111162529764790493016663293009874762508368525638941847231900343885261445947156750809610353469871993106541321586702348378650071280744325187008815644492901762982846918172490929686665685930171027025347681882771791979694860198923861056368757332892403443378901334093141301334821660310302126495523982841561397328341390132705915324031050090495728269394132127854104465905075024903084565094302112611168748510315544707735672573626182069394276930288993524352990499185616060260752323667489264489630908067458184281730462650899147968839641653355376506125394498576336837369855897546474851661706847745533596162957947982115286358720730394764295229631249285782478875027704034740879438555938208673302246621908228445135039516068898707125417081143345483636504199013304980295843842790204016029004700555429260363342122096827988234991844004752451197111577471130347776525126824357101043695267173949957623380215117981104130487165716260747562376150037625879893168402111252030084386777234297996408990229719810306287770550728548532924741176458099426118253699883537638651381309728038551970262314880188293212855787540780035796211492103634119917782706374452712382413117611881628154392457187337238098464919764084186044142392396379461155820810157895747721703200645758973175061267764767087758922809806267188739406489640648577451780035193858814611935344373025606186417579686078175815994061685200395870405004511966114465670358528586157947389303997977036588907563194261390968846732090614697845989758833495084732202579620141688656349341908991447020152264151845304545341207325847199407794160450838996345543574532895286455182609520679923857309376825343239869023507653266470945969516880802991911718779794066605180639835129337884066639901641237776571414151067082473118411486449585588469258669489094341600567439273780776159052120941506116668696788829907191670129940239808999154352374454365982738233134779799371846759003828980649865250116417047477591888867753896825136087659187464494925485159777763814864454336588170253291554117668303990261728971091053552405399603133095622513407214162459836197038654879074054067334822660110004900664311460132211970362164750415329224277048427940754331568496616676211512844939023327208188527009283777756186725566060385188814682861291660347651333976711234938055467875988787081261773377215899811458133766727089625645746446584939006995178558297318107309564446334794494586798934047562208555015653866388614013718071088162611504965301286250046793449661916823154257258686214486388470824979122471276043667000262534330792588341744511146341053682880207368146862161593697477104055373937696701626691801567033060177343015849505715626537897845556068979206109267062063896778661223663836847388628139192853140061742377000905203201874109860740766983415561123768754025905525032014575797893829957780623385367271082863940460117784071448149963872071182075197682922210134127042418785977393879786685211921525805450171514575994797372424749368596672705494405279310412581783593547449600592501807505290039048603855618939776125398051972200600295667787805287305317756801767324116411607531155928500280413992024389469373053786266129327076380766764020781743762919330624015323549185827410540521997321808900046898149337131361729313563223476744876552584222848482708028659407662502837522869533680671254376636457737667081321191822636005480075251066610081782013893838944235083132497644536765424512210779249940708930848258829012185885909004717481199256391291882561261718854091059349785996023816259875009284040137358050592275666751552579965408291680371565617625667385091493043802247056000913684486854919295240002535421705912450456632370542718591610478033027211025121515142471886504064482388884288230370494439803637376496971686560228128751838718256491139594767639671755581813715432663999867482948992170531580384808545169840629502794423344972775823645497430565174423323866776190277543313347271569368944761892571939841844202428855764479082110770271460137197449483047568654376100160956069579391454450470582823406297484476554535766770978524179801406161412479279751694149767059640487178346555985670603618075310787166042242680228983845147773038676059810081152850714852522454299447193267594731869907865064956353903043985161457265391746563119364656344631657801483784055437779381306233019279464503109413772123713680328371384063345454352371235854321994440760937416654341466183778281585536743064377944886169921050508025518772713588951003924775984459404624038830953444140673354455501165783742949716567833786047155547029247872932077369489152622263509718946077488814167968473568170009300170108561081285014830832300575360774266681583458682654799655726158107692889179718825013897143576211637021535769162811690043612120671265466969882897402119533268491308489935709955784545082290862295391821471803998055157291066485567211632245596064790196443076516218703274723260753748421207974142895642335054562648120549427140854413645485838085758037260604280926447880041577461283665334032607344466211844891694747717389761920052639078761132787113003346949098102213242880468095865813874913908802952143273076657686309292652645654558358349676977705439344553482548708838687283664308086160036639505120798755597993247590872190620162356955044271360084553991900990323230427744573763445902666514748168534311898114590313668363999519699184753774628618402284472900216102973868538336300797690289576575431906707211625283694437207579597914164388962360890243946362848429044722746649415906919948502100909130786450844582847360527908961920513559458389622148668432716082878229933332508146890489524611473120910248124612072150896989782437361716863849012178036849027926044397309592571582003644946114353958559573661824510688948112730948414558497054796819469239388926228026683961802481122070398285325387224784358446438310290466731777773334537928895918762424896832067075611109712919360806104587215983650416074532183780624377514355197468042288806588710385685458878801345427354640517788844148371235859857499169116619461665408107249944324166853501314621127297729635604133352697687708959856735147014564804605675396007715848953776944129804094040427724177371458928287097469873804852573644847274312773817320503294583328768651436233135957438566946885489796423496783591621781398145859685697268505136654546512211777370836565054346257985298287058038347767660927000825713934018920563658961499977393681010865039088989002727191375315900435482598820324888779116252561532734023122622764981750097110941173676396590943805172423767713250629078176314250062069529488295870564195651550686730387993511002309938853337933653240855531313150089103943748878517946758311933842031088173355936763347521510985214610767473292494399740063561834169949755400968295395295750264073487534018107481828202643867359232020377533241152668939418070518922486630207976142454722324308388642540670075308685046407389234880519440545384451341491133227388875360051292135290701827441573312150781311612263218633674459199465321666721365026748490507788335251962913427322927955260390270984351060530121586490824666919040352880712008088891820482672068377442829641703013448385959872304593097559809261067943349530335528448572518966076358052601696380080681508465190418398779640204165809328073774266706800392515855654050349303694773413179146656038086458853781137029277327919262433516239327728919632967279756593811140505780944548026736989319455896273822093101798492477615962006585117153820494524288821165570582538721537051282099084645247097250824263380239368750077248418352771338866867884273070449374990716537845620875095286393978424136816148124731842291584902510866701898360645289722133773936065009056259921860122120395026710393842087318552520445297377351774895913463649142359625453138484330773822539636634132393796826588719084078781842772217088123649704552730435549789186045432001680167991065629475460612156754939324297302711475781952665075783387964882884101884379267698796397669771269428260685512776675748715847598762151398288426620476831168549743814804235041344230270312959706538248078025161260506020120826861455008808035485713224672466598303979468427629942042506348431471609255230990222062631467562093348094419147047181787593464703191134946983176305674231274375761169322468711442506532090622342245548852700297717457699231107107146658478779512157610327839195387283869780707500165039001108988381715164848438269373036314442159605830136152753305101745673973374085996575061521192068305677775046223642053580459151629153056573620111089143969182423161171206521109868500948394793584689649810744900503307275384611072003403632996366065254805640372485840544333048382089537578805847031263641071641517093230080745647394572946638244793347327632494235245095165603676918838616639472135678354024486392670951408136034160534635517608563993539906352883198321088396122688784756453564932883692575461361256451778163080766013726087890322943361418587732059989403696076094368856700366091419036046245220064256699801043142771454372122742521582054195374177994297763290559010744316972313824376122494359405367980289143858426880569788839126090465807708836824040633528679063162617467923885519035867765648390014310287539687665423685806369302853777187285977391784884023583597893459937264311958033585460667440410690074377271382378099313065292660449501939241619852114144311265411332380757631920653414567567362740946266862668994913341100823770192004708431367042166865576323933964793353665096970100197763207907853628365468951675690271535305926745464562588277681037479879961262583941771279563838509403276282993370858894161645454826990649143598623374448717082907471173615732412725300561961693927402367496786447402189822791351373498484821115718503827860170541901220781842447103447030013057326352318234419807330823779009402145701863315503407241245168008888417155639433017014779512179132232728341322793331807204887063619686066637869325946987444065565654057192902512437476717961016652590608675861295433687901405297394761730593396792347810586153931488196222023636324134694652627256640968915756793507940447898280576770302696964386004702650184185584489139102778462514081369682628154057511785519307197330097006782495167497135709780809578251359734856465544510290857581130873336959693706059896604022943727903717848512765043679909318694114704317700143958264916066999640667521463865481262729263600251633611705647231268517585358870291453669970425628838868106108741907102741281900395380198646455330979058566568298306826273764555000704994359115039094195236939986173498481383668897072588120864664068335431213720825043552396757650040563567965080828909846027119210335356741285329775878575289018212750261546553100307636296106047687685093146703231868074842817852296645552410492968219869806080911987309301787672675498283328863413768664499315739254633875745753303194718218617253917450846585216387328398665503719919425761774640175174782523094763879933117940218939237956778441289175622475163635186949758380665637968477578025175068133330826276708513668720108203727811418482557015921793892251287200789714882586500390490504218727373688385421200538891453654939937302063411643413632363458453856289252221283898898148631805883503432421535349042149182103478090036917162784343446685178932529707521750849119590758170334231046753725849111446211591304490020042946484628987469485329960375249769326687365506918383720899226127476866209088513929265018539809102245034244338503119103354004502928714054736206429869410159915055245065412858724357360990067938249534153808367248500634097003185174432776484296190708925480597838731954561223567034409003694075585888507147693799694392576440704917241227660960991055562692726432746086560722284579319238274425875693581269820877234638879993021164278646951898627004040477857286921749391881511359242811080399621170232618805694779326483231160520278906478376639485144945553782393441460045038453343150145988518094545680474762984555030685687507359629846908991433511070250221408724300972569398987457874881075173909142902216687441525521857998415906916200027273757603420623897771360920167460253593623244775712150175060831354166422613367600258503208989994678807785238280548198442430060957767813188829819529482379403442574978533756189627586495140696990860366676306741185062950264757523316886954629373372817240197806908407332381333180006856117774140639016156888199604897401394959626171304877956099848994740583166401045620210304473189525159324246786671092973243488207446662745441630778814136506993607414904604080327771046523568606962540593950376406011554036625486338371928378973446661102517486495382056049921972041425461985138840394964159331626679799336673220985841078601386382639428690406829460736405770240880698319399758921048922716161590726890974839523725276495851970487723672255065119270656198476433346304319150784119038514936712537565376288877917111724484630603472671725435870015774533035026713463515017700176984318883624354035393425014335581163886159714733301651873732612659155541113206532923637101170729393941101500587495829285595462783797732741574701068646023794238347632047036493143522537841450989410234904052860706643954528318555886485020686449512717056356234907893562756610623739042897653525585355124307444876666049793017652234056020884775253795557244813150703167411950299495400383707085844032750706468655000837524829903708298302337369747498495067429033276738668894153652253822156552976232073004682763038746374956218064401797295437631573084923769207970502632996329044927238116931507306018524908875245433905581772692733298312265702105121035949477025757707657669993174306142922885668853659127783790986172900120934683082737729715274149246923047335503232697683007092677613960529073848152690315001719984581911687878740219957116992929515471161702624296837318593881292084989494826815368498514591998564392205667631332754765055324062845245406507669716689632476031068849435485220099706949172487524920782351940321096326981453455770258010284740528763543391330137344602724708625986918721406443508152185691975694089536652828950962211922845380180404395248619453725814610736143791315692183479932197853205455707032198650588244115960178074751853184738748093314870871193408443378027090805119268590512638213987472121484283565512122045127303272552580426489702223453837075937806469983047733706783391840404666846691594230097636795586966556338670620550358483008976962677081931078463912679552096089818655051542603693910480749302967495116955386156118484867719271725212115141975647978204175895489003847498256199510257452898307756483835922088600221126795872313862051000596290785906025072619888420139183272902151624918298855587605330137336023797441391110183278138420636447930424305563577447210942072368656153923512916574756115788185538620651927279141219141598455831467659642183463256972323525389501321744666286957319264383225162621308870458879001145307132751445214544356558506356023388998361087019115388650075804636457754939862208007053695383720552710260173375825032021774723505964334355803481736480335132729550679815610684802216129240319949820314167992755809663949890988212287776710990902090363961552276593722396106016025008662559204008972968790143077739223568940061477796721958339217387371543576938455463410336727028978615239803029630704061435630599334554973776079171909039676060822647104118916655740311135747548173677918819532369630068257337633752694634415567592155963150047850839119423378794024254207363862895341035513069546936604922510010166561324281592040629048593438481309893088974728898777973331637248268643593688390222871397880245897725215511860973571590592604500408346239839700130291608440933369605367825878168230444418031933783767812000897152832961651647087953042321829888634078598253669992811110692453577441222595849984691609945572961624170735556767641537310490167385188779291997859513104968341431278264068188704102914246325223180440117839009292827386836833519505627300406256373930144521462108568212732498285597135223879128843178862304669024457543340091430176854272734542641600806799212500365616851032924988492483133628023852194083024230549757447246018013844526704763291343996739187964069965192984028041566609517336330358421047880770920544525146802736040509687585088754046190732979125857555074537612047838564980900489232540882105652990098921712753576909469750205357915228091874005052892874704374743762003665387957380909346545741033036261651551364668803409600144388692341511333348441014873413835991615982459157847388895974716895975184945294848438448332486834962360400844712466451431922821932962393477527728990062604129836904357123021613338353495209259641645477696857894376489128941141376691052778267898588775111605727569683114568397836974819832656845658046716074412857053351177359447627081784407984870064836283176190944871348930498531678520224452532083574172740083099564048879816507450330100401081981627283058004160984771965266316321010154904093497759971248202454236900437991144962368543654964357135662180402884094061600803957115632079250614036069387180625062758424877159223725169246214661656599987733339242888886328449708481162928204072727483822085980078200721879919128846346262908732465932500994927580186849096920790148040994043329541888779389215246357156739319622298106711906333233345281230277534403372711462942847217812431903027710465665651713054968255692301328640126733400685468754683809894493080501070566482056001196129147897729186321813211919438446129052292203814413889681008033891973225178190084146384739842807170278032379499395158485340203790029694375081469160719448739257935253098367430930964969809884939629633441028111453989373695844334516667841049719403629315146235061769839909299274929241710236739354028713096687755878214607063089524554090502128920069020738460436636028296309763320903746630428473324286472095842443163665460020627001008545862456197429813363085409090253134518561801098524669288991837077919155278085158073296929992018843386806223856594014140100988264634535944126167722591052472823004347651314752098606475213658053536140446075348541094897406835327123791073697309726570453270450510067270179318004589663809334314471965521675406733578532033903184488959373674716247745827868294423091664795568328727373589783850324436878458708019224488500619716322448575314457276615125734298670092681889273222900365225032897206072421820423243979911587426098309930693151343328589557106600470132539696428981080727734471401747113074665511821876755342663124572506566922609608968692170179563796908705155603653047725560907753273316728232109571796498722541067211483783985352330549226015637548528851794627495521902627447840571326355494237785526994732501607049445586070510925371009140904908765564750785159849423863587146779586015034513413255864289571309359635789669123891049924251381706920913093309549514586157063784528067649871542594922725668732319792733045394001566239792841623645208090523607612000608525837989158991846739566875903142133913238706006976284459631458158361278032977740450556188560077299548738423984604705615061993202273312955891246075128807127192661336024555547375709135468553277911969986502086591683862411046994286201130611887678642794639734626042818536496748113563409743006161906500506453993768909249707713172444910842037708302136102407751906532376130302315412293113157658734083389901464231489685534192829025666038770362500818908795329813111093356812668844432375671986069089923695466613745105547240253191747867384266072010239255576892005445850901245342933211706421724711679010086892553764062230554837396176276037059440887352939170336447016066607749170845133060514381069632688680688800456109646719534531793395196671728946293266404950279923978450808214012062782082170827471926177128045951202317448353403775004361020654418741705994284369000562430641402900967674901739371486956312289343367067411147996932360366520500565928782721846409271566771077725070444054672802557073957349906951347985363919967691108400024089051413939192655838963262401020262485851795991161094258207733986045643149314725173764977128216392554088352940362763376269215113968041249426884932724455031628628605384018817807027929089655737557889495338302607145064616925057740860151382901300964354944275933025018471834858279838492828979986224676009429139697196579987534561914206572323910936634807110443562981364896125340993663390274910065771933463784549210746341092529954896752721734055980998605016545828768037692283833517430372831233997491623840494381635664365894501334702118198259284857011291159093824179529818699287169383403069378046989916558839637431212571021402876882783643467693896914866956062607065132607528348378454777910492438181340617038486324834437007299412012915025784562614353139009888703523012254740830743440846935674690291979902115278731200923667250898683418593022132186476275292894185724043999814898025537279931700751731493733072136792999733469812058739074345324603469296555699984302006864905718634212741678603340610033520307693381674467609946657040984829757567709321666098179309624086035092173902599988328080076084550706606047559353617143244358700842157222241354321738492888385582871830657967095789469031818619744131784697989721077941457818432816659656425032588952784100848364782611686979445863822407474167975076310430345451344624193941514064433943313029476652232006497711779595218686590887444540582665333459685871732380135283003335112147523287368974453439412755186132199137642761340257680805852746356193107764354732621154501403828584350376070937677370679170890807538814352247595216485239686235969177489459376087919960278019253924104739027555178961254612645731747334650610852855824037698262896914576533241013482707375396458080663103748312471482504904237401157800009466618204814793190983399902394445716567639182704364085384511207191066370671145167012082761482227865902128617611367041524858005884136701856397740376969844730264407686230498006580852757152625222336009106058623040371227607741522456444356911294624573737008033286658248359108447660306183909810295876511491079578890249157004737008577806924955681210492655508042765066105905461512207446120434080256928499271143926967089596641593722426899402908139353403853512595012353852613930573513642628351324467184326627246511581665643435774962846493149756962401621088588496714010811685684110059762865128292026500418204233131297713496385857625755168309739830933776219143208987511640209592895271466926329331004661908672148616229388100603893382709979266715408455290549390973715607647607073033701472962448906892860386826089851690292642598368901300808390011833659131523039359048845777586317718020367016891574134144464113722446795746932085036319470300848698220685089760930194907486042485350391222931867312475923385858450806853520528172486257147820273249952434708413940457534914077505947842726556797339610394834033103268158532809030668756084804912803273515909851432945953231407322135226835398399856328865603367579838841117871348833616247111828852398475096141762286100176216925076581173189272928863193282509244392213806042122321115359659697082704415440216736444570087607858312310144133810148369206187332399375699529795884174766678564367702391029802850473092403935462283918528112385351852438178185974413417630400418036847092851163268382247178755464517124546169838010375114292285202420780540551964588855888372338124335779949979884282431911028941134812153555768104331838238613788500711724966686046736919443353028029204615278577316076310171937377760837025999738581228042477550127578615531367459945476128355716305553857877439465168418043264384899119365787337261444210146359175746978950177517638921223856227524152967340568079065125452478558338137825714233441533226293833207922780177323911573750697193112413434275116315664248252077971275893434870827818934543453894340704867312447971691819889104406788808030290332164156151030408735223536753429663635139402808681731300699859615120205590148771425622792487453005558276131589582531082277134773288205085604015534848361842364892002556981506645626499848721533615170328935354646019774510540414699848229416151004427388854048964607293471014965492373852765635758819142666163476708836728864672003101740448409802897541901582776652972548848838127229322140150714069604638673844027267959401625285165924093529039520469537489061653831067769645957415253704591148629252677112855643005522518431299367200005444417281722842419456494581321469719019550199696764482723684941586373391788512179801902274335748017379074402214510227920628594820985488973966234893355000900595576838312707680316131159473493418264408944948865852434500584043647065308553180080538465086017929966864467255196816831507981413410635424579072213428726852643358320000219106184692862886647487174430544075872498943801888875400104479518771171332675702139652210567618503878393229801956007527499447602955632012424512218047033734847172867813699579325736117129668054264929894936142956917011990643432396436856013838277959906539578313616929430564932048967176298063455141867560587076504682616323288225902973471324956139342165925467927105103221969199013145207802216914229122438341748213837645794005546708137267412220071754860664060321585735780872567489760848442875305036588866283251956711819025983436738665851213773558267343678050736450017422591682956378888648258405205256790698244986259778393875085229187122543913183161290346350959870251605652930986785584894838095376643276769931668116255580665129265680241418796614212173671287250604202569757019128928143236863166169964824479873552503925028711156018447905728661453771989885078508292345857508094822849324330425352820578551849690487121826328825700161109931069219696839432442628750835653020567978985569032049658102788327704209307761987712441234432284708735636355616383086195264763377487100610882650483288624349398574159194889379593428113573100913569908406405167129258117084979094611269105166352605095453122323439788200486567307940619740204663981110159317668264404761168203061854483382007487819563504166615687659778075008096726526135606119872501400692045439456526883415928609895811168806456456106645424683571791862926865003776015228368825906209034882940492813137827225824912523734874987313519173548424746143828338532381429497301203217604377510523151872645819899438445653810039478601484624671108273060533541860956602712177955474439104394194890554606399916900811550665925109921723926024841400977825422557951742397310036407864140342794192637042006765966873225061295520034312421286051178245515400327496764755802381652254426042389637917695177683950852083516564630011675958263548368052264682357079155626509190939075639173774404105509787396499495589141878469599174225572445248912047803155492452376155520169494665089910913742527093709664626730378481130851532496452326062238146432450184146881897527703234282755204854011416409368083267027693596010672789186179689454624667590011452644749741231776968643514098298050641022094516757539603044838931573007774934047023003552040541539975713786298271368654441420305138342666037979016362476437551271611436047715042773753525049337799078972817338066189747980884446403877208621984348701251955313880978489981718752995394248627581811793861573246121373579425345525095759296350267311836973095861905182411791520403927381217573860930533576390001544271308522115604048600912313958575843255468714279389159617450249226614353620596065126602947719849452022166248847247336454313466393636050960549395165100443471683637385597706170340880952524152931190173780895648889095766573510088128966634276529477834160234562578436009332570216859056219078353860869034956702599741586358847803031835732469797322699362338313159473794715922599791317349236792937221704335145244830718965704559696966995106956769391879092304382118449462470402970195750801006934401712895994074755697581351732453083126312813548143569140944025023844490545647167267677491040611108806728823945496868786598420666302648914897199148907749617632084439150441941229394159532822533606875360623194562841289090296829765996022672033527958443546017477557488615218333335097846810178984592413638088126505878899989817167454371817669771600558178451718858660254504028077748731543212733199759415318368854130393610552733901958059731603413126317025398177603371199883933871559858860791552883224337464570501072645839985170939248992616089616638586973688430959777645950662275792712464644556398400018115337369969503645940712060352378244002914370316998831783707574411878551602660113760651014056140149541903047480470423585711751178539545437153361870997864428229621248610362655928592465798759472351092020069276637901276599455586158108929175712307297792456249962866477375550734987991059473951085529842637436390802991950098494195598561410368746806375067330203662172602436284396099032712215821036643987571275619905266365501464830211826486464975462564428856444794600282558098013973946854709879644897133928295451997419657436424317985280673345660733505711574754495933840412498552916732216916869985107841477309320174075370386155955104125796535643631997652593415681517544892180337880176688418300657681317055225392277387610303335892960021860478323738595665380983412312060792147244122720380648321015779331757347534758880073379917039752031239321066189941604915532342812938939450753121253118318184972126292017733343690870502932224607311198425324036167118726801212513319473327260728203168220788743803566681951487714016718343683965371250170366971364476247425854285892541770228969590574571596019714667858854445024007798366523291635678468894306281022104170577093004521455725531585813095039202147626000655556095089909269038436177556998850322464442406487393625590470303421712901148700228092777064032587559916659330206711526838121990569499608746100355742814573975488108411545035302435128437103607485160020475957646821301011020360252638876587190605150435652863082584008645994621976183653243328149478861844256372592905712644906724349011081671895070820066607560748639009338700636611326377687138402629431042595469344569445792902294331496589645729586664359646354768679208697219191720067309169798504262050024844720946466853218143730031397571284902115397096402796395795892516472341736727426631628441905356695199166919593438358402227464488648720233577847387138362535465410298656203764128135115353617697363555493412419235329160750869969804863800610457094291124922628586002854302700918251058206668196837067163289739743773021655878078425136778119635164208477993247757970391744224152806156086574835920063812840449923264698047256715218038217990773863980525422752668946696312712060884135020280646108295027873412601173456032293250574394362347858576869600105276620485780999748771175577261704090504996994755754439278971718591044839985875844155803430478313011964138385715541172641655269936654217861139423875147560624188037741415956474102267967312237771352399008706535199441126654207355326093544284551169825186597132039155441117521105706072788586201042078222193629636803555115256937808807763119513012027340862387881942802489871813562393966433140677730154624016655264063691052366273965785924174168271137513057629618803284042178906619198098681575306835361675198478196545017672341144007101668759225057732914786756065466448499822107982388178359718056528987218069661338335670212171205718705738217701574841899538003013334460477190670094803753787041771188430234529555814692752170504029716647461069845026062949247252378759763494575831544841042900849213795500908470107592061589733256378366189647001754984505997173009155406938384803877403043557116288714916074181627562986025141461932367123400957299490927370619191346287225291036911845630623707840070861814626823195408928792355588256336113755097061720760501306319367673031789179836681360816894064483489376963049308445487919395344452703078569916265901080962997953123718977909198729471130081613647454174351226097877050215655292391124445068361325002505828945418054494911230335821321864486142279123410459904594310588186543103905979967649978410878531074846717602609167518657540381350051155477815956088248578704065965323216882057207339830340742154800804777485704957572322873575756556794077381678809183538866549163515866661738122650699608263016676269061384631005068002357499413515606722032437065655679321684889587986459352487575018625254206648103408348683586238340431101731842228953866045509126597509313139891726021629455274927406272597417962370777169033735620910976915097545072501708436731124894104330033561442232225323952902059079794824094075661606637824719702597357729328352985113495504792030595546845678279657499881992160911272530450676268816893389056052349362393006910148658121545732068181174656096095318255945430033394530377751152725914282161169457466219187043651896716851946258275531399169673274848018225355275951663406647587341099583892565890485430743466286382457438430981652171647233311767546638110814770311765867478715822581329222814532941810009618057581004288686818998377353974505158538834502421903891313967710808102895507080803701201485729680779311384977551147798501452040425063490408455672786831088926160410106179931192612073212094437212537768925512545229636550203665595850539009284625681852549740336173053733047778225003556418390994464213162494820093769135626897210592786315670093782768229439726744961326667527069263425315248866998868332966475899352347000631386651981957420235632688754667146463022891669184083739344761670732070344482169582282561014521547549683816504374240077442762019132705117512759625706452239224692047225848012119822452862801799995462453897051984865985577271536377072832011026132078603809581849937715597468375639517418541717143767112623212575918270151066465792114552829701671567410170666209247613375538461829749926780519365768288336723318127375496207950455351059617564929739069340850670848995109926263480768153747834592654463819655732718732314959919138177611006640251035222825143041677754131057915196067934596240450132609131725654212267268944690987260359700203143274202806095733310730665788466460021797660498077401800430307744414418660522260149302828410515720105457507566715844962151849441767536878809574507862508591167061108964104631036675228746597980202574061002750576423474428400420420943247312487586076812262082163699508412105628533087104094532241916643239098710363941821145632515864414488891060346650541286398779007006009526568923345366388286967598158570795783850212446426535736350377309774695800825454485005870069706351141330100203644151892858200407945330294625913160770303859384503955612723805642837482360469241487346178104433152259783259561978195484808294854816698684065794579868152423431109122922810635170855261169340611605981358264964628226430090658479903585844674097930565361733885549148820563335076719874957062406758880927752465998443830543877455514951340416447665742677511890385626601788902371192719925373702837650956746610399510461614100812797139468981176803606177265374680143106743178459928407828470573016472259816284609332075842596269599945383149255578881137136850614644451039982686244931349985218872861925646588556999915523211042584215569917808576647152438143779159688604099105099341894432379141822411225604486707974809976664618687643839889296099838236448035343687105544891289308183225892447426516161372844996681813581151606703279491826069082181133882541312562674973656514396834578723936371567411736024482695394294771531114868445809551712475523948492805211557365021672196323945074010454975162739617115841105006287053857978946208093017999260004618813513510617713838143753415342060185611587681715473283550069304075924728832078477241582613761692405098613898809635967596598961277270133853926595503447643724705384537628745670174259989808787343227331276273938729417742723822777216544128995893221193273511210802935482209741648903878193805286212421992486939814035124691353082788811665369790238544734363869838782459771112026770812168821058870917744272302351073026245390103531983773408463171439178999123957785180256036576992563112350395874451202209267003262694589681579975586953211412071105121089654603793742197186396425941444704187090247076175356602233639012126380151539999683100113614840260920973395044744793339033548461315328143136768198086484760409425190549236654975021363518716445677658761961443001795058886567461933927205985848910024019159414025690103526281502031528271859072759926786336442550713428295013055453684743025520473824756134591507452544252323600262492712677830428116242754169379006006420023968009526818148092031226736826929838582279710819507370531206828526427670184928760510402702113597804183609995598675557718086688165733040570828803316239454524351235801624686341874475266272115435424357549550931112503847588179528636082409371694104322026749094253816190542078934330604849168784051008748882272288156986931286076148593692885234288387212203591601542609480653788429339028948029854736272820387649190089281099448603455857341435873844515079010246994530085048230184407775304623128250888059113057761774714428286408349552123113385225279708004042993765657435632018611066823161435791216769167420081158424931227035477844504449612791781271465855631269930432025570744617325707562573914393137894697817086586359390750498089498357497291343937686842129341762178206464871374265869135073468769363596490612596869983888319692353276522141079955864738102666333148541241669568137277636574021761989497791982255033205899651162201393087403404407055622106314483161705812456468087725705859447746105970694963250058449202664891052211746868453013055068391201393731367675873647391330586026824563472658730516970522161027731549566375109550422284767182978761868820690646759411829560458211668169808591201068992312186875456377892700950726101216313194905691877195407882223175194785037981866816430815482975941557013983486891448241467471251784752853605140941286866751743572065601944511442802475059455051775330210017356645407185243031183952504597559493965646979476476173057207841065568994994793937421705383743660226441581731703626562409546979743234465783949801785326469441010575939661050122629555528443850785448422143562477459001145515172511335453450477885452116961771024116352673870598778684891510655907603507516206587327813064008009962184015991118859395028771960193285951493599202449441051810449149012190337881614665279481191319886804003749961018298840403344107221175731628573605966531568783149715569933029753552517336203895087560857875694267743136822241616415294063152879555893584846562283706098388500284220049527448567246922166014147323431540924339116852219338587096520990248195775604246420087096479731106848289110753580534703119895782269966124026325471677749597060785066522360958038367782154481475333718356576532963184400850233131789682610220422486927590619725646126009175196084172276162969704978016957711689593321889947425812884710610831384508881613876999006386085577710677013654460629267932425881046708914981805496295098668247645671236742297124254956823779266908971435310034039834801388201398488078775437248709321137023351513825022013012569622704478584199594876528625788899383753305992588318697575136670661642406494811279834463205754569271942672540651775126843010049076368831219982129370479585815604903422229490656802016513064954352505561084281123809530181857754029137921186001665035638998243584023427148811213933758575375343459280576502085571340176385189515170809761728694575982202577166021121122601523447436232584753201254959528914179305680811341891116606019593885054016351144649660107871037167367838388904537872703071014437560869110806802484190506785901630919165004081342968338789706701347601339138067512658001325271648559309677687141458802343392222661322808369691301769338016790179543310607187390804472570515606161528385819065489546058792108735866114368922921480656407255082652885118522606130927440205579021408499758119343756600659542437950710687261335166151453262246052736776153995081787916144758713146509700062684875467923291053247933458375148273043699994669190518277172627163435691441776040188638928653047446008321546161852947941072532327825569076688833255817988866049612158524481108116587726857603787391599505898144947444302798194375131068494440622481921527951431078383956272433012170380875093736974368923940435469360747865658001198887718743214213553550354250733008045221035889399308225595974797713154304107162994226204923473876542110357711441908239049320252027837593836066139026773190817572405516857462283048203009650479315997785529815729085831946829433522034720057450595100108042864044677965884710616525455561591426340112955604055415814269782295231053462789338003126922961557469885814082956433092326792197830320283371449283779995149871369096543015032381733054573902241253401418258480443179817354340052977057568002034210555318685955621774164266246099084546607924017473642084765316393679995317662869526336567375285853955054834064724648254368268542597739216991750068141231348067382896365201190510740889346868016470331611083957127814423476956667640521480472588956406609769957344882107895879933548588028684514941944090434563515370560452602911802863844960064326807338561907428229008302402648840896265634455714833359413406118419992703084543552963626644062728810895836076663862269361463308176949806780449225536167151607906593289992223301046522624246444686525182167363730331764400508948645824428051512194440523317091247503940242391752395346096339141991453791120835671132198372958623508026405587924214129948590318483103546565538269256779363231210550918679084205866739643649211699142080970135406171123471781968634444374192154495169887989822147319160308764651480446252553876239073189617551344422234632684833167133499088540711017459730271950318610310764051226143177730309325805672191972244951651344399407399810601062169485649645601860397591513191790184403850926164729829069279683875567786932879181164708629307915448695632321830387040854675040626413180060282716993289512558166080123767782745509570520485708894197430059559576795904953272491286716092143674736841623797873907207471346550217633262098271849290090416383023708056178011978703249351229284789809148221484487113586270341462637758898833018950486681579511105051660433507951683858658803458688036780573770865416748425704617024117018785802158695961928235058189582137998979926685541279411417280951471559005488902904151507215435638804701891899725140399348583738981496255580907819854986108466122137405005517191016675449365593942345166280478060948028671367545796054311470299415263917203900224483500548133539923657742573201271600277727369424649252744744364196861058509854088199152129938958948508103036678513448306491587175472990050530339683093752294720671518770940965062900942695561712221779865019744393814898996368858224727236998957162678757251576663346012821012428740753453787697108116698270649547509271631355284817438457082641123052790666977322324952451127620347192907686502861130151856971613390791104093891957152770880601351844997670985963282873704425419571181284644626808498076276115110707947552991346770174844672305435281095620778642660770856896448546907461226882432142250599083138514229132655875558485884167588702805282447237454852547973062684593628154761393486945750038659699871735506781875656192127980068395770625382697111645666630422460527121459731970181946211285336181105218922651071711603292275513016778970649648196418047920845647726839362627804558444451328738370848599528211714299493106354707520380415297458293204922893123723496424953667092594630429047471682722846452068475740777794415408846961062023585985801376937853798889033465413272538628428393800865297106330526004950123809872958837437509709433979431697222097793683513769167911303795034439109251458549146373207823486830838898534971600104582908569065806982035629110840182971336150651746824884202994457201256266689229304069366654181597953029714757121930300892758114162854542134498372611006962194763572085063508065990250558560712185085899953304514884255128309936244621863935353055126086858821576076151143004705810867767580034147949170260357479934228431473368419336747806252655063915771777343438700669360893570777211389260787037314774380356089744384416667436088989822126896787593153941056573832591965611620935089793880042996197593466836800592209964968493346523100555055618913138205339148593384166288069069146842882194328701349705316120972524276151313400050248482452279270894000771914845792811267636291804625180428141590092246338602922038481491001506476249497992607392276028248384815243924854593569577516949522875974263150518516454379636188322834336105982237793105719987686703285956574545804772856601386650241858665495981426020674047654091236747872075390590283905457396806523800449804044436992724801489692839054581170272919437193533116005494892430094921338991019576349610309939008352891240778871844647368036327562442211533737960342540700941549458147937934880271991688218258444161291200304930286293817414639696820364417276367565793544672674424967656470246784514099040109343075090088959820283222717911903144109444929552801540125095005487317651217092937184190501978960039331842141700319791801039560882236837022383831320084374221339286719375807902961826503773432358880187850067118300520734505374702254206881120475015292788516043788300354769580256627000750206849287626902417465428610143959088826828492424879105256762315822917670973615767636440880816667981359597053755101520061558955692326624792215814927143510966508793772336163164896888697201235759567182805186232330168841963424466476498487311920021734923106095777917560715380362643775450335710556152139447468673257948568101756195382541120447317917136590700643679568504017148459330588668054213150426985701309066796352565920605932391273533032664971820670715632432925557315826860856945568322904725681916877888930453257748627745028456925125030639693605461543420383066917787401390099900559348481408689249554895599957549968028208442091131063640921762263644963370468886575744335526299329568081972718960142053341324816604827709385343468868280169630836959709616297381652256123527093068511113399045370065745104288217790443503422500548379444893377266487021949190378519467246750944812491380556893065485503962004120249154604767901794187013223491718771679240862650315294118137686181197650068698332353960648150270760120766075224921995474202921691439121093450176734578797615110330881740387204901841571295942384226495457546011927448936513714958518953876751671395166393402154949582982713058882264511946489489396061124038294094621709671848400089155683748809396033484889672992951052560492674388434622130088188792390807759884753194980636842296379250749190480735669166718915741229966724993630286691976743396525105074597270868094338373841007262108994576920815822395477387158924980780460111294769565509693240899171953715972573102312754040888312803440079332264346977364363348627495737015371296313965702248837301268007144574753055554700805215242075470234469633185223532601816601584512659424973562668734293623603883876193943483775589936576206609035212585919732672500195264234159913847887627494495389638340822217744976628973783333469970393757159696723634721798337967077037614690676508537579136226679342081094385983066288255672913866331247808218486452761618576373293724169697529430324447449814160493083898934001038863604547286092546896052076656543097155722455440812131223558957360042912980081960108731222349199482811945325110807526826258721622970663253478082164982160623174991973508532296861175288577304786772654189064238810181579325965095453986230810285515784304272550939428439988736607061122082038882501843535893212840407005807035170765463548941147155905541567022313715571374459096047467920374500371846778319838287067009145773415963030808986155940819730764522129347903166485256438452262952232275065795855448872870372299995601217003016760532957468143542746440101205214506632129585687717214129526133160043681404021212854339506910597490269373630246768138827437213319943361548243229845415331846589306939678454842592264589421276750252260649878179427666465496710314539381918743877108488755645441688157369945201446101328316464247170324609847442283878056663836480746357945691481690430104280348603373736426078744034517838398117248118097007875510414309332796169191477307459165847540915335819431325309767922419078141773660807956370041702000358773660291791626328838588549160387901287349170856312667618545342559291476211043173613330014476394771226001359365285585935680243829439968768696936126200741866048017249336858521645532291920304943395203151824640564310720236164427320683926417116968673972982144905557517125851753056271197641028247327543965780306874501783769383649948343868541712825471896625778533981943518726530325590948955291534829623740576699202188505171797181406048987637109290432271151746693273269885785541960588118337705201010626905033230550746451768455455972028791324082362345252715992565424875058326036620993404469855407136964591966540475858008861082053021428102108237333997343378832409054369959752627985170797081106533680324185718238294331999160627401856475740813981067052356257612780741320517965016853846805767091267067204140222146945869910522653689759182686638602106607109797635772118745807608346019182140235068503374553991369875122606772194151764794587779887977380061442525874954275286830197111502375710863213639794812304774166104706537558449530017844556309993257868747624593571886418944563102288970658709522097233731758695516986976053559151906297566199824609142910230581144076250089447657124950696863863787857276609258583736738008397588768514830741963483803795041670948306923026265255646195581263127579397159297250883996882019982090763511511112380712289692252183918039284648721880980884059488175731438352000746393528726782414853127304157259620574677114077493655514523674657790121949018603645340464575893756671349003263079753517607950219186818923172436335646692391039375038978372450593643837371830587211399812979275192292064656216492290615456055490812735884753203178357078789845354362688213559825146018854617737323994104225343754730593497306934524202750723077470162001288546194893398444041637548258216813290162508733156083002671430420267217805956426206600729663087661050326656721961569089164429345503598071955105712003410034469145912068475920310551563060747701254020292155538520318893538517248249342351263171201457404401815184731538239973271431419162642651740615156025703351017997483807655277087412390388756464773496935057903948231611577924884460813298044863117654800119325047011973359591490355658589354550459740648889076977060530569628988261384850311369981461313062180756166243059577422966482650168376058925469497916473139742095292353391435684228103527497344935116742512873630981794214505348251914021779534608464476404947846516161659055528284406014753580829174877646373473790867011691245796977123342638579425390906408331251261505807409407441171820662834003821034242866655096151609352326592014085453417587380983061588329860360270798232989994515260157379171709692709179621020130409051561356916275654811908533997044066422819511638228478539701347157494650822393817414072703205484339233664608579959334382787650330218588031110129659299084561667649781939477654102066183922634496367473646976644762395843410260425880222399222801739779216419111726162189114873143558627356137389925722982661440361533072618699111597482876077734422096329132638750082356791817928612659316927800025684466344357170422110416227304119313343042893934695504140026758275933099832305758658655744137168952972873045338410353843530141962794628617608614362488224343838514074431825624242802602973000768678835210348018973750463001444765557725918134394621777148871419642598972371506321131157749660968647513195379974603881589972665880616132615644486632385713646332600083012553532905191261191839904117368792720318318404598245374341611288656962531387298160116162865136592179728010239693995725224189627577203546918923431724375995980326611400585095194265710680073053527774978036628447063710489786082625166304067606585282671567671177923555616306504463400863889846108924670815566154996923829584366250643923929097228722737070085667258133005570613272300716700105831925631950715548941816962116410571160916969632918546666153154435689569231249390148625098788095499192891156812566808008494374297323608849190735831127404021604825712520107796060754386549794778317420154982371211892095585466633814451825865607616600918026530374627543459818508253044628700376735617338364481020553252660666410271328444576667031406342635169739088277358687277840939596449133874154959769755234672622469951739020089596388616596707891392621327692872947349946386991458251052808698311589082939618749638142738745883802549884528114504765670708585342634375113730864202562541395632870344342339630703021918520300069646729901328330114198033428351107057927618996551077944195858995409031572692794349168458557376544341469961004480517927650119149591961675824675888355714453519269431104524198196980397072993790814618847281396590208466793814303599577001529117610953790621377724793788572135482088706164930855021187889851555993619226825732695354193436024490612419300956235403254308911419445365188399322087409693256502301654300112082215154132780489940346926725719502829723896339181855898672176253941979499478754309952745626238944022772407189546176217869185104515816482035038321824433129703795466870407673871034265447849803425279965053936832173022953268874463157029733535425483936626708466491415287841045638791699546305783618593218521266079660106574936929950307014188287645645757904232715794155332096292785241458633175214743256518169910527454346253068609038693236227944044286568779312468419880048262480178155416558699983059766532778523004577882988255847299439415300576118755447030275053614899673476295415587704059808146346969546985677047183559000052618572352919725224004595477854370843164615455632154686765265301400002466871062776644717875174730108729516029245135474074918911706512495334452103909694991856151303271620193713089570832191961995555167900021392788651006876153064022748821767145703757239002579037799465285836323526312016968499211954237360782204094847456315575658227834156792230218143689910207360455182324360836908090848967712281047828728341765399162472454142171283595408480601338609002401107447368765400067281109255646983906284210324150592496198473922418925774600461385065943608569356262481819321559559606884490307960328170544425727322094854304301659180904624296530902754397184811904409003995190687677791172000940469707827418335517063326999118458155436008707768689337518486855658839180770016690236319271740281254317160893167693842047507029860751747821126239429965663495444278046513208494729403825410457138951100869754525622825348992688053916164536996628180107785536690428287968987428156674247453202884746500592336775308380290264184704771944575960527323014582358446688352494398619602720492863413938168231527689109008830203810641886815170405975249988038527399694990501350029911795964833586053644302261264951248935730528386406836651056512755195723625074708775242295606167858812548889288963313135832866542780345611458016845748856480408069970168245190063547357862318672230849767388560492363574880260657628615388617694170259866366081066213475741030247649788140132742799630046881682223600631202605933280502439034962797867069095605180481795112736356854786046862154458118402294274699505589594331238448338978501712334451143588405122130339725201963387094894741389255821040013511795550307906252345389322446607947947306455395512524730733023307583640363624530180813419651216102760949719012476037421543136702756610468208938803207635535241260969649747922179785573008125903958875078584009966127761848167525590108443099054471885272432628491960279848761419195356090671982748725699145255212763043443774568958376161814276509028448262628071513604693614205538900840825855141043344963147724727832831358376709634045612118944786466524584766974363657836743423470845732998491923464851483721986758087409381485887848694643489729283130181561191188884912977060388343597769408510772189516385930828873555037295271016049708422353187339884202748978911496383448704818675541801810282593406307605630733618488017938102444911093981899313620004669728763947298609535492041592844395982777052793051987656433677004714647464538144410850136120327140565548965352996002252384576132198289646152839437762209971666558833499174126840109777285034352672538426923439475285994634411383536750857851559910104159125880126983046590463203694114188427250296387015082377218295894792178907642867370014278518279972901708366695435855377254073916196600406960335940058484095336199080272528872344866286954351983782121878422562056645116552972364284072487792908740401223163192894877286020704520315430728509924898414026974867865046916275530172993912777822973284478418261262127981960985554683647278145930839420545339053912749582240221734553040033731399764451529694083702995262427382788759435667166867372746301037533753869682190272407503262820116781571783974645169263749384705005708118125386046194205632126451602067632675458928711287272090112757021757070443282255452536524629053005983394605207042888386942916615138004141518381549665565333081527569006646095205903028291295055150994074988079889275036045744923369130120117264952673253930364947895258780179236503041893106291851365915800851948599704435714872399540391530522640329665708945718595179118551136033953192751575153571118613159107827329614001209248056183060684011834549944212599657232733804697186356095282547323731582329026070239736280805606842432900632951006655299827016492670623687183227636944247489084484894273900190402474413559034122758765292572542951271011003667591774018090351021415871086738099632606493993272529102595859990848132640557205928722161752899630755355940506396844334293300732005638023944163291667785937695293509851829935818201267818734763990841058027662493091300051744313256403699495722242704321489204217027340498372564683880138059901547899139373850072442970304692567275004716628508537656552838036464545425260609934502165094223478737136891614499045771064616302043106738838086665288182806443216381488495887220932166968325949365996210074210579453933288433291438338905571218953437015948912129915937718215660796569105118545502657336039054339930475841108839655776652355498696326406026779631676021809477237505469676161096667151687100601478319293953610954902867440013660991330452304788337343264293301232223401434599748320423427419652788732085024973648898017442049168361262410300486882827516765111028081745714864180754557142084000779748524262606941294364598852980347215487607464550385157778357688416677530462558077654817661394770751683150609145026587663478581646403323294960211200508076597210522630903259643765706350008552696654854137328120487251658667333009537933875482912970119003138196183385352800952356219251816323639662185200696144998190646781785828798437745297723941268405801906391341477959292789152929174146027771771389870573597197597460902544456788509492826957379166054187656206662920023415431670938553961657865995252308368995871878053396666152773944568698359236693675940575758406479439960312344935402017894856567695111808164742620076484331484521772365754981927025912025524776617591608823444606704739076046868834577791050479350899436152268154017245146355360346722189891989678455880538311697474998724766895450697069702079332770700829902319383997674914613785361285099877381654261265734353618410182576733662131845901116532938100777604355482396034616657517357311655137122669093371523275734751285273446572917718824427310925632844000374893553955641150824098227857012554239923615206770105458570065595800306845158296384896658407116181377712916444801753060779475815646342458308212289196119780546374077596622428653270160932080469004579175020295661852818507824368137935941485183252249527382370756282483849984341801785777355200817260291169868969516604018739739404935268907266930545213664317948868920818119669500643793917762033361328988112062948108043359020337810291214472670262194918943033930471651100808580533712538155380793152663776983478119598967635875967900819744523724169287059283752368298649716365939797687241255611187288264623421940350570425799549617876842026622710723236322355996625927568454575034061254120709054109667259499134808246863678229383327581298918971663411218811497436022607778772233603362585704985583978667843783843851240999192344714649314721834161362975157438870286424970877525558214631803576293751857055716806127621968926945969065325996736330161864973976021982257220995271340952918996306033429446406154705469893441474965001152845571582234133232686806125709727734405424567069614063898443697305422806536540250304222201338418863684361115577971864123195085532391581941442236571542060053526948779713543972745708306970807808454750871893113585184432510242696867901826286615464088831937159783948522488749153777468585160706081127380550976328496335951267978587448073787679501073112364783921016088474148263807043808533875891657601756293590602750140477192518249744508930604047589996226365071286064141984198163359811282088659626458959623859260762381751956900746678987223692354221712874944449867183210122646576703983928946967922128895920220530781457441606451166734630310746277007468660424251591779747213712331132262187526958625358151747355224585121089828651387582620271364936089363398440751678139378341500855404929464842334718705194473953985674119598272290793873750434082262433688510304244044949004057759687440100296500161893530650680138787947052860521300873877779678985938886378872488478341039742073774686495948658632229684342479843783279364402046898837756882181391301998556625297194671670071819433944183283395227332620122248937194979206219410299973779586620644355059823431389035835501657253798722989243826491588192850087703277202992213776560829076990013220430084661056760785382846930263645837553918308769486372097337251719577668916344546941648879695978349787382758051042928087723017491649865717317075771708822912949363336575255667977312405781678047127151274140645888253736614616636541214834584221876701284844244874600867439991855357957656709669879273942999163805900790884207888393688292305069193896872699072322721761400191158746180415600432171429317939118751060728187669665527410751331389824604630861499040493534974176230650715755046817464113500459278330123546264295314584031020222565389808095869489388038472355513799502570042774300621927744897653045281486804115879438799187885503101504415281356974156984955505039223625129355873259143342939656275345669143199777770093286724199051088203301059628281461912973104145540390916969757572606752048462899481433104369906076309466527203580578630570552145610923151515834367676370449972617228460079332600414368732784214704556767197499746020813600907244105122641180528979379066543025360399014568501804683561431320625229331303542307205220445137402368391205081130274023979862136584805795614213251306309208979479109305354924683597396317000700208112350357184746417022932871757188878986472715992529473322298228568978728429606093747787539090876679818264618648091777022575255934899696930165051968294814752311225027841276243966134844503549739681585367937140315845000956140933269734536659370227203053136612850993197919717625541216243929296350019797710081251695009971566134879284580785650954295360356127660431443195355380451154828197488588809835913888203969293942202529711388038687028916270144238575047066668516723390067787793662693421397390211310240190255563934220450743508408689902834276865713038830342538936317378804010055439256409034283762966688545955209882170112445301028669592932451968253848234657187368969777802830448328575629515160113583837099292811867887588956822851840546453127101617680547442892874222301300521820373996341707092598891791643425261929431756021523752473519016498526841611719332464835569781728332610647709261039350762287280341963367887853643245024203113523903407060555582976886531768678875913960936123261422922844883883217947646348079952757466057230706779014127564775235442184806819595949970893683971271284340018349639990921254254193808910077056179275002954107230787116177706728495070280745564757124696901243955476179732823514775410073473249890822188264017806051627313968675874564368782696600855866239786461957475060941727664525132153813386464536364086114102386040170021107659186452088306453407618682982832678244342018405470933205304313869013542591195256774184415143193064056148397719333214005545031737959057433611236338599634232679734747398993021724933406107871107313472458883037848333598727316640583564747713109967893777352163202888867497227273790267469317345658550758252569946286488936934497849416664836931519544857946173195342303306025356978265407737746822160109555077347022420689732286492577907261111443302539628539543551n);





