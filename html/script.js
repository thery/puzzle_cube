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
const colorLocked= new THREE.Color( 'skyblue' );
const colorFree = new THREE.Color( 'white' );

// Our two mats 
const matLocked = new THREE.MeshBasicMaterial({color: colorLocked});
const matFree = new THREE.MeshBasicMaterial({color: colorFree});

// Our six axis 
var axisPX = new THREE.Vector3( 1, 0, 0);
var axisNX = new THREE.Vector3(-1, 0, 0);
var axisPY = new THREE.Vector3( 0, 1, 0);
var axisNY = new THREE.Vector3( 0,-1, 0);
var axisPZ = new THREE.Vector3( 0, 0, 1);
var axisNZ = new THREE.Vector3( 0, 0,-1);


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
var cube = new THREE.Mesh(geometry, material);

function getFaceDown() {
  var ax1 = new THREE.Vector3(cube.position.x, 0, cube.position.z);
  var ax = cube.worldToLocal(ax1).multiplyScalar(2);
  ax.x = Math.trunc(ax.x);
  ax.y = Math.trunc(ax.y);
  ax.z = Math.trunc(ax.z);  
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
  console.log(cube.position.x + " " + cube.position.y + " " + cube.position.z);
  console.log(ax.x + " " + ax.y + " " + ax.z);
}

function getBoardUnderCube() {
  for(var i = 0; i < 4; i++) {
    for(var j = 0; j < 4; j++) {
      var board = getBoard(i, j);
      if ((board.position.x == cube.position.x) &&
          (board.position.z == cube.position.z)) {
        return board;
      }
    }
  }
  console.log(cube.position.x + " " + cube.position.y + " " + cube.position.z);
}

function swapBoardCube() {
  var face = getFaceDown();
  var board = getBoardUnderCube();
  if ((face == null) || (board == null)) {
    return;
  }
  var mat = board.material;
  board.material = cube.material[face];
  cube.material[face] = mat;
} 

// show the border 
var geo = new THREE.EdgesGeometry( cube.geometry );
var mat = new THREE.LineBasicMaterial( { color: 0x000000 } );
var wireframe = new THREE.LineSegments( geo, mat );
cube.add( wireframe );

// The initial position
cube.position.z = 0.5;
cube.position.y = 0.5;
cube.position.x = 0.5;

//add the main cube to scene
scene.add(cube);
cube.visible = false;

// The dimension of the board 
const size = 4;
const divisions = 4;

// The board
var board = new Array(size);

var numberOfLocked = 0;

const initBoard = () => {
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

function getBoard(x, y) {
  return board[x][y];
}

function swapBoard(x, y) {
    if (board[x][y].material == matLocked) {
        board[x][y].material = matFree;
        numberOfLocked -= 1;
    } else {
        board[x][y].material = matLocked;
        numberOfLocked += 1;

    }
}

function isBoardSelected(i, j) {
  return (board[i][j].material == matLocked); 
}

//create renderer
var renderer = new THREE.WebGLRenderer();
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.render(scene, camera);
  
// Animation speed
var rx = 4 * 1 / 100;
var rr = 4 * Math.PI / 200;

function trunc2(x) {
  return (Math.round(x * 10) / 10);
}

function trunc(x) {
  return (Math.round(x * 100000) / 100000);
}

function truncCube() {
  cube.position.x = trunc(cube.position.x);
  cube.position.y = trunc(cube.position.y);
  cube.position.z = trunc(cube.position.z);
  cube.rotation.x = 
    trunc(cube.rotation.x / Math.PI) * Math.PI;
  cube.rotation.y = 
    trunc(cube.rotation.y / Math.PI) * Math.PI;
  cube.rotation.z = 
    trunc(cube.rotation.z / Math.PI) * Math.PI;
}

var rot = 0;


const moveXP = () => {
  cube.rotateOnWorldAxis(axisPZ, -rr);
  rot -= rr;
  cube.position.y = trunc(0.5 - 0.2 * Math.sin (2 * rot));
  cube.position.x += rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    truncCube();
    swapBoardCube();
  }
}

const moveXN = () => {
  cube.rotateOnWorldAxis(axisPZ, +rr);
  rot += rr;
  cube.position.y = trunc(0.5 + 0.2 * Math.sin (2 * rot));
  cube.position.x -= rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    truncCube();
    swapBoardCube();
  }
};

const moveZP = () => {
  cube.rotateOnWorldAxis(axisPX, +rr);
  rot += rr;
  cube.position.y = trunc(0.5 + 0.2 * Math.sin (2 * rot));
  cube.position.z += rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    truncCube();
    swapBoardCube();
  }
};

const moveZN = () => {
  cube.rotateOnWorldAxis(axisPX, -rr);
  rot -= rr;
  cube.position.y = trunc(0.5 - 0.2 * Math.sin (2 * rot));
  cube.position.z -= rx;
  if (cube.position.y == 0.5) {
    rot = 0;
    truncCube();
    swapBoardCube();
  }
};

var gx = cube.position.x;
var gz = cube.position.z;

//animation loop
const animate = () => {
  requestAnimationFrame(animate);
  var x = cube.position.x;
  var z = cube.position.z;
  if ((gx != x) || (gz != z)) {
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

function getSelectedBoard (raycaster) {
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

function flipCube() {
  for (var i = 0; i < 6; i++) {
    if (cube.material[i] == matFree) {
      cube.material[i] = matLocked;
    } else {
      cube.material[i] = matFree;
    }
  }
}
function onDocumentMouseDown(event){
  if ((gx != cube.position.x) || (gz != cube.position.z)) {
    return;
  }
  mouse.x = ( event.clientX / window.innerWidth ) * 2 - 1;
  mouse.y = - ( event.clientY / window.innerHeight ) * 2 + 1;
  raycaster.setFromCamera(mouse, camera);
  var bxy = getSelectedBoard(raycaster);
  if (bxy != null) {
    var board = getBoard(bxy.x, bxy.y);
    if (cube.visible == true) {
      gx = board.position.x;
      gz = board.position.z;
      return;
    }
    if (numberOfLocked < 6) {
        swapBoard(bxy.x,bxy.y);
    } else {
      if (isBoardSelected(bxy.x, bxy.y)) {
        swapBoard(bxy.x, bxy.y);
        renderer.render(scene, camera);
      } else {
        cube.visible = true;
        cube.position.x = board.position.x;
        cube.position.z = board.position.z;
        gx = board.position.x;
        gz = board.position.z;
        renderer.render(scene, camera);
      }
    }
    renderer.render(scene, camera);
  }
}

document.body.appendChild(renderer.domElement);
window.addEventListener('click', onDocumentMouseDown, false);

animate();
