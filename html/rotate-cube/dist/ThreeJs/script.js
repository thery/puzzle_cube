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


// The dimension of the board 
const size = 4;
const divisions = 4;

// The board
const board = new Array(size);

const init_board = () => {
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
      var wireframe = new THREE.LineSegments(geo, mat);
      cube.add(wireframe);
      scene.add(cube);
    }
  }
}

init_board();

function boardSwap(x, y) {
    if (board[x][y].material == matLocked) {
        board[x][y].material = matFree;
    } else {
        board[x][y].material = matLocked;
    }
}

boardSwap(0,0);
boardSwap(1,1);
boardSwap(2,2);


//create renderer
// const renderer = new THREE.WebGLRenderer({ antialias: true });
// renderer.setSize(window.innerWidth, window.innerHeight);
// renderer.render(scene, camera);
var renderer = new THREE.WebGLRenderer();
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.render(scene, camera);
  

var b = true;

var rx = 1 / 100;
var rr = Math.PI / 200;

const moveY = () => {
  if ((0.52 <= cube.position.x) || (cube.position.x <= -0.52)) {
    b = !b;
  }
  if (b) {
    cube.position.x += rx;
    cube.rotation.z -= rr;
    cube.position.y = 0.5 + 0.2 * Math.sin (2 * cube.rotation.z) ;
    board[0][3].material = matLocked;
    cube.material[0] = matLocked;
    cube.material[1] = matLocked;
    cube.material[2] = matLocked;
    cube.material[3] = matLocked;
    cube.material[4] = matLocked;
    cube.material[5] = matLocked;
  } else {
    cube.position.x -= rx;
    cube.rotation.z += rr;
    cube.position.y = 0.5 + 0.2 *  Math.sin (2 * cube.rotation.z) ;
    board[0][3].material = matFree;
    cube.material[0] = matFree;
    cube.material[1] = matFree;
    cube.material[2] = matFree;
    cube.material[3] = matFree;
    cube.material[4] = matFree;
    cube.material[5] = matFree;
  }
};

const moveX = () => {
  if ((0.52 <= cube.position.z) || (cube.position.z <= -0.52)) {
    b = !b;
  }
  if (b) {
    cube.position.z += rx;
    cube.rotation.x += rr;
    cube.position.y = 0.5 - 0.2 * Math.sin (2 * cube.rotation.x) ;
    board[0][3].material = matLocked;
    cube.material[0] = matLocked;
    cube.material[1] = matLocked;
    cube.material[2] = matLocked;
    cube.material[3] = matLocked;
    cube.material[4] = matLocked;
    cube.material[5] = matLocked;
  } else {
    cube.position.z -= rx;
    cube.rotation.x -= rr;
    cube.position.y = 0.5 - 0.2 *  Math.sin (2 * cube.rotation.x) ;
    board[0][3].material = matFree;
    cube.material[0] = matFree;
    cube.material[1] = matFree;
    cube.material[2] = matFree;
    cube.material[3] = matFree;
    cube.material[4] = matFree;
    cube.material[5] = matFree;
  }
};

//animation loop
 const animate = () => {
  requestAnimationFrame(animate);
  moveY();
  renderer.render(scene, camera);
};

animate();

var mouse = new THREE.Vector2();
var raycaster = new THREE.Raycaster();

function onDocumentMouseDown(event){
    mouse.x = ( event.clientX / window.innerWidth ) * 2 - 1;
    mouse.y = - ( event.clientY / window.innerHeight ) * 2 + 1;
    raycaster.setFromCamera(mouse, camera);
    let intersects = raycaster.intersectObjects(scene.children);
    if (intersects.length > 0) { 
        selectedPiece = intersects[0].object;
        for (var i = 0; i < size; i++) {
            for (var j = 0; j < size; j++) {
                if (selectedPiece == board[i][j]) {
                    boardSwap(i,j);
                    renderer.render(scene, camera);
                }
            }
        }
    }
}

 
 
//    for (var i = 0; i < size; i++) {
//        for (var j = 0; j < size; j++) {
//            if (event.target == board[i][j]) {
//                boardSwap(i,j);
//            }
//        }
//    }
//}

document.body.appendChild(renderer.domElement);
window.addEventListener('click', onDocumentMouseDown, false);
 
// var initializeDomEvents = require("threex-domevents");
// var THREEs = require("three");
// var THREEx = {};
// initializeDomEvents(THREEs, THREEx);
// var domEvents = new THREEx.DomEvents(camera, renderer.domElement);

//const init_listener = () => {
//    for (var i = 0; i < size; i++) {
//        for (var j = 0; j < size; j++) {
//            domEvents.addEventListener(board[i][j], 'click', 
//              onDocumentMouseDown, false);
//        }
//    }/
//}

//init_listener();

