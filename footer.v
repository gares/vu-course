(**
#
<hr/>

<script type="text/javascript">

function load_coq_snippets() {
  for (i = 0; i < coqdoc_ids.length; ++i) {
    document.getElementById(coqdoc_ids[i]).nextSibling.CodeMirror.setValue(
      localStorage.getItem('coq-snippet-'+coqdoc_ids[i]));
  }
}

function save_coq_snippets() {
  for (i = 0; i < coqdoc_ids.length; ++i) {
    localStorage.setItem('coq-snippet-'+coqdoc_ids[i], document.getElementById(coqdoc_ids[i]).nextSibling.CodeMirror.getValue());
  }
  alert("Coq snippets saved.");
}

function download_coq_snippets() {
   var chunks = []
   for (i = 0; i < coqdoc_ids.length; ++i) {
     chunks.push(document.getElementById(coqdoc_ids[i]).nextSibling.CodeMirror.getValue())
   }
  var data = new Blob(chunks, {type: "text/plain;charset=utf-8"});
  saveAs(data, 'source.v');
}
 


alignWithTop = true;
current = 0;
slides = [];
function select_current() {
  for (var i = 0; i < slides.length; i++) {
    var s = document.getElementById('slideno' + i);
    if (i == current) {
      s.setAttribute('class','slideno selected');
    } else {
      s.setAttribute('class','slideno');
    }
  }	
}

function mk_tooltip(label,text) {
 var t = document.createElement("div");
 t.setAttribute('class','slide-tooltip');
 t.innerHTML = label;

 var s = document.createElement("span");
 s.setAttribute('class','slide-tooltiptext slide-tooltip-left');
 s.innerHTML = text;

 t.appendChild(s);
 return t;
}

function find_hx(e) {
  for(var i = 0; i < e.children.length; i++) {
    var x = e.children[i];
    if (x.tagName == "H1" ||
        x.tagName == "H2" ||
        x.tagName == "H3" ||
        x.tagName == "H4") return x.textContent;
  } 
  return null;
}

function init_slides() {
  var toolbar = document.getElementById('panel-wrapper');
  if (toolbar) {
  var tools = document.createElement("div");
  var tprev = document.createElement("div");
  var tnext = document.createElement("div");
  tools.setAttribute('id','tools');
  tprev.setAttribute('id','prev');
  tprev.setAttribute('onclick','prev_slide();');
  tnext.setAttribute('id','next');
  tnext.setAttribute('onclick','next_slide();');
  toolbar.appendChild(tools);
  tools.appendChild(tprev);
  tools.appendChild(tnext);
  
  slides = document.getElementsByClassName('slide');
  for (var i = 0; i < slides.length; i++) {
    var s = document.createElement("div");
    s.setAttribute('id','slideno' + i);
    s.setAttribute('class','slideno');
    s.setAttribute('onclick','goto_slide('+ i +');');
    var title = find_hx(slides[i]);
    if (title == null) {
      title = "goto slide " + i;
    }
    var t = mk_tooltip(i, title);
    s.appendChild(t)
    tools.appendChild(s);
  }
  select_current();
  } else {
  //retry later
  setTimeout(init_slides,100);	  
  }
}
function on_screen(rect) {
  return (
    rect.top >= 0 &&
    rect.top <= (window.innerHeight || document.documentElement.clientHeight)
  );
}
function update_scrolled(){
  for (var i = slides.length-1; i >= 0; i--) {
    var rect = slides[i].getBoundingClientRect();
      if (on_screen(rect)) {
        current = i;
        select_current();	
    }
  }
}
function goto_slide(n) {
  current = n;
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function next_slide() {
  current++;
  if (current >= slides.length) { current = slides.length - 1; }
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function prev_slide() {
  current--;
  if (current < 0) { current = 0; }
  var element = slides[current];
  element.scrollIntoView(alignWithTop);
  select_current();
}

window.onload = init_slides;
window.onbeforeunload = save_coq_snippets;
window.onscroll = update_scrolled;
</script>
# *)
