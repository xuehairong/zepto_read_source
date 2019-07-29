//     Zepto.js
//     (c) 2010-2017 Thomas Fuchs
//     Zepto.js may be freely distributed under the MIT license.

var Zepto = (function() {
  var undefined, key, $, classList, emptyArray = [], concat = emptyArray.concat, filter = emptyArray.filter, slice = emptyArray.slice,
    document = window.document,
    elementDisplay = {}, classCache = {},
    //css中不需要带单位的数值
    cssNumber = { 'column-count': 1, 'columns': 1, 'font-weight': 1, 'line-height': 1,'opacity': 1, 'z-index': 1, 'zoom': 1 },
    fragmentRE = /^\s*<(\w+|!)[^>]*>/,
    singleTagRE = /^<(\w+)\s*\/?>(?:<\/\1>|)$/,
    tagExpanderRE = /<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/ig,
    rootNodeRE = /^(?:body|html)$/i,
    capitalRE = /([A-Z])/g,

    // special attributes that should be get/set via method calls
    methodAttributes = ['val', 'css', 'html', 'text', 'data', 'width', 'height', 'offset'],

    adjacencyOperators = [ 'after', 'prepend', 'before', 'append' ],
    table = document.createElement('table'),
    tableRow = document.createElement('tr'),
    //获取父容器tr的父级是tbody,tbody、thead、thead的父级是table，td、th的父级是tr，其他都算div
    containers = {
      'tr': document.createElement('tbody'),
      'tbody': table, 'thead': table, 'tfoot': table,
      'td': tableRow, 'th': tableRow,
      '*': document.createElement('div')
    },
    simpleSelectorRE = /^[\w-]*$/,
    class2type = {},
    toString = class2type.toString,
    zepto = {},
    camelize, uniq,
    tempParent = document.createElement('div'),
    propMap = {
      'tabindex': 'tabIndex',
      'readonly': 'readOnly',
      'for': 'htmlFor',
      'class': 'className',
      'maxlength': 'maxLength',
      'cellspacing': 'cellSpacing',
      'cellpadding': 'cellPadding',
      'rowspan': 'rowSpan',
      'colspan': 'colSpan',
      'usemap': 'useMap',
      'frameborder': 'frameBorder',
      'contenteditable': 'contentEditable'
    },
    //判断是否为数组
    isArray = Array.isArray ||
      function(object){ return object instanceof Array }
  //检测选择器是否能匹配元素
  zepto.matches = function(element, selector) {
    if (!selector || !element || element.nodeType !== 1) return false
    //自带的matches方法兼容写法
    var matchesSelector = element.matches || element.webkitMatchesSelector ||
                          element.mozMatchesSelector || element.oMatchesSelector ||
                          element.matchesSelector
    //如果有自带方法直接返回结果
    if (matchesSelector) return matchesSelector.call(element, selector)
    // fall back to performing a selector:
    var match, parent = element.parentNode, temp = !parent
    if (temp) (parent = tempParent).appendChild(element)//如果没有父级元素就临时用div
    match = ~zepto.qsa(parent, selector).indexOf(element)
    temp && tempParent.removeChild(element)//如果临时插入了div的还要把div删掉
    return match
  }

  function type(obj) {
    return obj == null ? String(obj) :
      class2type[toString.call(obj)] || "object"
  }
  //是否为函数
  function isFunction(value) { return type(value) == "function" }
  //对象不为null且为window
  function isWindow(obj)     { return obj != null && obj == obj.window }
  function isDocument(obj)   { return obj != null && obj.nodeType == obj.DOCUMENT_NODE }
  function isObject(obj)     { return type(obj) == "object" }
  //是否是纯粹的对象
  function isPlainObject(obj) {
    return isObject(obj) && !isWindow(obj) && Object.getPrototypeOf(obj) == Object.prototype
  }
  //检测是否类似数组
  function likeArray(obj) {
    var length = !!obj && 'length' in obj && obj.length,
      type = $.type(obj)

    return 'function' != type && !isWindow(obj) && (
      'array' == type || length === 0 ||
        (typeof length == 'number' && length > 0 && (length - 1) in obj)//只要有length属性且大于0且有相应的值
    )
  }
  //过滤数组中为null的
  function compact(array) { return filter.call(array, function(item){ return item != null }) }
  //转换成
  function flatten(array) { return array.length > 0 ? $.fn.concat.apply([], array) : array }
  camelize = function(str){ return str.replace(/-+(.)?/g, function(match, chr){ return chr ? chr.toUpperCase() : '' }) }
  function dasherize(str) {
    return str.replace(/::/g, '/')
           .replace(/([A-Z]+)([A-Z][a-z])/g, '$1_$2')
           .replace(/([a-z\d])([A-Z])/g, '$1_$2')
           .replace(/_/g, '-')
           .toLowerCase()
  }
  //数组去重
  uniq = function(array){ return filter.call(array, function(item, idx){ return array.indexOf(item) == idx }) }

  function classRE(name) {
    return name in classCache ?
      classCache[name] : (classCache[name] = new RegExp('(^|\\s)' + name + '(\\s|$)'))
  }
  //如果是数值类型就加上px
  function maybeAddPx(name, value) {
    return (typeof value == "number" && !cssNumber[dasherize(name)]) ? value + "px" : value
  }

  function defaultDisplay(nodeName) {
    var element, display
    if (!elementDisplay[nodeName]) {
      element = document.createElement(nodeName)
      document.body.appendChild(element)
      display = getComputedStyle(element, '').getPropertyValue("display")
      element.parentNode.removeChild(element)
      display == "none" && (display = "block")
      elementDisplay[nodeName] = display
    }
    return elementDisplay[nodeName]
  }

  function children(element) {//获取元素的所有子子元素
    return 'children' in element ?
      slice.call(element.children) :
      $.map(element.childNodes, function(node){ if (node.nodeType == 1) return node })
  }

  function Z(dom, selector) {
    var i, len = dom ? dom.length : 0
    for (i = 0; i < len; i++) this[i] = dom[i]
    this.length = len
    this.selector = selector || ''
  }

  // `$.zepto.fragment` takes a html string and an optional tag name
  // to generate DOM nodes from the given html string.
  // The generated DOM nodes are returned as an array.
  // This function can be overridden in plugins for example to make
  // it compatible with browsers that don't support the DOM fully.
  zepto.fragment = function(html, name, properties) {
    var dom, nodes, container

    // A special case optimization for a single tag
    //<div/>优化单个标签
    if (singleTagRE.test(html)) dom = $(document.createElement(RegExp.$1))

    if (!dom) {
      if (html.replace) html = html.replace(tagExpanderRE, "<$1></$2>")
      if (name === undefined) name = fragmentRE.test(html) && RegExp.$1//标签名为空就重新定义下
      if (!(name in containers)) name = '*' //除了containers中的标签全都转为div
      
      container = containers[name]//根据传入的html片段，创建父容器elemnt
      container.innerHTML = '' + html//将html片段放在容器element里
      //用[].slice.call()可以将其转成数组类型
      dom = $.each(slice.call(container.childNodes), function(){
        container.removeChild(this)
      })
    }

    if (isPlainObject(properties)) {
      nodes = $(dom)
      $.each(properties, function(key, value) {
        if (methodAttributes.indexOf(key) > -1) nodes[key](value)
        else nodes.attr(key, value)
      })
    }

    return dom
  }

  // `$.zepto.Z` swaps out the prototype of the given `dom` array
  // of nodes with `$.fn` and thus supplying all the Zepto functions
  // to the array. This method can be overridden in plugins.
  zepto.Z = function(dom, selector) {
    return new Z(dom, selector)
  }

  // `$.zepto.isZ` should return `true` if the given object is a Zepto
  // collection. This method can be overridden in plugins.
  zepto.isZ = function(object) {
    return object instanceof zepto.Z
  }

  // `$.zepto.init` is Zepto's counterpart to jQuery's `$.fn.init` and
  // takes a CSS selector and an optional context (and handles various
  // special cases).
  // This method can be overridden in plugins.
  zepto.init = function(selector, context) {
    var dom
    // If nothing given, return an empty Zepto collection
    //如果没有参数，就返回一个空的Zepto集合
    if (!selector) return zepto.Z()
    // Optimize for string selectors
    else if (typeof selector == 'string') {
      selector = selector.trim()
      // If it's a html fragment, create nodes from it
      //如果是html片段，就创建node
      // Note: In both Chrome 21 and Firefox 15, DOM error 12
      // is thrown if the fragment doesn't begin with <
      if (selector[0] == '<' && fragmentRE.test(selector))
        dom = zepto.fragment(selector, RegExp.$1, context), selector = null
      // If there's a context, create a collection on that context first, and select
      // nodes from there
      else if (context !== undefined) return $(context).find(selector)
      // If it's a CSS selector, use it to select nodes.
      else dom = zepto.qsa(document, selector)
    }
    // If a function is given, call it when the DOM is ready
    else if (isFunction(selector)) return $(document).ready(selector)
    // If a Zepto collection is given, just return it
    else if (zepto.isZ(selector)) return selector
    else {
      // normalize array if an array of nodes is given
      if (isArray(selector)) dom = compact(selector)
      // Wrap DOM nodes.直接包装dom节点
      else if (isObject(selector))
        dom = [selector], selector = null
      // If it's a html fragment, create nodes from it
      else if (fragmentRE.test(selector))
        dom = zepto.fragment(selector.trim(), RegExp.$1, context), selector = null
      // If there's a context, create a collection on that context first, and select
      // nodes from there
      else if (context !== undefined) return $(context).find(selector)
      // And last but no least, if it's a CSS selector, use it to select nodes.
      else dom = zepto.qsa(document, selector)
    }
    // create a new Zepto collection from the nodes found
    return zepto.Z(dom, selector)
  }

  // `$` will be the base `Zepto` object. When calling this
  // function just call `$.zepto.init, which makes the implementation
  // details of selecting nodes and creating Zepto collections
  // patchable in plugins.
  $ = function(selector, context){
    return zepto.init(selector, context)
  }

  function extend(target, source, deep) {
    for (key in source)
      if (deep && (isPlainObject(source[key]) || isArray(source[key]))) {
        if (isPlainObject(source[key]) && !isPlainObject(target[key]))
          target[key] = {}
        if (isArray(source[key]) && !isArray(target[key]))
          target[key] = []
        extend(target[key], source[key], deep)
      }
      else if (source[key] !== undefined) target[key] = source[key]
  }

  // Copy all but undefined properties from one or more
  // objects to the `target` object.
  $.extend = function(target){
    var deep, args = slice.call(arguments, 1)
    if (typeof target == 'boolean') {
      deep = target
      target = args.shift()
    }
    args.forEach(function(arg){ extend(target, arg, deep) })
    return target
  }

  // `$.zepto.qsa` is Zepto's CSS selector implementation which
  // uses `document.querySelectorAll` and optimizes for some special cases, like `#id`.
  // This method can be overridden in plugins.
  //用css选择器查找相应的元素
  zepto.qsa = function(element, selector){
    var found,
        maybeID = selector[0] == '#',
        maybeClass = !maybeID && selector[0] == '.',
        nameOnly = maybeID || maybeClass ? selector.slice(1) : selector, // Ensure that a 1 char tag name still gets checked
        isSimple = simpleSelectorRE.test(nameOnly)
    return (element.getElementById && isSimple && maybeID) ? // Safari DocumentFragment doesn't have getElementById
      ( (found = element.getElementById(nameOnly)) ? [found] : [] ) :
      (element.nodeType !== 1 && element.nodeType !== 9 && element.nodeType !== 11) ? [] :
      slice.call(
        isSimple && !maybeID && element.getElementsByClassName ? // DocumentFragment doesn't have getElementsByClassName/TagName
          maybeClass ? element.getElementsByClassName(nameOnly) : // If it's simple, it could be a class
          element.getElementsByTagName(selector) : // Or a tag
          element.querySelectorAll(selector) // Or it's not simple, and we need to query all
      )
  }

  function filtered(nodes, selector) {
    return selector == null ? $(nodes) : $(nodes).filter(selector)
  }
  //父节点是否包含子节点
  $.contains = document.documentElement.contains ?
    function(parent, node) {
      return parent !== node && parent.contains(node)
    } :
    function(parent, node) {
      while (node && (node = node.parentNode))
        if (node === parent) return true
      return false
    }
  //参数是函数进行处理
  function funcArg(context, arg, idx, payload) {
    return isFunction(arg) ? arg.call(context, idx, payload) : arg
  }

  function setAttribute(node, name, value) {
    value == null ? node.removeAttribute(name) : node.setAttribute(name, value)
  }

  // access className property while respecting SVGAnimatedString
  //添加classname
  function className(node, value){
    var klass = node.className || '',
        svg   = klass && klass.baseVal !== undefined//如果有baseVal属性说明是svg元素

    if (value === undefined) return svg ? klass.baseVal : klass //如果value为空的就单纯的返回className
    svg ? (klass.baseVal = value) : (node.className = value)//否则就设置类的值
  }

  // "true"  => true
  // "false" => false
  // "null"  => null
  // "42"    => 42
  // "42.5"  => 42.5
  // "08"    => "08"
  // JSON    => parse if valid
  // String  => self
  function deserializeValue(value) {
    try {
      return value ?
        value == "true" ||
        ( value == "false" ? false :
          value == "null" ? null :
          +value + "" == value ? +value :
          /^[\[\{]/.test(value) ? $.parseJSON(value) :
          value )
        : value
    } catch(e) {
      return value
    }
  }

  $.type = type
  $.isFunction = isFunction
  $.isWindow = isWindow
  $.isArray = isArray
  $.isPlainObject = isPlainObject

  $.isEmptyObject = function(obj) {
    var name
    for (name in obj) return false
    return true
  }

  $.isNumeric = function(val) {
    var num = Number(val), type = typeof val
    return val != null && type != 'boolean' &&
      (type != 'string' || val.length) &&
      !isNaN(num) && isFinite(num) || false
  }
  //等同于数组的indexOf
  $.inArray = function(elem, array, i){
    return emptyArray.indexOf.call(array, elem, i)
  }

  $.camelCase = camelize
  //调用原生方法，加了个null的处理使其不报错
  $.trim = function(str) {
    return str == null ? "" : String.prototype.trim.call(str)
  }

  // plugin compatibility
  $.uuid = 0
  $.support = { }
  $.expr = { }
  $.noop = function() {}
  //遍历并根据回调函数，返回新的集合
  $.map = function(elements, callback){
    var value, values = [], i, key
    if (likeArray(elements))
      for (i = 0; i < elements.length; i++) {
        value = callback(elements[i], i)
        if (value != null) values.push(value)
      }
    else
      for (key in elements) {
        value = callback(elements[key], key)
        if (value != null) values.push(value)
      }
    return flatten(values)//TODO 这边不懂为什么要转一下？？？
  }

  $.each = function(elements, callback){
    var i, key
    if (likeArray(elements)) {
      for (i = 0; i < elements.length; i++)
        if (callback.call(elements[i], i, elements[i]) === false) return elements
    } else {
      for (key in elements)
        if (callback.call(elements[key], key, elements[key]) === false) return elements
    }

    return elements
  }
  //等同于数组的filter函数
  $.grep = function(elements, callback){
    return filter.call(elements, callback)
  }

  if (window.JSON) $.parseJSON = JSON.parse

  // Populate the class2type map
  $.each("Boolean Number String Function Array Date RegExp Object Error".split(" "), function(i, name) {
    class2type[ "[object " + name + "]" ] = name.toLowerCase()
  })

  // Define methods that will be available on all
  // Zepto collections
  //所有zepto对象可用
  $.fn = {
    constructor: zepto.Z,
    length: 0,

    // Because a collection acts like an array
    // copy over these useful array functions.
    forEach: emptyArray.forEach,
    reduce: emptyArray.reduce,
    push: emptyArray.push,
    sort: emptyArray.sort,
    splice: emptyArray.splice,
    indexOf: emptyArray.indexOf,
    concat: function(){//合并2个数组
      var i, value, args = []
      for (i = 0; i < arguments.length; i++) {
        value = arguments[i]
        args[i] = zepto.isZ(value) ? value.toArray() : value//如果是zepto就转成普通数组，为了调用数组的concat
      }
      return concat.apply(zepto.isZ(this) ? this.toArray() : this, args)//把需要合并的数组转成普通数组，调用concat进行合并
    },

    // `map` and `slice` in the jQuery API work differently
    // from their array counterparts
    map: function(fn){//包装$.map方法，返回的是Zepto对象
      return $($.map(this, function(el, i){ return fn.call(el, i, el) }))
    },
    slice: function(){//包装slice方法，返回的是Zepto对象
      return $(slice.apply(this, arguments))  
    },

    ready: function(callback){
      // don't use "interactive" on IE <= 10 (it can fired premature)
      if (document.readyState === "complete" ||//如果加载状态是已完成，就调用回调方法
          (document.readyState !== "loading" && !document.documentElement.doScroll))
        setTimeout(function(){ callback($) }, 0)
      else {
        var handler = function() {//加载完成后触发，取消监听，并回调
          document.removeEventListener("DOMContentLoaded", handler, false)
          window.removeEventListener("load", handler, false)
          callback($)
        }
        document.addEventListener("DOMContentLoaded", handler, false)//没加载好就添加监听
        window.addEventListener("load", handler, false)
      }
      return this
    },
    get: function(idx){//获取当前对象，有参数就返回某一个值，没参数就返回对象的数组形式
      return idx === undefined ? slice.call(this) : this[idx >= 0 ? idx : idx + this.length]
    },
    toArray: function(){ return this.get() },//返回数组形式
    size: function(){
      return this.length
    },
    remove: function(){//从其父节点中 将其移除
      return this.each(function(){
        if (this.parentNode != null)
          this.parentNode.removeChild(this)
      })
    },
    each: function(callback){//调用数组的every有不符合条件的返回false,都符合条件的返回this
      emptyArray.every.call(this, function(el, idx){
        return callback.call(el, idx, el) !== false //call方法，第一个参数时指定this
      })
      return this
    },
    filter: function(selector){//筛选集合中符合selector的
      if (isFunction(selector)) return this.not(this.not(selector))
      return $(filter.call(this, function(element){
        return zepto.matches(element, selector)
      }))
    },
    add: function(selector,context){//需要添加的元素，利用conact合并数组的方式，添加到一起（添加元素到当前匹配的元素集合中）
      return $(uniq(this.concat($(selector,context))))
    },
    is: function(selector){//判断当前元素集合中的第一个元素是否符css选择器
      return typeof selector == 'string' ? this.length > 0 && zepto.matches(this[0], selector) : 
          selector && this.selector == selector.selector
    },
    not: function(selector){//返回不符合的集合
      var nodes=[]
      if (isFunction(selector) && selector.call !== undefined)//参数如果是函数，就返回函数返回false集合
        this.each(function(idx){
          if (!selector.call(this,idx)) nodes.push(this)
        })
      else {//先找到符合的
        var excludes = typeof selector == 'string' ? this.filter(selector) ://参数是字符串就视为css选择器
          (likeArray(selector) && isFunction(selector.item)) ? slice.call(selector) : $(selector)//如果是数组就直接视为集合
        this.forEach(function(el){
          if (excludes.indexOf(el) < 0) nodes.push(el)//符合之外的就是不符合的
        })
      }
      return $(nodes)
    },
    has: function(selector){
      return this.filter(function(){
        return isObject(selector) ?
          $.contains(this, selector) :
          $(this).find(selector).size()
      })
    },
    eq: function(idx){//获取集合中的第idx个元素，-1代表最后一个
      return idx === -1 ? this.slice(idx) : this.slice(idx, + idx + 1)//+1的意思就是取n到n+1之间的一个
    },
    first: function(){//获取当前对象集合中的第一个元素
      var el = this[0]
      return el && !isObject(el) ? el : $(el)
    },
    last: function(){//返回this中的最后一个元素
      var el = this[this.length - 1]
      return el && !isObject(el) ? el : $(el)
    },
    find: function(selector){//根据选择器返回Zepto对象
      var result, $this = this
      if (!selector) result = $()//返回空对象
      else if (typeof selector == 'object')
        result = $(selector).filter(function(){
          var node = this
          return emptyArray.some.call($this, function(parent){
            return $.contains(parent, node)
          })
        })
      else if (this.length == 1) result = $(zepto.qsa(this[0], selector))//如果要找的集合是一个对象
      else result = this.map(function(){ return zepto.qsa(this, selector) })//否则就需要遍历
      return result
    },
    closest: function(selector, context){//找出元素最近的符合selector的父级元素
      var nodes = [], collection = typeof selector == 'object' && $(selector)
      this.each(function(_, node){//循环判断，如果找到的父级元素符合selector就停止循环
        while (node && !(collection ? collection.indexOf(node) >= 0 : zepto.matches(node, selector)))
          node = node !== context && !isDocument(node) && node.parentNode//赋值为父节点
        if (node && nodes.indexOf(node) < 0) nodes.push(node)
      })
      return $(nodes)
    },
    parents: function(selector){//返回符合条件的所有父元素
      var ancestors = [], nodes = this
      while (nodes.length > 0)
        nodes = $.map(nodes, function(node){//map遍历找出集合中每个的父级集合,while循环一直往上查找
          if ((node = node.parentNode) && !isDocument(node) && ancestors.indexOf(node) < 0) {
            ancestors.push(node)
            return node
          }
        })
      return filtered(ancestors, selector)
    },
    parent: function(selector){//获取父元素，可以用参数过滤
      return filtered(uniq(this.pluck('parentNode')), selector)
    },
    children: function(selector){
      return filtered(this.map(function(){ return children(this) }), selector)
    },
    contents: function() {//获得每个匹配元素集合元素的子元素，包括文字和注释节点
      return this.map(function() { return this.contentDocument || slice.call(this.childNodes) })
    },
    siblings: function(selector){//获取对象集合中所有元素的兄弟节点。如果给定CSS选择器参数，过滤出符合选择器的元素。
      return filtered(this.map(function(i, el){
        return filter.call(children(el.parentNode), function(child){ return child!==el })//过滤当前的节点的父节点下的除了自己的节点，就是其他的兄弟节点了
      }), selector)
    },
    empty: function(){//清空元素内容
      return this.each(function(){ this.innerHTML = '' })
    },
    // `pluck` is borrowed from Prototype.js 获取对象集合中每一个元素的属性值（封装的Zepto，可能不包含一些原生属性，可以用这个方法获取）
    pluck: function(property){
      return $.map(this, function(el){ return el[property] })
    },
    show: function(){//显示元素
      return this.each(function(){
        this.style.display == "none" && (this.style.display = '')//如果设置了display='none'就设置为display=''
        if (getComputedStyle(this, '').getPropertyValue("display") == "none")//window的方法getComputedStyle获取元素的所有样式
          this.style.display = defaultDisplay(this.nodeName)
      })
    },
    replaceWith: function(newContent){
      return this.before(newContent).remove()//先将元素插入到this之前，然后再删除
    },
    wrap: function(structure){//在每个匹配的元素外层包上一个html元素
      var func = isFunction(structure)
      if (this[0] && !func)
        var dom   = $(structure).get(0),
            clone = dom.parentNode || this.length > 1

      return this.each(function(index){
        $(this).wrapAll(
          func ? structure.call(this, index) :
            clone ? dom.cloneNode(true) : dom
        )
      })
    },
    wrapAll: function(structure){//在所有匹配元素外面包一个单独的结构
      if (this[0]) {
        $(this[0]).before(structure = $(structure))//在匹配的第一个元素前面插入
        var children
        // drill down to the inmost element
        while ((children = structure.children()).length) structure = children.first()//找到要包裹的内容的最内层
        $(structure).append(this)//然后把元素放在包裹元素的最内层
      }
      return this
    },
    wrapInner: function(structure){
      var func = isFunction(structure)
      return this.each(function(index){
        var self = $(this), contents = self.contents(),
            dom  = func ? structure.call(this, index) : structure
        contents.length ? contents.wrapAll(dom) : self.append(dom)
      })
    },
    unwrap: function(){//删除直接父节点
      this.parent().each(function(){
        $(this).replaceWith($(this).children())//用子节点replace当前节点就可以做到只删除父节点了
      })
      return this
    },
    clone: function(){
      return this.map(function(){ return this.cloneNode(true) })//调用map方法，传入匿名函数
    },
    hide: function(){//隐藏元素
      return this.css("display", "none")
    },
    toggle: function(setting){//切换元素显示状态
      return this.each(function(){
        var el = $(this)//如果有传参数就根据参数，没有的话就判断当前是显示就设为隐藏，当前是隐藏就设为显示
        ;(setting === undefined ? el.css("display") == "none" : setting) ? el.show() : el.hide()
      })
    },
    prev: function(selector){ return $(this.pluck('previousElementSibling')).filter(selector || '*') },
    next: function(selector){ return $(this.pluck('nextElementSibling')).filter(selector || '*') },//先将this集合批量找到next形成新的数组，再根据selector过滤集合
    html: function(html){
      return 0 in arguments ?//有参数时替换遍历this替换其innerHtml
        this.each(function(idx){
          var originHtml = this.innerHTML
          $(this).empty().append( funcArg(this, html, idx, originHtml) )
        }) ://没有参数时返回this中第一的innerHtml
        (0 in this ? this[0].innerHTML : null)
    },
    text: function(text){//获取或设置文本
      return 0 in arguments ?
        this.each(function(idx){//有参数就设置
          var newText = funcArg(this, text, idx, this.textContent)
          this.textContent = newText == null ? '' : ''+newText
        }) :
        (0 in this ? this.pluck('textContent').join("") : null)//没有参数就读取值
    },
    attr: function(name, value){
      var result
      return (typeof name == 'string' && !(1 in arguments)) ? //没有第二个参数
        (0 in this && this[0].nodeType == 1 && (result = this[0].getAttribute(name)) != null ? result : undefined) ://读取属性
        this.each(function(idx){
          if (this.nodeType !== 1) return
          if (isObject(name)) for (key in name) setAttribute(this, key, name[key])
          else setAttribute(this, name, funcArg(this, value, idx, this.getAttribute(name)))
        })
    },
    removeAttr: function(name){//移除属性，可以用空格间隔多个属性
      return this.each(function(){ this.nodeType === 1 && name.split(' ').forEach(function(attribute){
        setAttribute(this, attribute)
      }, this)})
    },
    prop: function(name, value){
      name = propMap[name] || name//大小写映射转换一下
      return (typeof name == 'string' && !(1 in arguments)) ?
        (this[0] && this[0][name]) ://如果只有name参数就返回属性值
        this.each(function(idx){//否则就设置value
          if (isObject(name)) for (key in name) this[propMap[key] || key] = name[key]
          else this[name] = funcArg(this, value, idx, this[name])
        })
    },
    removeProp: function(name){
      name = propMap[name] || name
      return this.each(function(){ delete this[name] })
    },
    data: function(name, value){//获取data-开头的属性
      var attrName = 'data-' + name.replace(capitalRE, '-$1').toLowerCase()

      var data = (1 in arguments) ?
        this.attr(attrName, value) :
        this.attr(attrName)

      return data !== null ? deserializeValue(data) : undefined
    },
    val: function(value){//获取或设置元素的value
      if (0 in arguments) {
        if (value == null) value = ""//如果有参数就设置
        return this.each(function(idx){
          this.value = funcArg(this, value, idx, this.value)
        })
      } else {//没有参数就返回第一个的值
        return this[0] && (this[0].multiple ?//如果是多选下拉框要特别处理
           $(this[0]).find('option').filter(function(){ return this.selected }).pluck('value') :
           this[0].value)
      }
    },
    offset: function(coordinates){//获取元素的偏移量
      if (coordinates) return this.each(function(index){//有带有left和top属性对象时，调整元素的位置
        var $this = $(this),//遍历的时候是element对象，所以要转成$
            coords = funcArg(this, coordinates, index, $this.offset()),
            parentOffset = $this.offsetParent().offset(),//获取父级元素的位置
            props = {
              top:  coords.top  - parentOffset.top,//基于父级元素做调整
              left: coords.left - parentOffset.left
            }

        if ($this.css('position') == 'static') props['position'] = 'relative'//把元素从static改成relative
        $this.css(props)
      })
      if (!this.length) return null
      if (document.documentElement !== this[0] && !$.contains(document.documentElement, this[0]))
        return {top: 0, left: 0}
      var obj = this[0].getBoundingClientRect()//没有参数就获取偏移量
      return {
        left: obj.left + window.pageXOffset,
        top: obj.top + window.pageYOffset,
        width: Math.round(obj.width),
        height: Math.round(obj.height)
      }
    },
    css: function(property, value){//读取或处理css样式
      if (arguments.length < 2) {//当参数是一个时说明是读取
        var element = this[0]
        if (typeof property == 'string') {
          if (!element) return
          return element.style[camelize(property)] || getComputedStyle(element, '').getPropertyValue(property)
        } else if (isArray(property)) {//读取多个参数时用数组传进来
          if (!element) return
          var props = {}
          var computedStyle = getComputedStyle(element, '')//获取一个元素的所有style，window的方法
          $.each(property, function(_, prop){
            props[prop] = (element.style[camelize(prop)] || computedStyle.getPropertyValue(prop))
          })
          return props
        }
      }

      var css = ''
      if (type(property) == 'string') {
        if (!value && value !== 0)//如果值为空就遍历去除该属性
          this.each(function(){ this.style.removeProperty(dasherize(property)) })
        else//值不为空就处理下要添加的字符串格式
          css = dasherize(property) + ":" + maybeAddPx(property, value)
      } else {
        for (key in property)
          if (!property[key] && property[key] !== 0)
            this.each(function(){ this.style.removeProperty(dasherize(key)) })
          else
            css += dasherize(key) + ':' + maybeAddPx(key, property[key]) + ';'
      }

      return this.each(function(){ this.style.cssText += ';' + css })
    },
    index: function(element){//有参数就返回在this中的位置，没有参数就返回在兄弟节点的位置
      return element ? this.indexOf($(element)[0]) : this.parent().children().indexOf(this[0])
    },
    hasClass: function(name){
      if (!name) return false
      return emptyArray.some.call(this, function(el){
        return this.test(className(el))
      }, classRE(name))
    },
    addClass: function(name){
      if (!name) return this//参数为空直接返回对象
      return this.each(function(idx){//遍历
        if (!('className' in this)) return//检查当前对象是否有className属性
        classList = []
        var cls = className(this), newName = funcArg(this, name, idx, cls)//cls是原来已经有的className
        newName.split(/\s+/g).forEach(function(klass){//用空格split传入的name，处理多个的情况如：'class1 class 2'
          if (!$(this).hasClass(klass)) classList.push(klass)//遍历判断跟原来是否有重复的
        }, this)                            //如果原来有className就价格空格
        classList.length && className(this, cls + (cls ? " " : "") + classList.join(" "))//如果classList有内容就给节点添加className
      })
    },
    removeClass: function(name){//移除类名
      return this.each(function(idx){
        if (!('className' in this)) return
        if (name === undefined) return className(this, '')//如果没有参数就清除className的所有值
        classList = className(this)//获取当前元素的className
        funcArg(this, name, idx, classList).split(/\s+/g).forEach(function(klass){//遍历用空格隔开的多个类名
          classList = classList.replace(classRE(klass), " ")//把要去除的类名替换为空格
        })
        className(this, classList.trim())//再把处理好的classList赋值给className
      })
    },
    toggleClass: function(name, when){//切换类名，如果没有就添加，有就删除
      if (!name) return this
      return this.each(function(idx){
        var $this = $(this), names = func Arg(this, name, idx, className(this))
        names.split(/\s+/g).forEach(function(klass){
          (when === undefined ? !$this.hasClass(klass) : when) ?
            $this.addClass(klass) : $this.removeClass(klass)
        })
      })
    },
    scrollTop: function(value){
      if (!this.length) return
      var hasScrollTop = 'scrollTop' in this[0]
      if (value === undefined) return hasScrollTop ? this[0].scrollTop : this[0].pageYOffset
      return this.each(hasScrollTop ?
        function(){ this.scrollTop = value } :
        function(){ this.scrollTo(this.scrollX, value) })
    },
    scrollLeft: function(value){//获取或设置页面上的滚动元素或者整个窗口向右滚动的像素值
      if (!this.length) return
      var hasScrollLeft = 'scrollLeft' in this[0]
      if (value === undefined) return hasScrollLeft ? this[0].scrollLeft : this[0].pageXOffset//没有参数就返回第一个元素的scrollLeft值
      return this.each(hasScrollLeft ?//如果有参数就设置
        function(){ this.scrollLeft = value } :
        function(){ this.scrollTo(value, this.scrollY) })
    },
    position: function() {//获取集合中第一个元素的实际位置
      if (!this.length) return

      var elem = this[0],
        // Get *real* offsetParent
        offsetParent = this.offsetParent(),
        // Get correct offsets
        offset       = this.offset(),
        parentOffset = rootNodeRE.test(offsetParent[0].nodeName) ? { top: 0, left: 0 } : offsetParent.offset()

      // Subtract element margins
      // note: when an element has margin: auto the offsetLeft and marginLeft
      // are the same in Safari causing offset.left to incorrectly be 0
      offset.top  -= parseFloat( $(elem).css('margin-top') ) || 0
      offset.left -= parseFloat( $(elem).css('margin-left') ) || 0

      // Add offsetParent borders 父偏移要加上边框
      parentOffset.top  += parseFloat( $(offsetParent[0]).css('border-top-width') ) || 0
      parentOffset.left += parseFloat( $(offsetParent[0]).css('border-left-width') ) || 0

      // Subtract the two offsets
      return {
        top:  offset.top  - parentOffset.top,
        left: offset.left - parentOffset.left
      }
    },
    offsetParent: function() {//找到position不为static的父元素
      return this.map(function(){
        var parent = this.offsetParent || document.body
        while (parent && !rootNodeRE.test(parent.nodeName) && $(parent).css("position") == "static")
          parent = parent.offsetParent
        return parent
      })
    }
  }

  // for now
  $.fn.detach = $.fn.remove

  // Generate the `width` and `height` functions
  //生成获取高度和宽度的方法
  ;['width', 'height'].forEach(function(dimension){
    var dimensionProperty =
      dimension.replace(/./, function(m){ return m[0].toUpperCase() })

    $.fn[dimension] = function(value){
      var offset, el = this[0]
      if (value === undefined) return isWindow(el) ? el['inner' + dimensionProperty] ://如果是window对象返回innerWidth
        isDocument(el) ? el.documentElement['scroll' + dimensionProperty] ://如果是document对象返回scrollWidth
        (offset = this.offset()) && offset[dimension]
      else return this.each(function(idx){//有value参数就修改width或height
        el = $(this)
        el.css(dimension, funcArg(this, value, idx, el[dimension]()))//用css的sytle.width来修改
      })
    }
  })

  function traverseNode(node, fun) {
    fun(node)
    for (var i = 0, len = node.childNodes.length; i < len; i++)
      traverseNode(node.childNodes[i], fun)
  }

  // Generate the `after`, `prepend`, `before`, `append`,
  // `insertAfter`, `insertBefore`, `appendTo`, and `prependTo` methods.
  //批量生成这些方法
  adjacencyOperators.forEach(function(operator, operatorIndex) {
    var inside = operatorIndex % 2 //=> prepend, append

    $.fn[operator] = function(){
      // arguments can be nodes, arrays of nodes, Zepto objects and HTML strings
      //参数可以是nodes，nodes的数组，Zepto对象和html字符串
      var argType, nodes = $.map(arguments, function(arg) {
            var arr = []
            argType = type(arg)
            if (argType == "array") {
              arg.forEach(function(el) {
                if (el.nodeType !== undefined) return arr.push(el)
                else if ($.zepto.isZ(el)) return arr = arr.concat(el.get())
                arr = arr.concat(zepto.fragment(el))
              })
              return arr
            }
            return argType == "object" || arg == null ?
              arg : zepto.fragment(arg)
          }),
          parent, copyByClone = this.length > 1
      if (nodes.length < 1) return this

      return this.each(function(_, target){
        parent = inside ? target : target.parentNode// after和before父级就是当前元素的父级，prepend和append父级就是当前元素
        console.log(parent)
        // convert all methods to a "before" operation
        //将所有方法转成before操作
        target = operatorIndex == 0 ? target.nextSibling ://after转成before就是target变成后兄弟节点
                 operatorIndex == 1 ? target.firstChild ://prepend转成before就是target变成其第一个子节点
                 operatorIndex == 2 ? target :
                 null
        console.log(target)
        var parentInDocument = $.contains(document.documentElement, parent)

        nodes.forEach(function(node){
          if (copyByClone) node = node.cloneNode(true)
          else if (!parent) return $(node).remove()

          parent.insertBefore(node, target)
          if (parentInDocument) traverseNode(node, function(el){
            if (el.nodeName != null && el.nodeName.toUpperCase() === 'SCRIPT' &&
               (!el.type || el.type === 'text/javascript') && !el.src){
              var target = el.ownerDocument ? el.ownerDocument.defaultView : window
              target['eval'].call(target, el.innerHTML)
            }
          })
        })
      })
    }

    // after    => insertAfter
    // prepend  => prependTo
    // before   => insertBefore
    // append   => appendTo
    $.fn[inside ? operator+'To' : 'insert'+(operatorIndex ? 'Before' : 'After')] = function(html){
      $(html)[operator](this)//====等于$('ul')['append'](this)====等于$('ul').append(this) 根据传入的参数动态迪调用方法
      return this
    }
  })
  //把原型指定为$.fn
  zepto.Z.prototype = Z.prototype = $.fn

  // Export internal API functions in the `$.zepto` namespace
  zepto.uniq = uniq
  zepto.deserializeValue = deserializeValue
  $.zepto = zepto

  return $
})()

// If `$` is not yet defined, point it to `Zepto` 如果$还没有被定义，就指向为Zepto
window.Zepto = Zepto
window.$ === undefined && (window.$ = Zepto)
