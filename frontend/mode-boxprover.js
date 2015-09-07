define("ace/mode/boxprover_highlight_rules", function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var lang = require("../lib/lang");
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

var BoxProverHighlightRules = function(textClass) {
    this.$rules = {
        "start" : [
	        {
	            token : "comment",
	            regex : "%\ .*$"
	        }, {
                token : "keyword",
                regex : "\\b(?:assumption;)(?![a-zA-Z0-9_])"
            }, {
                token : "support.function.directive",
                regex : "%abbrev"
            }, {
                token : "invalid.illegal",
                regex : "\%[^n]+|type|([a-zA-Z_0-9;]+;)"
            }, {
	            token : "keyword",
	            regex : "\\b(?:by|var)\\b"
	        }, {
                token : "keyword",
                regex : ";(?![a-zA-Z0-9_])"
            }, {
                token : "support.constant",
                regex : "(?:lem|nne|copy|top\_i|bot\_e|con\_i|con\_e1|con\_e2|dis\_i1|dis\_i2|dis\_e|imp\_i|imp\_e|neg\_e|neg\_i|all\_i|all\_e|exi\_i|exi\_e|eq\_i|eq\_e)(?!;)\\b"
            }, {
                token : "keyword.operator",
                regex : "\\b(?:exi|all|top|bot)\\b"
            }, {
                token : "keyword.operator",
                regex : "(?:==|=>|\\\\/|/\\\\|~)"
            }, {
                token : "keyword",
                regex : "(?:proof|ref|,,,|prop|term|\\$)"
            }, {
               token : "paren.keyword.operator",
	            regex : "[[({]"
	        }, {
               token : "paren.keyword.operator",
	           regex : "[\\])}]"
	        }, {
                token : "variable.parameter",
                regex : "[a-z@?#][-a-zA-Z0-9_!'\"#¤&/=?@£$+><]*"
            } , {
                token : "variable.other",
                regex : "[A-Z_][-a-zA-Z0-9_!'\"#¤&/=?@£$+]*"
            }
        ]
    };
};

oop.inherits(BoxProverHighlightRules, TextHighlightRules);

exports.BoxProverHighlightRules = BoxProverHighlightRules;
});

define('ace/mode/boxprover', function(require, exports, module) {

var oop = require("ace/lib/oop");
var TextMode = require("ace/mode/text").Mode;
var Tokenizer = require("ace/tokenizer").Tokenizer;
var BoxProverHighlightRules = require("ace/mode/boxprover_highlight_rules").BoxProverHighlightRules;

var Mode = function() {
    this.$tokenizer = new Tokenizer(new BoxProverHighlightRules().getRules());
};
oop.inherits(Mode, TextMode);

(function() {
    // Extra logic goes here. (see below)
}).call(Mode.prototype);

exports.Mode = Mode;
});
