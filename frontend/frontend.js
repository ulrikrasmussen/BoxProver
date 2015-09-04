(function() {
    var SERVER_URL = 'http://localhost:8000'
    
    var main;
    var editor;
    var vsplitter;
    var hsplitter;
    var aceEditor;
    var results;
    var output;
    var prooftable;

    var hpos; // Position of horizontal splitter
    var vpos; // Position of vertical splitter
    
    function updateLayout() {
        var w = main.width();
        var h = main.height();
        var splitSize = 6;
        editor.width(vpos - splitSize);
        results.css({ left: vpos,
                      width: w - vpos });
        vsplitter.css({ left: vpos - splitSize,
                        width: splitSize });
        output.css({ height: hpos - splitSize });
        prooftable.css({ height: h - hpos,
                         top: hpos });
        hsplitter.css({ top: hpos - splitSize,
                        height: splitSize });
    }

    function setInitialLayout() {
        vpos = main.width() / 2;
        hpos = main.height() / 5;
    }

    var resizeTimer;
    function onWindowResizeHandler() {
        clearTimeout(resizeTimer);
        resizeTimer = setTimeout(updateLayout, 100);
    }

    function onVSplitterMouseDownHandler() {
        function hideVWindows() {
            editor.hide();
            results.hide();
        }
        function showVWindows() {
            editor.show();
            results.show();
        }        
        hideVWindows();
        $(window).mousemove(function(event) {
            vpos = event.pageX - main.position().left;
            updateLayout();
        });
        $(window).mouseup(function() {
            $(window).unbind('mouseup');
            $(window).unbind('mousemove');
            showVWindows();
        });
    }

    function onSaveClickHandler() {
        var a = document.createElement('a');
        a.setAttribute('download', 'proof.elf');
        a.setAttribute('href', 'data:text/plain;base64,' + window.btoa(aceEditor.getValue()));
        a.click();
    }

    function onOpenClickHandler() {
        var fileElem = document.createElement('input');
        fileElem.setAttribute('type', 'file');
        $(fileElem).change(function(evt) {
            var f = evt.target.files[0];
            if (f == null)
                return;
            var reader = new FileReader();
            reader.onload = (function(e) {
                aceEditor.setValue(reader.result);
            });
            reader.readAsText(f);
        });
        fileElem.click();
    }

    function onCheckClickHandler() {
        checkProof();
    }

    function onHSplitterMouseDownHandler() {
        function hideHWindows() {
            output.hide();
            prooftable.hide();
        }        
        function showHWindows() {
            output.show();
            prooftable.show();
        }

        hideHWindows();
        $(window).mousemove(function(event) {
            hpos = event.pageY - main.position().top;
            updateLayout();
        });
        $(window).mouseup(function() {
            $(window).unbind('mouseup');
            $(window).unbind('mousemove');
            showHWindows();
        });
    }

    var checkRequest = null;
    function checkProof()
    {
        if (checkRequest !== null)
            return;
        checkRequest = $.ajax(
            { url: SERVER_URL + "/check",
              method: "POST",
              data: {
                  proof: aceEditor.getValue()
              },
              timeout: 8000
            })
            .success(function(data) {
                var response = $.parseJSON(data);
                output.html('<pre><samp>' + response.output + '</samp></pre>');
                prooftable.html(response.prooftable);
                output.scrollTop(output.prop("scrollHeight"));
            })
            .fail(function(hxr, textStatus, errorThrown) {
                output.html("Request failed with error: " + textStatus);
            })
            .always(function() { checkRequest = null; });
    }
    
    $().ready(function() {
        main       = $("#main");
        editor     = $("#editor");
        vsplitter  = $("#vsplitter");
        hsplitter  = $("#hsplitter");
        results    = $("#results");
        output     = $("#output");
        prooftable = $("#prooftable");
        checkButton = $("#check");
        saveButton = $("#save");
        openButton = $("#open");
        
        aceEditor = ace.edit("editor");
        //        aceEditor.setTheme("ace/theme/solarized_dark");
        aceEditor.commands.addCommand({
            name: 'CheckCommand',
            bindKey: {win: 'Ctrl-Enter',  mac: 'Command-Enter'},
            exec: function(editor) {
                checkProof();
            },
            readOnly: true
        });
        
        setInitialLayout();
        updateLayout();

        $(window).resize(onWindowResizeHandler);
        vsplitter.mousedown(onVSplitterMouseDownHandler);
        hsplitter.mousedown(onHSplitterMouseDownHandler);
        checkButton.click(onCheckClickHandler);
        saveButton.click(onSaveClickHandler);
        openButton.click(onOpenClickHandler);
    });
})();
