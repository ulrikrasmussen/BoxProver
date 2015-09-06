(function() {
    var activeTabName;
    var main;
    var editor;
    var vsplitter;
    var hsplitter;
    var aceEditor;
    var left;
    var output;
    var prooftable;

    var hpos; // Position of horizontal splitter
    var vpos; // Position of vertical splitter

    function playSound(sound) {
        var audio = new Audio(sound);
        audio.play();
    }
    
    function updateLayout() {
        var w = main.width();
        var h = main.height();
        var splitSize = 6;
        left.width(vpos - splitSize);
        prooftable.css({ left: vpos,
                         width: w - vpos });
        vsplitter.css({ left: vpos - splitSize,
                        width: splitSize });
        editor.css({ height: hpos - splitSize });
        output.css({ height: h - hpos,
                     top: hpos });
        hsplitter.css({ top: hpos - splitSize,
                        height: splitSize });
    }

    function setInitialLayout() {
        vpos = main.width() / 2;
        hpos = main.height() - main.height() / 5;
    }

    var resizeTimer;
    function onWindowResizeHandler() {
        clearTimeout(resizeTimer);
        resizeTimer = setTimeout(updateLayout, 100);
    }

    function onVSplitterMouseDownHandler() {
        function hideVWindows() {
            left.hide();
            prooftable.hide();
        }
        function showVWindows() {
            left.show();
            prooftable.show();
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
        a.style.cssText = "visibility:hidden;";
        document.body.appendChild(a);
        a.click();
        setTimeout( function() { document.body.removeChild(a) }, 1 );
    }

    function onShareClickHandler() {
        var proof = aceEditor.getSession().getValue();
        var proofUrl = SERVER_URL + "/index.html?proof=" + encodeURIComponent(proof);
        if (proofUrl.length > 5000) {
            prooftable.html("<div style='padding: 10px;'>" +
            "<p>Your proof script is unfortunately too long to be shared this way.</p>" +
            "<p>Proof scripts are shared by encoding them as URLs, and the URL " +
            "shortening service does not support URLs of more than " +
            "<strong>5000</strong> characters. Your proof results in a URL " +
            "of length <strong>" + proofUrl.length + "</strong> characters.</p>" +
            "<p>Try shortening your proof script or "+
            "use the <i>Save as</i> button.</p></div>");
            return;
        }
        prooftable.html("<div style='padding:10px;'><p id='short-url-p'>Short URL: </p></div>");
        var link = document.createElement("a");
        link.href = link.textContent = proofUrl;
        prooftable.find('#short-url-p').append(link);

        $.ajax(
            { url: "https://is.gd/create.php?format=json&url="
                   + encodeURIComponent(proofUrl),
              method: "GET",
              dataType: "json",
              timeout: 8000
            })
            .success(function(response) {
                if ("shorturl" in response)
                    link.href = link.textContent = response.shorturl;
                if ("errormessage" in response)
                    prooftable.append("<p style='color:red;'>URL shortening service "
                                      + "reported an error: " + response.errormessage
                                     + "</p>");
            })
            .fail(function(xhr, textStatus, errorThrown) {
                prooftable.append("<p style='color:red;'>Something went wrong. "
                                  + "Shortened URL not available: "
                                  + textStatus + "</p>");
            });
    }

    function onOpenClickHandler() {
        var fileElem = document.createElement('input');
        fileElem.style.cssText = "visibility:hidden;";
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
        document.body.appendChild(fileElem);
        fileElem.click();
        setTimeout( function() { document.body.removeChild(fileElem); }, 1 );
    }

    function onCheckClickHandler() {
        checkProof();
    }

    function onReportClickHandler() {
        var m1 = "ZG9sbGVAZ";
        var m2 = "GlrdS5kaw==";
        var a = document.createElement('a');
        var mailto = 'mailto:' + window.atob(m1 + m2);
        mailto += '?subject=Bug%20report';
        mailto += '&body=';
        mailto +=
          encodeURIComponent("\n\n== Proof script causing unexpected behavior: ==\n\n");
        mailto += encodeURIComponent(aceEditor.getValue());
        a.setAttribute('href', mailto);
        a.style.cssText = "visibility:hidden;";
        document.body.appendChild(a);
        a.click();
        setTimeout( function() { document.body.removeChild(a) }, 1 );
    }

    function onEnhanceClickHandler() {
        optionalLocalStorageSetItem("enhance", enhanceCheckBox.prop('checked'));
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
            .success( handleCheckResponse )
            .fail(function(hxr, textStatus, errorThrown) {
                output.html("Request failed with error: " + textStatus);
                output.scrollTop(output.prop("scrollHeight"));
            })
            .always(function() { checkRequest = null; });
    }

    function handleCheckResponse(response) {
        output.html('<pre><samp>' + response.output + '</samp></pre>');
        output.scrollTop(output.prop("scrollHeight"));
        prooftable.html('');
        if (!response.check) {
            if (enhanceCheckBox.prop('checked'))
                playSound('trombone.wav');
            return;
        } else
        {
            var allClosed = true;
            $.each(response.prooftables, function(i, table) {
                allClosed = allClosed && table.closed;
            });
            if (enhanceCheckBox.prop('checked') && allClosed)
                playSound('coin.wav');
        }
        var tabsList = $('<ul id="tabButtons">');
        var contentDivs = $('<div id="tabPanels"></div>');
        var allNames = $.map(response.prooftables, function(o) { return o.name; });
        if (!($.inArray(activeTabName, allNames) >= 0))
            activeTabName = null;
        $.each(response.prooftables, function(i, table){
            var closedIndicator =
                table.closed ? '<i class="el el-ok closed-indicator"></i>'
                             : '<i class="el el-question open-indicator"></i>';
            var tab = $('<li><a>' + closedIndicator + table.name + '</a></li>');
            var content = $('<div></div>');
            if (table.closed)
                content.append("<p style='float:right;' class='closed-indicator'>Proof is closed!</p>");
            else
                content.append("<p style='float:right;' class='open-indicator'>Proof still has holes.</p>");
            content.append(table.html);
            content.addClass("tabContent");

            content.find("div.context-separator").each(function(i,sep) {
                var ctx = $(sep).next();
                $(sep).append('&nbsp;<i class="el el-caret-down"></i>');
                ctx.addClass("collapse");
                $(sep).click((function(theSep, theCtx) {
                    return function() {
                        theCtx.toggleClass("collapse");
                        theSep.find('i').toggleClass('el-caret-down');
                        theSep.find('i').toggleClass('el-caret-up');
                    }
                })($(sep),ctx));
            });
            
            activeTabName = activeTabName || table.name;
            if (table.name === activeTabName) {
                tab.addClass("active");
            }
            else
            {
                tab.addClass("inactive");
                content.addClass("hide");
            }
            
            tab.click((function(theTab, theContent, theName) {
                return function() {
                    $("#tabButtons li.active").addClass("inactive").removeClass("active");
                    $("#tabPanels div").addClass("hide");
                    theTab.removeClass("inactive").addClass("active");
                    theContent.removeClass("hide");
                    activeTabName = theName;
                };
            })(tab, content, table.name));
            
            tabsList.append(tab);
            contentDivs.append(content);
        });
        prooftable.append(tabsList);
        prooftable.append(contentDivs);
    }
    
    function optionalLocalStorageGetItem(key) {
        try {
            return localStorage.getItem(key);
        } catch(e) {
            return null;
        }
    }

    function optionalLocalStorageSetItem(key, value) {
        try {
            window.localStorage.setItem(key, value);
        } catch(e) {
            // ignore
        }
    }

    function getQueryParameters() {
        var a = window.location.search.substr(1).split('&');
        if (a === "") return {};
        var b = {};
        for (var i = 0; i < a.length; i++) {
            var p = a[i].split('=');
            if (p.length != 2) continue;
            b[p[0]] = decodeURIComponent(p[1].replace(/\+/g, " "));
        }
        return b;
    }

    $().ready(function() {
        main         = $("#main");
        editor       = $("#editor");
        vsplitter    = $("#vsplitter");
        hsplitter    = $("#hsplitter");
        left         = $("#left");
        output       = $("#output");
        prooftable   = $("#prooftable");
        checkButton  = $("#check");
        saveButton   = $("#save");
        shareButton  = $("#share");
        openButton   = $("#open");
        reportButton = $("#report");
        enhanceCheckBox = $("#enhance");
        
        aceEditor = ace.edit("editor");
        aceEditor.setTheme("ace/theme/chrome");
        aceEditor.commands.addCommand({
            name: 'CheckCommand',
            bindKey: {win: 'Ctrl-Enter',  mac: 'Command-Enter'},
            exec: function(editor) {
                checkProof();
            },
            readOnly: true
        });
        aceEditor.getSession().setMode("ace/mode/boxprover");
        
        setInitialLayout();
        updateLayout();

        $(window).resize(onWindowResizeHandler);
        vsplitter.mousedown(onVSplitterMouseDownHandler);
        hsplitter.mousedown(onHSplitterMouseDownHandler);
        checkButton.click(onCheckClickHandler);
        saveButton.click(onSaveClickHandler);
        shareButton.click(onShareClickHandler);
        openButton.click(onOpenClickHandler);
        reportButton.click(onReportClickHandler);
        enhanceCheckBox.click(onEnhanceClickHandler);

        query = getQueryParameters();
        if ("proof" in query)
        {
            aceEditor.getSession().setValue(query.proof);
        } else {
            var proof = optionalLocalStorageGetItem("proof");
            if (proof !== null)
                aceEditor.getSession().setValue(proof);
        }

        var enhance = optionalLocalStorageGetItem("enhance");
        if (enhance == "true")
            enhanceCheckBox.prop('checked', true);
        
        aceEditor.getSession().on("change", function() {
            var proof = aceEditor.getSession().getValue();
            optionalLocalStorageSetItem("proof", proof);
        });
    });
})();
