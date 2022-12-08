(function ($) {

  $.fn.tagcloud = function (options) {
    var opts = $.extend({}, $.fn.tagcloud.defaults, options);
    var tagWeights = this.map(function () {
      return $(this).attr("rel");
    });
    tagWeights = jQuery.makeArray(tagWeights).sort(compareWeights);

    var diffWeightsMap = {};
    for (var i = 1; i < tagWeights.length; i++) {
      diffWeightsMap[tagWeights[i] - tagWeights[i - 1]] = 0;
    }
    var diffWeights = Object.keys(diffWeightsMap);
    diffWeights.sort(compareWeights);
    for (var i = 0; i < diffWeights.length; i++) {
      diffWeightsMap[diffWeights[i]] = i;
    }
    var newWeightsMap = {};
    newWeightsMap[tagWeights[0]] = parseInt(tagWeights[0]);
    for (var i = 1; i < tagWeights.length; i++) {
      newWeightsMap[tagWeights[i]] = newWeightsMap[tagWeights[i - 1]] + diffWeightsMap[tagWeights[i] - tagWeights[i - 1]];
    }

    var lowest = newWeightsMap[tagWeights[0]];
    var highest = newWeightsMap[tagWeights.pop()];
    var range = highest - lowest;
    if (range === 0) {
      range = 1;
    }
    colorIncr = colorIncrement(opts.color, range);
    return this.each(function () {
      weighting = newWeightsMap[$(this).attr("rel")];
      $(this).css({ "backgroundColor": tagColor(opts.color, colorIncr, weighting) });
      // }
    });
  };

  $.fn.tagcloud.defaults = {
    color: { start: '#9f9fd2', end: '#1f83a4' },
  };

  // Converts hex to an RGB array
  function toRGB(code) {
    if (code.length == 4) {
      code = jQuery.map(/\w+/.exec(code), function (el) { return el + el; }).join("");
    }
    hex = /(\w{2})(\w{2})(\w{2})/.exec(code);
    return [parseInt(hex[1], 16), parseInt(hex[2], 16), parseInt(hex[3], 16)];
  }

  // Converts an RGB array to hex
  function toHex(ary) {
    return "#" + jQuery.map(ary, function (i) {
      hex = i.toString(16);
      hex = (hex.length == 1) ? "0" + hex : hex;
      return hex;
    }).join("");
  }

  function colorIncrement(color, range) {
    return jQuery.map(toRGB(color.end), function (n, i) {
      return (n - toRGB(color.start)[i]) / range;
    });
  }

  function tagColor(color, increment, weighting) {
    rgb = jQuery.map(toRGB(color.start), function (n, i) {
      ref = Math.round(n + (increment[i] * weighting));
      if (ref > 255) {
        ref = 255;
      } else {
        if (ref < 0) {
          ref = 0;
        }
      }
      return ref;
    });
    return toHex(rgb);
  }

  function compareWeights(a, b) {
    return a - b;
  }

})(jQuery);
