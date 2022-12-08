/*!
 * Clean Blog v1.0.0 (http://startbootstrap.com)
 * Copyright 2015 Start Bootstrap
 * Licensed under Apache 2.0 (https://github.com/IronSummitMedia/startbootstrap/blob/gh-pages/LICENSE)
 */

 /*!
 * Hux Blog v1.6.0 (http://startbootstrap.com)
 * Copyright 2016 @huxpro
 * Licensed under Apache 2.0
 */

// Tooltip Init
// Unuse by Hux since V1.6: Titles now display by default so there is no need for tooltip
// $(function() {
//     $("[data-toggle='tooltip']").tooltip();
// });


// make all images responsive
/*
 * Unuse by Hux
 * actually only Portfolio-Pages can't use it and only post-img need it.
 * so I modify the _layout/post and CSS to make post-img responsive!
 */
// $(function() {
//  $("img").addClass("img-responsive");
// });

// responsive tables
$(document).ready(function() {
    $("table").wrap("<div class='table-responsive'></div>");
    $("table").addClass("table");
});

// responsive embed videos
$(document).ready(function() {
    $('iframe[src*="youtube.com"]').wrap('<div class="embed-responsive embed-responsive-16by9"></div>');
    $('iframe[src*="youtube.com"]').addClass('embed-responsive-item');
});

// Navigation Scripts to Show Header on Scroll-Up
jQuery(document).ready(function($) {
    var MQL = 1170;

    //primary navigation slide-in effect
    if ($(window).width() > MQL) {
        var headerHeight = $('.navbar-custom').height(),
            bannerHeight  = $('.intro-header .container').height();
        $(window).on('scroll', function() {
                var currentTop = $(window).scrollTop(), $catalog = $('.side-catalog');
                if (this.previousTop === undefined) {
                    this.previousTop = 0;
                }

                //check if user is scrolling up by mouse or keyborad
                if (Math.abs(currentTop - this.previousTop) >= 50) {
                    if (currentTop < this.previousTop) {
                        //if scrolling up...
                        if (currentTop > 0 && $('.navbar-custom').hasClass('is-fixed')) {
                            $('.navbar-custom').addClass('is-visible');
                        } else {
                            $('.navbar-custom').removeClass('is-visible is-fixed');
                        }
                        this.previousTop = currentTop;
                    } else {
                        //if scrolling down...
                        $('.navbar-custom').removeClass('is-visible');
                        if (currentTop > headerHeight && !$('.navbar-custom').hasClass('is-fixed')) {
                            $('.navbar-custom').addClass('is-fixed');
                        }
                        this.previousTop = currentTop;
                    }
                }

                var articleTopAnchor = $('#top-anchor')
                var articleEndAnchor = $('#end-anchor')
                if (articleEndAnchor.length > 0) {
                    var endPos = articleEndAnchor.offset().top;
                    var topPos = articleTopAnchor.offset().top;
                    var catalogBodyHeight = $('.catalog-body').height();

                    //adjust the appearance of side-catalog
                    $catalog.show()
                    if (topPos > currentTop - 10) {
                        $catalog.offset({ top: topPos - 10 })
                    } else if (endPos < currentTop - 21 + catalogBodyHeight + 716 - 570) {
                        $catalog.offset({ top: endPos - catalogBodyHeight - 716 + 570 });
                    } else if (currentTop > (bannerHeight + 11)) {
                        $catalog.css("top", "-21px")
                    }
                }
            });
    }
});