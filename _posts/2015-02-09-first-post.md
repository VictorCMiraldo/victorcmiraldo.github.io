---
layout: post
title: "My First Post"
description: "just testing jekyll around"
modified: 2015-02-09
tags: [first]
image:
  feature: abstract-10.jpg
  credit: dargadgetz
  creditlink: http://www.dargadgetz.com/ios-7-abstract-wallpaper-pack-for-iphone-5-and-ipod-touch-retina/
---

And here is a first post!
Let's just test the haskell highlight:

{% highlight haskell %}
data MyTags 
  = Tag1
  | Tag2
  deriving (Eq, Show)

sum :: [Integer] -> Integer
sum = foldr (+) 0
{% endhighlight %}
