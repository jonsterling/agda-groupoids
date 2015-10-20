{-# OPTIONS --without-K #-}

module Everything where

import Ambient.Category.Base

import Ambient.Groupoid.Base
import Ambient.Groupoid.Discrete
import Ambient.Groupoid.Initial
import Ambient.Groupoid.Map
import Ambient.Groupoid.Map.Boot
import Ambient.Groupoid.Op
import Ambient.Groupoid.Tensor
import Ambient.Groupoid.Tensor.Boot
import Ambient.Groupoid.Terminal

import Ambient.Preorder.Base

import Ambient.Setoid.Base
import Ambient.Setoid.Discrete
import Ambient.Setoid.Initial
import Ambient.Setoid.Map
import Ambient.Setoid.Map.Boot
import Ambient.Setoid.Op
import Ambient.Setoid.Tensor
import Ambient.Setoid.Tensor.Boot
import Ambient.Setoid.Terminal

import Ambient.Type.Base
import Ambient.Type.Discrete
import Ambient.Type.Initial
import Ambient.Type.Map
import Ambient.Type.Map.Boot
import Ambient.Type.Op
import Ambient.Type.Tensor
import Ambient.Type.Tensor.Boot
import Ambient.Type.Terminal

import Category
import Category.Instances.SETOID
import Category.Instances.SETOID.Closed
import Category.Instances.SETOID.Monoidal
import Category.Iso
import Category.Reasoning
import Category.Yoneda

import Groupoid
import Groupoid.Bifunctor
import Groupoid.Closed
import Groupoid.Dinatural
import Groupoid.Enriched
import Groupoid.Instances.GROUPOID
import Groupoid.Instances.SETOID
import Groupoid.Iso
import Groupoid.Monoidal
import Groupoid.Presheaf
import Groupoid.Profunctor
import Groupoid.VirtualDouble

import Preorder
import Preorder.Reasoning

import Setoid
import Setoid.Reasoning

import Type
