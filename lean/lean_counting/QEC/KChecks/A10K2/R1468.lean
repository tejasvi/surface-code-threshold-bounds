import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5872 = true := by
  decide +kernel

theorem tot5872 : totK PA10K2 A10K2.t5872 = [0, 0, 0, 599929559741, 2012761935732, 1776430680089, 352798363185, 12790540575, 0, 0] := by
  decide +kernel

theorem rows5873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5873 = true := by
  decide +kernel

theorem tot5873 : totK PA10K2 A10K2.t5873 = [0, 0, 0, 454840941866, 1635709699817, 1901422655927, 584991828359, 50267370225, 0, 0] := by
  decide +kernel

theorem rows5874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5874 = true := by
  decide +kernel

theorem tot5874 : totK PA10K2 A10K2.t5874 = [0, 0, 0, 120878628610, 1344990694081, 2312024242088, 831344705000, 58503570348, 0, 0] := by
  decide +kernel

theorem rows5875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5875 = true := by
  decide +kernel

theorem tot5875 : totK PA10K2 A10K2.t5875 = [0, 0, 0, 307367748945, 1219896491454, 1803508654436, 1074755230402, 227545341017, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
