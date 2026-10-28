import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6872 = true := by
  decide +kernel

theorem tot6872 : totK PA10K2 A10K2.t6872 = [0, 0, 0, 599145896583, 2006168539777, 1882003712349, 416278383833, 11864432348, 0, 0] := by
  decide +kernel

theorem rows6873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6873 = true := by
  decide +kernel

theorem tot6873 : totK PA10K2 A10K2.t6873 = [0, 442864610808, 1469325418554, 1438419645675, 592868706012, 585567811927, 344628932980, 43132710386, 0, 0] := by
  decide +kernel

theorem rows6874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6874 = true := by
  decide +kernel

theorem tot6874 : totK PA10K2 A10K2.t6874 = [0, 400066482960, 1651422383636, 1953959087414, 703917164957, 55925584929, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6875 = true := by
  decide +kernel

theorem tot6875 : totK PA10K2 A10K2.t6875 = [0, 0, 509246126494, 1919036628044, 1748360366016, 414947193762, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
