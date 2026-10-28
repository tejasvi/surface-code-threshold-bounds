import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5364 = true := by
  decide +kernel

theorem tot5364 : totK PA10K2 A10K2.t5364 = [0, 0, 112276258614, 846818924100, 1978519637221, 1609086877780, 349280157326, 11991740650, 0, 0] := by
  decide +kernel

theorem rows5365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5365 = true := by
  decide +kernel

theorem tot5365 : totK PA10K2 A10K2.t5365 = [0, 0, 482456369876, 1859303739454, 2101504116050, 651174365525, 27140404744, 0, 0, 0] := by
  decide +kernel

theorem rows5366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5366 = true := by
  decide +kernel

theorem tot5366 : totK PA10K2 A10K2.t5366 = [0, 0, 108743828956, 819829354205, 2135990720644, 1708304292332, 307543941216, 7834437697, 0, 0] := by
  decide +kernel

theorem rows5367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5367 = true := by
  decide +kernel

theorem tot5367 : totK PA10K2 A10K2.t5367 = [0, 0, 444578802886, 1805206107414, 2088665350656, 596774043762, 29895930245, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
