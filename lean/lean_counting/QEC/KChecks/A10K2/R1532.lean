import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6128 = true := by
  decide +kernel

theorem tot6128 : totK PA10K2 A10K2.t6128 = [0, 509927910765, 1774902598755, 1853994253492, 615170564281, 51797108955, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6129 = true := by
  decide +kernel

theorem tot6129 : totK PA10K2 A10K2.t6129 = [0, 191141418488, 1337700168120, 2161449501009, 906277670850, 66905887177, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6130 = true := by
  decide +kernel

theorem tot6130 : totK PA10K2 A10K2.t6130 = [0, 0, 557131412029, 1936420716360, 1708164579348, 416338438260, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows6131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6131 = true := by
  decide +kernel

theorem tot6131 : totK PA10K2 A10K2.t6131 = [0, 0, 486171369113, 1850000859447, 1978592687813, 485270526338, 18535904725, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
