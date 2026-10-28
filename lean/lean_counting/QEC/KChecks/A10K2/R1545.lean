import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6180 = true := by
  decide +kernel

theorem tot6180 : totK PA10K2 A10K2.t6180 = [0, 0, 122355545644, 990556313862, 2157248998473, 1428536470815, 244715219240, 6853348008, 0, 0] := by
  decide +kernel

theorem rows6181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6181 = true := by
  decide +kernel

theorem tot6181 : totK PA10K2 A10K2.t6181 = [0, 213371739588, 562576911074, 829916630289, 1635254112255, 1414337066840, 394807760212, 28650013862, 0, 0] := by
  decide +kernel

theorem rows6182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6182 = true := by
  decide +kernel

theorem tot6182 : totK PA10K2 A10K2.t6182 = [0, 477466364302, 1777277443087, 1962211755820, 562032360536, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6183 = true := by
  decide +kernel

theorem tot6183 : totK PA10K2 A10K2.t6183 = [0, 147954321173, 1035615571017, 2046392081532, 1307965707710, 271472211373, 20070762815, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
