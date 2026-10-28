import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t132 = true := by
  decide +kernel

theorem tot132 : totK PA10K2 A10K2.t132 = [0, 380656640335, 1647440257501, 2027256113290, 650456384611, 39719428504, 0, 0, 0, 0] := by
  decide +kernel

theorem rows133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t133 = true := by
  decide +kernel

theorem tot133 : totK PA10K2 A10K2.t133 = [0, 0, 464351305361, 1775266116924, 1797581886814, 453300830313, 31003444686, 0, 0, 0] := by
  decide +kernel

theorem rows134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t134 = true := by
  decide +kernel

theorem tot134 : totK PA10K2 A10K2.t134 = [0, 512186877898, 1754477959221, 1785034611378, 510095103425, 40667894091, 0, 0, 0, 0] := by
  decide +kernel

theorem rows135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t135 = true := by
  decide +kernel

theorem tot135 : totK PA10K2 A10K2.t135 = [0, 308170643447, 1502375188868, 2050192913607, 772472450839, 59494161816, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
