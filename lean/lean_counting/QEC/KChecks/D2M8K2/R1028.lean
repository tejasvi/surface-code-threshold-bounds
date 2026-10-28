import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4112 = true := by
  decide +kernel

theorem tot4112 : totK PD2M8K2 D2M8K2.t4112 = [0, 0, 202145263864, 485419863187, 195255564967, 9934316065, 0, 0] := by
  decide +kernel

theorem rows4113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4113 = true := by
  decide +kernel

theorem tot4113 : totK PD2M8K2 D2M8K2.t4113 = [0, 0, 101405839705, 427567627374, 331101986799, 21463305928, 0, 0] := by
  decide +kernel

theorem rows4114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4114 = true := by
  decide +kernel

theorem tot4114 : totK PD2M8K2 D2M8K2.t4114 = [0, 0, 93391851717, 399768261663, 371406324098, 43728796657, 0, 0] := by
  decide +kernel

theorem rows4115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4115 = true := by
  decide +kernel

theorem tot4115 : totK PD2M8K2 D2M8K2.t4115 = [0, 0, 162136092157, 453097694203, 283549680149, 21301286250, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
