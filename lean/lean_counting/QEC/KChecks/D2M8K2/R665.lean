import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2660 = true := by
  decide +kernel

theorem tot2660 : totK PD2M8K2 D2M8K2.t2660 = [0, 0, 0, 220908739042, 498746474234, 142168610091, 2437267027, 0] := by
  decide +kernel

theorem rows2661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2661 = true := by
  decide +kernel

theorem tot2661 : totK PD2M8K2 D2M8K2.t2661 = [0, 159221153091, 335783779590, 146558752427, 149187418567, 88424503295, 6701800220, 0] := by
  decide +kernel

theorem rows2662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2662 = true := by
  decide +kernel

theorem tot2662 : totK PD2M8K2 D2M8K2.t2662 = [0, 163632999621, 453945161651, 247767096319, 15032356213, 0, 0, 0] := by
  decide +kernel

theorem rows2663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2663 = true := by
  decide +kernel

theorem tot2663 : totK PD2M8K2 D2M8K2.t2663 = [0, 0, 297463520368, 489759444703, 90299427793, 1275377855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
