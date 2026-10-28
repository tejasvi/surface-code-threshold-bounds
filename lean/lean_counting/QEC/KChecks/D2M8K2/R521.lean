import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2084 = true := by
  decide +kernel

theorem tot2084 : totK PD2M8K2 D2M8K2.t2084 = [0, 160859056123, 459481621961, 274609342942, 20372157838, 0, 0, 0] := by
  decide +kernel

theorem rows2085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2085 = true := by
  decide +kernel

theorem tot2085 : totK PD2M8K2 D2M8K2.t2085 = [0, 0, 234135075996, 505549420574, 148566830189, 2348440009, 0, 0] := by
  decide +kernel

theorem rows2086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2086 = true := by
  decide +kernel

theorem tot2086 : totK PD2M8K2 D2M8K2.t2086 = [0, 86458299975, 278564314854, 368036294904, 143681382454, 10895344854, 0, 0] := by
  decide +kernel

theorem rows2087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2087 = true := by
  decide +kernel

theorem tot2087 : totK PD2M8K2 D2M8K2.t2087 = [0, 171397378636, 466389874073, 254210962237, 22435143705, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
