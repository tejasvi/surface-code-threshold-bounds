import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2992 = true := by
  decide +kernel

theorem tot2992 : totK PD2M8K2 D2M8K2.t2992 = [0, 94308027437, 309834108751, 374259655288, 140345540349, 8859721110, 0, 0] := by
  decide +kernel

theorem rows2993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2993 = true := by
  decide +kernel

theorem tot2993 : totK PD2M8K2 D2M8K2.t2993 = [0, 174048464485, 458096541605, 274884271498, 18878258857, 0, 0, 0] := by
  decide +kernel

theorem rows2994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2994 = true := by
  decide +kernel

theorem tot2994 : totK PD2M8K2 D2M8K2.t2994 = [0, 176358198303, 473426754856, 247665217687, 13060942370, 0, 0, 0] := by
  decide +kernel

theorem rows2995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2995 = true := by
  decide +kernel

theorem tot2995 : totK PD2M8K2 D2M8K2.t2995 = [0, 0, 208116981280, 469370539423, 220660947836, 21400436502, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
