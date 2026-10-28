import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2124 = true := by
  decide +kernel

theorem tot2124 : totK PD2M8K2 D2M8K2.t2124 = [0, 55861247081, 325756706046, 419859321190, 91739392543, 1268739303, 0, 0] := by
  decide +kernel

theorem rows2125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2125 = true := by
  decide +kernel

theorem tot2125 : totK PD2M8K2 D2M8K2.t2125 = [0, 0, 203752965989, 485043681538, 178117776244, 7442000727, 0, 0] := by
  decide +kernel

theorem rows2126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2126 = true := by
  decide +kernel

theorem tot2126 : totK PD2M8K2 D2M8K2.t2126 = [0, 0, 178379215039, 463647646842, 227690161790, 15860424110, 0, 0] := by
  decide +kernel

theorem rows2127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2127 = true := by
  decide +kernel

theorem tot2127 : totK PD2M8K2 D2M8K2.t2127 = [0, 0, 173455847626, 455205908811, 223054049105, 16561712910, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
