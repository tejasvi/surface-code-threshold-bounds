import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2800 = true := by
  decide +kernel

theorem tot2800 : totK PD2M8K2 D2M8K2.t2800 = [40212644391, 319533490966, 445748773632, 93159961863, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows2801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2801 = true := by
  decide +kernel

theorem tot2801 : totK PD2M8K2 D2M8K2.t2801 = [0, 200618715806, 471082821418, 187594557251, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows2802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2802 = true := by
  decide +kernel

theorem tot2802 : totK PD2M8K2 D2M8K2.t2802 = [153659183205, 432665874419, 276213481984, 37265414580, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2803 = true := by
  decide +kernel

theorem tot2803 : totK PD2M8K2 D2M8K2.t2803 = [179705430958, 441391880943, 250768245402, 21400225618, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
