import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2552 = true := by
  decide +kernel

theorem tot2552 : totK PD2M8K2 D2M8K2.t2552 = [180823914976, 448082188649, 272415887374, 29782082599, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2553 = true := by
  decide +kernel

theorem tot2553 : totK PD2M8K2 D2M8K2.t2553 = [180448964665, 471778453911, 242395697602, 14827214149, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2554 = true := by
  decide +kernel

theorem tot2554 : totK PD2M8K2 D2M8K2.t2554 = [65600037915, 291863958149, 358895795800, 175888224072, 21396654552, 0, 0, 0] := by
  decide +kernel

theorem rows2555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2555 = true := by
  decide +kernel

theorem tot2555 : totK PD2M8K2 D2M8K2.t2555 = [0, 197013576261, 487123170533, 209186446075, 7994456143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
