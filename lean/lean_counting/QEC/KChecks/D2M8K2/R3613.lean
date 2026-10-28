import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14452 = true := by
  decide +kernel

theorem tot14452 : totK PD2M8K2 D2M8K2.t14452 = [0, 203660154598, 486118542726, 198182591573, 7727483130, 0, 0, 0] := by
  decide +kernel

theorem rows14453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14453 = true := by
  decide +kernel

theorem tot14453 : totK PD2M8K2 D2M8K2.t14453 = [0, 174134647445, 437610869439, 232028419596, 17940980630, 0, 0, 0] := by
  decide +kernel

theorem rows14454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14454 = true := by
  decide +kernel

theorem tot14454 : totK PD2M8K2 D2M8K2.t14454 = [0, 182538876452, 480041436564, 235137446745, 11192471642, 0, 0, 0] := by
  decide +kernel

theorem rows14455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14455 = true := by
  decide +kernel

theorem tot14455 : totK PD2M8K2 D2M8K2.t14455 = [0, 198539285682, 477058576370, 212662245969, 7870241454, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
