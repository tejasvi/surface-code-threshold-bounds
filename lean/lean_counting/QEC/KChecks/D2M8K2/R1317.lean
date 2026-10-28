import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5268 = true := by
  decide +kernel

theorem tot5268 : totK PD2M8K2 D2M8K2.t5268 = [0, 0, 188741698179, 470527274666, 236878954449, 13768144013, 0, 0] := by
  decide +kernel

theorem rows5269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5269 = true := by
  decide +kernel

theorem tot5269 : totK PD2M8K2 D2M8K2.t5269 = [0, 0, 33873731389, 382224598909, 459051547504, 53364376363, 0, 0] := by
  decide +kernel

theorem rows5270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5270 = true := by
  decide +kernel

theorem tot5270 : totK PD2M8K2 D2M8K2.t5270 = [0, 0, 134749218199, 372556784715, 322361288936, 73802954753, 1415142070, 0] := by
  decide +kernel

theorem rows5271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5271 = true := by
  decide +kernel

theorem tot5271 : totK PD2M8K2 D2M8K2.t5271 = [0, 0, 167018072516, 446052437425, 277299727030, 28444198081, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
