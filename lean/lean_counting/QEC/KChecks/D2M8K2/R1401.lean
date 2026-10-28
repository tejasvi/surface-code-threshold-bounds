import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5604 = true := by
  decide +kernel

theorem tot5604 : totK PD2M8K2 D2M8K2.t5604 = [171401420081, 445314238709, 247269791067, 18197172049, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5605 = true := by
  decide +kernel

theorem tot5605 : totK PD2M8K2 D2M8K2.t5605 = [70729578721, 335020850656, 384387505696, 86963302652, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows5606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5606 = true := by
  decide +kernel

theorem tot5606 : totK PD2M8K2 D2M8K2.t5606 = [4294967296, 324700890568, 507019377259, 66353243491, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5607 = true := by
  decide +kernel

theorem tot5607 : totK PD2M8K2 D2M8K2.t5607 = [168917789913, 443486935910, 280370007031, 30363365770, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
