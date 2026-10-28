import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12160 = true := by
  decide +kernel

theorem tot12160 : totK PD2M8K2 D2M8K2.t12160 = [0, 171666082890, 422487896320, 233144753418, 67599719226, 5618966238, 0, 0] := by
  decide +kernel

theorem rows12161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12161 = true := by
  decide +kernel

theorem tot12161 : totK PD2M8K2 D2M8K2.t12161 = [0, 181088653291, 449138841560, 249756823089, 18200164543, 0, 0, 0] := by
  decide +kernel

theorem rows12162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12162 = true := by
  decide +kernel

theorem tot12162 : totK PD2M8K2 D2M8K2.t12162 = [0, 71819796256, 336254698595, 398472079925, 88543000710, 1198073392, 0, 0] := by
  decide +kernel

theorem rows12163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12163 = true := by
  decide +kernel

theorem tot12163 : totK PD2M8K2 D2M8K2.t12163 = [0, 0, 208864615429, 483180711366, 179508603524, 9460988490, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
