import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16168 = true := by
  decide +kernel

theorem tot16168 : totK PD2M8K2 D2M8K2.t16168 = [0, 189219154771, 488078578833, 221876309561, 11323098214, 0, 0, 0] := by
  decide +kernel

theorem rows16169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16169 = true := by
  decide +kernel

theorem tot16169 : totK PD2M8K2 D2M8K2.t16169 = [0, 0, 239011858002, 453934847517, 199646726706, 21155077365, 0, 0] := by
  decide +kernel

theorem rows16170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16170 = true := by
  decide +kernel

theorem tot16170 : totK PD2M8K2 D2M8K2.t16170 = [0, 0, 167001049317, 485765991776, 236823262081, 6628085040, 0, 0] := by
  decide +kernel

theorem rows16171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16171 = true := by
  decide +kernel

theorem tot16171 : totK PD2M8K2 D2M8K2.t16171 = [0, 120438301973, 346008021113, 315069599605, 115491469396, 8209296672, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
