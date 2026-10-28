import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7276 = true := by
  decide +kernel

theorem tot7276 : totK PD2M8K2 D2M8K2.t7276 = [0, 0, 18439672747, 311902478085, 477822336761, 90282497782, 1409560813, 0] := by
  decide +kernel

theorem rows7277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7277 = true := by
  decide +kernel

theorem tot7277 : totK PD2M8K2 D2M8K2.t7277 = [0, 0, 186445188045, 464600313616, 236986724285, 15643007786, 0, 0] := by
  decide +kernel

theorem rows7278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7278 = true := by
  decide +kernel

theorem tot7278 : totK PD2M8K2 D2M8K2.t7278 = [0, 0, 193137474763, 476657801852, 217380335904, 12373752831, 0, 0] := by
  decide +kernel

theorem rows7279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7279 = true := by
  decide +kernel

theorem tot7279 : totK PD2M8K2 D2M8K2.t7279 = [0, 0, 10120087008, 302764645565, 473883138014, 91238815240, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
