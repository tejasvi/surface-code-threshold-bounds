import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14280 = true := by
  decide +kernel

theorem tot14280 : totK PD2M8K2 D2M8K2.t14280 = [0, 180075457386, 440558679018, 274434944500, 34623515837, 0, 0, 0] := by
  decide +kernel

theorem rows14281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14281 = true := by
  decide +kernel

theorem tot14281 : totK PD2M8K2 D2M8K2.t14281 = [0, 200879065639, 480764926043, 222816421912, 9040741374, 0, 0, 0] := by
  decide +kernel

theorem rows14282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14282 = true := by
  decide +kernel

theorem tot14282 : totK PD2M8K2 D2M8K2.t14282 = [0, 191315857900, 472683423650, 224195642254, 14800800293, 0, 0, 0] := by
  decide +kernel

theorem rows14283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14283 = true := by
  decide +kernel

theorem tot14283 : totK PD2M8K2 D2M8K2.t14283 = [0, 163647191780, 445907119489, 272938209575, 27940408362, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
