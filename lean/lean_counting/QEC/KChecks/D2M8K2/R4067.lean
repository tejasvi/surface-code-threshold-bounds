import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16268 = true := by
  decide +kernel

theorem tot16268 : totK PD2M8K2 D2M8K2.t16268 = [0, 0, 190607105505, 471889966870, 235801617589, 13538525587, 0, 0] := by
  decide +kernel

theorem rows16269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16269 = true := by
  decide +kernel

theorem tot16269 : totK PD2M8K2 D2M8K2.t16269 = [0, 0, 114681327135, 443524609884, 325560081563, 35434258357, 0, 0] := by
  decide +kernel

theorem rows16270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16270 = true := by
  decide +kernel

theorem tot16270 : totK PD2M8K2 D2M8K2.t16270 = [0, 0, 0, 186748097593, 480587971642, 223881337768, 17176308936, 0] := by
  decide +kernel

theorem rows16271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16271 = true := by
  decide +kernel

theorem tot16271 : totK PD2M8K2 D2M8K2.t16271 = [0, 0, 67008747100, 257694586157, 393426902887, 177115787715, 8340560233, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
