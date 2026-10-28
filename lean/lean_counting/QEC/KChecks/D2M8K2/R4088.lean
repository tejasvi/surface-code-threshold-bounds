import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16352 = true := by
  decide +kernel

theorem tot16352 : totK PD2M8K2 D2M8K2.t16352 = [0, 0, 0, 197320311313, 473973094193, 218857244612, 16877058464, 0] := by
  decide +kernel

theorem rows16353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16353 = true := by
  decide +kernel

theorem tot16353 : totK PD2M8K2 D2M8K2.t16353 = [0, 0, 18444143370, 215256622497, 474510741105, 192749343657, 8340560233, 0] := by
  decide +kernel

theorem rows16354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16354 = true := by
  decide +kernel

theorem tot16354 : totK PD2M8K2 D2M8K2.t16354 = [0, 0, 179460031406, 458775324664, 240887545563, 22467562413, 0, 0] := by
  decide +kernel

theorem rows16355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16355 = true := by
  decide +kernel

theorem tot16355 : totK PD2M8K2 D2M8K2.t16355 = [0, 0, 211511906904, 482846713071, 194774718591, 9152607109, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
