import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10508 = true := by
  decide +kernel

theorem tot10508 : totK PD2M8K2 D2M8K2.t10508 = [0, 191561561879, 476776108432, 224827722212, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows10509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10509 = true := by
  decide +kernel

theorem tot10509 : totK PD2M8K2 D2M8K2.t10509 = [0, 47545149827, 314590264970, 437949352436, 93067984182, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10510 = true := by
  decide +kernel

theorem tot10510 : totK PD2M8K2 D2M8K2.t10510 = [0, 0, 196940174883, 471382138131, 193414953512, 12052611869, 0, 0] := by
  decide +kernel

theorem rows10511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10511 = true := by
  decide +kernel

theorem tot10511 : totK PD2M8K2 D2M8K2.t10511 = [0, 159329899136, 442143952026, 268129357410, 35820105431, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
