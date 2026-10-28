import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14552 = true := by
  decide +kernel

theorem tot14552 : totK PD2M8K2 D2M8K2.t14552 = [0, 161978251187, 439711670421, 285711565319, 30871561252, 0, 0, 0] := by
  decide +kernel

theorem rows14553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14553 = true := by
  decide +kernel

theorem tot14553 : totK PD2M8K2 D2M8K2.t14553 = [0, 174398998991, 483320716291, 227365330527, 14475858478, 0, 0, 0] := by
  decide +kernel

theorem rows14554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14554 = true := by
  decide +kernel

theorem tot14554 : totK PD2M8K2 D2M8K2.t14554 = [0, 187427501115, 470646981770, 226129279567, 11042533554, 0, 0, 0] := by
  decide +kernel

theorem rows14555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14555 = true := by
  decide +kernel

theorem tot14555 : totK PD2M8K2 D2M8K2.t14555 = [0, 181978772450, 464395488408, 249830266312, 18333014298, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
