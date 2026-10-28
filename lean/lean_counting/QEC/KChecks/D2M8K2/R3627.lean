import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14508 = true := by
  decide +kernel

theorem tot14508 : totK PD2M8K2 D2M8K2.t14508 = [102652317539, 349789482118, 339761249911, 90103964737, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows14509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14509 = true := by
  decide +kernel

theorem tot14509 : totK PD2M8K2 D2M8K2.t14509 = [191915983520, 440118301876, 239689825840, 25239411539, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14510 = true := by
  decide +kernel

theorem tot14510 : totK PD2M8K2 D2M8K2.t14510 = [102007566730, 423154057824, 332338409483, 29113022881, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14511 = true := by
  decide +kernel

theorem tot14511 : totK PD2M8K2 D2M8K2.t14511 = [0, 287652096876, 508802772829, 100827635983, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
