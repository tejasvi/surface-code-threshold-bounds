import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14356 = true := by
  decide +kernel

theorem tot14356 : totK PD2M8K2 D2M8K2.t14356 = [0, 154819160950, 447993228064, 278029889632, 29716626810, 0, 0, 0] := by
  decide +kernel

theorem rows14357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14357 = true := by
  decide +kernel

theorem tot14357 : totK PD2M8K2 D2M8K2.t14357 = [0, 89994084580, 359903463206, 350976568359, 56920453530, 1062926506, 0, 0] := by
  decide +kernel

theorem rows14358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14358 = true := by
  decide +kernel

theorem tot14358 : totK PD2M8K2 D2M8K2.t14358 = [0, 0, 296285246725, 510363198076, 89871493044, 1037250189, 0, 0] := by
  decide +kernel

theorem rows14359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14359 = true := by
  decide +kernel

theorem tot14359 : totK PD2M8K2 D2M8K2.t14359 = [0, 173041957571, 421632749350, 246743880693, 53566449591, 2746131708, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
