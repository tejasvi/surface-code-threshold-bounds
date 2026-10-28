import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8416 = true := by
  decide +kernel

theorem tot8416 : totK PD2M8K2 D2M8K2.t8416 = [0, 0, 204576044302, 478036625280, 178504224204, 7785776211, 0, 0] := by
  decide +kernel

theorem rows8417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8417 = true := by
  decide +kernel

theorem tot8417 : totK PD2M8K2 D2M8K2.t8417 = [0, 160713320421, 365523572069, 246179586614, 113146647318, 13269537371, 0, 0] := by
  decide +kernel

theorem rows8418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8418 = true := by
  decide +kernel

theorem tot8418 : totK PD2M8K2 D2M8K2.t8418 = [0, 168854529408, 442851225014, 239747799953, 18072764109, 0, 0, 0] := by
  decide +kernel

theorem rows8419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8419 = true := by
  decide +kernel

theorem tot8419 : totK PD2M8K2 D2M8K2.t8419 = [0, 85777508425, 372752450322, 356118788326, 69181984678, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
