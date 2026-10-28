import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13296 = true := by
  decide +kernel

theorem tot13296 : totK PD2M8K2 D2M8K2.t13296 = [0, 0, 205578367093, 499545419245, 184783075748, 9587713104, 0, 0] := by
  decide +kernel

theorem rows13297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13297 = true := by
  decide +kernel

theorem tot13297 : totK PD2M8K2 D2M8K2.t13297 = [0, 84547450418, 324556877759, 371188749481, 97240546190, 3462014130, 0, 0] := by
  decide +kernel

theorem rows13298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13298 = true := by
  decide +kernel

theorem tot13298 : totK PD2M8K2 D2M8K2.t13298 = [0, 176853009588, 457208955851, 262818164325, 26328259923, 0, 0, 0] := by
  decide +kernel

theorem rows13299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13299 = true := by
  decide +kernel

theorem tot13299 : totK PD2M8K2 D2M8K2.t13299 = [0, 163431418577, 466662693404, 249332509179, 16440203113, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
