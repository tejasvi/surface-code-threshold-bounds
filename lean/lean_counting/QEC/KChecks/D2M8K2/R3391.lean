import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13564 = true := by
  decide +kernel

theorem tot13564 : totK PD2M8K2 D2M8K2.t13564 = [0, 0, 200666284975, 449069384991, 184085160158, 11853261585, 0, 0] := by
  decide +kernel

theorem rows13565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13565 = true := by
  decide +kernel

theorem tot13565 : totK PD2M8K2 D2M8K2.t13565 = [0, 149685247596, 443154312964, 281659243920, 24576434179, 0, 0, 0] := by
  decide +kernel

theorem rows13566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13566 = true := by
  decide +kernel

theorem tot13566 : totK PD2M8K2 D2M8K2.t13566 = [0, 208120984955, 455260473431, 202900923395, 13468795916, 0, 0, 0] := by
  decide +kernel

theorem rows13567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13567 = true := by
  decide +kernel

theorem tot13567 : totK PD2M8K2 D2M8K2.t13567 = [0, 19168557488, 329116485466, 431538629789, 69521936080, 1021600638, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
