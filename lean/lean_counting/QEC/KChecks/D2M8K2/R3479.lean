import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13916 = true := by
  decide +kernel

theorem tot13916 : totK PD2M8K2 D2M8K2.t13916 = [11978940098, 303604573952, 475437149215, 106075523565, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows13917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13917 = true := by
  decide +kernel

theorem tot13917 : totK PD2M8K2 D2M8K2.t13917 = [93610018881, 391478962866, 403118910657, 51688273663, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13918 = true := by
  decide +kernel

theorem tot13918 : totK PD2M8K2 D2M8K2.t13918 = [174769799367, 452907015934, 252857644786, 20907121809, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13919 = true := by
  decide +kernel

theorem tot13919 : totK PD2M8K2 D2M8K2.t13919 = [158242915027, 457497187748, 276604101310, 30913896920, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
