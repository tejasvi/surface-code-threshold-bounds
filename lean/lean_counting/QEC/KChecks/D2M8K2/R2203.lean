import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8812 = true := by
  decide +kernel

theorem tot8812 : totK PD2M8K2 D2M8K2.t8812 = [0, 167315818089, 450194616034, 271590896595, 37563101424, 0, 0, 0] := by
  decide +kernel

theorem rows8813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8813 = true := by
  decide +kernel

theorem tot8813 : totK PD2M8K2 D2M8K2.t8813 = [0, 163960185887, 451436754060, 268093737077, 20101845775, 0, 0, 0] := by
  decide +kernel

theorem rows8814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8814 = true := by
  decide +kernel

theorem tot8814 : totK PD2M8K2 D2M8K2.t8814 = [0, 85687109263, 344505519914, 388162530148, 86174194389, 1162515529, 0, 0] := by
  decide +kernel

theorem rows8815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8815 = true := by
  decide +kernel

theorem tot8815 : totK PD2M8K2 D2M8K2.t8815 = [0, 0, 212882903284, 484262757168, 178727891801, 8017271805, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
