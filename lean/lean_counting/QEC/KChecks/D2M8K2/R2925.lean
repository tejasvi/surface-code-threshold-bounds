import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11700 = true := by
  decide +kernel

theorem tot11700 : totK PD2M8K2 D2M8K2.t11700 = [200265460779, 482863063671, 204021972092, 9845055932, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11701 = true := by
  decide +kernel

theorem tot11701 : totK PD2M8K2 D2M8K2.t11701 = [184679460823, 456846228851, 226000094289, 13762147177, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11702 = true := by
  decide +kernel

theorem tot11702 : totK PD2M8K2 D2M8K2.t11702 = [0, 280131352799, 494464830628, 110348553657, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11703 = true := by
  decide +kernel

theorem tot11703 : totK PD2M8K2 D2M8K2.t11703 = [92632204243, 373574359400, 391910099607, 56513698721, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
