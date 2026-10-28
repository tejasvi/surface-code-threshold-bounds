import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9324 = true := by
  decide +kernel

theorem tot9324 : totK PD2M8K2 D2M8K2.t9324 = [0, 173789758966, 449591408725, 247436234429, 18197172049, 0, 0, 0] := by
  decide +kernel

theorem rows9325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9325 = true := by
  decide +kernel

theorem tot9325 : totK PD2M8K2 D2M8K2.t9325 = [0, 82226460504, 361262336115, 362870074530, 74343980058, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9326 = true := by
  decide +kernel

theorem tot9326 : totK PD2M8K2 D2M8K2.t9326 = [0, 0, 317072380136, 505512242439, 70040917439, 0, 0, 0] := by
  decide +kernel

theorem rows9327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9327 = true := by
  decide +kernel

theorem tot9327 : totK PD2M8K2 D2M8K2.t9327 = [0, 194114593336, 456958737309, 235667268693, 19980652151, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
