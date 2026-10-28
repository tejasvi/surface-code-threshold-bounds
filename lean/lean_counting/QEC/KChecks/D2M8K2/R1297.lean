import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5188 = true := by
  decide +kernel

theorem tot5188 : totK PD2M8K2 D2M8K2.t5188 = [0, 0, 82199135455, 304864110056, 375725266128, 102357300593, 5883432551, 0] := by
  decide +kernel

theorem rows5189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5189 = true := by
  decide +kernel

theorem tot5189 : totK PD2M8K2 D2M8K2.t5189 = [0, 0, 179560464830, 457289117429, 251463921404, 22546616505, 0, 0] := by
  decide +kernel

theorem rows5190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5190 = true := by
  decide +kernel

theorem tot5190 : totK PD2M8K2 D2M8K2.t5190 = [0, 0, 155067496513, 461268279418, 263733873513, 16447485014, 0, 0] := by
  decide +kernel

theorem rows5191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5191 = true := by
  decide +kernel

theorem tot5191 : totK PD2M8K2 D2M8K2.t5191 = [0, 0, 0, 244016168247, 501111205206, 125931886206, 2279498976, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
