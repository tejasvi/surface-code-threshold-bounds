import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10968 = true := by
  decide +kernel

theorem tot10968 : totK PD2M8K2 D2M8K2.t10968 = [0, 181184583598, 466474209636, 230347124296, 13757628116, 0, 0, 0] := by
  decide +kernel

theorem rows10969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10969 = true := by
  decide +kernel

theorem tot10969 : totK PD2M8K2 D2M8K2.t10969 = [0, 171835959905, 464641399579, 231857702422, 12886908819, 0, 0, 0] := by
  decide +kernel

theorem rows10970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10970 = true := by
  decide +kernel

theorem tot10970 : totK PD2M8K2 D2M8K2.t10970 = [0, 187831149894, 475189002437, 209985551154, 9757737807, 0, 0, 0] := by
  decide +kernel

theorem rows10971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10971 = true := by
  decide +kernel

theorem tot10971 : totK PD2M8K2 D2M8K2.t10971 = [0, 197414826819, 468347698670, 209871444425, 12403393969, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
