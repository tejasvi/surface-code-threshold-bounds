import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15452 = true := by
  decide +kernel

theorem tot15452 : totK PD2M8K2 D2M8K2.t15452 = [0, 172364711392, 439082251217, 272906658857, 30343566252, 0, 0, 0] := by
  decide +kernel

theorem rows15453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15453 = true := by
  decide +kernel

theorem tot15453 : totK PD2M8K2 D2M8K2.t15453 = [0, 143387218865, 458444340335, 274717654012, 18721956145, 0, 0, 0] := by
  decide +kernel

theorem rows15454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15454 = true := by
  decide +kernel

theorem tot15454 : totK PD2M8K2 D2M8K2.t15454 = [0, 0, 331549147297, 518115300096, 74650789895, 0, 0, 0] := by
  decide +kernel

theorem rows15455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15455 = true := by
  decide +kernel

theorem tot15455 : totK PD2M8K2 D2M8K2.t15455 = [0, 0, 182069284900, 452084254611, 258278666848, 25815485168, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
