import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10056 = true := by
  decide +kernel

theorem tot10056 : totK PD2M8K2 D2M8K2.t10056 = [0, 0, 156768896951, 389460753181, 289551963401, 76437762137, 1415142070, 0] := by
  decide +kernel

theorem rows10057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10057 = true := by
  decide +kernel

theorem tot10057 : totK PD2M8K2 D2M8K2.t10057 = [0, 0, 171636277593, 456055700815, 255684884916, 16629120796, 0, 0] := by
  decide +kernel

theorem rows10058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10058 = true := by
  decide +kernel

theorem tot10058 : totK PD2M8K2 D2M8K2.t10058 = [0, 0, 92515481918, 421394815988, 359093578882, 42097109024, 0, 0] := by
  decide +kernel

theorem rows10059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10059 = true := by
  decide +kernel

theorem tot10059 : totK PD2M8K2 D2M8K2.t10059 = [0, 0, 0, 222835276263, 502751129222, 148586555377, 2484078857, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
