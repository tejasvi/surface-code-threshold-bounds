import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1340 = true := by
  decide +kernel

theorem tot1340 : totK PD2M8K2 D2M8K2.t1340 = [0, 196441072689, 475134287801, 227429823322, 14512002466, 0, 0, 0] := by
  decide +kernel

theorem rows1341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1341 = true := by
  decide +kernel

theorem tot1341 : totK PD2M8K2 D2M8K2.t1341 = [0, 185554183975, 453021222145, 241557627499, 20707750022, 0, 0, 0] := by
  decide +kernel

theorem rows1342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1342 = true := by
  decide +kernel

theorem tot1342 : totK PD2M8K2 D2M8K2.t1342 = [0, 177465433587, 466736514881, 229368108087, 13266325470, 0, 0, 0] := by
  decide +kernel

theorem rows1343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1343 = true := by
  decide +kernel

theorem tot1343 : totK PD2M8K2 D2M8K2.t1343 = [0, 0, 301281729870, 488725055648, 86451675177, 1075657031, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
