import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6332 = true := by
  decide +kernel

theorem tot6332 : totK PD2M8K2 D2M8K2.t6332 = [0, 164616039915, 354029299401, 290780375754, 113550105848, 8859721110, 0, 0] := by
  decide +kernel

theorem rows6333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6333 = true := by
  decide +kernel

theorem tot6333 : totK PD2M8K2 D2M8K2.t6333 = [0, 186872049228, 472342715903, 233717997005, 13678200943, 0, 0, 0] := by
  decide +kernel

theorem rows6334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6334 = true := by
  decide +kernel

theorem tot6334 : totK PD2M8K2 D2M8K2.t6334 = [0, 88995923185, 403625414027, 375815083232, 53951814101, 0, 0, 0] := by
  decide +kernel

theorem rows6335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6335 = true := by
  decide +kernel

theorem tot6335 : totK PD2M8K2 D2M8K2.t6335 = [0, 0, 172213605309, 448005209913, 257871002928, 25373788367, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
