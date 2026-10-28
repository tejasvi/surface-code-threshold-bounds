import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8080 = true := by
  decide +kernel

theorem tot8080 : totK PA10K2 A10K2.t8080 = [0, 0, 0, 227410598617, 1276961957211, 2199493425111, 1203766504956, 117295285811, 0, 0] := by
  decide +kernel

theorem rows8081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8081 = true := by
  decide +kernel

theorem tot8081 : totK PA10K2 A10K2.t8081 = [0, 0, 0, 252824012363, 1263877429544, 2012671690937, 1144205965570, 203973077107, 7047025452, 0] := by
  decide +kernel

theorem rows8082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8082 = true := by
  decide +kernel

theorem tot8082 : totK PA10K2 A10K2.t8082 = [0, 0, 0, 615115902947, 2033323522240, 1892252803341, 452577773085, 11925330097, 0, 0] := by
  decide +kernel

theorem rows8083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8083 = true := by
  decide +kernel

theorem tot8083 : totK PA10K2 A10K2.t8083 = [0, 0, 0, 0, 768691476257, 2213759732687, 1639465162895, 255021691159, 6066958478, 0] := by
  decide +kernel

end QECKChecks.A10K2
