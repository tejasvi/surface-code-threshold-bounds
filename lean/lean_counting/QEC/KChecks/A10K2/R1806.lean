import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7224 = true := by
  decide +kernel

theorem tot7224 : totK PA10K2 A10K2.t7224 = [0, 0, 446934158437, 1655344325604, 1973858014997, 718092008844, 58003447868, 0, 0, 0] := by
  decide +kernel

theorem rows7225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7225 = true := by
  decide +kernel

theorem tot7225 : totK PA10K2 A10K2.t7225 = [0, 0, 71325059078, 985378280220, 2133518734030, 1166630570059, 148737352566, 0, 0, 0] := by
  decide +kernel

theorem rows7226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7226 = true := by
  decide +kernel

theorem tot7226 : totK PA10K2 A10K2.t7226 = [0, 0, 606824596561, 1989051520884, 1946999406983, 508579972910, 65343835037, 5546304973, 0, 0] := by
  decide +kernel

theorem rows7227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7227 = true := by
  decide +kernel

theorem tot7227 : totK PA10K2 A10K2.t7227 = [0, 305030648051, 1089622281978, 1618431776243, 1455710666610, 556150476393, 50548650670, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
