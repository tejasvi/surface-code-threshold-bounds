import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6984 = true := by
  decide +kernel

theorem tot6984 : totK PA10K2 A10K2.t6984 = [0, 0, 496604236678, 1874420062231, 2001774411089, 569786296014, 32317336324, 0, 0, 0] := by
  decide +kernel

theorem rows6985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6985 = true := by
  decide +kernel

theorem tot6985 : totK PA10K2 A10K2.t6985 = [0, 0, 0, 605225644109, 2196987922469, 1930991654504, 350056137856, 6962742351, 0, 0] := by
  decide +kernel

theorem rows6986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6986 = true := by
  decide +kernel

theorem tot6986 : totK PA10K2 A10K2.t6986 = [0, 0, 0, 624245015668, 1953459097438, 1828167303606, 515489726354, 34099770725, 0, 0] := by
  decide +kernel

theorem rows6987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6987 = true := by
  decide +kernel

theorem tot6987 : totK PA10K2 A10K2.t6987 = [0, 0, 0, 520096900792, 1774310821971, 1826958420030, 520771836459, 32070512872, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
