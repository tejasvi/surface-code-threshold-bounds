import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t212 = true := by
  decide +kernel

theorem tot212 : totK PA10K2 A10K2.t212 = [0, 0, 510607726161, 1961730518247, 2010353102291, 444169564286, 13653259670, 0, 0, 0] := by
  decide +kernel

theorem rows213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t213 = true := by
  decide +kernel

theorem tot213 : totK PA10K2 A10K2.t213 = [0, 0, 421615867255, 1650645733005, 2043419968133, 770935712637, 61177778713, 0, 0, 0] := by
  decide +kernel

theorem rows214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t214 = true := by
  decide +kernel

theorem tot214 : totK PA10K2 A10K2.t214 = [0, 0, 479050269602, 1798210163500, 2022447542424, 670394009942, 50420510388, 0, 0, 0] := by
  decide +kernel

theorem rows215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t215 = true := by
  decide +kernel

theorem tot215 : totK PA10K2 A10K2.t215 = [0, 0, 66902179772, 832200813229, 2226664346233, 1483418155277, 222225963357, 6318667960, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
