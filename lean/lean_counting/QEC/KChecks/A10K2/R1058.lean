import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4232 = true := by
  decide +kernel

theorem tot4232 : totK PA10K2 A10K2.t4232 = [0, 421501596606, 1586629646021, 1996860178066, 822329677556, 74832387466, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4233 = true := by
  decide +kernel

theorem tot4233 : totK PA10K2 A10K2.t4233 = [0, 420834055255, 1772027352584, 2041303411480, 583646823017, 34548791282, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4234 = true := by
  decide +kernel

theorem tot4234 : totK PA10K2 A10K2.t4234 = [0, 0, 461417741280, 1794799305024, 1791201510808, 436968260938, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows4235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4235 = true := by
  decide +kernel

theorem tot4235 : totK PA10K2 A10K2.t4235 = [0, 418471038443, 1644559632366, 1981323015606, 745167651543, 103088633770, 5410721913, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
