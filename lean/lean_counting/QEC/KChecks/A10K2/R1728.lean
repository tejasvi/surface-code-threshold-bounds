import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6912 = true := by
  decide +kernel

theorem tot6912 : totK PA10K2 A10K2.t6912 = [0, 0, 117873321971, 561302128230, 1557563581350, 1961567827802, 705169086215, 55043167628, 0, 0] := by
  decide +kernel

theorem rows6913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6913 = true := by
  decide +kernel

theorem tot6913 : totK PA10K2 A10K2.t6913 = [0, 0, 437011931680, 1775909175282, 1913088261032, 474681038118, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows6914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6914 = true := by
  decide +kernel

theorem tot6914 : totK PA10K2 A10K2.t6914 = [0, 0, 292098887399, 1390920682287, 2170191109435, 1052952444534, 85998451798, 0, 0, 0] := by
  decide +kernel

theorem rows6915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6915 = true := by
  decide +kernel

theorem tot6915 : totK PA10K2 A10K2.t6915 = [0, 0, 0, 524502419547, 1844425434986, 1710083281193, 467951952927, 30831673886, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
