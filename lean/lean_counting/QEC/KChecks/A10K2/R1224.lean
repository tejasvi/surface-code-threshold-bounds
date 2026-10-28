import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4896 = true := by
  decide +kernel

theorem tot4896 : totK PA10K2 A10K2.t4896 = [154985961063, 820155799287, 1924816280169, 1528968854324, 290600734112, 11427838733, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4897 = true := by
  decide +kernel

theorem tot4897 : totK PA10K2 A10K2.t4897 = [485040731892, 1738546541804, 1859111592742, 638669610912, 52217710783, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4898 = true := by
  decide +kernel

theorem tot4898 : totK PA10K2 A10K2.t4898 = [108061833447, 1213618300187, 2270357474247, 1035677067674, 86815038553, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4899 = true := by
  decide +kernel

theorem tot4899 : totK PA10K2 A10K2.t4899 = [368063465345, 1369681946654, 1874527488782, 1069983301348, 203680952981, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
