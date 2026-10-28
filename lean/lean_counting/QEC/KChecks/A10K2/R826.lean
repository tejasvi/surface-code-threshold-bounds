import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3304 = true := by
  decide +kernel

theorem tot3304 : totK PA10K2 A10K2.t3304 = [0, 0, 477601264476, 1816607923438, 1882422308109, 490122756873, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows3305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3305 = true := by
  decide +kernel

theorem tot3305 : totK PA10K2 A10K2.t3305 = [0, 0, 135647698596, 916000880267, 2086471281468, 1257738359805, 181345609191, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3306 = true := by
  decide +kernel

theorem tot3306 : totK PA10K2 A10K2.t3306 = [0, 0, 446672217090, 1800130407305, 1991023089899, 529432095918, 26491486257, 0, 0, 0] := by
  decide +kernel

theorem rows3307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3307 = true := by
  decide +kernel

theorem tot3307 : totK PA10K2 A10K2.t3307 = [0, 0, 186511936084, 1040151569527, 1943088536659, 1337977060558, 297346357009, 24969229125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
