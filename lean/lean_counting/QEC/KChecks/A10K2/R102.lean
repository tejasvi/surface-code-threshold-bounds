import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t408 = true := by
  decide +kernel

theorem tot408 : totK PA10K2 A10K2.t408 = [0, 380420953409, 1674174149752, 1956200129821, 561486229431, 32744407728, 0, 0, 0, 0] := by
  decide +kernel

theorem rows409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t409 = true := by
  decide +kernel

theorem tot409 : totK PA10K2 A10K2.t409 = [0, 225182653036, 1040613030795, 1960042865679, 1169154782228, 172237192518, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t410 = true := by
  decide +kernel

theorem tot410 : totK PA10K2 A10K2.t410 = [0, 465449925228, 1908577905257, 2203489771779, 638263282481, 32193730877, 0, 0, 0, 0] := by
  decide +kernel

theorem rows411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t411 = true := by
  decide +kernel

theorem tot411 : totK PA10K2 A10K2.t411 = [568825667955, 1696152081796, 1615706598632, 697513974364, 254835644160, 37581533170, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
