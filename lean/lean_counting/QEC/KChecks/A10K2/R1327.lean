import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5308 = true := by
  decide +kernel

theorem tot5308 : totK PA10K2 A10K2.t5308 = [0, 0, 377659829977, 1643652147426, 2092954444068, 673339752545, 39719428504, 0, 0, 0] := by
  decide +kernel

theorem rows5309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5309 = true := by
  decide +kernel

theorem tot5309 : totK PA10K2 A10K2.t5309 = [0, 0, 0, 484578399460, 1835342480463, 1788664241506, 453300830313, 31003444686, 0, 0] := by
  decide +kernel

theorem rows5310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5310 = true := by
  decide +kernel

theorem tot5310 : totK PA10K2 A10K2.t5310 = [0, 0, 527726960312, 1817396628330, 1834680454004, 497694311793, 35277947640, 0, 0, 0] := by
  decide +kernel

theorem rows5311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5311 = true := by
  decide +kernel

theorem tot5311 : totK PA10K2 A10K2.t5311 = [0, 0, 308170643447, 1500648188004, 2082743899367, 783466151806, 59494161816, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
