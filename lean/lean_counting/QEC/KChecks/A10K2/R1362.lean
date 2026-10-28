import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5448 = true := by
  decide +kernel

theorem tot5448 : totK PA10K2 A10K2.t5448 = [0, 146919968670, 1078122591805, 2009673663228, 1312463113906, 288684675249, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5449 = true := by
  decide +kernel

theorem tot5449 : totK PA10K2 A10K2.t5449 = [0, 276491011440, 1187746433388, 1920802725769, 1189146280023, 178342460783, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5450 = true := by
  decide +kernel

theorem tot5450 : totK PA10K2 A10K2.t5450 = [0, 502204280108, 1783756316714, 1875729456824, 621194829475, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5451 = true := by
  decide +kernel

theorem tot5451 : totK PA10K2 A10K2.t5451 = [0, 0, 980216254634, 2448712910155, 1221675636960, 107172403957, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
