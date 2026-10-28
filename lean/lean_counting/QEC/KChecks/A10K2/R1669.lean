import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6676 = true := by
  decide +kernel

theorem tot6676 : totK PA10K2 A10K2.t6676 = [0, 80722090061, 797000837884, 2130344511716, 1560172166111, 265449272785, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows6677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6677 = true := by
  decide +kernel

theorem tot6677 : totK PA10K2 A10K2.t6677 = [0, 493833116513, 1929223775756, 2035923928378, 575120728585, 31032884205, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6678 = true := by
  decide +kernel

theorem tot6678 : totK PA10K2 A10K2.t6678 = [0, 0, 705742537487, 2205221890608, 1789127691541, 293627697897, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows6679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6679 = true := by
  decide +kernel

theorem tot6679 : totK PA10K2 A10K2.t6679 = [0, 540460088909, 1873835552837, 1899602045982, 597997707977, 49903094792, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
