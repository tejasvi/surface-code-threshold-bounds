import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2732 = true := by
  decide +kernel

theorem tot2732 : totK PA10K2 A10K2.t2732 = [0, 0, 307739496603, 1510499112715, 2091293591025, 706701124547, 51402059204, 0, 0, 0] := by
  decide +kernel

theorem rows2733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2733 = true := by
  decide +kernel

theorem tot2733 : totK PA10K2 A10K2.t2733 = [0, 0, 156758555584, 986163824341, 1978210642217, 1263733055346, 239904770714, 6354482628, 0, 0] := by
  decide +kernel

theorem rows2734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2734 = true := by
  decide +kernel

theorem tot2734 : totK PA10K2 A10K2.t2734 = [0, 0, 415013008705, 1716745725219, 1951769479145, 550196265566, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows2735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2735 = true := by
  decide +kernel

theorem tot2735 : totK PA10K2 A10K2.t2735 = [0, 0, 187747219659, 1049126007738, 1961015225545, 1277610248322, 284449603478, 24941563133, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
