import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5024 = true := by
  decide +kernel

theorem tot5024 : totK PA10K2 A10K2.t5024 = [0, 294356378534, 1238442105944, 1893797155728, 1097368067774, 162236040066, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5025 = true := by
  decide +kernel

theorem tot5025 : totK PA10K2 A10K2.t5025 = [0, 450717101824, 1760012705954, 1997382355634, 583428257774, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5026 = true := by
  decide +kernel

theorem tot5026 : totK PA10K2 A10K2.t5026 = [0, 0, 638761895571, 2060623964191, 1603116728743, 329532410865, 24969229125, 0, 0, 0] := by
  decide +kernel

theorem rows5027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5027 = true := by
  decide +kernel

theorem tot5027 : totK PA10K2 A10K2.t5027 = [0, 377644818022, 1322259547015, 1770052337019, 1030125159908, 184027137457, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
