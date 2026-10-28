import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t452 = true := by
  decide +kernel

theorem tot452 : totK PA10K2 A10K2.t452 = [0, 203908507248, 1051543029894, 1935574724275, 1379250139738, 345464092022, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t453 = true := by
  decide +kernel

theorem tot453 : totK PA10K2 A10K2.t453 = [0, 227968504973, 1035444878166, 1921288418613, 1356836091465, 225068933673, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t454 = true := by
  decide +kernel

theorem tot454 : totK PA10K2 A10K2.t454 = [0, 277640871317, 1528687424271, 2069791510167, 723340674706, 53860405152, 0, 0, 0, 0] := by
  decide +kernel

theorem rows455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t455 = true := by
  decide +kernel

theorem tot455 : totK PA10K2 A10K2.t455 = [0, 277188877889, 1152461933822, 1855817357335, 1181028521506, 195770755261, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
