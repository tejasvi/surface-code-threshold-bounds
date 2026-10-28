import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5640 = true := by
  decide +kernel

theorem tot5640 : totK PA10K2 A10K2.t5640 = [0, 0, 455284613437, 1764452743135, 2071025903791, 674951827170, 42870841294, 0, 0, 0] := by
  decide +kernel

theorem rows5641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5641 = true := by
  decide +kernel

theorem tot5641 : totK PA10K2 A10K2.t5641 = [0, 0, 440108546096, 1782123195803, 1957551250262, 541950840830, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows5642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5642 = true := by
  decide +kernel

theorem tot5642 : totK PA10K2 A10K2.t5642 = [0, 0, 246572654185, 1263581266971, 2069512679873, 1125865646466, 145494059389, 0, 0, 0] := by
  decide +kernel

theorem rows5643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5643 = true := by
  decide +kernel

theorem tot5643 : totK PA10K2 A10K2.t5643 = [0, 0, 73017544754, 677251271056, 1817777381503, 1607091250005, 408262618773, 31082886609, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
