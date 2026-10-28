import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4884 = true := by
  decide +kernel

theorem tot4884 : totK PA10K2 A10K2.t4884 = [0, 0, 457006179772, 1780612022988, 1922782964729, 504748473774, 31756067336, 0, 0, 0] := by
  decide +kernel

theorem rows4885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4885 = true := by
  decide +kernel

theorem tot4885 : totK PA10K2 A10K2.t4885 = [0, 0, 682430224060, 2166667537859, 1695428745791, 291001060054, 6795308320, 0, 0, 0] := by
  decide +kernel

theorem rows4886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4886 = true := by
  decide +kernel

theorem tot4886 : totK PA10K2 A10K2.t4886 = [0, 0, 513419612032, 1849339402380, 1835416262906, 464962542774, 30973630058, 0, 0, 0] := by
  decide +kernel

theorem rows4887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4887 = true := by
  decide +kernel

theorem tot4887 : totK PA10K2 A10K2.t4887 = [0, 0, 298252571475, 1581431582927, 2054781833176, 628919383922, 38031574496, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
