import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1956 = true := by
  decide +kernel

theorem tot1956 : totK PA10K2 A10K2.t1956 = [0, 0, 476366589444, 1788523024638, 1925725410451, 624301427165, 48666249715, 0, 0, 0] := by
  decide +kernel

theorem rows1957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1957 = true := by
  decide +kernel

theorem tot1957 : totK PA10K2 A10K2.t1957 = [0, 0, 291018669035, 1443742654771, 2148572067694, 835312470586, 65580985535, 0, 0, 0] := by
  decide +kernel

theorem rows1958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1958 = true := by
  decide +kernel

theorem tot1958 : totK PA10K2 A10K2.t1958 = [0, 0, 537525504914, 1955675874730, 2104358221269, 540445350401, 27069190465, 0, 0, 0] := by
  decide +kernel

theorem rows1959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1959 = true := by
  decide +kernel

theorem tot1959 : totK PA10K2 A10K2.t1959 = [0, 409801074616, 1367492485648, 1552413161185, 1025089516043, 450156469786, 50548650670, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
