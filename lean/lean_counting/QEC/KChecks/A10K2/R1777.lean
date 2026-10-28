import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7108 = true := by
  decide +kernel

theorem tot7108 : totK PA10K2 A10K2.t7108 = [0, 251956656316, 1339837331094, 1999092308313, 1016514935079, 164798217269, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows7109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7109 = true := by
  decide +kernel

theorem tot7109 : totK PA10K2 A10K2.t7109 = [0, 451939543529, 1464819804856, 1728627916693, 959427025234, 168626083080, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows7110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7110 = true := by
  decide +kernel

theorem tot7110 : totK PA10K2 A10K2.t7110 = [0, 290480228743, 1476963261297, 2050011899974, 729323178947, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7111 = true := by
  decide +kernel

theorem tot7111 : totK PA10K2 A10K2.t7111 = [0, 0, 704162308172, 2082119236684, 1558744584192, 269313011847, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
