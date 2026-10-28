import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8068 = true := by
  decide +kernel

theorem tot8068 : totK PA10K2 A10K2.t8068 = [0, 0, 281949883425, 1205020073920, 1855183975951, 1259704629130, 227636526351, 6356241174, 0, 0] := by
  decide +kernel

theorem rows8069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8069 = true := by
  decide +kernel

theorem tot8069 : totK PA10K2 A10K2.t8069 = [0, 0, 306766947263, 1509260220532, 2220694658492, 915057976807, 70028841574, 0, 0, 0] := by
  decide +kernel

theorem rows8070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8070 = true := by
  decide +kernel

theorem tot8070 : totK PA10K2 A10K2.t8070 = [0, 0, 308574149355, 1200694488438, 1885757804025, 1330409553578, 294210941339, 12462147902, 0, 0] := by
  decide +kernel

theorem rows8071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8071 = true := by
  decide +kernel

theorem tot8071 : totK PA10K2 A10K2.t8071 = [0, 0, 487680674989, 1843644765520, 2027296515781, 544307470191, 26212230095, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
