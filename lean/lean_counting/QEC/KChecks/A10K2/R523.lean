import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2092 = true := by
  decide +kernel

theorem tot2092 : totK PA10K2 A10K2.t2092 = [0, 494410525705, 1811968898575, 1946095747534, 578539476151, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2093 = true := by
  decide +kernel

theorem tot2093 : totK PA10K2 A10K2.t2093 = [0, 0, 747793971910, 2131172904524, 1634841008503, 384522673028, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2094 = true := by
  decide +kernel

theorem tot2094 : totK PA10K2 A10K2.t2094 = [0, 195420298816, 974903324805, 1802004232585, 1365851273962, 239812395224, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2095 = true := by
  decide +kernel

theorem tot2095 : totK PA10K2 A10K2.t2095 = [0, 579089448452, 1867980208850, 1791928405637, 525441855681, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
